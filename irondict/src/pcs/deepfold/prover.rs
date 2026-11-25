//! DeepFold opening (prover side)

use ark_ff::{Field as _, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use rayon::prelude::*;

use crate::crypto::merkle::{Digest, MerkleMultiProof, MerkleTree};
use crate::crypto::transcript::Transcript;
use crate::pcs::deepfold::commitment::{Commitment, ProverData, derive_deep_point};
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::pcs::deepfold::polynomial::{
    deep_point_powered, fold_coefficients, line_endpoints, line_evaluate,
};
use crate::{Error, Field, Parameters, Result};

/// one folding round: a line for every point we are tracking, and the root of the folded codeword
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundProof {
    pub lines: Vec<(Field, Field)>,
    pub next_root: Option<Digest>,
}

/// an opened leaf, the codeword values at x (positive) and -x (negative)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MultiProofLeaf {
    pub index: usize,
    pub positive: Field,
    pub negative: Field,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RoundMultiProof {
    pub leaves: Vec<MultiProofLeaf>,
    pub authentication: MerkleMultiProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpeningProof {
    pub rounds: Vec<RoundProof>,
    pub final_value: Field,
    pub queries: Vec<RoundMultiProof>,
}

enum Layer<'a> {
    Committed {
        codeword: &'a [Field],
        tree: &'a MerkleTree,
    },
    Folded {
        codeword: Vec<Field>,
        tree: MerkleTree,
    },
}

impl Layer<'_> {
    fn codeword(&self) -> &[Field] {
        match self {
            Self::Committed { codeword, .. } => codeword,
            Self::Folded { codeword, .. } => codeword,
        }
    }

    fn tree(&self) -> &MerkleTree {
        match self {
            Self::Committed { tree, .. } => tree,
            Self::Folded { tree, .. } => tree,
        }
    }
}

pub fn open(
    parameters: &Parameters,
    commitment: &Commitment,
    prover_data: &ProverData,
    point: &[Field],
) -> Result<(Field, OpeningProof)> {
    open_with_config(
        parameters,
        commitment,
        prover_data,
        point,
        &ProverConfig::default(),
    )
}

/// opening with the prover's thread pool, returns f(point) and the proof
pub fn open_with_config(
    parameters: &Parameters,
    commitment: &Commitment,
    prover_data: &ProverData,
    point: &[Field],
    config: &ProverConfig,
) -> Result<(Field, OpeningProof)> {
    config.install(|| open_with_folding(parameters, commitment, prover_data, point))
}

/// The opening itself, each round the prover: 1. samples a new DEEP point alpha_i and adds it to the tracked points, 2. sends the line through x_0 for every tracked point, 3. gets
/// the folding challenge r_i and folds the coefficients and codeword, 4. commits to the folded codeword, after n rounds f is a constant (final_value), then the query leaves are opened
fn open_with_folding(
    parameters: &Parameters,
    commitment: &Commitment,
    prover_data: &ProverData,
    point: &[Field],
) -> Result<(Field, OpeningProof)> {
    let claimed_value = prover_data.polynomial.evaluate(point)?;
    // Tracked points: the point we open at, and the DEEP point from commit
    let mut transcript = evaluation_transcript(parameters, commitment, point, claimed_value);
    let alpha = derive_deep_point(parameters, &commitment.root);

    let mut points = vec![
        (point.to_vec(), Some(claimed_value)),
        (
            deep_point_powered(alpha, parameters.num_vars),
            Some(commitment.deep_value),
        ),
    ];
    let mut coefficients = prover_data.polynomial.coefficients().to_vec();
    let mut layers = vec![Layer::Committed {
        codeword: &prover_data.codeword,
        tree: &prover_data.tree,
    }];
    let mut rounds = Vec::with_capacity(parameters.num_vars);

    for round in 0..parameters.num_vars {
        let remaining = parameters.num_vars - round;

        let alpha_i = transcript.challenge_field(b"deep-alpha");
        points.push((deep_point_powered(alpha_i, remaining), None));

        let lines = points
            .par_iter()
            .map(|(evaluation_point, _)| line_endpoints(&coefficients, &evaluation_point[1..]))
            .collect::<Vec<_>>();
        append_lines(&mut transcript, &lines);

        let folding_challenge = transcript.challenge_field(b"folding-challenge");

        let next_points = points
            .iter()
            .zip(&lines)
            .map(|((evaluation_point, _), line)| {
                (
                    evaluation_point[1..].to_vec(),
                    Some(line_evaluate(*line, folding_challenge)),
                )
            })
            .collect();
        points = next_points;
        coefficients = fold_coefficients(&coefficients, folding_challenge);

        let next_root = if round + 1 < parameters.num_vars {
            let codeword = fold_codeword(
                layers.last().expect("initial layer exists").codeword(),
                folding_challenge,
            )?;
            let tree = build_merkle_tree(&codeword)?;
            let root = tree.root();
            transcript.append_bytes(b"round-root", &root);
            layers.push(Layer::Folded { codeword, tree });
            Some(root)
        } else {
            transcript.append_field(b"final-value", &coefficients[0]);
            None
        };
        rounds.push(RoundProof { lines, next_root });
    }

    let final_value = coefficients[0];
    if parameters.num_vars == 0 {
        transcript.append_field(b"final-value", &final_value);
    }
    let queries = build_queries(parameters, &mut transcript, &layers)?;
    Ok((
        claimed_value,
        OpeningProof {
            rounds,
            final_value,
            queries,
        },
    ))
}

/// fri-style fold of the codeword with challenge r based of Deepfold paper
fn fold_codeword(codeword: &[Field], challenge: Field) -> Result<Vec<Field>> {
    if codeword.len() < 2 || !codeword.len().is_power_of_two() {
        return Err(Error::InvalidParameters(
            "folded codeword requires a radix-2 domain of size at least two",
        ));
    }
    let domain = Radix2EvaluationDomain::<Field>::new(codeword.len())
        .ok_or(Error::InvalidParameters("unsupported radix-2 domain"))?;
    let half = codeword.len() / 2;
    let inverse_two = Field::from(2u64)
        .inverse()
        .ok_or(Error::InvalidParameters("field has characteristic two"))?;
    let (positives, negatives) = codeword.split_at(half);
    let mut folded = vec![Field::zero(); half];
    // Each chunk starts inverse_x at g^-start itself so the chunks can run in parallel
    let fold_chunk = |start: usize, out: &mut [Field]| {
        let mut inverse_x = inverse_two * domain.group_gen_inv.pow([start as u64]);
        for (offset, slot) in out.iter_mut().enumerate() {
            let positive = positives[start + offset];
            let negative = negatives[start + offset];
            *slot =
                (positive + negative) * inverse_two + challenge * (positive - negative) * inverse_x;
            inverse_x *= domain.group_gen_inv;
        }
    };
    if half >= FOLD_CHUNK {
        folded
            .par_chunks_mut(FOLD_CHUNK)
            .enumerate()
            .for_each(|(chunk, out)| fold_chunk(chunk * FOLD_CHUNK, out));
    } else {
        fold_chunk(0, &mut folded);
    }
    Ok(folded)
}

const FOLD_CHUNK: usize = 1 << 12;

fn build_queries(
    parameters: &Parameters,
    transcript: &mut Transcript,
    layers: &[Layer<'_>],
) -> Result<Vec<RoundMultiProof>> {
    let initial_indices = (0..parameters.num_queries)
        .map(|_| transcript.challenge_index(b"query-index", parameters.domain_size() / 2))
        .collect::<Vec<_>>();

    build_multiproof_queries(parameters, layers, &initial_indices)
}

fn build_multiproof_queries(
    parameters: &Parameters,
    layers: &[Layer<'_>],
    initial_indices: &[usize],
) -> Result<Vec<RoundMultiProof>> {
    let mut rounds = Vec::with_capacity(layers.len());
    for (round, layer) in layers.iter().enumerate() {
        let size = parameters.domain_size() >> round;
        let mut indices = Vec::with_capacity(initial_indices.len());
        for initial_index in initial_indices {
            let positive_index = initial_index % (size / 2);
            indices.push(positive_index);
        }
        // Late layers are small, so queries often hit the same leaf, each leaf is only sent once
        indices.sort_unstable();
        indices.dedup();

        let leaves = indices
            .iter()
            .map(|index| MultiProofLeaf {
                index: *index,
                positive: layer.codeword()[*index],
                negative: layer.codeword()[*index + size / 2],
            })
            .collect();
        let authentication = layer.tree().open_multi_pairs(layer.codeword(), &indices)?;
        rounds.push(RoundMultiProof {
            leaves,
            authentication,
        });
    }
    Ok(rounds)
}

fn build_merkle_tree(codeword: &[Field]) -> Result<MerkleTree> {
    MerkleTree::from_field_pairs_parallel(codeword)
}

pub fn evaluation_transcript(
    parameters: &Parameters,
    commitment: &Commitment,
    point: &[Field],
    claimed_value: Field,
) -> Transcript {
    let mut transcript = Transcript::new(b"evaluate");
    transcript.append_parameters(parameters);
    transcript.append_bytes(b"commitment-root", &commitment.root);
    transcript.append_field(b"commitment-deep-value", &commitment.deep_value);
    transcript.append_bytes(b"point-length", &(point.len() as u64).to_le_bytes());
    for coordinate in point {
        transcript.append_field(b"point-coordinate", coordinate);
    }
    transcript.append_field(b"claimed-value", &claimed_value);
    transcript
}

pub fn append_lines(transcript: &mut Transcript, lines: &[(Field, Field)]) {
    transcript.append_bytes(b"line-count", &(lines.len() as u64).to_le_bytes());
    for (at_zero, at_one) in lines {
        transcript.append_field(b"line-at-zero", at_zero);
        transcript.append_field(b"line-at-one", at_one);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Plain sequential fold, to check the chunked one
    fn fold_codeword_reference(codeword: &[Field], challenge: Field) -> Vec<Field> {
        let domain = Radix2EvaluationDomain::<Field>::new(codeword.len()).unwrap();
        let half = codeword.len() / 2;
        let inverse_two = Field::from(2u64).inverse().unwrap();
        let mut inverse_x = inverse_two;
        (0..half)
            .map(|index| {
                let (positive, negative) = (codeword[index], codeword[index + half]);
                let value = (positive + negative) * inverse_two
                    + challenge * (positive - negative) * inverse_x;
                inverse_x *= domain.group_gen_inv;
                value
            })
            .collect()
    }

    #[test]
    fn fold_codeword_matches_naive() {
        let pool = ProverConfig::new(4).unwrap();
        for log_size in [1usize, 4, 12, 13, 16] {
            let codeword = (0..1u64 << log_size)
                .map(|i| Field::from(i.wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ 0xabcd))
                .collect::<Vec<_>>();
            let challenge = Field::from(0x1234_5678u64);
            let parallel = pool.install(|| fold_codeword(&codeword, challenge).unwrap());
            assert_eq!(
                parallel,
                fold_codeword_reference(&codeword, challenge),
                "log_size = {log_size}"
            );
        }
    }
}
