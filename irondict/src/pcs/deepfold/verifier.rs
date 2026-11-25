//! DeepFold opening (verifier side)

use ark_ff::Field as _;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

use crate::crypto::merkle;
use crate::crypto::transcript::Transcript;
use crate::pcs::deepfold::commitment::{Commitment, derive_deep_point};
use crate::pcs::deepfold::polynomial::{deep_point_powered, line_evaluate};
use crate::pcs::deepfold::prover::{
    MultiProofLeaf, OpeningProof, RoundMultiProof, append_lines, evaluation_transcript,
};
use crate::{Error, Field, Parameters, Result};

/// checks that claimed_value = f(point) for the committed f
pub fn verify(
    parameters: &Parameters,
    commitment: &Commitment,
    point: &[Field],
    claimed_value: Field,
    proof: &OpeningProof,
) -> Result<()> {
    validate_proof_shape(parameters, point, proof)?;

    let mut transcript = evaluation_transcript(parameters, commitment, point, claimed_value);
    let alpha = derive_deep_point(parameters, &commitment.root);
    let mut claims = vec![
        (point.to_vec(), claimed_value),
        (
            deep_point_powered(alpha, parameters.num_vars),
            commitment.deep_value,
        ),
    ];
    let mut roots = vec![commitment.root];
    let mut folding_challenges = Vec::with_capacity(parameters.num_vars);

    for (round_index, round) in proof.rounds.iter().enumerate() {
        let remaining = parameters.num_vars - round_index;
        let alpha_i = transcript.challenge_field(b"deep-alpha");
        let deep_point = deep_point_powered(alpha_i, remaining);
        // One line per existing claim plus one for the new DEEP point
        if round.lines.len() != claims.len() + 1 {
            return Err(Error::MalformedProof("incorrect number of DEEP lines"));
        }

        for ((evaluation_point, expected), line) in claims.iter().zip(&round.lines) {
            if line_evaluate(*line, evaluation_point[0]) != *expected {
                return Err(Error::VerificationFailed("DEEP evaluation chain"));
            }
        }
        append_lines(&mut transcript, &round.lines);
        let folding_challenge = transcript.challenge_field(b"folding-challenge");
        folding_challenges.push(folding_challenge);

        let mut next_claims = claims
            .iter()
            .zip(&round.lines)
            .map(|((evaluation_point, _), line)| {
                (
                    evaluation_point[1..].to_vec(),
                    line_evaluate(*line, folding_challenge),
                )
            })
            .collect::<Vec<_>>();
        // The new DEEP line is only checked from the next round on
        let deep_line = round.lines[claims.len()];
        next_claims.push((
            deep_point[1..].to_vec(),
            line_evaluate(deep_line, folding_challenge),
        ));
        claims = next_claims;

        if round_index + 1 < parameters.num_vars {
            let root = round
                .next_root
                .ok_or(Error::MalformedProof("missing round root"))?;
            transcript.append_bytes(b"round-root", &root);
            roots.push(root);
        } else {
            if round.next_root.is_some() {
                return Err(Error::MalformedProof("unexpected final round root"));
            }
            transcript.append_field(b"final-value", &proof.final_value);
        }
    }

    // after n folds every claim should be the same constant
    if parameters.num_vars == 0 {
        transcript.append_field(b"final-value", &proof.final_value);
        if claimed_value != commitment.deep_value || claimed_value != proof.final_value {
            return Err(Error::VerificationFailed("constant evaluation mismatch"));
        }
    } else if claims
        .iter()
        .any(|(point, claim)| !point.is_empty() || *claim != proof.final_value)
    {
        return Err(Error::VerificationFailed("final folded claims disagree"));
    }

    verify_queries(
        parameters,
        &mut transcript,
        &roots,
        &folding_challenges,
        proof,
    )
}

fn validate_proof_shape(
    parameters: &Parameters,
    point: &[Field],
    proof: &OpeningProof,
) -> Result<()> {
    if point.len() != parameters.num_vars {
        return Err(Error::MalformedProof("incorrect evaluation point length"));
    }
    if proof.rounds.len() != parameters.num_vars {
        return Err(Error::MalformedProof("incorrect folding round count"));
    }

    for (round_index, round) in proof.rounds.iter().enumerate() {
        let should_have_root = round_index + 1 < parameters.num_vars;
        if round.next_root.is_some() != should_have_root {
            return Err(Error::MalformedProof("incorrect round commitment roots"));
        }
    }

    let expected_layers = parameters.num_vars.max(1);
    if proof.queries.len() != expected_layers {
        return Err(Error::MalformedProof("incorrect multiproof round count"));
    }
    Ok(())
}

fn verify_queries(
    parameters: &Parameters,
    transcript: &mut Transcript,
    roots: &[[u8; 32]],
    folding_challenges: &[Field],
    proof: &OpeningProof,
) -> Result<()> {
    let domain = Radix2EvaluationDomain::<Field>::new(parameters.domain_size())
        .ok_or(Error::InvalidParameters("unsupported radix-2 domain"))?;
    let inverse_two = Field::from(2u64)
        .inverse()
        .ok_or(Error::InvalidParameters("field has characteristic two"))?;
    let initial_indices = (0..parameters.num_queries)
        .map(|_| transcript.challenge_index(b"query-index", parameters.domain_size() / 2))
        .collect::<Vec<_>>();

    verify_multiproof_queries(
        parameters,
        roots,
        folding_challenges,
        proof.final_value,
        &domain,
        inverse_two,
        &initial_indices,
        &proof.queries,
    )
}

fn verify_multiproof_queries(
    parameters: &Parameters,
    roots: &[[u8; 32]],
    folding_challenges: &[Field],
    final_value: Field,
    domain: &Radix2EvaluationDomain<Field>,
    inverse_two: Field,
    initial_indices: &[usize],
    rounds: &[RoundMultiProof],
) -> Result<()> {
    for (round, round_proof) in rounds.iter().enumerate() {
        let size = parameters.domain_size() >> round;
        let expected_indices = multiproof_indices(initial_indices, size);
        if round_proof.leaves.len() != expected_indices.len()
            || round_proof
                .leaves
                .iter()
                .zip(&expected_indices)
                .any(|(leaf, expected)| leaf.index != *expected)
        {
            return Err(Error::MalformedProof(
                "incorrect multiproof opened leaf indices",
            ));
        }
        let mut opened = Vec::with_capacity(round_proof.leaves.len());
        for leaf in &round_proof.leaves {
            let digest =
                merkle::paired_field_leaf_digest(leaf.index, &leaf.positive, &leaf.negative);
            opened.push((leaf.index, digest));
        }
        let root = roots
            .get(round)
            .ok_or(Error::MalformedProof("missing query commitment root"))?;
        if !merkle::verify_multi(root, size / 2, &opened, &round_proof.authentication) {
            return Err(Error::MalformedProof("Merkle multiproof"));
        }
    }

    for &initial_index in initial_indices {
        let mut beta_inverse =
            domain.element((parameters.domain_size() - initial_index) % parameters.domain_size());
        for (round, round_proof) in rounds.iter().enumerate() {
            let size = parameters.domain_size() >> round;
            let actual_index = initial_index % size;
            let index = actual_index % (size / 2);
            let positive = multiproof_value(&round_proof.leaves, index, size)?;
            let negative = multiproof_value(&round_proof.leaves, index + size / 2, size)?;

            if let Some(challenge) = folding_challenges.get(round) {
                let (at_beta, at_negative_beta) = if actual_index < size / 2 {
                    (positive, negative)
                } else {
                    (negative, positive)
                };
                let even = (at_beta + at_negative_beta) * inverse_two;
                let odd = (at_beta - at_negative_beta) * inverse_two * beta_inverse;
                let folded = even + *challenge * odd;
                let expected = if let Some(next_round) = rounds.get(round + 1) {
                    let next_size = size / 2;
                    let next_index = initial_index % next_size;
                    multiproof_value(&next_round.leaves, next_index, next_size)?
                } else {
                    final_value
                };
                if folded != expected {
                    return Err(Error::VerificationFailed("FRI folding relation"));
                }
            } else if positive != final_value || negative != final_value {
                return Err(Error::VerificationFailed("constant codeword query"));
            }
            beta_inverse.square_in_place();
        }
    }
    Ok(())
}

fn multiproof_indices(initial_indices: &[usize], size: usize) -> Vec<usize> {
    let mut indices = Vec::with_capacity(initial_indices.len());
    for initial_index in initial_indices {
        let positive = initial_index % (size / 2);
        indices.push(positive);
    }
    indices.sort_unstable();
    indices.dedup();
    indices
}

/// Looks up a codeword value among the opened leaves
fn multiproof_value(
    leaves: &[MultiProofLeaf],
    codeword_index: usize,
    codeword_size: usize,
) -> Result<Field> {
    let leaf_index = codeword_index % (codeword_size / 2);
    let position = leaves
        .binary_search_by_key(&leaf_index, |leaf| leaf.index)
        .map_err(|_| Error::MalformedProof("missing multiproof leaf value"))?;
    if codeword_index < codeword_size / 2 {
        Ok(leaves[position].positive)
    } else {
        Ok(leaves[position].negative)
    }
}
