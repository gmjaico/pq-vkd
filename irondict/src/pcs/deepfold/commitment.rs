//! DeepFold commitment functions

use std::sync::Arc;

use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

use crate::crypto::merkle::MerkleTree;
use crate::crypto::transcript::Transcript;
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::pcs::deepfold::polynomial::MultilinearPolynomial;
use crate::{Field, Parameters, Result, field};

/// what the verifier sees for the commitment in bulletin board for PCS commitment
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Commitment {
    pub root: [u8; 32],
    pub deep_value: Field,
}

impl Commitment {
    pub fn root(&self) -> &[u8; 32] {
        &self.root
    }

    pub fn deep_value(&self) -> Field {
        self.deep_value
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut bytes = self.root.to_vec();
        bytes.extend(field::encode(&self.deep_value));
        bytes
    }
}

/// prover/server keeps data related to commitment, so opening
/// queries is more efficient as don't need to redo FFT
#[derive(Clone)]
pub struct ProverData {
    pub(crate) polynomial: Arc<MultilinearPolynomial>,
    pub(crate) codeword: Vec<Field>,
    pub(crate) tree: MerkleTree,
}

impl ProverData {
    pub fn polynomial(&self) -> &MultilinearPolynomial {
        &self.polynomial
    }

    pub(crate) fn codeword(&self) -> &[Field] {
        &self.codeword
    }

    pub fn retained_bytes(&self) -> usize {
        std::mem::size_of_val(self.polynomial.coefficients()) + self.encoded_retained_bytes()
    }

    pub fn encoded_retained_bytes(&self) -> usize {
        std::mem::size_of_val(self.codeword.as_slice()) + self.tree.retained_bytes()
    }
}

pub fn commit(
    parameters: &Parameters,
    polynomial: &MultilinearPolynomial,
) -> Result<(Commitment, ProverData)> {
    parameters.validate()?;
    if polynomial.num_vars() != parameters.num_vars {
        return Err(crate::Error::InvalidParameters(
            "polynomial dimension does not match DeepFold parameters",
        ));
    }
    commit_with_config(parameters, polynomial, &ProverConfig::default())
}

/// actual commit function which is used for value polynomial commitment
pub fn commit_with_config(
    parameters: &Parameters,
    polynomial: &MultilinearPolynomial,
    config: &ProverConfig,
) -> Result<(Commitment, ProverData)> {
    let codeword =
        encode_polynomial_with_config(parameters.domain_size(), polynomial.coefficients(), config)?;
    commit_encoded(parameters, Arc::new(polynomial.clone()), codeword, config)
}

/// The result is the same as calling commit_with_config, same function as commit_with_config, but
/// don't need to do FFT as the codeword is already known, used for updating the Rand polynomial
pub fn commit_encoded(
    parameters: &Parameters,
    polynomial: Arc<MultilinearPolynomial>,
    codeword: Vec<Field>,
    config: &ProverConfig,
) -> Result<(Commitment, ProverData)> {
    if polynomial.num_vars() != parameters.num_vars || codeword.len() != parameters.domain_size() {
        return Err(crate::Error::InvalidParameters(
            "pre-encoded commitment has mismatched dimensions",
        ));
    }
    let tree = build_paired_merkle_with_config(&codeword, config)?;
    let root = tree.root();
    let alpha = derive_deep_point(parameters, &root);
    let commitment = Commitment {
        root,
        // f(alpha, alpha^2, alpha^4, ...), which is the coefficients
        // evaluated as a univariate polynomial at alpham, from deepfold paper
        deep_value: polynomial.twin_evaluate(alpha),
    };
    let data = ProverData {
        polynomial,
        codeword,
        tree,
    };
    Ok((commitment, data))
}

pub fn derive_deep_point(parameters: &Parameters, root: &[u8; 32]) -> Field {
    let mut transcript = Transcript::new(b"commit");
    transcript.append_parameters(parameters);
    transcript.append_bytes(b"root-0", root);
    transcript.challenge_field(b"alpha-0")
}

pub fn encode_polynomial(size: usize, coefficients: &[Field]) -> Result<Vec<Field>> {
    let domain = Radix2EvaluationDomain::<Field>::new(size).expect("unsupported radix-2 domain");
    let mut padded = coefficients.to_vec();
    padded.resize(size, Field::from(0u64));
    domain.fft_in_place(&mut padded);
    Ok(padded)
}

pub fn encode_polynomial_with_config(
    size: usize,
    coefficients: &[Field],
    config: &ProverConfig,
) -> Result<Vec<Field>> {
    const PARALLEL_FFT_MIN_SIZE: usize = 1 << 16;
    if config.threads() > 1 && size >= PARALLEL_FFT_MIN_SIZE {
        config.install(|| encode_polynomial(size, coefficients))
    } else {
        config.install_sequential(|| encode_polynomial(size, coefficients))
    }
}

/// Leaf i holds the pair (codeword[i], codeword[i + N/2]), which is the values at x and -x, so one opened leaf gives both
/// values a fold needs, which is what the Deepfold implementation does to make merkle proofs smaller for the verification
fn build_paired_merkle_with_config(
    codeword: &[Field],
    config: &ProverConfig,
) -> Result<MerkleTree> {
    config.install(|| MerkleTree::from_field_pairs_parallel(codeword))
}
