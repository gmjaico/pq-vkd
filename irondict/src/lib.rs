//! IronDict with DeepFold: the Index is a sparse Merkle tree audited with a
//! STARK, Value and Randomizer are DeepFold-committed multilinear polynomials

pub mod crypto;
pub mod index_stark;
pub mod pcs;
pub mod protocol;

pub use crypto::field::{self, Field};
pub use pcs::deepfold::params::Parameters;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Error {
    InvalidParameters(&'static str),
    InvalidInput(&'static str),
    InvalidState(&'static str),
    Serialization(&'static str),
    MalformedProof(&'static str),
    InconsistentProverData,
    VerificationFailed(&'static str),
}

impl std::fmt::Display for Error {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InvalidParameters(message) => formatter.write_str(message),
            Self::InvalidInput(message) => formatter.write_str(message),
            Self::InvalidState(message) => formatter.write_str(message),
            Self::Serialization(message) => formatter.write_str(message),
            Self::MalformedProof(message) => formatter.write_str(message),
            Self::InconsistentProverData => formatter.write_str("inconsistent prover data"),
            Self::VerificationFailed(message) => formatter.write_str(message),
        }
    }
}

impl std::error::Error for Error {}

pub type Result<T> = std::result::Result<T, Error>;
