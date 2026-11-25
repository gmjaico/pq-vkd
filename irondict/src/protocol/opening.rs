//! DeepFold openings as used by the protocol

use crate::pcs::deepfold::commitment::{Commitment, ProverData};
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::pcs::deepfold::prover::{OpeningProof, open_with_config};
use crate::pcs::deepfold::verifier::verify;
use crate::{Error, Field, Parameters, Result};

/// A value and the DeepFold proof that the committed polynomial has it
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AuthenticatedOpening {
    pub value: Field,
    pub proof: OpeningProof,
}

impl AuthenticatedOpening {
    pub fn prove(
        parameters: &Parameters,
        commitment: &Commitment,
        prover_data: &ProverData,
        point: &[Field],
        config: &ProverConfig,
    ) -> Result<Self> {
        let (value, proof) = open_with_config(parameters, commitment, prover_data, point, config)?;
        Ok(Self { value, proof })
    }

    pub fn verify(
        &self,
        parameters: &Parameters,
        commitment: &Commitment,
        point: &[Field],
    ) -> Result<()> {
        verify(parameters, commitment, point, self.value, &self.proof)
    }

    pub fn encoded_len(&self) -> usize {
        self.proof.to_bytes(self.value).len()
    }
}

/// Slot to a point on {0,1}^n (bit i of the slot is coordinate i)
pub fn slot_to_point(slot: usize, num_vars: usize) -> Result<Vec<Field>> {
    let parameters = Parameters::new(num_vars)?;
    if slot >= parameters.polynomial_size() {
        return Err(Error::InvalidInput("slot is outside the polynomial domain"));
    }
    Ok((0..num_vars)
        .map(|variable| Field::from(((slot >> variable) & 1) as u64))
        .collect())
}
