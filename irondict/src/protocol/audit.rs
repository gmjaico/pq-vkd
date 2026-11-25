//! Auditor: checking genesis and the chain of transitions

use crate::pcs::deepfold::commitment::commit;
use crate::pcs::deepfold::polynomial::MultilinearPolynomial;
use crate::protocol::epoch::{TransitionProof, VerifiedTransition, verify_transition};
use crate::protocol::state::PublicEpoch;
use crate::protocol::state::push_bytes;
use crate::{Error, Result};
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

static ZERO_COMMITMENTS: OnceLock<
    Mutex<BTreeMap<(usize, usize, usize, usize), crate::pcs::deepfold::Commitment>>,
> = OnceLock::new();

/// commitment to the zero polynomial, cached since every genesis check needs it
pub fn expected_zero_commitment(
    parameters: &crate::Parameters,
) -> Result<crate::pcs::deepfold::Commitment> {
    let key = (
        parameters.num_vars,
        parameters.log_blowup,
        parameters.num_queries,
        parameters.security_bits,
    );
    let cache = ZERO_COMMITMENTS.get_or_init(|| Mutex::new(BTreeMap::new()));
    if let Some(value) = cache
        .lock()
        .map_err(|_| Error::InvalidState("zero commitment cache poisoned"))?
        .get(&key)
        .cloned()
    {
        return Ok(value);
    }
    let zero = MultilinearPolynomial::zero(parameters.num_vars)?;
    let (commitment, _) = commit(parameters, &zero)?;
    cache
        .lock()
        .map_err(|_| Error::InvalidState("zero commitment cache poisoned"))?
        .insert(key, commitment.clone());
    Ok(commitment)
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedGenesis {
    pub digest: [u8; 32],
}

/// genesis is epoch 0 with empty index and zero Value and Randomizer
pub fn verify_genesis(state: &PublicEpoch) -> Result<VerifiedGenesis> {
    state.parameters.validate()?;
    if state.epoch != 0
        || state.previous_digest != [0; 32]
        || state.recurrence_challenge.is_some()
        || state.placement_id != crate::crypto::placement::BLAKE3_PLACEMENT_ID
    {
        return Err(Error::VerificationFailed(
            "invalid trusted genesis metadata",
        ));
    }
    let commitment = expected_zero_commitment(&state.parameters)?;
    let empty_index =
        crate::crypto::sparse_merkle::SparseMerkleTree::empty_root(state.parameters.num_vars)?;
    if state.index_root != empty_index
        || state.commitments.value != commitment
        || state.commitments.randomizer != commitment
    {
        return Err(Error::VerificationFailed(
            "genesis is not committed zero state",
        ));
    }
    Ok(VerifiedGenesis {
        digest: state.digest(),
    })
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// everything the auditor downloads: all public epochs and the proofs between them
pub struct AuditEvidence {
    pub epochs: Vec<PublicEpoch>,
    pub proofs: Vec<TransitionProof>,
}

impl AuditEvidence {
    pub fn new(epochs: Vec<PublicEpoch>, proofs: Vec<TransitionProof>) -> Result<Self> {
        if epochs.is_empty() || proofs.len() + 1 != epochs.len() {
            return Err(Error::InvalidState(
                "audit evidence requires genesis and one proof per successor",
            ));
        }
        Ok(Self { epochs, proofs })
    }

    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.epochs.len() as u32).to_le_bytes());
        for epoch in &self.epochs {
            push_bytes(&mut out, &epoch.to_bytes());
        }
        out.extend_from_slice(&(self.proofs.len() as u32).to_le_bytes());
        for proof in &self.proofs {
            push_bytes(&mut out, &proof.to_bytes());
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedHistory {
    pub genesis: VerifiedGenesis,
    pub transitions: Vec<VerifiedTransition>,
    pub first_digest: [u8; 32],
    pub last_digest: [u8; 32],
}

/// full audit from genesis to the latest epoch
pub fn verify_history(
    genesis: &PublicEpoch,
    successors: &[PublicEpoch],
    proofs: &[TransitionProof],
) -> Result<VerifiedHistory> {
    if successors.len() != proofs.len() {
        return Err(Error::VerificationFailed("audit history is incomplete"));
    }
    let verified_genesis = verify_genesis(genesis)?;
    let mut previous = genesis;
    let mut transitions = Vec::with_capacity(successors.len());
    for (next, proof) in successors.iter().zip(proofs) {
        transitions.push(verify_transition(previous, next, proof)?);
        previous = next;
    }
    Ok(VerifiedHistory {
        genesis: verified_genesis,
        transitions,
        first_digest: genesis.digest(),
        last_digest: previous.digest(),
    })
}

/// same as verify_history but starting from an epoch you already trust
pub fn verify_range(
    checkpoint: &PublicEpoch,
    successors: &[PublicEpoch],
    proofs: &[TransitionProof],
) -> Result<Vec<VerifiedTransition>> {
    if successors.len() != proofs.len() {
        return Err(Error::VerificationFailed("audit range is incomplete"));
    }
    let mut previous = checkpoint;
    let mut verified = Vec::with_capacity(successors.len());
    for (next, proof) in successors.iter().zip(proofs) {
        verified.push(verify_transition(previous, next, proof)?);
        previous = next;
    }
    Ok(verified)
}
