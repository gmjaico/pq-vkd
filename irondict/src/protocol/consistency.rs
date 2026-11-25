//! Consistency check between two epochs (the Randomizer is what makes this work)

use crate::crypto::placement::PlacementBackend;
use crate::crypto::protocol_transcript::ProtocolTranscript;
use crate::protocol::epoch::VerifiedTransition;
use crate::protocol::lookup::{PlacementPath, VerifiedPlacement, verify_placement};
use crate::protocol::opening::{AuthenticatedOpening, slot_to_point};
use crate::protocol::state::{EpochSnapshot, PublicEpoch, ServerState};
use crate::{Error, Result};

/// Client Monitoring Implementation of Report Section 4
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ConsistencyProof<P> {
    pub statement_digest: [u8; 32],
    pub old_placement: PlacementPath<P>,
    pub new_placement: PlacementPath<P>,
    pub old_randomizer: AuthenticatedOpening,
    pub new_randomizer: AuthenticatedOpening,
}

impl<P> ConsistencyProof<P> {
    pub fn opening_count(&self) -> usize {
        2
    }
}

impl ConsistencyProof<()> {
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.statement_digest);
        self.old_placement.push_bytes(&mut out);
        self.new_placement.push_bytes(&mut out);
        crate::protocol::epoch::push_opening(&mut out, &self.old_randomizer);
        crate::protocol::epoch::push_opening(&mut out, &self.new_randomizer);
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedConsistency {
    pub label: Vec<u8>,
    pub slot: usize,
    pub first_epoch: u64,
    pub last_epoch: u64,
    pub statement_digest: [u8; 32],
}

impl<B: PlacementBackend> ServerState<B> {
    /// fails if the label is missing or its value changed in the range
    pub fn prove_consistency(
        &self,
        old: &EpochSnapshot,
        new: &EpochSnapshot,
        label: &[u8],
    ) -> Result<ConsistencyProof<B::Proof>> {
        validate_endpoints(old.public(), new.public())?;
        let (old_placement, old_result) = self.prove_placement(old, label)?;
        let (new_placement, new_result) = self.prove_placement(new, label)?;
        let slot = match (old_result, new_result) {
            (
                VerifiedPlacement::Occupied { slot },
                VerifiedPlacement::Occupied { slot: new_slot },
            ) if slot == new_slot => slot,
            (VerifiedPlacement::Empty { .. }, _) => {
                return Err(Error::InvalidState(
                    "consistency label is absent at old epoch",
                ));
            }
            _ => {
                return Err(Error::VerificationFailed(
                    "consistency endpoint lookup mismatch",
                ));
            }
        };
        let point = slot_to_point(slot, old.public.parameters.num_vars)?;
        let old_randomizer = AuthenticatedOpening::prove(
            &old.public.parameters,
            old.randomizer.commitment(),
            old.randomizer.prover_data(),
            &point,
            &self.prover_config,
        )?;
        let new_randomizer = AuthenticatedOpening::prove(
            &new.public.parameters,
            new.randomizer.commitment(),
            new.randomizer.prover_data(),
            &point,
            &self.prover_config,
        )?;
        if old_randomizer.value != new_randomizer.value {
            return Err(Error::VerificationFailed(
                "label value changed in requested epoch range",
            ));
        }
        Ok(ConsistencyProof {
            statement_digest: consistency_statement_digest(old.public(), new.public(), label),
            old_placement,
            new_placement,
            old_randomizer,
            new_randomizer,
        })
    }
}

pub fn verify_consistency<B: PlacementBackend>(
    backend: &B,
    old: &PublicEpoch,
    new: &PublicEpoch,
    transitions: &[VerifiedTransition],
    label: &[u8],
    proof: &ConsistencyProof<B::Proof>,
) -> Result<VerifiedConsistency> {
    validate_endpoints(old, new)?;
    validate_chain(old, new, transitions)?;
    let digest = consistency_statement_digest(old, new, label);
    if proof.statement_digest != digest {
        return Err(Error::VerificationFailed("consistency statement binding"));
    }
    let old_result = verify_placement(backend, old, label, &proof.old_placement.probes)?;
    let new_result = verify_placement(backend, new, label, &proof.new_placement.probes)?;
    let slot = match (old_result, new_result) {
        (VerifiedPlacement::Occupied { slot }, VerifiedPlacement::Occupied { slot: new_slot })
            if slot == new_slot =>
        {
            slot
        }
        (VerifiedPlacement::Empty { .. }, _) => {
            return Err(Error::VerificationFailed(
                "consistency label absent at old endpoint",
            ));
        }
        _ => return Err(Error::VerificationFailed("consistency endpoint mismatch")),
    };
    let point = slot_to_point(slot, old.parameters.num_vars)?;
    proof
        .old_randomizer
        .verify(&old.parameters, &old.commitments.randomizer, &point)?;
    proof
        .new_randomizer
        .verify(&new.parameters, &new.commitments.randomizer, &point)?;
    if proof.old_randomizer.value != proof.new_randomizer.value {
        return Err(Error::VerificationFailed("randomizer consistency equality"));
    }
    Ok(VerifiedConsistency {
        label: label.to_vec(),
        slot,
        first_epoch: old.epoch,
        last_epoch: new.epoch,
        statement_digest: digest,
    })
}

fn validate_endpoints(old: &PublicEpoch, new: &PublicEpoch) -> Result<()> {
    if old.epoch >= new.epoch
        || old.parameters != new.parameters
        || old.placement_id != new.placement_id
    {
        return Err(Error::InvalidState("incompatible consistency endpoints"));
    }
    Ok(())
}

fn validate_chain(
    old: &PublicEpoch,
    new: &PublicEpoch,
    transitions: &[VerifiedTransition],
) -> Result<()> {
    let expected = usize::try_from(new.epoch - old.epoch)
        .map_err(|_| Error::InvalidState("consistency range is too large"))?;
    if transitions.len() != expected {
        return Err(Error::VerificationFailed(
            "consistency audit chain is incomplete",
        ));
    }
    let mut epoch = old.epoch;
    let mut digest = old.digest();
    for transition in transitions {
        if transition.previous_epoch != epoch
            || transition.next_epoch != epoch + 1
            || transition.previous_digest != digest
        {
            return Err(Error::VerificationFailed(
                "consistency audit chain is reordered",
            ));
        }
        epoch += 1;
        digest = transition.next_digest;
    }
    if epoch != new.epoch || digest != new.digest() {
        return Err(Error::VerificationFailed(
            "consistency audit chain endpoint",
        ));
    }
    Ok(())
}

fn consistency_statement_digest(old: &PublicEpoch, new: &PublicEpoch, label: &[u8]) -> [u8; 32] {
    let mut transcript = ProtocolTranscript::new(b"client-consistency-statement");
    transcript.append_bytes(b"old-public-epoch", &old.to_bytes());
    transcript.append_bytes(b"new-public-epoch", &new.to_bytes());
    transcript.append_bytes(b"label", label);
    transcript.digest()
}
