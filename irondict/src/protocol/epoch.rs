//! epoch transitions, this is what the server needs to prove each epoch,
//! which is the index stark proof + value and rand consistency proof

use std::time::{Duration, Instant};

use crate::crypto::protocol_transcript::ProtocolTranscript;
use crate::index_stark::{IndexUpdateProof, verify_index_update};
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::protocol::opening::AuthenticatedOpening;
use crate::protocol::state::push_bytes;
use crate::protocol::state::{CommittedStatePolynomial, EpochSnapshot, PublicEpoch};
use crate::{Error, Field, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
/// openings of R and V in both epochs at the same random point
pub struct RecurrenceProof {
    pub old_randomizer: AuthenticatedOpening,
    pub new_randomizer: AuthenticatedOpening,
    pub old_value: AuthenticatedOpening,
    pub new_value: AuthenticatedOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TransitionProof {
    pub statement_digest: [u8; 32],
    pub registration: Option<IndexUpdateProof>,
    pub recurrence: RecurrenceProof,
}

impl TransitionProof {
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn opening_count(&self) -> usize {
        4
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.statement_digest);
        match &self.registration {
            None => out.push(0),
            Some(registration) => {
                out.push(1);
                push_bytes(&mut out, &registration.to_bytes());
            }
        }
        for opening in [
            &self.recurrence.old_randomizer,
            &self.recurrence.new_randomizer,
            &self.recurrence.old_value,
            &self.recurrence.new_value,
        ] {
            push_opening(&mut out, opening);
        }
        out
    }
}

pub(crate) fn push_opening(out: &mut Vec<u8>, opening: &AuthenticatedOpening) {
    push_bytes(out, &opening.proof.to_bytes(opening.value));
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedTransition {
    pub previous_epoch: u64,
    pub next_epoch: u64,
    pub previous_digest: [u8; 32],
    pub next_digest: [u8; 32],
    pub statement_digest: [u8; 32],
}

/// builds the transition proof between two epochs
pub fn prove_transition(
    previous: &EpochSnapshot,
    next: &EpochSnapshot,
    registration: Option<IndexUpdateProof>,
    config: &ProverConfig,
) -> Result<TransitionProof> {
    prove_transition_timed(
        previous,
        next,
        registration,
        config,
        &mut [Duration::ZERO; 4],
    )
}

/// prove_transition that also records how long each of the four openings took
/// (old/new Randomizer, old/new Value)
pub(crate) fn prove_transition_timed(
    previous: &EpochSnapshot,
    next: &EpochSnapshot,
    registration: Option<IndexUpdateProof>,
    config: &ProverConfig,
    opening_times: &mut [Duration; 4],
) -> Result<TransitionProof> {
    validate_successor(previous.public(), next.public())?;
    let statement_digest = transition_statement_digest(previous.public(), next.public());
    let parameters = &previous.public().parameters;
    match (
        &registration,
        previous.public.index_root == next.public.index_root,
    ) {
        (Some(proof), false) if proof.k > 0 => {}
        (None, true) => {}
        (Some(_), true) => {
            return Err(Error::InvalidState(
                "registration did not change Index root",
            ));
        }
        (Some(_), false) => {
            return Err(Error::InvalidState("empty Index update proof"));
        }
        (None, false) => {
            return Err(Error::InvalidState(
                "changed Index lacks registration witnesses",
            ));
        }
    }
    let audit_point = recurrence_audit_point(&statement_digest, parameters.num_vars);
    let mut open = |i: usize, poly: &CommittedStatePolynomial| {
        let start = Instant::now();
        let opening = AuthenticatedOpening::prove(
            parameters,
            poly.commitment(),
            poly.prover_data(),
            &audit_point,
            config,
        );
        opening_times[i] = start.elapsed();
        opening
    };
    let recurrence = RecurrenceProof {
        old_randomizer: open(0, &previous.randomizer)?,
        new_randomizer: open(1, &next.randomizer)?,
        old_value: open(2, &previous.value)?,
        new_value: open(3, &next.value)?,
    };
    Ok(TransitionProof {
        statement_digest,
        registration,
        recurrence,
    })
}

/// auditor check for one epoch: 1. the epoch links to the previous one (validate_successor), 2. the Index STARK if the root changed (one
/// STARK verification no matter how many labels were added), 3. the four openings and R_new(z) - R_old(z) = rho * (V_new(z) - V_old(z))
pub fn verify_transition(
    previous: &PublicEpoch,
    next: &PublicEpoch,
    proof: &TransitionProof,
) -> Result<VerifiedTransition> {
    validate_successor(previous, next)?;
    let statement_digest = transition_statement_digest(previous, next);
    if proof.statement_digest != statement_digest {
        return Err(Error::VerificationFailed("transition statement binding"));
    }
    let index_changed = previous.index_root != next.index_root;
    match (&proof.registration, index_changed) {
        (Some(registration), true) => {
            verify_index_update(
                previous.parameters.num_vars,
                next.epoch,
                &previous.index_root,
                &next.index_root,
                registration,
            )?;
        }
        (None, false) => {}
        (Some(_), false) => {
            return Err(Error::MalformedProof(
                "unexpected registration proof for unchanged Index",
            ));
        }
        (None, true) => return Err(Error::MalformedProof("missing registration proof")),
    }

    let point = recurrence_audit_point(&statement_digest, previous.parameters.num_vars);
    let recurrence = &proof.recurrence;
    for (commitment, opening) in [
        (&previous.commitments.randomizer, &recurrence.old_randomizer),
        (&next.commitments.randomizer, &recurrence.new_randomizer),
        (&previous.commitments.value, &recurrence.old_value),
        (&next.commitments.value, &recurrence.new_value),
    ] {
        opening.verify(&previous.parameters, commitment, &point)?;
    }
    let rho = next.recurrence_challenge.ok_or(Error::MalformedProof(
        "successor lacks recurrence challenge",
    ))?;
    if recurrence.new_randomizer.value - recurrence.old_randomizer.value
        != rho * (recurrence.new_value.value - recurrence.old_value.value)
    {
        return Err(Error::VerificationFailed("randomizer recurrence"));
    }
    Ok(VerifiedTransition {
        previous_epoch: previous.epoch,
        next_epoch: next.epoch,
        previous_digest: previous.digest(),
        next_digest: next.digest(),
        statement_digest,
    })
}

/// rho for this epoch, from the previous epoch and the new Index root and Value
/// commitment, fixed only after V_new is committed, used for Rand polynomial construction
pub(crate) fn derive_recurrence_challenge(
    previous: &PublicEpoch,
    next_epoch: u64,
    next_index_root: &[u8; 32],
    next_value: &crate::pcs::deepfold::Commitment,
) -> Field {
    let mut transcript = ProtocolTranscript::new(b"epoch-recurrence-challenge");
    transcript.append_bytes(b"previous-public-epoch", &previous.to_bytes());
    transcript.append_u64(b"next-epoch", next_epoch);
    transcript.append_bytes(b"next-index-root", next_index_root);
    transcript.append_bytes(b"next-value-commitment", &next_value.to_bytes());
    transcript.challenge_field(b"rho")
}

pub fn transition_statement_digest(previous: &PublicEpoch, next: &PublicEpoch) -> [u8; 32] {
    let mut transcript = ProtocolTranscript::new(b"epoch-transition-statement");
    transcript.append_bytes(b"previous", &previous.to_bytes());
    transcript.append_bytes(b"next", &next.to_bytes());
    transcript.digest()
}

pub fn recurrence_audit_point(statement: &[u8; 32], num_vars: usize) -> Vec<Field> {
    let mut transcript = ProtocolTranscript::new(b"randomizer-recurrence-audit");
    transcript.append_bytes(b"transition-statement", statement);
    transcript.challenge_fields(b"audit-coordinate", num_vars)
}

/// epoch number +1, previous digest matches, same parameters, and rho was derived correctly
pub fn validate_successor(previous: &PublicEpoch, next: &PublicEpoch) -> Result<()> {
    previous.parameters.validate()?;
    next.parameters.validate()?;
    if next.epoch
        != previous
            .epoch
            .checked_add(1)
            .ok_or(Error::InvalidState("epoch overflow"))?
    {
        return Err(Error::InvalidState("epochs are not consecutive"));
    }
    if next.previous_digest != previous.digest() {
        return Err(Error::InvalidState("incorrect predecessor digest"));
    }
    if next.parameters != previous.parameters || next.placement_id != previous.placement_id {
        return Err(Error::InvalidState("public protocol configuration changed"));
    }
    let expected = derive_recurrence_challenge(
        previous,
        next.epoch,
        &next.index_root,
        &next.commitments.value,
    );
    if next.recurrence_challenge != Some(expected) {
        return Err(Error::InvalidState("incorrect recurrence challenge"));
    }
    Ok(())
}
