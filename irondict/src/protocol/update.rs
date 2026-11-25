//! Value updates, and the code that completes every epoch

use std::sync::Arc;
use std::time::Instant;

use crate::crypto::placement::PlacementBackend;
use crate::crypto::sparse_merkle::SparseMerkleTree;
use crate::index_stark::IndexUpdateProof;
use crate::protocol::epoch::{
    derive_recurrence_challenge, prove_transition_timed, verify_transition,
};
use crate::protocol::state::{
    CommittedStatePolynomial, Entry, EpochSnapshot, EpochTimings, PublicEpoch, ServerState,
    StateCommitments,
};
use crate::{Error, Result};

impl<B: PlacementBackend> ServerState<B> {
    pub fn update(&mut self, label: &[u8], value: &[u8]) -> Result<Arc<EpochSnapshot>> {
        self.update_batch(&[(label.to_vec(), value.to_vec())])
    }

    /// change the values of existing labels in one epoch, the Index doesn't change, so there is no Index STARK
    pub fn update_batch(&mut self, batch: &[(Vec<u8>, Vec<u8>)]) -> Result<Arc<EpochSnapshot>> {
        if batch.is_empty() {
            return Err(Error::InvalidInput("update batch must not be empty"));
        }
        let mut timings = EpochTimings::default();
        let start = Instant::now();
        let mut value_evaluations = self.current.value.evaluations().to_vec();
        let mut entries = self.current.entries.as_ref().clone();
        self.apply_updates(&mut value_evaluations, &mut entries, batch)?;
        timings.placement = start.elapsed();
        let start = Instant::now();
        let committed_value = CommittedStatePolynomial::commit(
            &self.current.public.parameters,
            value_evaluations,
            &self.prover_config,
        )?;
        timings.value_commit = start.elapsed();
        let index = self.current.index.clone();
        self.commit_candidate(index, committed_value, entries, None, timings)
    }

    /// Shared end of every epoch: derive rho, update the Randomizer, build
    /// the public epoch, prove the transition and check it before accepting
    pub(crate) fn commit_candidate(
        &mut self,
        index: Arc<SparseMerkleTree>,
        value: CommittedStatePolynomial,
        entries: std::collections::BTreeMap<usize, Entry>,
        registration: Option<IndexUpdateProof>,
        mut timings: EpochTimings,
    ) -> Result<Arc<EpochSnapshot>> {
        let previous = Arc::clone(&self.current);
        let next_epoch = previous
            .public
            .epoch
            .checked_add(1)
            .ok_or(Error::InvalidState("epoch number overflow"))?;
        let rho = derive_recurrence_challenge(
            &previous.public,
            next_epoch,
            &index.root(),
            value.commitment(),
        );
        // R_new = R_old + rho * (V_new - V_old), committed without an FFT
        let start = Instant::now();
        let randomizer = CommittedStatePolynomial::commit_linear_update(
            &previous.public.parameters,
            &previous.randomizer,
            &previous.value,
            &value,
            rho,
            &self.prover_config,
        )?;
        timings.randomizer_update = start.elapsed();
        let public = PublicEpoch {
            epoch: next_epoch,
            parameters: previous.public.parameters,
            placement_id: previous.public.placement_id.clone(),
            previous_digest: previous.public.digest(),
            recurrence_challenge: Some(rho),
            index_root: index.root(),
            commitments: StateCommitments {
                value: value.commitment().clone(),
                randomizer: randomizer.commitment().clone(),
            },
        };
        let candidate = Arc::new(EpochSnapshot {
            public,
            index,
            value,
            randomizer,
            entries: Arc::new(entries),
        });
        let proof = prove_transition_timed(
            &previous,
            &candidate,
            registration,
            &self.prover_config,
            &mut timings.openings,
        )?;
        let start = Instant::now();
        verify_transition(previous.public(), candidate.public(), &proof)?;
        timings.self_verify = start.elapsed();
        self.last_epoch_timings = timings;
        self.transitions.push(proof);
        self.snapshots.push(Arc::clone(&candidate));
        self.current = Arc::clone(&candidate);
        Ok(candidate)
    }
}
