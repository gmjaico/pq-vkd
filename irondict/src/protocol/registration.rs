//! Registration: adding new labels

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Instant;

use crate::crypto::index_hash::{h_leaf, label_identifier};
use crate::crypto::placement::PlacementBackend;
use crate::crypto::protocol_transcript::hash_to_nonzero_field;
use crate::crypto::sparse_merkle::SparseMerkleTree;
use crate::index_stark::{IndexInsertion, prove_index_update};
use crate::protocol::state::{
    CommittedStatePolynomial, Entry, EpochSnapshot, EpochTimings, ServerState,
};
use crate::{Error, Field, Result};

impl<B: PlacementBackend> ServerState<B> {
    pub fn register(&mut self, label: &[u8], value: &[u8]) -> Result<Arc<EpochSnapshot>> {
        self.register_batch(&[(label.to_vec(), value.to_vec())])
    }

    /// Register a batch of new labels in one epoch
    pub fn register_batch(&mut self, batch: &[(Vec<u8>, Vec<u8>)]) -> Result<Arc<EpochSnapshot>> {
        if batch.is_empty() {
            return self.commit_candidate(
                Arc::clone(&self.current.index),
                self.current.value.clone(),
                self.current.entries.as_ref().clone(),
                None,
                EpochTimings::default(),
            );
        }
        self.publish_batch(batch, &[])
    }

    /// one epoch with new labels and value updates together (used for the mixed epochs in the comparison), one Index STARK
    /// for the new labels, one Value commit for everything, a label can't be registered and updated in the same epoch
    pub fn publish_batch(
        &mut self,
        registrations: &[(Vec<u8>, Vec<u8>)],
        updates: &[(Vec<u8>, Vec<u8>)],
    ) -> Result<Arc<EpochSnapshot>> {
        if registrations.is_empty() {
            return self.update_batch(updates);
        }
        let mut timings = EpochTimings::default();
        let start = Instant::now();
        let mut index = self.current.index.as_ref().clone();
        let mut value_evaluations = self.current.value.evaluations().to_vec();
        let mut entries = self.current.entries.as_ref().clone();
        self.apply_updates(&mut value_evaluations, &mut entries, updates)?;
        let insertions = self.place_registrations(
            &mut index,
            &mut value_evaluations,
            &mut entries,
            registrations,
        )?;
        timings.placement = start.elapsed();

        let next_epoch = self
            .current
            .public
            .epoch
            .checked_add(1)
            .ok_or(Error::InvalidState("epoch number overflow"))?;
        let start = Instant::now();
        let (index_proof, proven_root) = prove_index_update(
            self.current.public.parameters.num_vars,
            next_epoch,
            &self.current.index.root(),
            &insertions,
            &self.prover_config,
        )?;
        timings.index_stark = start.elapsed();
        if proven_root != index.root() {
            return Err(Error::InvalidState(
                "Index STARK root disagrees with the native tree",
            ));
        }
        let start = Instant::now();
        let committed_value = CommittedStatePolynomial::commit(
            &self.current.public.parameters,
            value_evaluations,
            &self.prover_config,
        )?;
        timings.value_commit = start.elapsed();
        self.commit_candidate(
            Arc::new(index),
            committed_value,
            entries,
            Some(index_proof),
            timings,
        )
    }

    pub(crate) fn place_registrations(
        &self,
        index: &mut SparseMerkleTree,
        value_evaluations: &mut [Field],
        entries: &mut BTreeMap<usize, Entry>,
        batch: &[(Vec<u8>, Vec<u8>)],
    ) -> Result<Vec<IndexInsertion>> {
        let capacity = self.current.public.parameters.polynomial_size();
        let mut insertions = Vec::with_capacity(batch.len());
        for (label, value) in batch {
            if label.is_empty() || value.is_empty() {
                return Err(Error::InvalidInput("labels and values must not be empty"));
            }
            let mut target = None;
            for probe in 0..capacity as u64 {
                let slot = self.backend.derive_slot(label, probe, capacity)?;
                match entries.get(&slot) {
                    Some(entry) if entry.label == *label => {
                        return Err(Error::InvalidState("label is already registered"));
                    }
                    Some(_) => continue,
                    None => {
                        target = Some((slot, probe));
                        break;
                    }
                }
            }
            let (slot, probe) = target.ok_or(Error::InvalidState(
                "placement probe limit exhausted or dictionary is full",
            ))?;
            // insert returns the path from before the insert (empty leaf)
            let witness = index.insert(slot, label)?;
            insertions.push(IndexInsertion {
                slot,
                leaf: h_leaf(&label_identifier(label)),
                siblings: witness.siblings,
            });
            value_evaluations[slot] = hash_to_nonzero_field(b"value-encoding", value);
            entries.insert(
                slot,
                Entry {
                    label: label.clone(),
                    value: value.clone(),
                    probe,
                },
            );
        }
        Ok(insertions)
    }

    /// find each label's slot and overwrite its value, for value update
    pub(crate) fn apply_updates(
        &self,
        value_evaluations: &mut [Field],
        entries: &mut BTreeMap<usize, Entry>,
        batch: &[(Vec<u8>, Vec<u8>)],
    ) -> Result<()> {
        let capacity = self.current.public.parameters.polynomial_size();
        for (label, value) in batch {
            if label.is_empty() || value.is_empty() {
                return Err(Error::InvalidInput("labels and values must not be empty"));
            }
            let mut target = None;
            for probe in 0..capacity as u64 {
                let slot = self.backend.derive_slot(label, probe, capacity)?;
                match entries.get(&slot) {
                    Some(entry) if entry.label == *label => {
                        target = Some(slot);
                        break;
                    }
                    Some(_) => continue,
                    None => return Err(Error::InvalidState("label is not registered")),
                }
            }
            let slot = target.ok_or(Error::InvalidState("placement probe limit exhausted"))?;
            value_evaluations[slot] = hash_to_nonzero_field(b"value-encoding", value);
            entries
                .get_mut(&slot)
                .expect("target lookup found an entry")
                .value = value.clone();
        }
        Ok(())
    }
}
