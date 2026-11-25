//! Server state: the Index tree, the Value and Randomizer
//! polynomials, and the public epoch that commits to them

use std::collections::BTreeMap;
use std::sync::Arc;
use std::time::Duration;

use ark_ff::Zero;

use crate::crypto::placement::PlacementBackend;
use crate::crypto::protocol_transcript::hash_to_nonzero_field;
use crate::crypto::sparse_merkle::SparseMerkleTree;
use rayon::prelude::*;

use crate::pcs::deepfold::commitment::{
    Commitment, ProverData, commit_encoded, commit_with_config,
};
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::pcs::deepfold::polynomial::MultilinearPolynomial;
use crate::{Error, Field, Parameters, Result};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
/// two DeepFold-committed polynomials, Index is a Merkle tree
pub enum StatePolynomial {
    Value,
    Randomizer,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Entry {
    pub label: Vec<u8>,
    pub value: Vec<u8>,
    pub probe: u64,
}

#[derive(Clone, Copy, Debug, Default)]
/// Wall-clock time of each step of the last epoch the server published, measured where the step runs.
/// The parts don't cover small bookkeeping (clones, deriving rho), so they sum to a bit less than the call
pub struct EpochTimings {
    /// finding slots, building the Index witnesses and the new Value table
    pub placement: Duration,
    /// zero when the epoch only updates values
    pub index_stark: Duration,
    /// interpolation of the new Value table plus its DeepFold commitment
    pub value_commit: Duration,
    /// R + rho * (V_new - V_old), combined from existing data, only the Merkle tree is rebuilt
    pub randomizer_update: Duration,
    /// old/new Randomizer, old/new Value
    pub openings: [Duration; 4],
    /// the server checks its own transition proof before accepting the epoch
    pub self_verify: Duration,
}

#[derive(Clone)]
/// a Value or Randomizer polynomial with its table, commitment and the prover data needed to open it later
pub struct CommittedStatePolynomial {
    evaluations: Arc<Vec<Field>>,
    polynomial: Arc<MultilinearPolynomial>,
    commitment: Commitment,
    prover_data: Arc<ProverData>,
}

impl CommittedStatePolynomial {
    pub(crate) fn commit(
        parameters: &Parameters,
        evaluations: Vec<Field>,
        config: &ProverConfig,
    ) -> Result<Self> {
        if evaluations.len() != parameters.polynomial_size() {
            return Err(Error::InvalidParameters("state table has the wrong length"));
        }
        let polynomial = Arc::new(MultilinearPolynomial::from_boolean_evaluations(
            evaluations.clone(),
        )?);
        let (commitment, prover_data) = commit_with_config(parameters, &polynomial, config)?;
        Ok(Self {
            evaluations: Arc::new(evaluations),
            polynomial,
            commitment,
            prover_data: Arc::new(prover_data),
        })
    }

    /// new Randomizer, R + rho * (V_new - V_old), table, coefficients and codeword are all linear in the table,
    /// so they are combined from the three existing ones and no FFT is needed, only merkle tree is rebuilt
    pub(crate) fn commit_linear_update(
        parameters: &Parameters,
        randomizer: &Self,
        old_value: &Self,
        new_value: &Self,
        rho: Field,
        config: &ProverConfig,
    ) -> Result<Self> {
        let combine = |r: &[Field], old: &[Field], new: &[Field]| -> Result<Vec<Field>> {
            if r.len() != old.len() || r.len() != new.len() {
                return Err(Error::InvalidParameters(
                    "linear state update operands have different lengths",
                ));
            }
            Ok(config.install(|| {
                r.par_iter()
                    .zip(old.par_iter())
                    .zip(new.par_iter())
                    .with_min_len(1 << 12)
                    .map(|((r, old), new)| *r + rho * (*new - *old))
                    .collect()
            }))
        };
        let evaluations = combine(
            randomizer.evaluations(),
            old_value.evaluations(),
            new_value.evaluations(),
        )?;
        let polynomial = Arc::new(MultilinearPolynomial::new(combine(
            randomizer.polynomial.coefficients(),
            old_value.polynomial.coefficients(),
            new_value.polynomial.coefficients(),
        )?)?);
        let codeword = combine(
            randomizer.prover_data.codeword(),
            old_value.prover_data.codeword(),
            new_value.prover_data.codeword(),
        )?;
        let (commitment, prover_data) =
            commit_encoded(parameters, Arc::clone(&polynomial), codeword, config)?;
        Ok(Self {
            evaluations: Arc::new(evaluations),
            polynomial,
            commitment,
            prover_data: Arc::new(prover_data),
        })
    }

    pub fn evaluations(&self) -> &[Field] {
        &self.evaluations
    }

    pub fn polynomial(&self) -> &MultilinearPolynomial {
        &self.polynomial
    }

    pub fn commitment(&self) -> &Commitment {
        &self.commitment
    }

    pub fn prover_data(&self) -> &ProverData {
        &self.prover_data
    }

    pub fn retained_bytes(&self) -> usize {
        std::mem::size_of_val(self.evaluations.as_slice()) + self.prover_data.retained_bytes()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateCommitments {
    pub value: Commitment,
    pub randomizer: Commitment,
}

impl StateCommitments {
    pub fn get(&self, which: StatePolynomial) -> &Commitment {
        match which {
            StatePolynomial::Value => &self.value,
            StatePolynomial::Randomizer => &self.randomizer,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// What is posted to the bulletin board each epoch, each epoch
/// includes the digest of the previous one, so they form a chain
pub struct PublicEpoch {
    pub epoch: u64,
    pub parameters: Parameters,
    pub placement_id: Vec<u8>,
    pub previous_digest: [u8; 32],
    pub recurrence_challenge: Option<Field>,
    pub index_root: [u8; 32],
    pub commitments: StateCommitments,
}

impl PublicEpoch {
    /// BLAKE3 of the encoded epoch, used for chaining
    pub fn digest(&self) -> [u8; 32] {
        blake3::hash(&self.to_bytes()).into()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.epoch.to_le_bytes());
        out.extend_from_slice(&(self.parameters.num_vars as u64).to_le_bytes());
        out.extend_from_slice(&(self.parameters.log_blowup as u64).to_le_bytes());
        out.extend_from_slice(&(self.parameters.num_queries as u64).to_le_bytes());
        out.extend_from_slice(&(self.parameters.security_bits as u64).to_le_bytes());
        push_bytes(&mut out, &self.placement_id);
        out.extend_from_slice(&self.previous_digest);
        match self.recurrence_challenge {
            Some(value) => {
                out.push(1);
                out.extend_from_slice(&crate::field::encode_array(&value));
            }
            None => out.push(0),
        }
        out.extend_from_slice(&self.index_root);
        for commitment in [&self.commitments.value, &self.commitments.randomizer] {
            out.extend_from_slice(&commitment.to_bytes());
        }
        out
    }
}

#[derive(Clone)]
/// server-side state of one epoch: the public part plus everything needed to
/// answer lookups for it, probably stored in database in real-word deplyoment
pub struct EpochSnapshot {
    pub(crate) public: PublicEpoch,
    pub(crate) index: Arc<SparseMerkleTree>,
    pub(crate) value: CommittedStatePolynomial,
    pub(crate) randomizer: CommittedStatePolynomial,
    pub(crate) entries: Arc<BTreeMap<usize, Entry>>,
}

impl EpochSnapshot {
    pub fn public(&self) -> &PublicEpoch {
        &self.public
    }

    pub fn polynomial(&self, which: StatePolynomial) -> &CommittedStatePolynomial {
        match which {
            StatePolynomial::Value => &self.value,
            StatePolynomial::Randomizer => &self.randomizer,
        }
    }

    pub fn entries(&self) -> &BTreeMap<usize, Entry> {
        &self.entries
    }

    pub fn index(&self) -> &SparseMerkleTree {
        &self.index
    }
}

/// The IronDict server, keeps every epoch's snapshot and transition proof
pub struct ServerState<B: PlacementBackend> {
    pub(crate) backend: B,
    pub(crate) prover_config: ProverConfig,
    pub(crate) current: Arc<EpochSnapshot>,
    pub(crate) snapshots: Vec<Arc<EpochSnapshot>>,
    pub(crate) transitions: Vec<crate::protocol::epoch::TransitionProof>,
    pub(crate) last_epoch_timings: EpochTimings,
}

impl<B: PlacementBackend> ServerState<B> {
    /// Empty dictionary with 2^num_vars slots, genesis is the
    /// empty tree and two commitments to the zero polynomial
    pub fn new(num_vars: usize, backend: B, prover_threads: usize) -> Result<Self> {
        let parameters = Parameters::new(num_vars)?;
        let prover_config = ProverConfig::new(prover_threads)?;
        let zero = vec![Field::zero(); parameters.polynomial_size()];
        let committed = CommittedStatePolynomial::commit(&parameters, zero, &prover_config)?;
        let index = Arc::new(SparseMerkleTree::new(num_vars)?);
        let public = PublicEpoch {
            epoch: 0,
            parameters,
            placement_id: backend.algorithm_id().to_vec(),
            previous_digest: [0; 32],
            recurrence_challenge: None,
            index_root: index.root(),
            commitments: StateCommitments {
                value: committed.commitment.clone(),
                randomizer: committed.commitment.clone(),
            },
        };
        let snapshot = Arc::new(EpochSnapshot {
            public,
            index,
            value: committed.clone(),
            randomizer: committed,
            entries: Arc::new(BTreeMap::new()),
        });
        Ok(Self {
            backend,
            prover_config,
            current: Arc::clone(&snapshot),
            snapshots: vec![snapshot],
            transitions: Vec::new(),
            last_epoch_timings: EpochTimings::default(),
        })
    }

    /// Load a lot of entries at once without proving them, mainly used for benchmarking
    pub fn from_trusted_checkpoint<I>(
        num_vars: usize,
        backend: B,
        prover_threads: usize,
        entries: I,
    ) -> Result<Self>
    where
        I: IntoIterator<Item = (Vec<u8>, Vec<u8>)>,
    {
        let parameters = Parameters::new(num_vars)?;
        let prover_config = ProverConfig::new(prover_threads)?;
        let capacity = parameters.polynomial_size();
        let mut slots: BTreeMap<usize, Entry> = BTreeMap::new();
        let mut index = SparseMerkleTree::new(num_vars)?;
        let mut value_evaluations = vec![Field::zero(); capacity];

        for (label, value) in entries {
            if label.is_empty() || value.is_empty() {
                return Err(Error::InvalidInput("labels and values must not be empty"));
            }
            let mut placement = None;
            for probe in 0..capacity as u64 {
                let slot = backend.derive_slot(&label, probe, capacity)?;
                match slots.get(&slot) {
                    Some(existing) if existing.label == label => {
                        return Err(Error::InvalidState("duplicate checkpoint label"));
                    }
                    Some(_) => continue,
                    None => {
                        placement = Some((slot, probe));
                        break;
                    }
                }
            }
            let (slot, probe) = placement.ok_or(Error::InvalidState(
                "checkpoint placement exhausted the probe bound",
            ))?;
            index.insert(slot, &label)?;
            value_evaluations[slot] = hash_to_nonzero_field(b"value-encoding", &value);
            slots.insert(
                slot,
                Entry {
                    label,
                    value,
                    probe,
                },
            );
        }

        let value =
            CommittedStatePolynomial::commit(&parameters, value_evaluations, &prover_config)?;
        let randomizer = CommittedStatePolynomial::commit(
            &parameters,
            vec![Field::zero(); capacity],
            &prover_config,
        )?;
        let public = PublicEpoch {
            epoch: 0,
            parameters,
            placement_id: backend.algorithm_id().to_vec(),
            previous_digest: [0; 32],
            recurrence_challenge: None,
            index_root: index.root(),
            commitments: StateCommitments {
                value: value.commitment.clone(),
                randomizer: randomizer.commitment.clone(),
            },
        };
        let snapshot = Arc::new(EpochSnapshot {
            public,
            index: Arc::new(index),
            value,
            randomizer,
            entries: Arc::new(slots),
        });
        Ok(Self {
            backend,
            prover_config,
            current: Arc::clone(&snapshot),
            snapshots: vec![snapshot],
            transitions: Vec::new(),
            last_epoch_timings: EpochTimings::default(),
        })
    }

    pub fn current(&self) -> &Arc<EpochSnapshot> {
        &self.current
    }

    pub fn snapshots(&self) -> &[Arc<EpochSnapshot>] {
        &self.snapshots
    }

    pub fn transitions(&self) -> &[crate::protocol::epoch::TransitionProof] {
        &self.transitions
    }

    /// Keep only the current epoch, long benchmark runs at 2^21 ran out of memory otherwise
    pub fn prune_history(&mut self) {
        self.snapshots = vec![Arc::clone(&self.current)];
        self.transitions.clear();
    }

    /// timings of the epoch published by the last register/update call
    pub fn last_epoch_timings(&self) -> &EpochTimings {
        &self.last_epoch_timings
    }

    pub fn prover_threads(&self) -> usize {
        self.prover_config.threads()
    }

    pub fn prover_config(&self) -> &ProverConfig {
        &self.prover_config
    }

    pub fn retained_state_bytes(&self) -> usize {
        self.current.index.retained_bytes()
            + self.current.value.retained_bytes()
            + self.current.randomizer.retained_bytes()
            + self
                .current
                .entries
                .values()
                .map(|entry| entry.label.len() + entry.value.len() + std::mem::size_of::<Entry>())
                .sum::<usize>()
    }
}

pub(crate) fn push_bytes(out: &mut Vec<u8>, value: &[u8]) {
    out.extend_from_slice(&(value.len() as u32).to_le_bytes());
    out.extend_from_slice(value);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn table(num_vars: usize, seed: u64) -> Vec<Field> {
        (0..1u64 << num_vars)
            .map(|i| Field::from((i ^ seed).wrapping_mul(0x9e37_79b9_7f4a_7c15)))
            .collect()
    }

    #[test]
    fn linear_update_commitment_matches_full_commit() {
        let num_vars = 10;
        let parameters = Parameters::new(num_vars).unwrap();
        let config = ProverConfig::new(4).unwrap();
        let commit =
            |values| CommittedStatePolynomial::commit(&parameters, values, &config).unwrap();
        let randomizer = commit(table(num_vars, 1));
        let old_value = commit(table(num_vars, 2));
        let new_value = commit(table(num_vars, 3));
        let rho = Field::from(0xdead_beefu64);

        let fast = CommittedStatePolynomial::commit_linear_update(
            &parameters,
            &randomizer,
            &old_value,
            &new_value,
            rho,
            &config,
        )
        .unwrap();
        let expected = commit(
            (0..1usize << num_vars)
                .map(|i| {
                    randomizer.evaluations()[i]
                        + rho * (new_value.evaluations()[i] - old_value.evaluations()[i])
                })
                .collect(),
        );
        assert_eq!(fast.commitment(), expected.commitment());
        assert_eq!(fast.evaluations(), expected.evaluations());
        assert_eq!(fast.polynomial(), expected.polynomial());
        assert_eq!(
            fast.prover_data().codeword(),
            expected.prover_data().codeword()
        );
    }
}
