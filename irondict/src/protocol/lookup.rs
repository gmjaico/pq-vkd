//! Lookups: proving a label's value, or that the label is not there. Client lookup in report

use crate::crypto::placement::PlacementBackend;
use crate::crypto::protocol_transcript::{ProtocolTranscript, hash_to_nonzero_field};
use crate::crypto::sparse_merkle::{IndexLeaf, MerkleProof, label_identifier};
use crate::protocol::opening::{AuthenticatedOpening, slot_to_point};
use crate::protocol::state::push_bytes;
use crate::protocol::state::{EpochSnapshot, PublicEpoch, ServerState};
use crate::{Error, Result};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupProbe<P> {
    pub counter: u64,
    pub slot: usize,
    pub placement_proof: P,
    pub index: MerkleProof,
}

#[derive(Clone, Debug, PartialEq, Eq)]

pub struct MembershipClaim {
    pub value: Vec<u8>,
    pub opening: AuthenticatedOpening,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LookupProof<P> {
    pub statement_digest: [u8; 32],
    pub probes: Vec<LookupProbe<P>>,
    pub membership: Option<MembershipClaim>,
}

impl<P> LookupProof<P> {
    pub fn opening_count(&self) -> usize {
        usize::from(self.membership.is_some())
    }
}

impl LookupProof<()> {
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.statement_digest);
        out.extend_from_slice(&(self.probes.len() as u32).to_le_bytes());
        for probe in &self.probes {
            out.extend_from_slice(&probe.counter.to_le_bytes());
            out.extend_from_slice(&(probe.slot as u64).to_le_bytes());
            push_bytes(&mut out, &probe.index.to_bytes());
        }
        match &self.membership {
            None => out.push(0),
            Some(claim) => {
                out.push(1);
                push_bytes(&mut out, &claim.value);
                crate::protocol::epoch::push_opening(&mut out, &claim.opening);
            }
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifiedLookupResult {
    Present { value: Vec<u8>, slot: usize },
    Absent,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedLookup {
    pub epoch: u64,
    pub state_digest: [u8; 32],
    pub result: VerifiedLookupResult,
}

/// probes of a label up to its own slot, Merkle paths only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlacementPath<P> {
    pub probes: Vec<LookupProbe<P>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedPlacement {
    Occupied { slot: usize },
    Empty { slot: usize },
}

impl PlacementPath<()> {
    pub(crate) fn push_bytes(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&(self.probes.len() as u32).to_le_bytes());
        for probe in &self.probes {
            out.extend_from_slice(&probe.counter.to_le_bytes());
            out.extend_from_slice(&(probe.slot as u64).to_le_bytes());
            push_bytes(out, &probe.index.to_bytes());
        }
    }
}

impl<B: PlacementBackend> ServerState<B> {
    /// follow the label's probe sequence until we hit its slot or an empty one.
    pub fn prove_placement(
        &self,
        snapshot: &EpochSnapshot,
        label: &[u8],
    ) -> Result<(PlacementPath<B::Proof>, VerifiedPlacement)> {
        if label.is_empty() {
            return Err(Error::InvalidInput("labels must not be empty"));
        }
        let capacity = snapshot.public.parameters.polynomial_size();
        let mut probes = Vec::new();
        for counter in 0..capacity as u64 {
            let slot = self.backend.derive_slot(label, counter, capacity)?;
            probes.push(LookupProbe {
                counter,
                slot,
                placement_proof: self.backend.prove_slot(label, counter, capacity)?,
                index: snapshot.index.proof(slot)?,
            });
            match snapshot.entries.get(&slot) {
                Some(entry) if entry.label == label => {
                    return Ok((
                        PlacementPath { probes },
                        VerifiedPlacement::Occupied { slot },
                    ));
                }
                Some(_) => continue,
                None => {
                    return Ok((PlacementPath { probes }, VerifiedPlacement::Empty { slot }));
                }
            }
        }
        Err(Error::InvalidState(
            "lookup probe bound exhausted without a terminal slot",
        ))
    }

    /// lookup proof: the probe paths, plus a Value opening if the label exists.
    pub fn prove_lookup(
        &self,
        snapshot: &EpochSnapshot,
        label: &[u8],
    ) -> Result<LookupProof<B::Proof>> {
        let (path, placement) = self.prove_placement(snapshot, label)?;
        let membership = match placement {
            VerifiedPlacement::Empty { .. } => None,
            VerifiedPlacement::Occupied { slot } => {
                let entry = snapshot
                    .entries
                    .get(&slot)
                    .ok_or(Error::InvalidState("occupied slot lacks entry"))?;
                let point = slot_to_point(slot, snapshot.public.parameters.num_vars)?;
                Some(MembershipClaim {
                    value: entry.value.clone(),
                    opening: AuthenticatedOpening::prove(
                        &snapshot.public.parameters,
                        snapshot.value.commitment(),
                        snapshot.value.prover_data(),
                        &point,
                        &self.prover_config,
                    )?,
                })
            }
        };
        Ok(LookupProof {
            statement_digest: lookup_statement_digest(&snapshot.public, label),
            probes: path.probes,
            membership,
        })
    }
}

/// checks the probes are the label's probes in order, every path matches the
/// Index root, and the chain only stops at the label or an empty slot.
pub fn verify_placement<B: PlacementBackend>(
    backend: &B,
    public: &PublicEpoch,
    label: &[u8],
    probes: &[LookupProbe<B::Proof>],
) -> Result<VerifiedPlacement> {
    public.parameters.validate()?;
    if label.is_empty() || public.placement_id != backend.algorithm_id() {
        return Err(Error::InvalidInput("lookup placement context is invalid"));
    }
    if probes.is_empty() {
        return Err(Error::VerificationFailed("lookup statement binding"));
    }
    let capacity = public.parameters.polynomial_size();
    if probes.len() > capacity {
        return Err(Error::MalformedProof("lookup exceeds probe bound"));
    }
    let identifier = label_identifier(label);
    for (position, probe) in probes.iter().enumerate() {
        if probe.counter != position as u64 {
            return Err(Error::VerificationFailed(
                "lookup probes are reordered or skipped",
            ));
        }
        backend.verify_slot(
            label,
            probe.counter,
            capacity,
            probe.slot,
            &probe.placement_proof,
        )?;
        if probe.index.slot != probe.slot {
            return Err(Error::VerificationFailed("Index proof slot mismatch"));
        }
        probe
            .index
            .verify(public.parameters.num_vars, &public.index_root)?;
        let final_probe = position + 1 == probes.len();
        if !final_probe
            && (matches!(&probe.index.leaf, IndexLeaf::Empty)
                || matches!(&probe.index.leaf, IndexLeaf::Occupied(existing) if *existing == identifier))
        {
            return Err(Error::VerificationFailed(
                "lookup continued after terminal probe",
            ));
        }
    }
    let terminal = probes.last().expect("non-empty checked");
    match &terminal.index.leaf {
        IndexLeaf::Empty => Ok(VerifiedPlacement::Empty {
            slot: terminal.slot,
        }),
        IndexLeaf::Occupied(existing) if *existing == identifier => {
            Ok(VerifiedPlacement::Occupied {
                slot: terminal.slot,
            })
        }
        _ => Err(Error::VerificationFailed(
            "lookup probe chain ends at a foreign slot",
        )),
    }
}

/// client check. If the label exists, also checks the Value opening and that
/// it matches the hash of the returned value.
pub fn verify_lookup<B: PlacementBackend>(
    backend: &B,
    public: &PublicEpoch,
    label: &[u8],
    proof: &LookupProof<B::Proof>,
) -> Result<VerifiedLookup> {
    let expected_digest = lookup_statement_digest(public, label);
    if proof.statement_digest != expected_digest {
        return Err(Error::VerificationFailed("lookup statement binding"));
    }
    let placement = verify_placement(backend, public, label, &proof.probes)?;
    let result = match (&proof.membership, placement) {
        (None, VerifiedPlacement::Empty { .. }) => VerifiedLookupResult::Absent,
        (None, VerifiedPlacement::Occupied { .. }) => {
            return Err(Error::VerificationFailed(
                "non-membership does not end at an empty slot",
            ));
        }
        (Some(_), VerifiedPlacement::Empty { .. }) => {
            return Err(Error::VerificationFailed(
                "invalid membership terminal claim",
            ));
        }
        (Some(claim), VerifiedPlacement::Occupied { slot }) => {
            if claim.value.is_empty() {
                return Err(Error::VerificationFailed(
                    "invalid membership terminal claim",
                ));
            }
            let point = slot_to_point(slot, public.parameters.num_vars)?;
            claim
                .opening
                .verify(&public.parameters, &public.commitments.value, &point)?;
            if claim.opening.value != hash_to_nonzero_field(b"value-encoding", &claim.value) {
                return Err(Error::VerificationFailed("membership value encoding"));
            }
            VerifiedLookupResult::Present {
                value: claim.value.clone(),
                slot,
            }
        }
    };
    Ok(VerifiedLookup {
        epoch: public.epoch,
        state_digest: public.digest(),
        result,
    })
}

pub(crate) fn lookup_statement_digest(public: &PublicEpoch, label: &[u8]) -> [u8; 32] {
    let mut transcript = ProtocolTranscript::new(b"lookup-statement");
    transcript.append_bytes(b"public-epoch", &public.to_bytes());
    transcript.append_bytes(b"label", label);
    transcript.digest()
}
