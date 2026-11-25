//! Where a label goes in the table (the probe sequence used by registration and lookup)

use crate::{Error, Result};

pub const BLAKE3_PLACEMENT_ID: &[u8] = b"irondict-poc/blake3-placement/v1";

/// Maps (label, probe) to a slot, it is swappable for a VRF for future work
pub trait PlacementBackend: Clone {
    type Proof: Clone + std::fmt::Debug + PartialEq + Eq;

    fn algorithm_id(&self) -> &'static [u8];
    fn derive_slot(&self, label: &[u8], probe: u64, capacity: usize) -> Result<usize>;
    fn prove_slot(&self, label: &[u8], probe: u64, capacity: usize) -> Result<Self::Proof>;
    fn verify_slot(
        &self,
        label: &[u8],
        probe: u64,
        capacity: usize,
        slot: usize,
        proof: &Self::Proof,
    ) -> Result<()>;
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
/// slot = BLAKE3(label, probe, capacity) mod capacity
pub struct Blake3Placement;

impl PlacementBackend for Blake3Placement {
    type Proof = ();

    fn algorithm_id(&self) -> &'static [u8] {
        BLAKE3_PLACEMENT_ID
    }

    fn derive_slot(&self, label: &[u8], probe: u64, capacity: usize) -> Result<usize> {
        if label.is_empty() {
            return Err(Error::InvalidInput("labels must not be empty"));
        }
        if capacity == 0 || capacity > u64::MAX as usize {
            return Err(Error::InvalidParameters("invalid placement capacity"));
        }
        let bound = capacity as u64;
        // Rejection sampling so every slot is equally likely (no modulo bias)
        let zone = u64::MAX - (u64::MAX % bound);
        for rejection_counter in 0u64..1024 {
            let mut hasher = blake3::Hasher::new();
            append(&mut hasher, b"protocol", BLAKE3_PLACEMENT_ID);
            append(&mut hasher, b"label", label);
            append(&mut hasher, b"probe", &probe.to_le_bytes());
            append(
                &mut hasher,
                b"capacity",
                &u64::try_from(capacity)
                    .map_err(|_| Error::InvalidParameters("placement capacity exceeds u64"))?
                    .to_le_bytes(),
            );
            append(
                &mut hasher,
                b"rejection-counter",
                &rejection_counter.to_le_bytes(),
            );
            let bytes = hasher.finalize();
            let candidate = u64::from_le_bytes(bytes.as_bytes()[..8].try_into().expect("8 bytes"));
            if candidate < zone {
                return Ok((candidate % bound) as usize);
            }
        }
        Err(Error::InvalidState(
            "placement rejection sampling exhausted",
        ))
    }

    fn prove_slot(&self, label: &[u8], probe: u64, capacity: usize) -> Result<Self::Proof> {
        self.derive_slot(label, probe, capacity).map(|_| ())
    }

    fn verify_slot(
        &self,
        label: &[u8],
        probe: u64,
        capacity: usize,
        slot: usize,
        _proof: &Self::Proof,
    ) -> Result<()> {
        if self.derive_slot(label, probe, capacity)? != slot {
            return Err(Error::VerificationFailed("incorrect placement slot"));
        }
        Ok(())
    }
}

fn append(hasher: &mut blake3::Hasher, label: &[u8], value: &[u8]) {
    hasher.update(&(label.len() as u64).to_le_bytes());
    hasher.update(label);
    hasher.update(&(value.len() as u64).to_le_bytes());
    hasher.update(value);
}
