//! Poseidon2 hashes for the Index tree, the STARK uses the exact same
//! functions, so the tree built here and the one in the AIR always agree

use std::sync::OnceLock;

use p3_field::{PrimeCharacteristicRing, PrimeField32};
use p3_koala_bear::{
    KoalaBear, Poseidon2KoalaBear, default_koalabear_poseidon2_16, default_koalabear_poseidon2_24,
};
use p3_symmetric::Permutation;

use crate::{Error, Result};

/// Index tree uses KoalaBear so the same hashes can be checked inside the Plonky3 STARK
pub type F = KoalaBear;
pub const DIGEST_ELEMS: usize = 8;
pub type Digest = [F; DIGEST_ELEMS];
pub type DigestBytes = [u8; 32];

pub const DIGEST_ZERO: Digest = [F::ZERO; DIGEST_ELEMS];

pub const LEAF_TAG: u32 = 1;
pub const BATCH_TAG: u32 = 3;

const LABEL_DOMAIN: &[u8] = b"irondict/index/v1/label-identifier";

pub fn poseidon2_16() -> &'static Poseidon2KoalaBear<16> {
    static PERM: OnceLock<Poseidon2KoalaBear<16>> = OnceLock::new();
    PERM.get_or_init(default_koalabear_poseidon2_16)
}

pub fn poseidon2_24() -> &'static Poseidon2KoalaBear<24> {
    static PERM: OnceLock<Poseidon2KoalaBear<24>> = OnceLock::new();
    PERM.get_or_init(default_koalabear_poseidon2_24)
}

fn truncate<const W: usize>(state: [F; W]) -> Digest {
    std::array::from_fn(|i| state[i])
}

pub fn node_input(left: &Digest, right: &Digest) -> [F; 16] {
    std::array::from_fn(|i| if i < 8 { left[i] } else { right[i - 8] })
}

pub fn leaf_input(identifier: &Digest) -> [F; 24] {
    let mut input = [F::ZERO; 24];
    input[0] = F::new(LEAF_TAG);
    input[1..9].copy_from_slice(identifier);
    input
}

pub fn batch_input(previous: &Digest, idx: usize, leaf: &Digest) -> [F; 24] {
    let mut input = [F::ZERO; 24];
    input[0] = F::new(BATCH_TAG);
    input[1..9].copy_from_slice(previous);
    input[9] = slot_element(idx);
    input[10..18].copy_from_slice(leaf);
    input
}

/// Internal node: width-16 Poseidon2 on left || right, keep the first 8
pub fn h_node(left: &Digest, right: &Digest) -> Digest {
    truncate(poseidon2_16().permute(node_input(left, right)))
}

/// Occupied leaf: width-24 Poseidon2 on (LEAF_TAG, identifier, 0...)
pub fn h_leaf(identifier: &Digest) -> Digest {
    truncate(poseidon2_24().permute(leaf_input(identifier)))
}

/// One step of the batch digest: d_i = H(BATCH_TAG, d_(i-1), slot,
/// leaf), this fixes the order of the insertions inside the STARK
pub fn h_batch(previous: &Digest, idx: usize, leaf: &Digest) -> Digest {
    truncate(poseidon2_24().permute(batch_input(previous, idx, leaf)))
}

/// d_0 = (epoch, 0, ..., 0), so a batch proof can't be replayed in another epoch
pub fn initial_batch_digest(epoch: u64) -> Result<Digest> {
    let mut digest = DIGEST_ZERO;
    digest[0] = canonical_u64(epoch, "epoch exceeds the KoalaBear modulus")?;
    Ok(digest)
}

/// d_k for a list of (slot, leaf) insertions in placement order
pub fn batch_digest(epoch: u64, insertions: &[(usize, Digest)]) -> Result<Digest> {
    let mut digest = initial_batch_digest(epoch)?;
    for (idx, leaf) in insertions {
        digest = h_batch(&digest, *idx, leaf);
    }
    Ok(digest)
}

/// labels are arbitrary bytes, so they are hashed with BLAKE3 outside the STARK
/// and mapped to 8 KoalaBear elements, the leaf stores this, not the label
pub fn label_identifier(label: &[u8]) -> Digest {
    let mut hasher = blake3::Hasher::new();
    hasher.update(&(LABEL_DOMAIN.len() as u64).to_le_bytes());
    hasher.update(LABEL_DOMAIN);
    hasher.update(&(label.len() as u64).to_le_bytes());
    hasher.update(label);
    let mut bytes = [0u8; 64];
    hasher.finalize_xof().fill(&mut bytes);
    std::array::from_fn(|i| {
        let chunk = u64::from_le_bytes(bytes[8 * i..8 * i + 8].try_into().expect("8 bytes"));
        F::new((chunk % u64::from(F::ORDER_U32)) as u32)
    })
}

pub fn slot_element(idx: usize) -> F {
    debug_assert!(idx < F::ORDER_U32 as usize);
    F::new(idx as u32)
}

pub fn canonical_u64(value: u64, message: &'static str) -> Result<F> {
    if value >= u64::from(F::ORDER_U32) {
        return Err(Error::InvalidInput(message));
    }
    Ok(F::new(value as u32))
}

pub fn encode_digest(digest: &Digest) -> DigestBytes {
    let mut out = [0u8; 32];
    for (chunk, element) in out.chunks_exact_mut(4).zip(digest) {
        chunk.copy_from_slice(&element.as_canonical_u32().to_le_bytes());
    }
    out
}

pub fn decode_digest(bytes: &DigestBytes) -> Result<Digest> {
    let mut digest = DIGEST_ZERO;
    for (element, chunk) in digest.iter_mut().zip(bytes.chunks_exact(4)) {
        let value = u32::from_le_bytes(chunk.try_into().expect("4 bytes"));
        if value >= F::ORDER_U32 {
            return Err(Error::Serialization("non-canonical Index digest element"));
        }
        *element = F::new(value);
    }
    Ok(digest)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn digest_encoding_round_trip() {
        let digest = label_identifier(b"alice");
        assert_eq!(decode_digest(&encode_digest(&digest)).unwrap(), digest);
        let mut bad = encode_digest(&digest);
        bad[..4].copy_from_slice(&F::ORDER_U32.to_le_bytes());
        assert!(decode_digest(&bad).is_err());
    }

    #[test]
    fn domains_and_inputs_are_separated() {
        let id = label_identifier(b"alice");
        assert_ne!(label_identifier(b"alice"), label_identifier(b"bob"));
        assert_ne!(h_leaf(&id), DIGEST_ZERO);
        assert_ne!(h_leaf(&id), h_batch(&DIGEST_ZERO, 0, &id));
        assert_ne!(h_node(&id, &DIGEST_ZERO), h_node(&DIGEST_ZERO, &id));
        let d1 = batch_digest(7, &[(1, id), (2, id)]).unwrap();
        let d2 = batch_digest(7, &[(2, id), (1, id)]).unwrap();
        assert_ne!(d1, d2);
        assert_ne!(d1, batch_digest(8, &[(1, id), (2, id)]).unwrap());
        assert!(initial_batch_digest(u64::from(F::ORDER_U32)).is_err());
    }
}
