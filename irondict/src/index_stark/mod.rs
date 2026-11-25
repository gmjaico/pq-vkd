//! Index-update STARK, one per registration epoch, it proves the Index root went from the old root to the new root by exactly k insertions into empty slots, in the order fixed by the batch digest, with nothing else
//! changed, the auditor only needs the two roots, k, the digest and the epoch, not the Merkle paths, it doesn't prove a label went into the *right* slot, Clients check that for their own label when they do a lookup

mod air;
mod config;
mod trace;

use p3_uni_stark::{prove, verify};

pub use air::IndexUpdateAir;
pub use config::{IndexStarkConfig, IndexStarkParams};
pub use trace::IndexInsertion;
use trace::trace_height;

use crate::crypto::index_hash::{DigestBytes, canonical_u64, decode_digest, encode_digest};
use crate::pcs::deepfold::parallel::ProverConfig;
use crate::{Error, Result};

type StarkProof = p3_uni_stark::Proof<IndexStarkConfig>;

/// Size limit when deserializing the STARK proof bytes
const MAX_STARK_BYTES: u64 = 64 * 1024 * 1024;

/// Published for an epoch with registrations (the roots are already in the public epochs)
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexUpdateProof {
    /// Number of insertions
    pub k: u64,
    /// Batch digest over the (slot, leaf) insertions, in order
    pub batch_digest: DigestBytes,
    /// The Plonky3 proof, serialized with bincode
    pub stark: Vec<u8>,
}

impl IndexUpdateProof {
    pub fn encoded_len(&self) -> usize {
        self.to_bytes().len()
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.k.to_le_bytes());
        out.extend_from_slice(&self.batch_digest);
        crate::protocol::state::push_bytes(&mut out, &self.stark);
        out
    }
}

fn bincode_options() -> impl bincode::Options {
    use bincode::Options;
    bincode::DefaultOptions::new()
        .with_fixint_encoding()
        .with_limit(MAX_STARK_BYTES)
}

/// Prove the update and return the proof with the new root
pub fn prove_index_update(
    depth: usize,
    epoch: u64,
    old_root: &DigestBytes,
    insertions: &[IndexInsertion],
    prover: &ProverConfig,
) -> Result<(IndexUpdateProof, DigestBytes)> {
    prove_index_update_with(
        &IndexStarkParams::default(),
        depth,
        epoch,
        old_root,
        insertions,
        prover,
    )
}

/// Replays the insertions natively first, so a bad witness (e.g. an
/// occupied slot) fails here instead of producing a proof that won't verify
fn prove_index_update_with(
    params: &IndexStarkParams,
    depth: usize,
    epoch: u64,
    old_root: &DigestBytes,
    insertions: &[IndexInsertion],
    prover: &ProverConfig,
) -> Result<(IndexUpdateProof, DigestBytes)> {
    let config = params.config()?;
    let replay = trace::replay(depth, epoch, decode_digest(old_root)?, insertions)?;
    let k = insertions.len() as u64;
    let public = trace::public_values(
        &replay.old_root,
        &replay.new_root,
        k,
        &replay.batch_digest,
        replay.epoch,
    )?;
    let air = IndexUpdateAir::new(depth);
    let proof: StarkProof = prover.install(|| {
        let trace = trace::generate_trace(&replay);
        prove(&config, &air, trace, &public)
    });
    use bincode::Options;
    let stark = bincode_options()
        .serialize(&proof)
        .map_err(|_| Error::Serialization("Index STARK serialization failed"))?;
    Ok((
        IndexUpdateProof {
            k,
            batch_digest: encode_digest(&replay.batch_digest),
            stark,
        },
        encode_digest(&replay.new_root),
    ))
}

/// What the auditor runs for a registration epoch
pub fn verify_index_update(
    depth: usize,
    epoch: u64,
    old_root: &DigestBytes,
    new_root: &DigestBytes,
    proof: &IndexUpdateProof,
) -> Result<()> {
    verify_index_update_with(
        &IndexStarkParams::default(),
        depth,
        epoch,
        old_root,
        new_root,
        proof,
    )
}

fn verify_index_update_with(
    params: &IndexStarkParams,
    depth: usize,
    epoch: u64,
    old_root: &DigestBytes,
    new_root: &DigestBytes,
    proof: &IndexUpdateProof,
) -> Result<()> {
    if !(1..=crate::Parameters::MAX_NUM_VARS).contains(&depth) {
        return Err(Error::InvalidParameters("Index depth out of range"));
    }
    if proof.k == 0 || proof.k > (1u64 << depth) {
        return Err(Error::MalformedProof("invalid Index insertion count"));
    }
    let config = params.config()?;
    let public = trace::public_values(
        &decode_digest(old_root)?,
        &decode_digest(new_root)?,
        proof.k,
        &decode_digest(&proof.batch_digest)?,
        canonical_u64(epoch, "epoch exceeds the KoalaBear modulus")?,
    )?;
    use bincode::Options;
    let stark: StarkProof = bincode_options()
        .deserialize(&proof.stark)
        .map_err(|_| Error::MalformedProof("malformed Index STARK"))?;
    // The trace height only depends on k and depth, so reject anything else
    let expected_bits = trace_height(depth, proof.k as usize).trailing_zeros() as usize;
    if stark.degree_bits != expected_bits {
        return Err(Error::MalformedProof("unexpected Index STARK trace height"));
    }
    let air = IndexUpdateAir::new(depth);
    // Plonky3's verifier can panic on malformed proofs, so treat a panic as a rejection
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        verify(&config, &air, &stark, &public)
    }));
    match outcome {
        Ok(Ok(())) => Ok(()),
        _ => Err(Error::VerificationFailed("Index STARK verification failed")),
    }
}

/// Optional auditor check if the server also publishes the insertion list
pub fn check_published_insertions(
    epoch: u64,
    published: &[(usize, crate::crypto::index_hash::Digest)],
    proof: &IndexUpdateProof,
) -> Result<()> {
    if published.len() as u64 != proof.k {
        return Err(Error::VerificationFailed("Q_t length does not match k"));
    }
    let digest = crate::crypto::index_hash::batch_digest(epoch, published)?;
    if encode_digest(&digest) != proof.batch_digest {
        return Err(Error::VerificationFailed("Q_t does not match batch digest"));
    }
    Ok(())
}

#[cfg(test)]
mod tests;
