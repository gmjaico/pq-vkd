//! Plonky3 setup for the Index STARK: FRI with Poseidon2 Merkle trees over KoalaBear

use p3_challenger::{
    CanObserve, CanSample, CanSampleBits, DuplexChallenger, FieldChallenger, GrindingChallenger,
};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::extension::BinomialExtensionField;
use p3_field::{Field, PrimeField64};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_koala_bear::{KoalaBear, Poseidon2KoalaBear};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{MerkleCap, PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use rayon::prelude::*;

use crate::crypto::index_hash::{poseidon2_16, poseidon2_24};
use crate::{Error, Result};

pub type Val = KoalaBear;
pub type Challenge = BinomialExtensionField<Val, 4>;
type Perm16 = Poseidon2KoalaBear<16>;
type Perm24 = Poseidon2KoalaBear<24>;
type LeafHash = PaddingFreeSponge<Perm24, 24, 16, 8>;
type NodeCompress = TruncatedPermutation<Perm16, 2, 8, 16>;
type ValMmcs =
    MerkleTreeMmcs<<Val as Field>::Packing, <Val as Field>::Packing, LeafHash, NodeCompress, 2, 8>;
type ChallengeMmcs = ExtensionMmcs<Val, Challenge, ValMmcs>;
type Challenger = DeterministicChallenger;
type Duplex = DuplexChallenger<Val, Perm24, 24, 16>;

#[derive(Clone, Debug)]
pub struct DeterministicChallenger(Duplex);

impl CanObserve<Val> for DeterministicChallenger {
    fn observe(&mut self, value: Val) {
        self.0.observe(value);
    }
}

impl<const N: usize> CanObserve<MerkleCap<Val, [Val; N]>> for DeterministicChallenger {
    fn observe(&mut self, cap: MerkleCap<Val, [Val; N]>) {
        self.0.observe(cap);
    }
}

impl<T> CanSample<T> for DeterministicChallenger
where
    Duplex: CanSample<T>,
{
    fn sample(&mut self) -> T {
        self.0.sample()
    }
}

impl CanSampleBits<usize> for DeterministicChallenger {
    fn sample_bits(&mut self, bits: usize) -> usize {
        self.0.sample_bits(bits)
    }
}

impl FieldChallenger<Val> for DeterministicChallenger {}

impl GrindingChallenger for DeterministicChallenger {
    type Witness = Val;

    fn grind(&mut self, bits: usize) -> Val {
        assert!(bits < 31, "proof-of-work bit count exceeds field size");
        let witness = (0..Val::ORDER_U64)
            .into_par_iter()
            .map(|i| Val::new(i as u32))
            .find_first(|witness| self.clone().check_witness(bits, *witness))
            .expect("failed to find proof-of-work witness");
        assert!(self.check_witness(bits, witness));
        witness
    }
}
type Dft = Radix2DitParallel<Val>;
type Pcs = TwoAdicFriPcs<Val, Dft, ValMmcs, ChallengeMmcs>;
pub type IndexStarkConfig = StarkConfig<Pcs, Challenge, Challenger>;

/// FRI parameters (prover and auditor must use the same)
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct IndexStarkParams {
    pub log_blowup: usize,
    pub num_queries: usize,
    pub query_pow_bits: usize,
    pub log_final_poly_len: usize,
    pub max_log_arity: usize,
}

impl Default for IndexStarkParams {
    /// Log blowup 1, 16 PoW bits, and enough queries for 100 conjectured bits
    fn default() -> Self {
        Self::with_blowup(1)
    }
}

impl IndexStarkParams {
    pub const TARGET_BITS: usize = 100;
    pub const POW_BITS: usize = 16;

    /// Pick the number of queries so log_blowup * queries + pow_bits >= 100
    pub fn with_blowup(log_blowup: usize) -> Self {
        let log_blowup = log_blowup.max(1);
        let needed = Self::TARGET_BITS - Self::POW_BITS;
        Self {
            log_blowup,
            num_queries: needed.div_ceil(log_blowup),
            query_pow_bits: Self::POW_BITS,
            log_final_poly_len: 0,
            // Fold by 8 instead of 2: fewer FRI layers, so fewer Merkle paths per query, commit-phase
            // error is about 2^-103 at 2^18 rows, still below the 2^-100 from the queries
            max_log_arity: 3,
        }
    }

    pub fn validate(&self) -> Result<()> {
        if !(1..=4).contains(&self.log_blowup)
            || self.num_queries == 0
            || self.num_queries > 512
            || self.query_pow_bits > 30
            || self.max_log_arity == 0
            || self.max_log_arity > 4
            || self.log_final_poly_len > 8
        {
            return Err(Error::InvalidParameters("invalid Index STARK parameters"));
        }
        Ok(())
    }

    pub fn config(&self) -> Result<IndexStarkConfig> {
        self.validate()?;
        let perm16 = poseidon2_16().clone();
        let perm24 = poseidon2_24().clone();
        let val_mmcs = ValMmcs::new(LeafHash::new(perm24.clone()), NodeCompress::new(perm16), 0);
        let challenge_mmcs = ChallengeMmcs::new(val_mmcs.clone());
        let fri = FriParameters {
            log_blowup: self.log_blowup,
            log_final_poly_len: self.log_final_poly_len,
            max_log_arity: self.max_log_arity,
            num_queries: self.num_queries,
            commit_proof_of_work_bits: 0,
            query_proof_of_work_bits: self.query_pow_bits,
            mmcs: challenge_mmcs,
        };
        let pcs = Pcs::new(Dft::default(), val_mmcs, fri);
        Ok(IndexStarkConfig::new(
            pcs,
            DeterministicChallenger(Duplex::new(perm24)),
        ))
    }
}
