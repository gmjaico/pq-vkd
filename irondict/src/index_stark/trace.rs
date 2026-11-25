//! Builds the trace for the Index STARK from a batch of insertions

use core::borrow::BorrowMut;
use core::mem::MaybeUninit;

use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::generate_trace_rows_for_perm;
use rayon::prelude::*;

use super::air::{
    A_RANGE, B_RANGE, C_RANGE, Cols16, Cols24, HALF_FULL_ROUNDS, Linear, MAIN_WIDTH, MainCols,
    NUM_PUBLIC_VALUES, PARTIAL_ROUNDS_16, PARTIAL_ROUNDS_24, PV_DIGEST, PV_EPOCH, PV_K,
    PV_NEW_ROOT, PV_OLD_ROOT, SBOX_DEGREE, SBOX_REGISTERS, TRACE_WIDTH, constants_16, constants_24,
};
use crate::crypto::index_hash::{
    DIGEST_ELEMS, DIGEST_ZERO, Digest, F, batch_input, canonical_u64, h_batch, h_node,
    initial_batch_digest, node_input, slot_element,
};
use crate::{Error, Result};

/// One insertion into a previously empty slot, in placement order
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndexInsertion {
    pub slot: usize,
    pub leaf: Digest,
    pub siblings: Vec<Digest>,
}

/// the batch replayed outside the STARK: roots, digests and path values for every step
pub(crate) struct Replay {
    pub depth: usize,
    pub epoch: F,
    pub old_root: Digest,
    pub new_root: Digest,
    pub batch_digest: Digest,
    pub steps: Vec<ReplayStep>,
}

pub(crate) struct ReplayStep {
    pub slot: usize,
    pub leaf: Digest,
    pub siblings: Vec<Digest>,
    /// Node values entering each level on the old and the new path
    pub cur_old: Vec<Digest>,
    pub cur_new: Vec<Digest>,
    pub r_cur: Digest,
    pub r_next: Digest,
    pub d_prev: Digest,
    pub d_cur: Digest,
}

// (left, right) at this level, depending on bit height of the slot
fn ordered(slot: usize, height: usize, cur: &Digest, sib: &Digest) -> (Digest, Digest) {
    if (slot >> height) & 1 == 0 {
        (*cur, *sib)
    } else {
        (*sib, *cur)
    }
}

/// replays the batch: checks each slot is empty under the current
/// root, then works out the root and batch digest after every insertion
pub(crate) fn replay(
    depth: usize,
    epoch: u64,
    old_root: Digest,
    insertions: &[IndexInsertion],
) -> Result<Replay> {
    if !(1..=crate::Parameters::MAX_NUM_VARS).contains(&depth) {
        return Err(Error::InvalidParameters("Index depth out of range"));
    }
    if insertions.is_empty() {
        return Err(Error::InvalidInput(
            "Index update needs at least one insertion",
        ));
    }
    let epoch_element = canonical_u64(epoch, "epoch exceeds the KoalaBear modulus")?;
    let mut root = old_root;
    let mut digest = initial_batch_digest(epoch)?;
    let mut steps = Vec::with_capacity(insertions.len());
    for insertion in insertions {
        if insertion.slot >= (1usize << depth) || insertion.siblings.len() != depth {
            return Err(Error::InvalidInput("malformed Index insertion witness"));
        }
        if insertion.leaf == DIGEST_ZERO {
            return Err(Error::InvalidInput("Index leaf hash must be non-zero"));
        }
        let mut cur_old = Vec::with_capacity(depth);
        let mut cur_new = Vec::with_capacity(depth);
        let (mut old, mut new) = (DIGEST_ZERO, insertion.leaf);
        for (height, sib) in insertion.siblings.iter().enumerate() {
            cur_old.push(old);
            cur_new.push(new);
            let (l, r) = ordered(insertion.slot, height, &old, sib);
            old = h_node(&l, &r);
            let (l, r) = ordered(insertion.slot, height, &new, sib);
            new = h_node(&l, &r);
        }
        if old != root {
            return Err(Error::InvalidState(
                "Index insertion slot is not empty under the running root",
            ));
        }
        let d_cur = h_batch(&digest, insertion.slot, &insertion.leaf);
        steps.push(ReplayStep {
            slot: insertion.slot,
            leaf: insertion.leaf,
            siblings: insertion.siblings.clone(),
            cur_old,
            cur_new,
            r_cur: root,
            r_next: new,
            d_prev: digest,
            d_cur,
        });
        root = new;
        digest = d_cur;
    }
    Ok(Replay {
        depth,
        epoch: epoch_element,
        old_root,
        new_root: root,
        batch_digest: digest,
        steps,
    })
}

/// The public values in the order the AIR reads them
pub(crate) fn public_values(
    old_root: &Digest,
    new_root: &Digest,
    k: u64,
    batch_digest: &Digest,
    epoch: F,
) -> Result<Vec<F>> {
    let mut values = vec![F::ZERO; NUM_PUBLIC_VALUES];
    values[PV_OLD_ROOT..PV_OLD_ROOT + DIGEST_ELEMS].copy_from_slice(old_root);
    values[PV_NEW_ROOT..PV_NEW_ROOT + DIGEST_ELEMS].copy_from_slice(new_root);
    values[PV_K] = canonical_u64(k, "insertion count exceeds the KoalaBear modulus")?;
    values[PV_DIGEST..PV_DIGEST + DIGEST_ELEMS].copy_from_slice(batch_digest);
    values[PV_EPOCH] = epoch;
    Ok(values)
}

pub fn trace_height(depth: usize, k: usize) -> usize {
    (k * depth).next_power_of_two().max(4)
}

fn as_uninit(slice: &mut [F]) -> &mut [MaybeUninit<F>] {
    // SAFETY: MaybeUninit<F> has the same layout as F, and every element
    // is overwritten with an initialised value by the Poseidon2 generator
    unsafe { &mut *(slice as *mut [F] as *mut [MaybeUninit<F>]) }
}

pub(crate) fn generate_trace(replay: &Replay) -> RowMajorMatrix<F> {
    let depth = replay.depth;
    let k = replay.steps.len();
    let height = trace_height(depth, k);
    let c16 = constants_16();
    let c24 = constants_24();
    let pad_q: Digest = std::array::from_fn(|j| if j == 0 { F::ONE } else { F::ZERO });
    let mut values = F::zero_vec(height * TRACE_WIDTH);
    values
        .par_chunks_exact_mut(TRACE_WIDTH)
        .enumerate()
        .for_each(|(row_index, row)| {
            let step_index = row_index / depth;
            let h = row_index % depth;
            let step = replay.steps.get(step_index);
            let (main, hashes) = row.split_at_mut(MAIN_WIDTH);
            let main: &mut MainCols<F> = main.borrow_mut();

            main.cnt = F::from_usize(h);
            main.is_first = F::from_bool(h == 0);
            main.is_last = F::from_bool(h + 1 == depth);
            main.inv_last = if h + 1 == depth {
                F::ZERO
            } else {
                (F::from_usize(h) - F::from_usize(depth - 1))
                    .try_inverse()
                    .expect("non-zero")
            };
            main.pow = F::from_u64(1u64 << h);

            let (a_input, b_input, c_input) = match step {
                Some(step) => {
                    main.is_insert = F::ONE;
                    main.bit = F::from_bool((step.slot >> h) & 1 == 1);
                    main.acc = slot_element(step.slot & ((1usize << (h + 1)) - 1));
                    main.idx = slot_element(step.slot);
                    main.kcnt = F::from_usize(step_index + 1);
                    main.sib = step.siblings[h];
                    main.cur_old = step.cur_old[h];
                    main.cur_new = step.cur_new[h];
                    main.q = step.leaf;
                    main.r_cur = step.r_cur;
                    main.r_next = step.r_next;
                    main.d_prev = step.d_prev;
                    main.d_cur = step.d_cur;
                    let (l, r) = ordered(step.slot, h, &step.cur_old[h], &step.siblings[h]);
                    let a = node_input(&l, &r);
                    let (l, r) = ordered(step.slot, h, &step.cur_new[h], &step.siblings[h]);
                    let b = node_input(&l, &r);
                    let c = if h == 0 {
                        batch_input(&step.d_prev, step.slot, &step.leaf)
                    } else {
                        [F::ZERO; 24]
                    };
                    (a, b, c)
                }
                None => {
                    main.kcnt = F::from_usize(k);
                    main.q = pad_q;
                    main.r_cur = replay.new_root;
                    main.r_next = replay.new_root;
                    main.d_prev = replay.batch_digest;
                    main.d_cur = replay.batch_digest;
                    ([F::ZERO; 16], [F::ZERO; 16], [F::ZERO; 24])
                }
            };
            let nz = main
                .q
                .iter()
                .position(|value| !value.is_zero())
                .expect("q is non-zero");
            main.nz_sel[nz] = F::ONE;
            main.nz_inv = main.q[nz].inverse();

            let (a, rest) = hashes.split_at_mut(B_RANGE.start - A_RANGE.start);
            let (b, c) = rest.split_at_mut(C_RANGE.start - B_RANGE.start);
            let a: &mut Cols16<MaybeUninit<F>> = as_uninit(a).borrow_mut();
            let b: &mut Cols16<MaybeUninit<F>> = as_uninit(b).borrow_mut();
            let c: &mut Cols24<MaybeUninit<F>> = as_uninit(c).borrow_mut();
            generate_trace_rows_for_perm::<
                F,
                Linear,
                16,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS_16,
            >(a, a_input, &c16);
            generate_trace_rows_for_perm::<
                F,
                Linear,
                16,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS_16,
            >(b, b_input, &c16);
            generate_trace_rows_for_perm::<
                F,
                Linear,
                24,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS_24,
            >(c, c_input, &c24);
        });
    RowMajorMatrix::new(values, TRACE_WIDTH)
}
