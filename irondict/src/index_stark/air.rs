//! AIR (the constraints) for the Index-update STARK

use core::borrow::{Borrow, BorrowMut};
use core::mem::size_of;
use core::ops::Range;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::PrimeCharacteristicRing;
use p3_koala_bear::{
    GenericPoseidon2LinearLayersKoalaBear, KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL, KOALABEAR_POSEIDON2_RC_16_INTERNAL,
    KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL, KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL,
    KOALABEAR_POSEIDON2_RC_24_INTERNAL, KoalaBear,
};
use p3_poseidon2_air::{Poseidon2Air, Poseidon2Cols, RoundConstants, num_cols};
use p3_uni_stark::SubAirBuilder;

use crate::crypto::index_hash::{BATCH_TAG, DIGEST_ELEMS};

pub(crate) const SBOX_DEGREE: u64 = 3;
pub(crate) const SBOX_REGISTERS: usize = 0;
pub(crate) const HALF_FULL_ROUNDS: usize = 4;
pub(crate) const PARTIAL_ROUNDS_16: usize = 20;
pub(crate) const PARTIAL_ROUNDS_24: usize = 23;

pub(crate) type Linear = GenericPoseidon2LinearLayersKoalaBear;
pub(crate) type P2Air16 = Poseidon2Air<
    KoalaBear,
    Linear,
    16,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS_16,
>;
pub(crate) type P2Air24 = Poseidon2Air<
    KoalaBear,
    Linear,
    24,
    SBOX_DEGREE,
    SBOX_REGISTERS,
    HALF_FULL_ROUNDS,
    PARTIAL_ROUNDS_24,
>;
pub(crate) type Cols16<T> =
    Poseidon2Cols<T, 16, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_16>;
pub(crate) type Cols24<T> =
    Poseidon2Cols<T, 24, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_24>;
pub(crate) type Constants16 = RoundConstants<KoalaBear, 16, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_16>;
pub(crate) type Constants24 = RoundConstants<KoalaBear, 24, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_24>;

pub(crate) const P16_WIDTH: usize =
    num_cols::<16, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_16>();
pub(crate) const P24_WIDTH: usize =
    num_cols::<24, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS_24>();

/// Same round constants as the native Poseidon2 in index_hash.rs
pub(crate) fn constants_16() -> Constants16 {
    RoundConstants::new(
        KOALABEAR_POSEIDON2_RC_16_EXTERNAL_INITIAL,
        KOALABEAR_POSEIDON2_RC_16_INTERNAL,
        KOALABEAR_POSEIDON2_RC_16_EXTERNAL_FINAL,
    )
}

pub(crate) fn constants_24() -> Constants24 {
    RoundConstants::new(
        KOALABEAR_POSEIDON2_RC_24_EXTERNAL_INITIAL,
        KOALABEAR_POSEIDON2_RC_24_INTERNAL,
        KOALABEAR_POSEIDON2_RC_24_EXTERNAL_FINAL,
    )
}

/// The columns besides the Poseidon2 ones, is_insert, idx, q, r_cur,
/// r_next, d_prev, d_cur and kcnt stay the same for all rows of a step
#[repr(C)]
pub struct MainCols<T> {
    /// 1 on INSERT steps, 0 on PAD steps
    pub is_insert: T,
    pub cnt: T,
    pub is_first: T,
    /// 1 on the last row of a step (inv_last proves it is 0 elsewhere)
    pub is_last: T,
    pub inv_last: T,
    pub bit: T,
    pub pow: T,
    /// Running sum of bit_h * 2^h, ends as the slot index
    pub acc: T,
    pub idx: T,
    /// Real insertions completed, including this step
    pub kcnt: T,
    /// Shows q is not zero: a one-hot selector and an inverse
    pub nz_inv: T,
    pub nz_sel: [T; DIGEST_ELEMS],
    pub sib: [T; DIGEST_ELEMS],
    /// Node values entering this level on the old and new path
    pub cur_old: [T; DIGEST_ELEMS],
    pub cur_new: [T; DIGEST_ELEMS],
    pub q: [T; DIGEST_ELEMS],
    /// Index root before and after this step
    pub r_cur: [T; DIGEST_ELEMS],
    pub r_next: [T; DIGEST_ELEMS],
    /// Batch digest before and after this step
    pub d_prev: [T; DIGEST_ELEMS],
    pub d_cur: [T; DIGEST_ELEMS],
}

pub const MAIN_WIDTH: usize = size_of::<MainCols<u8>>();
pub(crate) const A_RANGE: Range<usize> = MAIN_WIDTH..MAIN_WIDTH + P16_WIDTH;
pub(crate) const B_RANGE: Range<usize> = A_RANGE.end..A_RANGE.end + P16_WIDTH;
pub(crate) const C_RANGE: Range<usize> = B_RANGE.end..B_RANGE.end + P24_WIDTH;
pub const TRACE_WIDTH: usize = C_RANGE.end;

/// Public values: old root (8), new root (8), k, batch digest (8), epoch
pub const PV_OLD_ROOT: usize = 0;
pub const PV_NEW_ROOT: usize = 8;
pub const PV_K: usize = 16;
pub const PV_DIGEST: usize = 17;
pub const PV_EPOCH: usize = 25;
pub const NUM_PUBLIC_VALUES: usize = 26;

impl<T> Borrow<MainCols<T>> for [T] {
    fn borrow(&self) -> &MainCols<T> {
        debug_assert_eq!(self.len(), MAIN_WIDTH);
        // SAFETY: MainCols<T> is repr(C) and consists solely of Ts
        let (prefix, cols, suffix) = unsafe { self.align_to::<MainCols<T>>() };
        debug_assert!(prefix.is_empty() && suffix.is_empty() && cols.len() == 1);
        &cols[0]
    }
}

impl<T> BorrowMut<MainCols<T>> for [T] {
    fn borrow_mut(&mut self) -> &mut MainCols<T> {
        debug_assert_eq!(self.len(), MAIN_WIDTH);
        // SAFETY: as above
        let (prefix, cols, suffix) = unsafe { self.align_to_mut::<MainCols<T>>() };
        debug_assert!(prefix.is_empty() && suffix.is_empty() && cols.len() == 1);
        &mut cols[0]
    }
}

pub(crate) fn hash_output<T: Copy, const W: usize, const P: usize>(
    cols: &Poseidon2Cols<T, W, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, P>,
) -> [T; DIGEST_ELEMS] {
    let post = &cols.ending_full_rounds[HALF_FULL_ROUNDS - 1].post;
    core::array::from_fn(|i| post[i])
}

pub struct IndexUpdateAir {
    depth: usize,
    p16: P2Air16,
    p24: P2Air24,
}

impl IndexUpdateAir {
    pub fn new(depth: usize) -> Self {
        assert!(
            (1..=crate::Parameters::MAX_NUM_VARS).contains(&depth),
            "Index depth out of range"
        );
        Self {
            depth,
            p16: P2Air16::new(constants_16()),
            p24: P2Air24::new(constants_24()),
        }
    }

    pub fn depth(&self) -> usize {
        self.depth
    }
}

impl BaseAir<KoalaBear> for IndexUpdateAir {
    fn width(&self) -> usize {
        TRACE_WIDTH
    }

    // The Poseidon2 columns are never read on the next row
    fn main_next_row_columns(&self) -> Vec<usize> {
        (0..MAIN_WIDTH).collect()
    }

    fn num_public_values(&self) -> usize {
        NUM_PUBLIC_VALUES
    }

    fn max_constraint_degree(&self) -> Option<usize> {
        Some(3)
    }
}

impl<AB: AirBuilder<F = KoalaBear>> Air<AB> for IndexUpdateAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.current_slice();
        let next = main.next_slice();
        let l: &MainCols<AB::Var> = local[..MAIN_WIDTH].borrow();
        let n: &MainCols<AB::Var> = next[..MAIN_WIDTH].borrow();
        let a: &Cols16<AB::Var> = local[A_RANGE].borrow();
        let b: &Cols16<AB::Var> = local[B_RANGE].borrow();
        let c: &Cols24<AB::Var> = local[C_RANGE].borrow();
        let a_out = hash_output(a);
        let b_out = hash_output(b);
        let c_out = hash_output(c);
        let pv: Vec<AB::Expr> = builder
            .public_values()
            .iter()
            .map(|&value| value.into())
            .collect();

        let x = |v: AB::Var| -> AB::Expr { v.into() };
        let is_insert = x(l.is_insert);
        let is_pad = AB::Expr::ONE - is_insert.clone();
        let is_first = x(l.is_first);
        let is_last = x(l.is_last);
        let not_last = AB::Expr::ONE - is_last.clone();
        let first_insert = is_first.clone() * is_insert.clone();
        let last_insert = is_last.clone() * is_insert.clone();

        builder.assert_bool(l.is_insert);
        builder.assert_bool(l.bit);
        builder.assert_bool(l.is_first);
        builder.assert_bool(l.is_last);
        let last_offset = x(l.cnt) - AB::Expr::from_usize(self.depth - 1);
        builder.assert_eq(last_offset.clone() * x(l.inv_last), not_last.clone());
        builder.assert_zero(last_offset * is_last.clone());

        // The new leaf q can't be zero (zero means empty), nz_sel picks a
        // non-zero element of q and nz_inv is its inverse, PAD rows use a dummy q
        let mut sel_sum = AB::Expr::ZERO;
        let mut sel_dot = AB::Expr::ZERO;
        for j in 0..DIGEST_ELEMS {
            builder.assert_bool(l.nz_sel[j]);
            sel_sum += x(l.nz_sel[j]);
            sel_dot += x(l.nz_sel[j]) * x(l.q[j]);
        }
        builder.assert_one(sel_sum);
        builder.assert_one(sel_dot * x(l.nz_inv));

        {
            let mut first = builder.when_first_row();
            first.assert_zero(l.cnt);
            first.assert_one(l.is_first);
            first.assert_eq(l.kcnt, l.is_insert);
            for j in 0..DIGEST_ELEMS {
                first.assert_eq(l.r_cur[j], pv[PV_OLD_ROOT + j].clone());
            }
            first.assert_eq(l.d_prev[0], pv[PV_EPOCH].clone());
            for j in 1..DIGEST_ELEMS {
                first.assert_zero(l.d_prev[j]);
            }
        }

        {
            let mut last = builder.when_last_row();
            for j in 0..DIGEST_ELEMS {
                last.assert_eq(l.r_next[j], pv[PV_NEW_ROOT + j].clone());
                last.assert_eq(l.d_cur[j], pv[PV_DIGEST + j].clone());
            }
            last.assert_eq(l.kcnt, pv[PV_K].clone());
            // The trace may end inside a PAD step but never inside an INSERT
            // step, otherwise an unfinished insertion could skip its root check
            last.assert_zero(is_insert.clone() * not_last.clone());
        }

        {
            let mut tr = builder.when_transition();
            tr.assert_eq(n.cnt, (x(l.cnt) + AB::Expr::ONE) * not_last.clone());
            tr.assert_eq(n.is_first, l.is_last);
            // Padding stays at the end
            tr.assert_zero(is_last.clone() * is_pad.clone() * x(n.is_insert));

            let mut within = tr.when(not_last.clone());
            within.assert_eq(n.is_insert, l.is_insert);
            within.assert_eq(n.idx, l.idx);
            within.assert_eq(n.kcnt, l.kcnt);
            for j in 0..DIGEST_ELEMS {
                within.assert_eq(n.q[j], l.q[j]);
                within.assert_eq(n.r_cur[j], l.r_cur[j]);
                within.assert_eq(n.r_next[j], l.r_next[j]);
                within.assert_eq(n.d_prev[j], l.d_prev[j]);
                within.assert_eq(n.d_cur[j], l.d_cur[j]);
            }
            // Rebuild the slot index from the path bits
            within.assert_eq(n.pow, x(l.pow) * AB::Expr::TWO);
            within.assert_eq(n.acc, x(l.acc) + x(n.bit) * x(n.pow));

            // Between steps: the root and batch digest carry over
            let mut boundary = tr.when(is_last.clone());
            boundary.assert_eq(n.kcnt, x(l.kcnt) + x(n.is_insert));
            for j in 0..DIGEST_ELEMS {
                boundary.assert_eq(n.r_cur[j], l.r_next[j]);
                boundary.assert_eq(n.d_prev[j], l.d_cur[j]);
            }

            // Inside an insertion: a node's hash is the input to the next level
            let mut merkle = tr.when(is_insert.clone() * not_last.clone());
            for j in 0..DIGEST_ELEMS {
                merkle.assert_eq(n.cur_old[j], a_out[j]);
                merkle.assert_eq(n.cur_new[j], b_out[j]);
            }
        }

        // Last row of a step: the rebuilt index must equal idx
        {
            let mut first = builder.when(is_first.clone());
            first.assert_one(l.pow);
            first.assert_eq(l.acc, l.bit);
        }
        builder.when(is_last.clone()).assert_eq(l.acc, l.idx);

        // Merkle rows: put cur and sib in left/right order using the path bit
        {
            let mut merkle = builder.when(is_insert.clone());
            let bit = x(l.bit);
            for j in 0..DIGEST_ELEMS {
                let sib = x(l.sib[j]);
                for (cols, cur) in [(a, x(l.cur_old[j])), (b, x(l.cur_new[j]))] {
                    let left = cur.clone() + bit.clone() * (sib.clone() - cur.clone());
                    let right = sib.clone() + bit.clone() * (cur - sib.clone());
                    merkle.assert_eq(cols.inputs[j], left);
                    merkle.assert_eq(cols.inputs[DIGEST_ELEMS + j], right);
                }
            }
        }
        for j in 0..DIGEST_ELEMS {
            // Old leaf empty, new leaf q, and the paths end at the two roots
            builder.when(first_insert.clone()).assert_zero(l.cur_old[j]);
            builder
                .when(first_insert.clone())
                .assert_eq(l.cur_new[j], l.q[j]);
            builder
                .when(last_insert.clone())
                .assert_eq(a_out[j], l.r_cur[j]);
            builder
                .when(last_insert.clone())
                .assert_eq(b_out[j], l.r_next[j]);
            // PAD steps change nothing
            builder
                .when(is_pad.clone())
                .assert_eq(l.r_next[j], l.r_cur[j]);
            builder
                .when(is_pad.clone())
                .assert_eq(l.d_cur[j], l.d_prev[j]);
        }

        // d_cur = h_batch(d_prev, idx, q) on the first row of an insertion
        {
            let mut digest = builder.when(first_insert);
            digest.assert_eq(c.inputs[0], AB::Expr::from_u32(BATCH_TAG));
            for j in 0..DIGEST_ELEMS {
                digest.assert_eq(c.inputs[1 + j], l.d_prev[j]);
                digest.assert_eq(c.inputs[10 + j], l.q[j]);
                digest.assert_eq(l.d_cur[j], c_out[j]);
            }
            digest.assert_eq(c.inputs[9], l.idx);
            for input in &c.inputs[18..24] {
                digest.assert_zero(*input);
            }
        }

        let mut sub = SubAirBuilder::<AB, P2Air16, AB::Var>::new(builder, A_RANGE);
        self.p16.eval(&mut sub);
        let mut sub = SubAirBuilder::<AB, P2Air16, AB::Var>::new(builder, B_RANGE);
        self.p16.eval(&mut sub);
        let mut sub = SubAirBuilder::<AB, P2Air24, AB::Var>::new(builder, C_RANGE);
        self.p24.eval(&mut sub);
    }
}
