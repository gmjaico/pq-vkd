//! Index STARK tests, besides honest batches, most tests build a trace that
//! breaks one rule (overwrite, wrong sibling, zero leaf, ...) and check it fails

use core::borrow::{Borrow, BorrowMut};
use core::mem::MaybeUninit;

use p3_field::PrimeCharacteristicRing;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2_air::generate_trace_rows_for_perm;
use p3_symmetric::Permutation;

use super::air::*;
use super::trace::{Replay, generate_trace, public_values, replay};
use super::*;
use crate::crypto::index_hash::{
    DIGEST_ZERO, F, h_leaf, label_identifier, poseidon2_16, poseidon2_24,
};
use crate::crypto::sparse_merkle::SparseMerkleTree;

fn prover() -> ProverConfig {
    ProverConfig::new(2).unwrap()
}

/// Inserts labels into tree, returning the STARK witnesses
fn insert_all(tree: &mut SparseMerkleTree, items: &[(usize, String)]) -> Vec<IndexInsertion> {
    items
        .iter()
        .map(|(slot, label)| {
            let witness = tree.insert(*slot, label.as_bytes()).unwrap();
            IndexInsertion {
                slot: *slot,
                leaf: h_leaf(&label_identifier(label.as_bytes())),
                siblings: witness.siblings,
            }
        })
        .collect()
}

fn satisfies(depth: usize, trace: &RowMajorMatrix<F>, public: &[F]) -> bool {
    let air = IndexUpdateAir::new(depth);
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        p3_air::check_constraints(&air, trace, public);
    }))
    .is_ok()
}

fn public_of(replay: &Replay) -> Vec<F> {
    public_values(
        &replay.old_root,
        &replay.new_root,
        replay.steps.len() as u64,
        &replay.batch_digest,
        replay.epoch,
    )
    .unwrap()
}

/// Rewrites a Poseidon2 sub-trace in place with an honest permutation of input
fn rewrite16(row: &mut [F], range: core::ops::Range<usize>, input: [F; 16]) {
    let slice = &mut row[range];
    let uninit = unsafe { &mut *(slice as *mut [F] as *mut [MaybeUninit<F>]) };
    let cols: &mut Cols16<MaybeUninit<F>> = uninit.borrow_mut();
    generate_trace_rows_for_perm::<
        F,
        Linear,
        16,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS_16,
    >(cols, input, &constants_16());
}

fn sample_tree(
    depth: usize,
    prefill: usize,
    k: usize,
) -> (SparseMerkleTree, [u8; 32], Vec<IndexInsertion>) {
    let mut tree = SparseMerkleTree::new(depth).unwrap();
    let capacity = 1usize << depth;
    let mut slot = 0usize;
    let mut next_slot = || {
        slot = (slot + 7) % capacity;
        slot
    };
    let pre: Vec<_> = (0..prefill)
        .map(|i| (next_slot(), format!("pre-{i}")))
        .collect();
    insert_all(&mut tree, &pre);
    let old_root = tree.root();
    let items: Vec<_> = (0..k).map(|i| (next_slot(), format!("new-{i}"))).collect();
    let insertions = insert_all(&mut tree, &items);
    (tree, old_root, insertions)
}

#[test]
fn air_poseidon2_matches_native_permutations() {
    let input16: [F; 16] = core::array::from_fn(|i| F::from_usize(3 * i + 1));
    let input24: [F; 24] = core::array::from_fn(|i| F::from_usize(5 * i + 2));
    let mut row16 = F::zero_vec(P16_WIDTH);
    rewrite16(&mut row16, 0..P16_WIDTH, input16);
    let cols: &Cols16<F> = row16[..].borrow();
    let native = poseidon2_16().permute(input16);
    assert_eq!(hash_output(cols), core::array::from_fn(|i| native[i]));

    let mut row24 = F::zero_vec(P24_WIDTH);
    let uninit = unsafe { &mut *(&mut row24[..] as *mut [F] as *mut [MaybeUninit<F>]) };
    let c: &mut Cols24<MaybeUninit<F>> = uninit.borrow_mut();
    generate_trace_rows_for_perm::<
        F,
        Linear,
        24,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS_24,
    >(c, input24, &constants_24());
    let cols: &Cols24<F> = row24[..].borrow();
    let native = poseidon2_24().permute(input24);
    assert_eq!(hash_output(cols), core::array::from_fn(|i| native[i]));
}

#[test]
fn honest_batches_prove_and_verify() {
    // (depth, prefill, k): exact power of two, partial PAD step at the
    // end (depth 5 does not divide the trace height), and a full tree
    for (depth, prefill, k) in [(4, 0, 1), (4, 3, 2), (5, 10, 17), (3, 0, 8)] {
        let (tree, old_root, insertions) = sample_tree(depth, prefill, k);
        let epoch = 42;
        let (proof, new_root) =
            prove_index_update(depth, epoch, &old_root, &insertions, &prover()).unwrap();
        assert_eq!(new_root, tree.root(), "STARK root matches native SMT");
        verify_index_update(depth, epoch, &old_root, &new_root, &proof).unwrap();
        let published: Vec<_> = insertions.iter().map(|i| (i.slot, i.leaf)).collect();
        check_published_insertions(epoch, &published, &proof).unwrap();
    }
}

#[test]
fn wrong_public_inputs_are_rejected() {
    let depth = 4;
    let (_, old_root, insertions) = sample_tree(depth, 2, 3);
    let (proof, new_root) =
        prove_index_update(depth, 9, &old_root, &insertions, &prover()).unwrap();
    verify_index_update(depth, 9, &old_root, &new_root, &proof).unwrap();
    // Wrong C_I, C_I', epoch
    assert!(verify_index_update(depth, 9, &new_root, &new_root, &proof).is_err());
    assert!(verify_index_update(depth, 9, &old_root, &old_root, &proof).is_err());
    assert!(verify_index_update(depth, 10, &old_root, &new_root, &proof).is_err());
    // Wrong k (same trace height and different height)
    let mut wrong_k = proof.clone();
    wrong_k.k = 4;
    assert!(verify_index_update(depth, 9, &old_root, &new_root, &wrong_k).is_err());
    wrong_k.k = 2;
    assert!(verify_index_update(depth, 9, &old_root, &new_root, &wrong_k).is_err());
    // Wrong d
    let mut wrong_d = proof.clone();
    wrong_d.batch_digest = encode_digest(&h_leaf(&label_identifier(b"x")));
    assert!(verify_index_update(depth, 9, &old_root, &new_root, &wrong_d).is_err());
    // Tampered proof bytes
    let mut tampered = proof.clone();
    let middle = tampered.stark.len() / 2;
    tampered.stark[middle] ^= 1;
    assert!(verify_index_update(depth, 9, &old_root, &new_root, &tampered).is_err());
    let mut truncated = proof.clone();
    truncated.stark.truncate(100);
    assert!(verify_index_update(depth, 9, &old_root, &new_root, &truncated).is_err());
    // Wrong depth
    assert!(verify_index_update(depth + 1, 9, &old_root, &new_root, &proof).is_err());
}

#[test]
fn reordered_published_list_is_rejected() {
    let depth = 4;
    let (_, old_root, insertions) = sample_tree(depth, 0, 3);
    let (proof, _) = prove_index_update(depth, 1, &old_root, &insertions, &prover()).unwrap();
    let mut published: Vec<_> = insertions.iter().map(|i| (i.slot, i.leaf)).collect();
    published.swap(0, 1);
    assert!(check_published_insertions(1, &published, &proof).is_err());
    published.swap(0, 1);
    published.pop();
    assert!(check_published_insertions(1, &published, &proof).is_err());
}

#[test]
fn native_replay_rejects_overwrite_and_zero_leaf() {
    let depth = 4;
    let (tree, old_root, insertions) = sample_tree(depth, 0, 2);
    let old = decode_digest(&old_root).unwrap();
    // Same slot twice: the second insertion is not into an empty slot
    let mut twice = insertions.clone();
    twice[1].slot = twice[0].slot;
    twice[1].siblings = twice[0].siblings.clone();
    assert!(replay(depth, 1, old, &twice).is_err());
    let mut zero = insertions.clone();
    zero[0].leaf = DIGEST_ZERO;
    assert!(replay(depth, 1, old, &zero).is_err());
    assert!(replay(depth, 1, old, &[]).is_err());
    let _ = tree;
}

#[test]
fn honest_trace_satisfies_constraints() {
    let depth = 5;
    let (_, old_root, insertions) = sample_tree(depth, 4, 5);
    let r = replay(depth, 3, decode_digest(&old_root).unwrap(), &insertions).unwrap();
    let trace = generate_trace(&r);
    assert!(satisfies(depth, &trace, &public_of(&r)));
}

#[test]
fn malicious_traces_violate_constraints() {
    let depth = 4;
    let (_, old_root, insertions) = sample_tree(depth, 3, 3);
    let honest = replay(depth, 3, decode_digest(&old_root).unwrap(), &insertions).unwrap();
    let public = public_of(&honest);
    let base = generate_trace(&honest);
    assert!(satisfies(depth, &base, &public));
    let width = TRACE_WIDTH;
    let main_mut = |trace: &mut RowMajorMatrix<F>, row: usize| -> *mut MainCols<F> {
        let slice = &mut trace.values[row * width..row * width + MAIN_WIDTH];
        let cols: &mut MainCols<F> = slice.borrow_mut();
        cols as *mut _
    };

    // 1. Overwrite an occupied slot: the old leaf entering step 0 is not empty
    {
        let mut tree = SparseMerkleTree::new(depth).unwrap();
        tree.insert(insertions[0].slot, b"occupant").unwrap();
        let occupied_root = tree.root_digest();
        let proof = tree.proof(insertions[0].slot).unwrap();
        let overwrite = IndexInsertion {
            slot: insertions[0].slot,
            leaf: h_leaf(&label_identifier(b"intruder")),
            siblings: proof.siblings.clone(),
        };
        assert!(
            replay(depth, 3, occupied_root, &[overwrite]).is_err(),
            "native replay refuses to overwrite"
        );
        // Build the malicious trace by hand: start from an honest empty-slot replay and rewrite the old
        // path to begin at the occupant's leaf, so every constraint holds except "old leaf is DIGEST_ZERO"
        let empty = SparseMerkleTree::new(depth).unwrap();
        let empty_proof = empty.proof(insertions[0].slot).unwrap();
        let mut forged = replay(
            depth,
            3,
            empty.root_digest(),
            &[IndexInsertion {
                slot: insertions[0].slot,
                leaf: h_leaf(&label_identifier(b"intruder")),
                siblings: empty_proof.siblings.clone(),
            }],
        )
        .unwrap();
        let occupant = h_leaf(&label_identifier(b"occupant"));
        let step = &mut forged.steps[0];
        let mut cur = occupant;
        for h in 0..depth {
            step.cur_old[h] = cur;
            let sib = step.siblings[h];
            cur = if (step.slot >> h) & 1 == 0 {
                crate::crypto::index_hash::h_node(&cur, &sib)
            } else {
                crate::crypto::index_hash::h_node(&sib, &cur)
            };
        }
        assert_eq!(cur, occupied_root);
        step.r_cur = occupied_root;
        forged.old_root = occupied_root;
        let trace = generate_trace(&forged);
        assert!(!satisfies(depth, &trace, &public_of(&forged)));
    }

    // 2. Different sibling on the new path (slot B fed a different sibling)
    {
        let mut trace = base.clone();
        let row = 1;
        let main = unsafe { &*main_mut(&mut trace, row) };
        let mut sib = main.sib;
        sib[0] += F::ONE;
        let (left, right) = if main.bit == F::ZERO {
            (main.cur_new, sib)
        } else {
            (sib, main.cur_new)
        };
        let input = crate::crypto::index_hash::node_input(&left, &right);
        rewrite16(
            &mut trace.values[row * width..(row + 1) * width],
            B_RANGE,
            input,
        );
        assert!(!satisfies(depth, &trace, &public));
    }

    // 3. Flip one path bit so idx and the hashed path disagree
    {
        let mut trace = base.clone();
        let main = unsafe { &mut *main_mut(&mut trace, 2) };
        main.bit = F::ONE - main.bit;
        assert!(!satisfies(depth, &trace, &public));
    }

    // 4. q = DIGEST_ZERO on an INSERT step
    {
        let mut trace = base.clone();
        for row in 0..depth {
            let main = unsafe { &mut *main_mut(&mut trace, row) };
            main.q = DIGEST_ZERO;
        }
        assert!(!satisfies(depth, &trace, &public));
    }

    // 5. Wrong public values against an honest trace
    for index in [PV_OLD_ROOT, PV_NEW_ROOT + 3, PV_K, PV_DIGEST + 7, PV_EPOCH] {
        let mut wrong = public.clone();
        wrong[index] += F::ONE;
        assert!(!satisfies(depth, &base, &wrong));
    }

    // 6. A PAD step claiming a root change
    {
        let mut trace = base.clone();
        let last = trace.height() - 1;
        let main = unsafe { &mut *main_mut(&mut trace, last) };
        assert_eq!(main.is_insert, F::ZERO);
        main.r_next[0] += F::ONE;
        assert!(!satisfies(depth, &trace, &public));
    }

    // 7. Changing the step type mid-step
    {
        let mut trace = base.clone();
        let main = unsafe { &mut *main_mut(&mut trace, 1) };
        main.is_insert = F::ZERO;
        assert!(!satisfies(depth, &trace, &public));
    }
}

#[test]
fn trace_dimensions() {
    assert_eq!(trace_height(4, 1), 4);
    assert_eq!(trace_height(20, 1000), 32768);
    assert_eq!(trace_height(24, 1000), 32768);
    assert!(MAIN_WIDTH < 100);
}

#[test]
fn proofs_are_identical_across_worker_counts() {
    let depth = 5;
    let (_, old_root, insertions) = sample_tree(depth, 6, 9);
    let mut reference = None;
    for workers in [1, 2, 4, 8] {
        let config = ProverConfig::new(workers).unwrap();
        let output = prove_index_update(depth, 5, &old_root, &insertions, &config).unwrap();
        match &reference {
            None => reference = Some(output),
            Some(expected) => assert_eq!(&output, expected, "{workers} workers"),
        }
    }
}
