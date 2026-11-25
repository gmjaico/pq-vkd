use ark_ff::{One, Zero};

use irondict::crypto::placement::{Blake3Placement, PlacementBackend};
use irondict::pcs::deepfold::commitment::commit;
use irondict::pcs::deepfold::polynomial::MultilinearPolynomial;
use irondict::protocol::audit::{verify_genesis, verify_history, verify_range};
use irondict::protocol::consistency::verify_consistency;
use irondict::protocol::epoch::verify_transition;
use irondict::protocol::lookup::{VerifiedLookupResult, verify_lookup};
use irondict::protocol::{ServerState, StatePolynomial};
use irondict::{Field, Parameters};

#[test]
fn table_round_trip() {
    let evaluations = (0..8)
        .map(|value| Field::from(value as u64))
        .collect::<Vec<_>>();
    let polynomial = MultilinearPolynomial::from_boolean_evaluations(evaluations.clone()).unwrap();
    assert_eq!(polynomial.to_boolean_evaluations(), evaluations);
    for (slot, expected) in evaluations.iter().enumerate() {
        let point = (0..3)
            .map(|bit| Field::from(((slot >> bit) & 1) as u64))
            .collect::<Vec<_>>();
        assert_eq!(polynomial.evaluate(&point).unwrap(), *expected);
    }

    let arbitrary = [Field::from(2u64), Field::from(3u64), Field::from(5u64)];
    let manually = polynomial.coefficients().iter().enumerate().fold(
        Field::zero(),
        |sum, (monomial, coefficient)| {
            let product = arbitrary
                .iter()
                .enumerate()
                .fold(*coefficient, |term, (bit, x)| {
                    if monomial & (1 << bit) != 0 {
                        term * x
                    } else {
                        term
                    }
                });
            sum + product
        },
    );
    assert_eq!(polynomial.evaluate(&arbitrary).unwrap(), manually);
    assert!(MultilinearPolynomial::from_boolean_evaluations(vec![]).is_err());
    assert!(MultilinearPolynomial::from_boolean_evaluations(vec![Field::one(); 3]).is_err());
}

#[test]
fn table_and_coefficients_give_same_commitment() {
    let parameters = Parameters::new(2).unwrap();
    let evaluations = vec![
        Field::from(2u64),
        Field::from(5u64),
        Field::from(11u64),
        Field::from(19u64),
    ];
    let transformed = MultilinearPolynomial::from_boolean_evaluations(evaluations).unwrap();
    let manual = MultilinearPolynomial::new(vec![
        Field::from(2u64),
        Field::from(3u64),
        Field::from(9u64),
        Field::from(5u64),
    ])
    .unwrap();
    assert_eq!(
        commit(&parameters, &transformed).unwrap().0,
        commit(&parameters, &manual).unwrap().0
    );
}

#[test]
fn end_to_end() {
    let backend = Blake3Placement;
    let mut server = ServerState::new(3, backend, 1).unwrap();
    let genesis = server.current().clone();
    verify_genesis(genesis.public()).unwrap();
    assert_eq!(
        genesis.public().index_root,
        irondict::crypto::sparse_merkle::SparseMerkleTree::empty_root(3).unwrap()
    );

    let registered = server.register(b"alice", b"v1").unwrap();
    assert!(server.register(b"alice", b"duplicate").is_err());
    let member = server.prove_lookup(&registered, b"alice").unwrap();
    let verified = verify_lookup(&backend, registered.public(), b"alice", &member).unwrap();
    assert_eq!(
        verified.result,
        VerifiedLookupResult::Present {
            value: b"v1".to_vec(),
            slot: member.probes.last().unwrap().slot,
        }
    );
    let absent = server.prove_lookup(&registered, b"nobody").unwrap();
    assert_eq!(
        verify_lookup(&backend, registered.public(), b"nobody", &absent)
            .unwrap()
            .result,
        VerifiedLookupResult::Absent
    );

    let old_index = registered.public().index_root;
    let updated = server.update(b"alice", b"v2").unwrap();
    assert_eq!(old_index, updated.public().index_root);
    assert!(server.update(b"missing", b"v").is_err());
    let updated_lookup = server.prove_lookup(&updated, b"alice").unwrap();
    assert_eq!(
        verify_lookup(&backend, updated.public(), b"alice", &updated_lookup)
            .unwrap()
            .result,
        VerifiedLookupResult::Present {
            value: b"v2".to_vec(),
            slot: updated_lookup.probes.last().unwrap().slot
        }
    );

    let successors = server.snapshots()[1..]
        .iter()
        .map(|snapshot| snapshot.public().clone())
        .collect::<Vec<_>>();
    let history = verify_history(genesis.public(), &successors, server.transitions()).unwrap();
    assert_eq!(history.transitions.len(), 2);
    assert_eq!(history.last_digest, updated.public().digest());
    assert!(verify_history(genesis.public(), &successors, &server.transitions()[..1]).is_err());
}

#[test]
fn lookup_with_collisions() {
    let backend = Blake3Placement;
    let capacity = 4;
    let mut labels_by_slot: [Option<Vec<u8>>; 4] = std::array::from_fn(|_| None);
    let mut collision = None;
    for counter in 0..10_000u64 {
        let label = format!("collision-{counter}").into_bytes();
        let slot = backend.derive_slot(&label, 0, capacity).unwrap();
        if let Some(first) = &labels_by_slot[slot] {
            collision = Some((first.clone(), label));
            break;
        }
        labels_by_slot[slot] = Some(label);
    }
    let (first, second) = collision.expect("small table must yield a collision");
    let mut server = ServerState::new(2, backend, 1).unwrap();
    server.register(&first, b"first").unwrap();
    let snapshot = server.register(&second, b"second").unwrap();
    let proof = server.prove_lookup(&snapshot, &second).unwrap();
    assert!(proof.probes.len() >= 2);
    verify_lookup(&backend, snapshot.public(), &second, &proof).unwrap();

    let mut skipped = proof.clone();
    skipped.probes.remove(0);
    assert!(verify_lookup(&backend, snapshot.public(), &second, &skipped).is_err());
    let mut forged_slot = proof.clone();
    forged_slot.probes[0].slot ^= 1;
    assert!(verify_lookup(&backend, snapshot.public(), &second, &forged_slot).is_err());
    let mut reordered = proof.clone();
    reordered.probes.swap(0, 1);
    assert!(verify_lookup(&backend, snapshot.public(), &second, &reordered).is_err());
    let mut early = proof.clone();
    early.probes.truncate(1);
    early.membership = None;
    assert!(verify_lookup(&backend, snapshot.public(), &second, &early).is_err());
    let mut forged_path = proof.clone();
    forged_path.probes[0].index.siblings[0][0] +=
        <irondict::crypto::index_hash::F as p3_field::PrimeCharacteristicRing>::ONE;
    assert!(verify_lookup(&backend, snapshot.public(), &second, &forged_path).is_err());
    let mut wrong_leaf = proof.clone();
    wrong_leaf.probes.last_mut().unwrap().index.leaf =
        irondict::crypto::sparse_merkle::IndexLeaf::Empty;
    assert!(verify_lookup(&backend, snapshot.public(), &second, &wrong_leaf).is_err());
    let mut wrong_public = snapshot.public().clone();
    wrong_public.index_root[0] ^= 1;
    assert!(verify_lookup(&backend, &wrong_public, &second, &proof).is_err());
}

#[test]
fn full_table_rejects_new_label() {
    // Depth 1 is the smallest Index the update STARK supports (capacity 2),
    // A label's two probes may both hit the same slot, so fill until full
    let mut server = ServerState::new(1, Blake3Placement, 1).unwrap();
    let mut registered = 0;
    for i in 0..64 {
        if server
            .register(format!("label-{i}").as_bytes(), b"value")
            .is_ok()
        {
            registered += 1;
        }
        if registered == 2 {
            break;
        }
    }
    assert_eq!(registered, 2);
    let full = server.current().clone();
    assert!(server.register(b"overflow", b"value").is_err());
    assert!(server.prove_lookup(&full, b"absent").is_err());
}

#[test]
fn tampered_transition_fails() {
    let mut server = ServerState::new(2, Blake3Placement, 1).unwrap();
    let genesis = server.current().clone();
    let next = server.register(b"alice", b"v1").unwrap();
    let honest = server.transitions()[0].clone();
    verify_transition(genesis.public(), next.public(), &honest).unwrap();

    let mut bad_stark = honest.clone();
    let stark = &mut bad_stark.registration.as_mut().unwrap().stark;
    let middle = stark.len() / 2;
    stark[middle] ^= 1;
    assert!(verify_transition(genesis.public(), next.public(), &bad_stark).is_err());
    let mut bad_count = honest.clone();
    bad_count.registration.as_mut().unwrap().k += 1;
    assert!(verify_transition(genesis.public(), next.public(), &bad_count).is_err());
    let mut bad_digest = honest.clone();
    bad_digest.registration.as_mut().unwrap().batch_digest[0] ^= 1;
    assert!(verify_transition(genesis.public(), next.public(), &bad_digest).is_err());
    let mut missing = honest.clone();
    missing.registration = None;
    assert!(verify_transition(genesis.public(), next.public(), &missing).is_err());
    let mut bad_recurrence = honest.clone();
    bad_recurrence.recurrence.new_value.value += Field::one();
    assert!(verify_transition(genesis.public(), next.public(), &bad_recurrence).is_err());
    let mut bad_deepfold = honest.clone();
    bad_deepfold.recurrence.old_randomizer.proof.final_value += Field::one();
    assert!(verify_transition(genesis.public(), next.public(), &bad_deepfold).is_err());

    let mut changed_public = next.public().clone();
    changed_public.previous_digest[0] ^= 1;
    assert!(verify_transition(genesis.public(), &changed_public, &honest).is_err());
}

#[test]
fn consistency_detects_change_and_change_then_revert() {
    let backend = Blake3Placement;
    let mut server = ServerState::new(3, backend, 1).unwrap();
    let alice_epoch = server.register(b"alice", b"stable").unwrap();
    server.register(b"bob", b"b1").unwrap();
    let bob_updated = server.update(b"bob", b"b2").unwrap();

    let proof = server
        .prove_consistency(&alice_epoch, &bob_updated, b"alice")
        .unwrap();
    assert_eq!(proof.opening_count(), 2);
    assert_eq!(proof.encoded_len(), proof.to_bytes().len());
    let start = alice_epoch.public().epoch as usize;
    let end = bob_updated.public().epoch as usize;
    let successor_public = server.snapshots()[start + 1..=end]
        .iter()
        .map(|snapshot| snapshot.public().clone())
        .collect::<Vec<_>>();
    let audited = verify_range(
        alice_epoch.public(),
        &successor_public,
        &server.transitions()[start..end],
    )
    .unwrap();
    verify_consistency(
        &backend,
        alice_epoch.public(),
        bob_updated.public(),
        &audited,
        b"alice",
        &proof,
    )
    .unwrap();
    assert!(
        verify_consistency(
            &backend,
            alice_epoch.public(),
            bob_updated.public(),
            &audited[..1],
            b"alice",
            &proof
        )
        .is_err()
    );

    let changed = server.update(b"alice", b"changed").unwrap();
    assert!(
        server
            .prove_consistency(&alice_epoch, &changed, b"alice")
            .is_err()
    );
    let reverted = server.update(b"alice", b"stable").unwrap();
    assert!(
        server
            .prove_consistency(&alice_epoch, &reverted, b"alice")
            .is_err()
    );
}

#[test]
fn same_output_for_any_thread_count() {
    let mut reference = None;
    for workers in [1, 2, 4, 8] {
        let mut server = ServerState::new(1, Blake3Placement, workers).unwrap();
        let public = server
            .register(b"worker-test", b"value")
            .unwrap()
            .public()
            .clone();
        let transition = server.transitions()[0].clone();
        let current = (public, transition);
        if let Some(expected) = &reference {
            assert_eq!(expected, &current);
        } else {
            reference = Some(current);
        }
    }
}

#[test]
fn snapshot_commitments_match_public() {
    let server = ServerState::new(1, Blake3Placement, 1).unwrap();
    for which in [StatePolynomial::Value, StatePolynomial::Randomizer] {
        assert_eq!(
            server.current().polynomial(which).commitment(),
            server.current().public().commitments.get(which)
        );
    }
}

#[test]
fn mixed_epoch() {
    let mut server = ServerState::new(8, Blake3Placement, 1).unwrap();
    let entry = |prefix: &str, i: usize, v: &str| {
        (
            format!("{prefix}-{i}").into_bytes(),
            format!("{v}-{i}").into_bytes(),
        )
    };
    let old: Vec<_> = (0..16).map(|i| entry("old", i, "v1")).collect();
    let first = server.register_batch(&old).unwrap();

    let fresh: Vec<_> = (0..8).map(|i| entry("new", i, "n1")).collect();
    let changed: Vec<_> = (0..8).map(|i| entry("old", i, "v2")).collect();
    let mixed = server.publish_batch(&fresh, &changed).unwrap();
    assert_eq!(mixed.public().epoch, 2);
    assert_ne!(first.public().index_root, mixed.public().index_root);

    // Same proof shape as a registration epoch: one STARK over
    // the 8 insertions plus the 4-opening recurrence audit
    let proof = server.transitions().last().unwrap().clone();
    assert_eq!(proof.registration.as_ref().unwrap().k, 8);
    assert_eq!(proof.opening_count(), 4);
    let _ = verify_transition(first.public(), mixed.public(), &proof).unwrap();
    let mut fewer = proof.clone();
    fewer.registration.as_mut().unwrap().k = 16;
    assert!(verify_transition(first.public(), mixed.public(), &fewer).is_err());
    let mut dropped = proof.clone();
    dropped.registration = None;
    assert!(verify_transition(first.public(), mixed.public(), &dropped).is_err());

    // New labels, updated labels and untouched labels all resolve correctly
    let expect = |label: &[u8], value: &[u8]| {
        let lookup = server.prove_lookup(&mixed, label).unwrap();
        let verified = verify_lookup(&Blake3Placement, mixed.public(), label, &lookup).unwrap();
        assert!(
            matches!(verified.result, VerifiedLookupResult::Present { value: ref v, .. } if v == value),
            "{}",
            String::from_utf8_lossy(label)
        );
    };
    for (label, value) in fresh.iter().chain(&changed) {
        expect(label, value);
    }
    for (label, value) in &old[8..] {
        expect(label, value);
    }

    // Rejected batches leave the state untouched
    let both = vec![entry("both", 0, "x")];
    assert!(server.publish_batch(&both, &both).is_err());
    assert!(
        server
            .publish_batch(&[entry("new", 0, "x")], &changed)
            .is_err()
    );
    assert!(
        server
            .publish_batch(&[entry("z", 0, "x")], &[entry("missing", 0, "x")])
            .is_err()
    );
    assert_eq!(server.current().public().epoch, 2);

    // No registrations: an ordinary update epoch without an Index proof
    let only_updates = server.publish_batch(&[], &changed[..2]).unwrap();
    assert!(server.transitions().last().unwrap().registration.is_none());
    let _ = verify_transition(
        mixed.public(),
        only_updates.public(),
        server.transitions().last().unwrap(),
    )
    .unwrap();
}

#[test]
fn batch_is_one_epoch() {
    let mut server = ServerState::new(8, Blake3Placement, 1).unwrap();
    let batch = (0..16)
        .map(|i| {
            (
                format!("label-{i}").into_bytes(),
                format!("v1-{i}").into_bytes(),
            )
        })
        .collect::<Vec<_>>();
    let genesis = server.current().clone();
    let registered = server.register_batch(&batch).unwrap();
    assert_eq!(registered.public().epoch, 1);
    let _ = verify_transition(
        genesis.public(),
        registered.public(),
        &server.transitions()[0],
    )
    .unwrap();
    // The Index evidence is one STARK, independent of the batch size
    let index_proof = server.transitions()[0].registration.clone().unwrap();
    assert_eq!(index_proof.k, 16);
    // A different insertion order changes the batch digest d
    let mut reordered = server.transitions()[0].clone();
    reordered.registration.as_mut().unwrap().batch_digest[1] ^= 1;
    assert!(verify_transition(genesis.public(), registered.public(), &reordered).is_err());
    let mut fewer = server.transitions()[0].clone();
    fewer.registration.as_mut().unwrap().k = 15;
    assert!(verify_transition(genesis.public(), registered.public(), &fewer).is_err());

    let updates = batch
        .iter()
        .map(|(label, _)| (label.clone(), b"v2".to_vec()))
        .collect::<Vec<_>>();
    let updated = server.update_batch(&updates).unwrap();
    assert_eq!(updated.public().epoch, 2);
    assert_eq!(server.transitions()[1].opening_count(), 4);
    let _ = verify_transition(
        registered.public(),
        updated.public(),
        &server.transitions()[1],
    )
    .unwrap();
    for (label, _) in &batch {
        let proof = server.prove_lookup(&updated, label).unwrap();
        let verified = verify_lookup(&Blake3Placement, updated.public(), label, &proof).unwrap();
        assert!(
            matches!(verified.result, VerifiedLookupResult::Present { ref value, .. } if value == b"v2")
        );
    }

    let duplicate = vec![batch[0].clone()];
    assert!(server.register_batch(&duplicate).is_err());
    let within_batch = vec![
        (b"fresh".to_vec(), b"a".to_vec()),
        (b"fresh".to_vec(), b"b".to_vec()),
    ];
    assert!(server.register_batch(&within_batch).is_err());
    assert!(
        server
            .update_batch(&[(b"missing".to_vec(), b"x".to_vec())])
            .is_err()
    );
    assert_eq!(server.current().public().epoch, 2);

    let before_empty = server.current().clone();
    let after_empty = server.register_batch(&[]).unwrap();
    assert_eq!(
        before_empty.public().index_root,
        after_empty.public().index_root
    );
    assert!(server.transitions().last().unwrap().registration.is_none());
    let _ = verify_transition(
        before_empty.public(),
        after_empty.public(),
        server.transitions().last().unwrap(),
    )
    .unwrap();
}

#[test]
fn genesis_check_with_cache() {
    let server = ServerState::new(4, Blake3Placement, 1).unwrap();
    let first = verify_genesis(server.current().public()).unwrap();
    let second = verify_genesis(server.current().public()).unwrap();
    assert_eq!(first, second);
    let mut bad = server.current().public().clone();
    bad.index_root[0] ^= 1;
    assert!(verify_genesis(&bad).is_err());
}
