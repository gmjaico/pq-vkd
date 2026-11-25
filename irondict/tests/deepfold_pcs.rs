use irondict::Field;
use irondict::pcs::deepfold::commitment::{
    Commitment, commit, commit_with_config, encode_polynomial_with_config,
};
use irondict::pcs::deepfold::parallel::ProverConfig;
use irondict::pcs::deepfold::params::Parameters;
use irondict::pcs::deepfold::polynomial::MultilinearPolynomial;
use irondict::pcs::deepfold::prover::{OpeningProof, open, open_with_config};
use irondict::pcs::deepfold::verifier::verify;

fn fixture() -> (Parameters, Commitment, Vec<Field>, Field, OpeningProof) {
    let parameters = Parameters::new(4).unwrap();
    let coefficients = (0..parameters.polynomial_size())
        .map(|value| Field::from(value as u64 + 1))
        .collect();
    let polynomial = MultilinearPolynomial::new(coefficients).unwrap();
    let (commitment, prover_data) = commit(&parameters, &polynomial).unwrap();
    let point = (0..parameters.num_vars)
        .map(|value| Field::from(value as u64 + 2))
        .collect::<Vec<_>>();
    let (claimed_value, proof) = open(&parameters, &commitment, &prover_data, &point).unwrap();
    (parameters, commitment, point, claimed_value, proof)
}

#[test]
fn honest_opening_verifies() {
    let (parameters, commitment, point, value, proof) = fixture();
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_ok());
}

#[test]
fn malformed_shapes_are_rejected() {
    let (parameters, commitment, point, value, mut proof) = fixture();
    proof.queries.clear();
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());

    let (parameters, commitment, mut point, value, mut proof) = fixture();
    point.pop();
    proof.rounds[0].next_root = None;
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());
}

#[test]
fn altered_leaf_values_are_rejected() {
    let (parameters, commitment, point, value, mut proof) = fixture();
    proof.queries[0].leaves[0].positive += Field::from(1u64);
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());

    let (parameters, commitment, point, value, mut proof) = fixture();
    let leaf = &mut proof.queries[0].leaves[0];
    std::mem::swap(&mut leaf.positive, &mut leaf.negative);
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());
}

#[test]
fn malformed_authentication_is_rejected() {
    let (parameters, commitment, point, value, mut proof) = fixture();
    proof.queries[0].authentication.siblings.pop();
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());

    let (parameters, commitment, point, value, mut proof) = fixture();
    proof.queries[0].authentication.siblings[0][0] ^= 1;
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());
}

#[test]
fn late_round_query_collisions_are_deduplicated() {
    let (parameters, commitment, point, value, proof) = fixture();
    assert!(proof.queries.last().unwrap().leaves.len() < parameters.num_queries);
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_ok());
}

#[test]
fn altered_final_value_breaks_folding_checks() {
    let (parameters, commitment, point, value, mut proof) = fixture();
    proof.final_value += Field::from(1u64);
    assert!(verify(&parameters, &commitment, &point, value, &proof).is_err());
}

#[test]
fn proof_size_matches_breakdown() {
    let (_, commitment, _, value, proof) = fixture();
    let (first, breakdown) = proof.to_bytes_with_breakdown(value);
    assert_eq!(first, proof.to_bytes(value));
    assert_eq!(first.len(), breakdown.total_bytes());
    assert_eq!(commitment.to_bytes().len(), 64);
}

#[test]
fn same_proof_for_any_thread_count() {
    // Large enough to cross both the FFT and paired-Merkle parallel thresholds
    let parameters = Parameters::new(14).unwrap();
    let coefficients = (0..parameters.polynomial_size())
        .map(|index| Field::from((index as u64).wrapping_mul(0x9e37_79b9).wrapping_add(7)))
        .collect::<Vec<_>>();
    let polynomial = MultilinearPolynomial::new(coefficients.clone()).unwrap();
    let point = (0..parameters.num_vars)
        .map(|index| Field::from(index as u64 + 11))
        .collect::<Vec<_>>();
    let mut baseline = None;

    for threads in [1, 2, 4, 8] {
        let config = ProverConfig::new(threads).unwrap();
        let encoded =
            encode_polynomial_with_config(parameters.domain_size(), &coefficients, &config)
                .unwrap();
        let (commitment, data) = commit_with_config(&parameters, &polynomial, &config).unwrap();
        let (value, proof) =
            open_with_config(&parameters, &commitment, &data, &point, &config).unwrap();
        verify(&parameters, &commitment, &point, value, &proof).unwrap();
        let output = (encoded, commitment.to_bytes(), value, proof.to_bytes(value));
        if let Some(expected) = &baseline {
            assert_eq!(&output, expected, "different output with {threads} workers");
        } else {
            baseline = Some(output);
        }
    }
}
