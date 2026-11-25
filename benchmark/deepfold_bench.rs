//! DeepFold PCS on its own: commit, open and verify time and proof size for 2^n coefficients, sizes given as arguments

use std::time::{Duration, Instant};

use irondict::pcs::deepfold::commitment::commit_with_config;
use irondict::pcs::deepfold::parallel::ProverConfig;
use irondict::pcs::deepfold::params::Parameters;
use irondict::pcs::deepfold::polynomial::MultilinearPolynomial;
use irondict::pcs::deepfold::proof::ProofSizeBreakdown;
use irondict::pcs::deepfold::prover::open_with_config;
use irondict::pcs::deepfold::verifier::verify;
use irondict::{Field, Result};

const DEFAULT_VARIABLE_COUNTS: &[usize] = &[8, 10, 12, 14, 16, 18, 20];
/// n = 24 needs roughly 11 GiB of RAM
const BENCH_MAX_NUM_VARS: usize = 24;

fn benchmark_deepfold(
    num_vars: usize,
    repetitions: usize,
    config: &ProverConfig,
) -> Result<BenchmarkResult> {
    let parameters = Parameters::new(num_vars)?;
    let polynomial = MultilinearPolynomial::new(deterministic_coefficients(num_vars))?;
    let point = deterministic_point(num_vars);

    let mut commit_total = Duration::ZERO;
    let mut open_total = Duration::ZERO;
    let mut verify_total = Duration::ZERO;
    let mut proof_bytes = 0;
    let mut commitment_bytes = 0;
    let mut size_breakdown = ProofSizeBreakdown::default();

    for _ in 0..repetitions {
        let started = Instant::now();
        let (commitment, prover_data) = commit_with_config(&parameters, &polynomial, config)?;
        commit_total += started.elapsed();

        let started = Instant::now();
        let (claimed_value, proof) =
            open_with_config(&parameters, &commitment, &prover_data, &point, config)?;
        open_total += started.elapsed();

        // Serialization isn't timed (as in Fig. 5 of the DeepFold
        // paper), the proof size is the real encoded length
        let (encoded_proof, current_breakdown) = proof.to_bytes_with_breakdown(claimed_value);
        let current_commitment_bytes = commitment.to_bytes().len();
        if proof_bytes != 0 {
            assert_eq!(proof_bytes, encoded_proof.len());
            assert_eq!(commitment_bytes, current_commitment_bytes);
            assert_eq!(size_breakdown, current_breakdown);
        }
        proof_bytes = encoded_proof.len();
        commitment_bytes = current_commitment_bytes;
        size_breakdown = current_breakdown;

        let started = Instant::now();
        verify(&parameters, &commitment, &point, claimed_value, &proof)?;
        verify_total += started.elapsed();
        std::hint::black_box(encoded_proof);
    }

    let divisor = u32::try_from(repetitions).expect("repetition count exceeds u32::MAX");
    let commit_time = commit_total / divisor;
    let open_time = open_total / divisor;
    Ok(BenchmarkResult {
        num_vars,
        polynomial_elements: parameters.polynomial_size(),
        domain_elements: parameters.domain_size(),
        commit_time,
        open_time,
        prover_time: commit_time + open_time,
        verify_time: verify_total / divisor,
        proof_bytes,
        commitment_bytes,
        size_breakdown,
    })
}

fn deterministic_coefficients(num_vars: usize) -> Vec<Field> {
    (0..(1usize << num_vars))
        .map(|index| {
            let value = (index as u64)
                .wrapping_mul(0x9e37_79b9_7f4a_7c15)
                .wrapping_add(0xd1b5_4a32_d192_ed03);
            Field::from(value)
        })
        .collect()
}

fn deterministic_point(num_vars: usize) -> Vec<Field> {
    (0..num_vars)
        .map(|index| Field::from((index as u64 + 1) * 17))
        .collect()
}

struct BenchmarkResult {
    num_vars: usize,
    polynomial_elements: usize,
    domain_elements: usize,
    commit_time: Duration,
    open_time: Duration,
    prover_time: Duration,
    verify_time: Duration,
    proof_bytes: usize,
    commitment_bytes: usize,
    size_breakdown: ProofSizeBreakdown,
}

fn main() {
    if cfg!(debug_assertions) {
        eprintln!(
            "WARNING: unoptimized build. Use:\n  \
             cargo run --release --bin deepfold_bench -- 16 18 20"
        );
    }

    let variable_counts = variable_counts_from_args();
    let repetitions = repetitions_from_environment();
    let prover_threads = prover_threads_from_environment();
    let config = ProverConfig::new(prover_threads).expect("valid prover worker count");

    println!("DeepFold paired-multiproof benchmark");
    println!("{repetitions} repetition(s), arithmetic mean, {prover_threads} prover worker(s)");
    println!("Commit + open is the Figure 5-style prover metric.\n");
    println!(
        "{:>4} {:>12} {:>12} {:>11} {:>11} {:>11} {:>11} {:>11} {:>8}",
        "Vars",
        "Poly elems",
        "Domain elems",
        "Commit ms",
        "Open ms",
        "Prover ms",
        "Verify ms",
        "Proof KiB",
        "Cmmt B"
    );
    println!("{}", "-".repeat(110));

    let mut results = Vec::new();
    for num_vars in variable_counts {
        match benchmark_deepfold(num_vars, repetitions, &config) {
            Ok(result) => {
                println!(
                    "{:>4} {:>12} {:>12} {:>11.2} {:>11.2} {:>11.2} {:>11.2} {:>11.2} {:>8}",
                    result.num_vars,
                    result.polynomial_elements,
                    result.domain_elements,
                    milliseconds(result.commit_time),
                    milliseconds(result.open_time),
                    milliseconds(result.prover_time),
                    milliseconds(result.verify_time),
                    result.proof_bytes as f64 / 1024.0,
                    result.commitment_bytes,
                );
                results.push(result);
            }
            Err(error) => eprintln!("num_vars={num_vars} failed: {error}"),
        }
    }

    println!("\nSerialized opening proof breakdown");
    println!("Fields B is Leaf vals B + DEEP B; the remaining categories do not overlap.");
    println!(
        "{:>4} {:>12} {:>12} {:>12} {:>12} {:>12} {:>12}",
        "Vars", "Fields B*", "Leaf vals B", "Auth B", "Roots B", "DEEP B", "Metadata B"
    );
    println!("{}", "-".repeat(84));
    for result in results {
        let breakdown = result.size_breakdown;
        println!(
            "{:>4} {:>12} {:>12} {:>12} {:>12} {:>12} {:>12}",
            result.num_vars,
            breakdown.field_element_bytes(),
            breakdown.merkle_leaf_value_bytes,
            breakdown.merkle_authentication_bytes,
            breakdown.intermediate_root_bytes,
            breakdown.deep_folding_message_bytes,
            breakdown.metadata_bytes,
        );
    }
}

fn variable_counts_from_args() -> Vec<usize> {
    let values = std::env::args()
        .skip(1)
        .map(|value| {
            value
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid variable count: {value}"))
        })
        .collect::<Vec<_>>();
    assert!(
        values.iter().all(|&value| value <= BENCH_MAX_NUM_VARS),
        "benchmark variable counts must be at most {BENCH_MAX_NUM_VARS}"
    );
    if values.is_empty() {
        DEFAULT_VARIABLE_COUNTS.to_vec()
    } else {
        values
    }
}

fn repetitions_from_environment() -> usize {
    let repetitions = std::env::var("BENCH_REPETITIONS")
        .ok()
        .map(|value| {
            value
                .parse::<usize>()
                .unwrap_or_else(|_| panic!("invalid BENCH_REPETITIONS: {value}"))
        })
        .unwrap_or(1);
    assert!(repetitions > 0, "BENCH_REPETITIONS must be at least 1");
    repetitions
}

fn prover_threads_from_environment() -> usize {
    let threads = std::env::var("PROVER_THREADS")
        .ok()
        .map(|value| value.parse().expect("invalid PROVER_THREADS"))
        .unwrap_or(1);
    assert!(
        (1..=8).contains(&threads),
        "PROVER_THREADS must be between 1 and 8"
    );
    threads
}

fn milliseconds(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}
