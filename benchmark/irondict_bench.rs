//! IronDict results program

use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::PathBuf;
use std::time::{Duration, Instant};

use irondict::crypto::placement::Blake3Placement;
use irondict::index_stark::verify_index_update;
use irondict::pcs::deepfold::proof::ProofSizeBreakdown;
use irondict::protocol::audit::verify_genesis;
use irondict::protocol::epoch::{recurrence_audit_point, transition_statement_digest};
use irondict::protocol::opening::{AuthenticatedOpening, slot_to_point};
use irondict::protocol::{
    LookupProof, PublicEpoch, ServerState, TransitionProof, verify_history, verify_lookup,
    verify_range, verify_transition,
};
use irondict::{Error, Result};

type Server = ServerState<Blake3Placement>;

const WARMUP_LOG: usize = 2;
const AUDIT_BATCH_LOG: usize = 2;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Workload {
    Setup,
    UpdateReg,
    UpdateKeys,
    Lookup,
    Audit,
}

impl Workload {
    const ALL: [Workload; 5] = [
        Self::Setup,
        Self::UpdateReg,
        Self::UpdateKeys,
        Self::Lookup,
        Self::Audit,
    ];

    fn name(self) -> &'static str {
        match self {
            Self::Setup => "setup",
            Self::UpdateReg => "update_reg",
            Self::UpdateKeys => "update_keys",
            Self::Lookup => "lookup",
            Self::Audit => "audit",
        }
    }
}

#[derive(Clone, Copy)]
enum LookupLoad {
    Sqrt,
    Quarter,
    Half,
}

impl LookupLoad {
    fn occupied(self, num_vars: usize) -> usize {
        match self {
            Self::Sqrt => 1 << (num_vars / 2),
            Self::Quarter => 1 << (num_vars - 2),
            Self::Half => 1 << (num_vars - 1),
        }
    }

    fn name(self) -> &'static str {
        match self {
            Self::Sqrt => "sqrt",
            Self::Quarter => "quarter",
            Self::Half => "half",
        }
    }
}

struct Options {
    caps: Vec<usize>,
    update_logs: Vec<usize>,
    threads: usize,
    reps: usize,
    lookup_samples: usize,
    lookup_load: LookupLoad,
    workloads: Vec<Workload>,
    out_dir: PathBuf,
}

fn main() -> Result<()> {
    let options = parse_options()?;
    fs::create_dir_all(&options.out_dir)
        .map_err(|_| Error::InvalidState("failed to create output directory"))?;
    for workload in &options.workloads {
        let csv = match workload {
            Workload::Setup => bench_setup(&options)?,
            Workload::UpdateReg => bench_update(&options, true)?,
            Workload::UpdateKeys => bench_update(&options, false)?,
            Workload::Lookup => bench_lookup(&options)?,
            Workload::Audit => bench_audit(&options)?,
        };
        let path = options.out_dir.join(format!("{}.csv", workload.name()));
        fs::write(&path, csv).map_err(|_| Error::InvalidState("failed to write CSV"))?;
        eprintln!("wrote {}", path.display());
    }
    Ok(())
}

// setup

fn bench_setup(options: &Options) -> Result<String> {
    let mut csv = String::from(
        "log_capacity,threads,setup_ms,commitment_bytes,public_epoch_bytes,retained_state_bytes\n",
    );
    for &cap in &options.caps {
        let (server, elapsed) = timed(|| Server::new(cap, Blake3Placement, options.threads));
        let server = server?;
        let public = server.current().public();
        let commitment_bytes = public.index_root.len();
        let public_bytes = public.to_bytes().len();
        let retained = server.retained_state_bytes();
        writeln!(
            csv,
            "{cap},{},{:.3},{commitment_bytes},{public_bytes},{retained}",
            options.threads,
            millis(elapsed)
        )
        .unwrap();
    }
    Ok(csv)
}

// update_reg / update_keys

/// registration = true is the authors' light_update_reg (2^k new labels in one epoch),
/// false is light_update_keys (2^k registered labels get new values)
fn bench_update(options: &Options, registration: bool) -> Result<String> {
    let mut csv = String::from(
        "log_capacity,log_batch,batch,threads,\
         server_total_ms,placement_ms,index_stark_prove_ms,value_commit_ms,randomizer_update_ms,\
         open_old_rand_ms,open_new_rand_ms,open_old_value_ms,open_new_value_ms,\
         server_self_verify_ms,server_other_ms,\
         openings,transition_proof_bytes,index_stark_bytes,\
         old_rand_opening_bytes,new_rand_opening_bytes,old_value_opening_bytes,new_value_opening_bytes,\
         public_epoch_bytes,bulletin_board_bytes,\
         audit_verify_ms,audit_index_stark_verify_ms,audit_recurrence_openings_verify_ms,\
         opening_folding_bytes,opening_leaf_bytes,opening_merkle_auth_bytes,opening_root_bytes,opening_metadata_bytes\n",
    );
    for &cap in &options.caps {
        let capacity = 1usize << cap;
        for &k in &options.update_logs {
            let batch = 1usize << k;
            let warmup = 1usize << WARMUP_LOG;
            if (warmup + batch) * 2 > capacity {
                eprintln!("skip 2^{cap} batch 2^{k}: load would exceed 1/2");
                continue;
            }
            let pre_registered = if registration { warmup } else { warmup + batch };
            let mut server = Server::from_trusted_checkpoint(
                cap,
                Blake3Placement,
                options.threads,
                (1..=pre_registered).map(|i| author_entry(i, 0)),
            )?;
            let new_entries: Vec<_> = (warmup + 1..=warmup + batch)
                .map(|i| author_entry(i, if registration { 0 } else { 1 }))
                .collect();

            let previous = server.current().clone();
            let (next, server_total) = timed(|| {
                if registration {
                    server.register_batch(&new_entries)
                } else {
                    server.update_batch(&new_entries)
                }
            });
            let next = next?;
            let proof = server.transitions().last().expect("epoch proved").clone();
            // measured inside the server during the call above
            let t = *server.last_epoch_timings();
            let other = server_total
                - (t.placement
                    + t.index_stark
                    + t.value_commit
                    + t.randomizer_update
                    + t.openings.iter().sum::<Duration>()
                    + t.self_verify);

            let verifier =
                verifier_breakdown(previous.public(), next.public(), &proof, options.reps)?;
            let sizes = TransitionSizes::of(&proof);
            let public_bytes = next.public().to_bytes().len();
            let b = &sizes.recurrence_breakdown;
            writeln!(
                csv,
                "{cap},{k},{batch},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},\
                 {},{},{},{},{},{},{},{},{},{:.3},{:.3},{:.3},{},{},{},{},{}",
                options.threads,
                millis(server_total),
                millis(t.placement),
                millis(t.index_stark),
                millis(t.value_commit),
                millis(t.randomizer_update),
                millis(t.openings[0]),
                millis(t.openings[1]),
                millis(t.openings[2]),
                millis(t.openings[3]),
                millis(t.self_verify),
                millis(other),
                proof.opening_count(),
                sizes.total,
                sizes.index_stark,
                sizes.recurrence[0],
                sizes.recurrence[1],
                sizes.recurrence[2],
                sizes.recurrence[3],
                public_bytes,
                public_bytes + sizes.total,
                millis(verifier.total),
                millis(verifier.index_stark),
                millis(verifier.recurrence_openings),
                b.deep_folding_message_bytes,
                b.merkle_leaf_value_bytes,
                b.merkle_authentication_bytes,
                b.intermediate_root_bytes,
                b.metadata_bytes,
            )
            .unwrap();
        }
    }
    Ok(csv)
}

struct VerifierBreakdown {
    total: Duration,
    index_stark: Duration,
    recurrence_openings: Duration,
}

fn verifier_breakdown(
    previous: &PublicEpoch,
    next: &PublicEpoch,
    proof: &TransitionProof,
    reps: usize,
) -> Result<VerifierBreakdown> {
    let parameters = &previous.parameters;
    let total = median(reps, || {
        verify_transition(previous, next, proof).map(|_| ())
    })?;
    let statement = transition_statement_digest(previous, next);
    let mut index_stark = Duration::ZERO;
    if let Some(registration) = &proof.registration {
        index_stark = median(reps, || {
            verify_index_update(
                parameters.num_vars,
                next.epoch,
                &previous.index_root,
                &next.index_root,
                registration,
            )
        })?;
    }
    let point = recurrence_audit_point(&statement, parameters.num_vars);
    let r = &proof.recurrence;
    let recurrence_openings = median(reps, || {
        r.old_randomizer
            .verify(parameters, &previous.commitments.randomizer, &point)?;
        r.new_randomizer
            .verify(parameters, &next.commitments.randomizer, &point)?;
        r.old_value
            .verify(parameters, &previous.commitments.value, &point)?;
        r.new_value
            .verify(parameters, &next.commitments.value, &point)
    })?;
    Ok(VerifierBreakdown {
        total,
        index_stark,
        recurrence_openings,
    })
}

struct TransitionSizes {
    total: usize,
    index_stark: usize,
    /// old/new Randomizer, old/new Value
    recurrence: [usize; 4],
    recurrence_breakdown: ProofSizeBreakdown,
}

impl TransitionSizes {
    fn of(proof: &TransitionProof) -> Self {
        let index_stark = proof
            .registration
            .as_ref()
            .map_or(0, |registration| registration.encoded_len());
        let r = &proof.recurrence;
        Self {
            total: proof.encoded_len(),
            index_stark,
            recurrence: [
                r.old_randomizer.encoded_len(),
                r.new_randomizer.encoded_len(),
                r.old_value.encoded_len(),
                r.new_value.encoded_len(),
            ],
            recurrence_breakdown: breakdown(&r.new_value),
        }
    }
}

// lookup

fn bench_lookup(options: &Options) -> Result<String> {
    let mut csv = String::from(
        "log_capacity,occupied,load,threads,label,kind,probes,openings,index_paths,value_openings,\
         server_prove_ms,client_verify_ms,client_index_paths_verify_ms,client_value_opening_verify_ms,\
         proof_bytes,index_paths_bytes,index_path_bytes_each,value_opening_bytes,probe_framing_bytes,\
         opening_folding_bytes,opening_leaf_bytes,opening_merkle_auth_bytes,opening_root_bytes,opening_metadata_bytes\n",
    );
    for &cap in &options.caps {
        let occupied = options.lookup_load.occupied(cap);
        let server = Server::from_trusted_checkpoint(
            cap,
            Blake3Placement,
            options.threads,
            (1..=occupied).map(|i| author_entry(i, 0)),
        )?;
        let snapshot = server.current().clone();

        // The authors look up label "1", the extra labels show how the number of probes varies
        let mut labels = vec![("1".to_string(), "member")];
        let step = (occupied / options.lookup_samples.max(1)).max(1);
        labels.extend(
            (1..options.lookup_samples)
                .map(|s| ((1 + s * step).min(occupied).to_string(), "member")),
        );
        labels.extend((0..options.lookup_samples).map(|s| (format!("absent-{s}"), "absent")));

        for (label, kind) in labels {
            let (proof, prove) = timed(|| server.prove_lookup(&snapshot, label.as_bytes()));
            let proof = proof?;
            let row = measure_lookup(snapshot.public(), label.as_bytes(), &proof, options.reps)?;
            let b = &row.breakdown;
            writeln!(
                csv,
                "{cap},{occupied},{},{},{label},{kind},{},{},{},{},{:.3},{:.3},{:.3},{:.3},{},{},{},{},{},{},{},{},{},{}",
                options.lookup_load.name(),
                options.threads,
                proof.probes.len(),
                proof.opening_count(),
                proof.probes.len(),
                usize::from(proof.membership.is_some()),
                millis(prove),
                millis(row.verify),
                millis(row.index_verify),
                millis(row.value_verify),
                row.total_bytes,
                row.index_bytes,
                row.index_bytes / proof.probes.len(),
                row.value_bytes,
                row.framing_bytes,
                b.deep_folding_message_bytes,
                b.merkle_leaf_value_bytes,
                b.merkle_authentication_bytes,
                b.intermediate_root_bytes,
                b.metadata_bytes,
            )
            .unwrap();
        }
    }
    Ok(csv)
}

struct LookupRow {
    verify: Duration,
    index_verify: Duration,
    value_verify: Duration,
    total_bytes: usize,
    index_bytes: usize,
    value_bytes: usize,
    framing_bytes: usize,
    breakdown: ProofSizeBreakdown,
}

fn measure_lookup(
    public: &PublicEpoch,
    label: &[u8],
    proof: &LookupProof<()>,
    reps: usize,
) -> Result<LookupRow> {
    let parameters = &public.parameters;
    let verify = median(reps, || {
        verify_lookup(&Blake3Placement, public, label, proof).map(|_| ())
    })?;
    let points = proof
        .probes
        .iter()
        .map(|probe| slot_to_point(probe.slot, parameters.num_vars))
        .collect::<Result<Vec<_>>>()?;
    let index_verify = median(reps, || {
        for probe in &proof.probes {
            probe
                .index
                .verify(parameters.num_vars, &public.index_root)?;
        }
        Ok(())
    })?;
    let value_verify = match &proof.membership {
        Some(claim) => median(reps, || {
            claim.opening.verify(
                parameters,
                &public.commitments.value,
                points.last().expect("non-empty"),
            )
        })?,
        None => Duration::ZERO,
    };
    let total_bytes = proof.to_bytes().len();
    let index_bytes: usize = proof.probes.iter().map(|p| p.index.encoded_len()).sum();
    let value_bytes = proof
        .membership
        .as_ref()
        .map_or(0, |claim| claim.opening.encoded_len());
    Ok(LookupRow {
        verify,
        index_verify,
        value_verify,
        total_bytes,
        index_bytes,
        value_bytes,
        framing_bytes: total_bytes - index_bytes - value_bytes,
        breakdown: proof
            .membership
            .as_ref()
            .map_or(ProofSizeBreakdown::default(), |claim| {
                breakdown(&claim.opening)
            }),
    })
}

// audit

fn bench_audit(options: &Options) -> Result<String> {
    // two epochs of 2^AUDIT_BATCH_LOG registrations each
    let mut csv = String::from(
        "log_capacity,threads,epochs,verify_latest_ms,verify_history_ms,verify_genesis_cold_ms,verify_genesis_warm_ms,verify_range_ms,\
         index_stark_verify_ms,recurrence_openings_verify_ms,openings_latest,proof_bytes_latest,\
         history_openings,history_bytes\n",
    );
    for &cap in &options.caps {
        let batch = 1usize << AUDIT_BATCH_LOG;
        let mut server = Server::new(cap, Blake3Placement, options.threads)?;
        let first: Vec<_> = (1..=batch).map(|i| author_entry(i, 0)).collect();
        let second: Vec<_> = (batch + 1..=2 * batch)
            .map(|i| author_entry(i, 0))
            .collect();
        server.register_batch(&first)?;
        server.register_batch(&second)?;

        let snapshots = server.snapshots();
        let previous = snapshots[snapshots.len() - 2].public();
        let latest = snapshots[snapshots.len() - 1].public();
        let proof = server.transitions().last().expect("two epochs");
        let latest_breakdown = verifier_breakdown(previous, latest, proof, options.reps)?;

        let successors: Vec<_> = snapshots[1..].iter().map(|s| s.public().clone()).collect();
        let genesis_cold = {
            let start = Instant::now();
            verify_genesis(snapshots[0].public())?;
            start.elapsed()
        };
        let genesis_warm = median(options.reps, || {
            verify_genesis(snapshots[0].public()).map(|_| ())
        })?;
        let range = median(options.reps, || {
            verify_range(snapshots[0].public(), &successors, server.transitions()).map(|_| ())
        })?;
        let history = median(options.reps, || {
            verify_history(snapshots[0].public(), &successors, server.transitions()).map(|_| ())
        })?;
        let history_openings: usize = server.transitions().iter().map(|p| p.opening_count()).sum();
        let history_bytes: usize = server.transitions().iter().map(|p| p.encoded_len()).sum();

        writeln!(
            csv,
            "{cap},{},{},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{:.3},{},{},{history_openings},{history_bytes}",
            options.threads,
            successors.len(),
            millis(latest_breakdown.total),
            millis(history),
            millis(genesis_cold),
            millis(genesis_warm),
            millis(range),
            millis(latest_breakdown.index_stark),
            millis(latest_breakdown.recurrence_openings),
            proof.opening_count(),
            proof.encoded_len(),
        )
        .unwrap();
    }
    Ok(csv)
}

// helpers

/// Same labels/values as the authors' benches: label i, value i
fn author_entry(i: usize, version: usize) -> (Vec<u8>, Vec<u8>) {
    (
        i.to_string().into_bytes(),
        format!("{i}#{version}").into_bytes(),
    )
}

fn breakdown(opening: &AuthenticatedOpening) -> ProofSizeBreakdown {
    opening.proof.to_bytes_with_breakdown(opening.value).1
}

fn timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
    let start = Instant::now();
    let value = f();
    (value, start.elapsed())
}

fn median(reps: usize, mut f: impl FnMut() -> Result<()>) -> Result<Duration> {
    let mut samples = Vec::with_capacity(reps);
    for _ in 0..reps.max(1) {
        let (result, elapsed) = timed(&mut f);
        result?;
        samples.push(elapsed);
    }
    samples.sort();
    Ok(samples[samples.len() / 2])
}

fn millis(duration: Duration) -> f64 {
    duration.as_secs_f64() * 1_000.0
}

// options

fn parse_options() -> Result<Options> {
    let mut options = Options {
        caps: (16..=21).collect(),
        update_logs: (4..=10).collect(),
        threads: 8,
        reps: 5,
        lookup_samples: 4,
        lookup_load: LookupLoad::Sqrt,
        workloads: Workload::ALL.to_vec(),
        out_dir: PathBuf::from("bench-results"),
    };
    let arguments = env::args().skip(1).collect::<Vec<_>>();
    let mut index = 0;
    while index < arguments.len() {
        let flag = arguments[index].as_str();
        if flag == "--help" || flag == "-h" {
            print_help();
            std::process::exit(0);
        }
        let value = arguments
            .get(index + 1)
            .ok_or(Error::InvalidInput("missing command-line option value"))?;
        match flag {
            "--caps" => options.caps = parse_list(value)?,
            "--update-logs" => options.update_logs = parse_list(value)?,
            "--threads" => options.threads = parse_usize(value)?,
            "--reps" => options.reps = parse_usize(value)?,
            "--lookup-samples" => options.lookup_samples = parse_usize(value)?,
            "--lookup-load" => {
                options.lookup_load = match value.as_str() {
                    "sqrt" => LookupLoad::Sqrt,
                    "quarter" => LookupLoad::Quarter,
                    "half" => LookupLoad::Half,
                    _ => {
                        return Err(Error::InvalidInput(
                            "lookup load must be sqrt, quarter, or half",
                        ));
                    }
                }
            }
            "--only" => {
                options.workloads = value
                    .split(',')
                    .map(|name| {
                        Workload::ALL
                            .into_iter()
                            .find(|w| w.name() == name)
                            .ok_or(Error::InvalidInput("unknown workload name"))
                    })
                    .collect::<Result<_>>()?
            }
            "--out-dir" => options.out_dir = PathBuf::from(value),
            _ => return Err(Error::InvalidInput("unknown command-line option")),
        }
        index += 2;
    }
    if options.caps.is_empty() || options.caps.iter().any(|&cap| cap < 6 || cap > 22) {
        return Err(Error::InvalidInput("capacities must be between 6 and 22"));
    }
    if options.threads == 0 || options.threads > 8 {
        return Err(Error::InvalidInput("threads must be between 1 and 8"));
    }
    Ok(options)
}

/// Accepts a,b,c or an inclusive range a..b
fn parse_list(value: &str) -> Result<Vec<usize>> {
    if let Some((lo, hi)) = value.split_once("..") {
        return Ok((parse_usize(lo)?..=parse_usize(hi)?).collect());
    }
    value.split(',').map(parse_usize).collect()
}

fn parse_usize(value: &str) -> Result<usize> {
    value
        .trim()
        .parse()
        .map_err(|_| Error::InvalidInput("command-line value must be an integer"))
}

fn print_help() {
    eprintln!(
        "Usage: cargo run --release --bin irondict_bench -- [options]\n\
         Mirrors the authors' iron-key-bench workloads on IronDict/DeepFold.\n\
         Options:\n\
           --caps LIST          log2 capacities, e.g. 16,18,20 or 14..20 (default 16..21; max 22)\n\
                                authors use 22,28,34 with KZH; DeepFold here is capped at 2^22\n\
           --update-logs LIST   log2 batch sizes for update_reg/update_keys (default 4..10; authors 4..17)\n\
           --threads N          DeepFold prover workers, 1..8 (default 8)\n\
           --reps N             repetitions for verifier timings, median reported (default 5)\n\
           --lookup-samples N   extra member and absent labels per capacity (default 4)\n\
           --lookup-load L      sqrt (authors: 2^(cap/2) entries), quarter, or half (default sqrt)\n\
           --only LIST          subset of setup,update_reg,update_keys,lookup,audit\n\
           --out-dir DIR        CSV output directory (default bench-results)"
    );
}
