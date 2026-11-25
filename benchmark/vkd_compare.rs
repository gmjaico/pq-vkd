//! Program to get VKD results to compare against Whatsapp AKD and IronDict

use std::collections::HashMap;
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::time::{Duration, Instant};

use irondict::crypto::placement::Blake3Placement;
use irondict::protocol::{ServerState, VerifiedLookupResult, verify_lookup, verify_transition};
use irondict::{Error, Result};

type Server = ServerState<Blake3Placement>;

// Shared workload, must match the other two harnesses
const LABEL_BASE: u64 = 1_000_000_000_000;
const UPDATE_STRIDE: u64 = 0x9E37_79B1;
const LOOKUP_STRIDE: u64 = 0x2545_F491;

fn label(i: u64) -> Vec<u8> {
    (LABEL_BASE + i).to_string().into_bytes()
}
fn value(i: u64, version: u64) -> Vec<u8> {
    let mut v = vec![0x76u8; 32];
    v[..8].copy_from_slice(&i.to_le_bytes());
    v[8..16].copy_from_slice(&version.to_le_bytes());
    v
}
fn update_index(epoch: u64, batch: u64, j: u64, prefill: u64) -> u64 {
    1 + ((epoch * batch + j).wrapping_mul(UPDATE_STRIDE) % prefill)
}
fn lookup_index(s: u64, prefill: u64) -> u64 {
    1 + ((s.wrapping_mul(LOOKUP_STRIDE) + 7) % prefill)
}

struct Options {
    cap: usize,
    prefill_log: usize,
    batch_logs: Vec<usize>,
    mixed_logs: Vec<usize>,
    epochs: usize,
    lookups: usize,
    threads: usize,
    reps: usize,
    out: String,
}

struct Csv {
    head: String,
    body: String,
}

impl Csv {
    fn row(
        &mut self,
        phase: &str,
        batch: usize,
        sample: usize,
        server: Duration,
        verify: Duration,
        bytes: usize,
        ok: bool,
        detail: &str,
    ) {
        let line = format!(
            "{},{phase},{batch},{sample},{:.3},{:.3},{bytes},{ok},{:.1},{detail}",
            self.head,
            ms(server),
            ms(verify),
            peak_rss_mib()
        );
        println!("{line}");
        writeln!(self.body, "{line}").unwrap();
    }
}

fn main() -> Result<()> {
    let o = parse()?;
    let prefill = 1u64 << o.prefill_log;
    let mut csv = Csv {
        head: format!("deepfold,ours,{},{prefill},{}", o.cap, o.threads),
        body: String::from(HEADER),
    };
    let one_thread = rayon::ThreadPoolBuilder::new()
        .num_threads(1)
        .build()
        .map_err(|_| Error::InvalidState("thread pool"))?;

    // setup: empty directory of capacity 2^cap
    let (empty, t) = timed(|| Server::new(o.cap, Blake3Placement, o.threads));
    drop(empty?);
    csv.row("setup", 0, 0, t, Duration::ZERO, 0, true, "");

    // prefill: trusted bulk load (not proved), as in the authors' harnesses
    let (server, t) = timed(|| {
        Server::from_trusted_checkpoint(
            o.cap,
            Blake3Placement,
            o.threads,
            (1..=prefill).map(|i| (label(i), value(i, 0))),
        )
    });
    let mut server = server?;
    csv.row(
        "prefill",
        prefill as usize,
        0,
        t,
        Duration::ZERO,
        0,
        true,
        "trusted checkpoint",
    );

    let mut versions: HashMap<u64, u64> = HashMap::new();
    let mut next_fresh = prefill + 1;

    // register: B new labels; update: B existing labels; mixed: B new + B existing labels in the same epoch
    let mut update_epoch = 0u64;
    let phases = [
        ("register", true, false, &o.batch_logs),
        ("update", false, true, &o.batch_logs),
        ("mixed", true, true, &o.mixed_logs),
    ];
    for (phase, with_reg, with_upd, logs) in phases {
        for &k in logs {
            let batch = 1u64 << k;
            for sample in 0..o.epochs {
                let mut registrations: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
                let mut updates: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
                if with_reg {
                    let range = next_fresh..next_fresh + batch;
                    next_fresh += batch;
                    registrations = range.map(|i| (label(i), value(i, 0))).collect();
                }
                if with_upd {
                    let e = update_epoch;
                    update_epoch += 1;
                    updates = (0..batch)
                        .map(|j| {
                            let i = update_index(e, batch, j, prefill);
                            let v = versions.entry(i).or_insert(0);
                            *v += 1;
                            (label(i), value(i, *v))
                        })
                        .collect();
                }
                let previous = server.current().public().clone();
                let (next, t) = timed(|| server.publish_batch(&registrations, &updates));
                let next = next?.public().clone();
                let proof = server.transitions().last().expect("proved").clone();
                let mut ok = true;
                let verify = median(o.reps, || {
                    ok &= one_thread
                        .install(|| verify_transition(&previous, &next, &proof))
                        .is_ok();
                });
                let bytes = proof.encoded_len() + next.to_bytes().len();
                csv.row(
                    phase,
                    batch as usize,
                    sample,
                    t,
                    verify,
                    bytes,
                    ok,
                    "incl. server self-verify",
                );
                server.prune_history();
            }
        }
    }

    let snapshot = server.current().clone();
    for s in 0..o.lookups as u64 {
        let i = lookup_index(s, prefill);
        let expected = value(i, versions.get(&i).copied().unwrap_or(0));
        let l = label(i);
        let (proof, t) = timed(|| server.prove_lookup(&snapshot, &l));
        let proof = proof?;
        let mut ok = true;
        let verify = median(o.reps, || {
            let r = one_thread
                .install(|| verify_lookup(&Blake3Placement, snapshot.public(), &l, &proof));
            ok &= matches!(&r, Ok(v) if matches!(
                &v.result,
                VerifiedLookupResult::Present { value, .. } if *value == expected
            ));
        });
        let detail = format!("probes={}", proof.probes.len());
        csv.row(
            "lookup",
            1,
            s as usize,
            t,
            verify,
            proof.to_bytes().len(),
            ok,
            &detail,
        );
    }

    fs::write(&o.out, csv.body).map_err(|_| Error::InvalidState("write csv"))?;
    eprintln!("-> {}", o.out);
    Ok(())
}

const HEADER: &str = "system,variant,log_capacity,prefill,threads,phase,batch,sample,server_ms,verify_ms,proof_bytes,ok,peak_rss_mib,detail\n";

fn timed<T>(f: impl FnOnce() -> T) -> (T, Duration) {
    let start = Instant::now();
    let v = f();
    (v, start.elapsed())
}

fn median(reps: usize, mut f: impl FnMut()) -> Duration {
    let mut samples: Vec<Duration> = (0..reps.max(1)).map(|_| timed(&mut f).1).collect();
    samples.sort();
    samples[samples.len() / 2]
}

fn ms(d: Duration) -> f64 {
    d.as_secs_f64() * 1e3
}

fn peak_rss_mib() -> f64 {
    fs::read_to_string("/proc/self/status")
        .ok()
        .and_then(|s| {
            s.lines()
                .find(|l| l.starts_with("VmHWM:"))
                .and_then(|l| l.split_whitespace().nth(1)?.parse::<f64>().ok())
        })
        .map_or(0.0, |kb| kb / 1024.0)
}

fn parse() -> Result<Options> {
    let mut o = Options {
        cap: 16,
        prefill_log: 0,
        batch_logs: vec![4, 8, 12],
        mixed_logs: Vec::new(),
        epochs: 3,
        lookups: 32,
        threads: 8,
        reps: 5,
        out: "vkd_compare_deepfold.csv".into(),
    };
    let mut prefill_set = false;
    let args: Vec<String> = env::args().skip(1).collect();
    let bad = || Error::InvalidInput("bad argument");
    let mut it = args.iter();
    while let Some(flag) = it.next() {
        let v = it.next().ok_or_else(bad)?;
        let n = || v.parse::<usize>().map_err(|_| bad());
        match flag.as_str() {
            "--log-capacity" => o.cap = n()?,
            "--prefill-log" => {
                o.prefill_log = n()?;
                prefill_set = true;
            }
            "--batches" => {
                o.batch_logs = v
                    .split(',')
                    .map(|x| x.parse().map_err(|_| bad()))
                    .collect::<Result<_>>()?
            }
            "--mixed" => {
                o.mixed_logs = v
                    .split(',')
                    .filter(|x| !x.is_empty())
                    .map(|x| x.parse().map_err(|_| bad()))
                    .collect::<Result<_>>()?
            }
            "--epochs" => o.epochs = n()?,
            "--lookups" => o.lookups = n()?,
            "--threads" => o.threads = n()?,
            "--reps" => o.reps = n()?,
            "--out" => o.out = v.clone(),
            _ => return Err(bad()),
        }
    }
    if !prefill_set {
        o.prefill_log = o.cap - 2;
    }
    Ok(o)
}
