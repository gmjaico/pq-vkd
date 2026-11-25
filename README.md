# Auditor Accessible Post Quantum Verifiable Key Directory 

This is a proof of concept implementation for my auditor-accessible post-quantum VKD and is solely for academic benchmarking purposes

## Layout

- `irondict/src/pcs/deepfold/`: DeepFold polynomial commitment
- `irondict/src/index_stark/`: Index-update STARK
- `irondict/src/crypto/`: Merkle trees, Poseidon2 hashes, transcripts, placement
- `irondict/src/protocol/`: registration, updates, lookup, consistency, audit
- `benchmark/`: benchmark programs

## Setup

Requires Rust 1.85 or newer on Linux x86-64. 

```bash
cargo build --release
cargo test --release
```

## Benchmarking

DeepFold on its own (arguments are log2 polynomial sizes):
```bash
cargo run --release --bin deepfold_bench -- 16 18 20
```

Protocol scenarios (setup, registration, updates, lookup, audit), with CSVs
written to `bench-results/`:
```bash
cargo run --release --bin irondict_bench -- --caps 16..20
```

Comparison workload against IronDict (KZH) and AKD: prefill, registration and
update epochs, then lookups, written to one CSV:
```bash
cargo run --release --bin vkd_compare -- --log-capacity 21 --prefill-log 18 \
    --batches 4,8,12 --epochs 3 --lookups 32 --out vkd_compare_deepfold.csv
```
