//! Parallel STARK prover for symbolic exploration fixtures.
//!
//! Usage:
//!   cargo run --bin prove_symbolic --release -- fixtures/*.json
//!   cargo run --bin prove_symbolic --release -- tests/fixtures/solc_symbolic_*.json
//!
//! Uses rayon par_iter to prove all fixtures in parallel.
//! Each fixture is independently proved via `prove_json` (no shared state).

use std::time::Instant;
use rayon::prelude::*;
use proof_checker::bridge::prove_json;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("Usage: prove_symbolic <fixture1.json> [fixture2.json ...]");
        std::process::exit(1);
    }

    eprintln!("Proving {} fixtures in parallel ({} threads)...",
        args.len(), rayon::current_num_threads());

    let t0 = Instant::now();

    let results: Vec<(String, Result<f64, String>)> = args.par_iter()
        .map(|path| {
            let name = std::path::Path::new(path)
                .file_stem()
                .map(|s| s.to_string_lossy().to_string())
                .unwrap_or_else(|| path.clone());

            let json = match std::fs::read_to_string(path) {
                Ok(j) => j,
                Err(e) => return (name, Err(format!("read error: {e}"))),
            };

            let t = Instant::now();
            match prove_json(&json) {
                Ok(()) => (name, Ok(t.elapsed().as_secs_f64())),
                Err(e) => (name, Err(e)),
            }
        })
        .collect();

    let total = t0.elapsed().as_secs_f64();
    let mut ok = 0;
    let mut fail = 0;

    for (name, result) in &results {
        match result {
            Ok(secs) => { eprintln!("  OK  {name} ({secs:.2}s)"); ok += 1; }
            Err(e)   => { eprintln!("  FAIL {name}: {e}"); fail += 1; }
        }
    }

    eprintln!("\n{ok}/{} passed, {fail} failed, {total:.2}s wall time", results.len());

    if fail > 0 {
        std::process::exit(1);
    }
}
