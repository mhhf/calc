//! Parallel STARK prover for symbolic exploration fixtures.
//!
//! Usage:
//!   cargo run --bin prove_symbolic --release -- fixtures/*.json
//!   cargo run --bin prove_symbolic --release -- tests/fixtures/solc_symbolic_*.json
//!
//! Uses `normalize_tree_witnesses` + `prove_witnesses_shared_keygen` for
//! single keygen, constant VK, and parallel proving across all fixtures.

use std::time::Instant;
use proof_checker::bridge::{
    normalize_tree_witnesses, prove_witnesses_shared_keygen, WitnessJson,
};

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() {
        eprintln!("Usage: prove_symbolic <fixture1.json> [fixture2.json ...]");
        std::process::exit(1);
    }

    eprintln!("Loading {} fixtures...", args.len());

    let names: Vec<String> = args.iter().map(|path| {
        std::path::Path::new(path)
            .file_stem()
            .map(|s| s.to_string_lossy().to_string())
            .unwrap_or_else(|| path.clone())
    }).collect();

    let mut witnesses: Vec<WitnessJson> = Vec::with_capacity(args.len());
    for (i, path) in args.iter().enumerate() {
        let json = match std::fs::read_to_string(path) {
            Ok(j) => j,
            Err(e) => {
                eprintln!("  FAIL {}: read error: {e}", names[i]);
                std::process::exit(1);
            }
        };
        match serde_json::from_str::<WitnessJson>(&json) {
            Ok(w) => witnesses.push(w),
            Err(e) => {
                eprintln!("  FAIL {}: parse error: {e}", names[i]);
                std::process::exit(1);
            }
        }
    }

    let t0 = Instant::now();
    normalize_tree_witnesses(&mut witnesses);
    eprintln!("Normalized {} fixtures in {:.2}s", witnesses.len(), t0.elapsed().as_secs_f64());

    eprintln!("Proving with shared keygen ({} threads)...", rayon::current_num_threads());
    let t1 = Instant::now();
    match prove_witnesses_shared_keygen(&witnesses) {
        Ok(results) => {
            let total = t1.elapsed().as_secs_f64();
            for (i, _r) in results.iter().enumerate() {
                eprintln!("  OK  {}", names[i]);
            }
            eprintln!("\n{}/{} passed, 0 failed, {total:.2}s wall time ({:.2}s avg)",
                results.len(), results.len(), total / results.len() as f64);
        }
        Err(e) => {
            eprintln!("  FAIL: {e}");
            std::process::exit(1);
        }
    }
}
