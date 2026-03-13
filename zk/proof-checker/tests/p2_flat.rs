//! Phase 2: Adversarial flat path tests.
//!
//! Tests FlatStepChip soundness for compiled rules:
//! - Wrong consumed hash → CONTEXT_BUS imbalance
//! - Wrong tensor spine → FORMULA_BUS mismatch

mod common;

use std::sync::Arc;

use proof_checker::chips::{
    flat_final::FlatFinalChip,
    flat_init::FlatInitChip,
    flat_step::FlatStepChip,
    subst::SubstChip,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::{baby_bear_poseidon2::BabyBearPoseidon2Engine, FriParameters},
    engine::StarkFriEngine,
};

use common::{make_formula_rom, make_gamma_rom, padded_trace};

// Tags
const TAG_LOLI: u32 = 2;
const TAG_MONAD: u32 = 8;
const TAG_TENSOR: u32 = 1;

// Hash constants
const H_CONSUMED: u32 = 10;
const H_PRODUCED: u32 = 20;
const H_MONAD_P: u32 = 30;     // monad(H_PRODUCED)
const H_LOLI: u32 = 40;        // loli(H_CONSUMED, H_MONAD_P)
const ONE_HASH: u32 = 5;

const MIN: usize = 4;

/// Build a flat step row for a compiled rule with 1 consumed, 1 produced.
fn compiled_step(consumed: u32, produced: u32, loli: u32, monad: u32) -> [u32; 42] {
    let mut row = [0u32; 42];
    row[0] = 1;               // active
    row[1] = 0;               // is_loli=0 (compiled)
    row[2] = loli;            // ground_loli
    row[3] = consumed;        // consumed[0]
    row[9] = 1;               // consumed_active[0]
    row[15] = produced;       // produced[0]
    row[21] = 1;              // produced_active[0]
    row[27] = consumed;       // ant_hash = consumed (1 slot)
    row[32] = produced;       // cons_hash = produced (1 slot)
    row[37] = monad;          // monad_hash
    row[38] = 1;              // compiled = active * (1 - is_loli)
    row[40] = produced;       // ground_cons
    row
}

/// Run flat path test with FlatStepChip (requires log_blowup=2 for degree-4 constraints).
fn run_flat_test(
    init_hashes: &[u32],
    step_rows: &[[u32; 42]],
    step_prep: &[u32],
    final_rows: &[[u32; 2]],
    formula_rom: &[[u32; 6]],
    gamma_rom: &[[u32; 3]],
) {
    let init = FlatInitChip { ctx_hashes: init_hashes.to_vec(), min_rows: MIN };
    let init_trace = padded_trace::<1>(&[[0u32; 1]; 0], init_hashes.len().max(MIN));

    let step_min = step_rows.len().max(MIN);
    let step_chip = FlatStepChip {
        loli_tag: TAG_LOLI, monad_tag: TAG_MONAD, tensor_tag: TAG_TENSOR,
        one_hash: ONE_HASH,
        canon_cons: step_prep.to_vec(),
        min_rows: step_min,
    };
    let step_trace = padded_trace::<42>(step_rows, step_min);

    let final_trace = padded_trace::<2>(final_rows, MIN);

    let (rom_chip, rom_trace) = make_formula_rom(formula_rom, MIN);
    let (gamma_chip, gamma_trace) = make_gamma_rom(gamma_rom, MIN);

    // SubstChip always present (even if empty)
    let subst_trace = padded_trace::<16>(&[], MIN);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(step_chip),
        Arc::new(FlatFinalChip),
        Arc::new(rom_chip),
        Arc::new(gamma_chip),
        Arc::new(SubstChip),
    ];
    let traces = vec![init_trace, step_trace, final_trace, rom_trace, gamma_trace, subst_trace];
    let pis = vec![vec![]; 6];

    let engine = BabyBearPoseidon2Engine::new(
        FriParameters::standard_with_100_bits_security(2),
    );
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .expect("flat path test");
}

// ---------------------------------------------------------------------------
// Happy path: valid compiled rule (1 consumed, 1 produced)
// ---------------------------------------------------------------------------

#[test]
fn p2_flat_compiled_basic() {
    let step = compiled_step(H_CONSUMED, H_PRODUCED, H_LOLI, H_MONAD_P);

    run_flat_test(
        &[H_CONSUMED],
        &[step],
        &[0], // canon_cons=0 (unused for compiled)
        &[[1, H_PRODUCED]], // final receives produced
        &[
            [H_LOLI, TAG_LOLI, H_CONSUMED, H_MONAD_P, 1, 1],
            [H_MONAD_P, TAG_MONAD, H_PRODUCED, 0, 1, 1],
        ],
        &[[H_LOLI, 1, 1]], // gamma
    );
}

// ---------------------------------------------------------------------------
// Adversarial: wrong consumed hash → CONTEXT_BUS imbalance
// Init sends H_CONSUMED but step receives H_WRONG
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_flat_wrong_consumed_fails() {
    const H_WRONG: u32 = 15;
    const H_MONAD_W: u32 = 35;
    const H_LOLI_W: u32 = 45;

    let step = compiled_step(H_WRONG, H_PRODUCED, H_LOLI_W, H_MONAD_W);

    run_flat_test(
        &[H_CONSUMED], // init sends the REAL hash
        &[step],       // step consumes the WRONG hash
        &[0],
        &[[1, H_PRODUCED]],
        &[
            [H_LOLI_W, TAG_LOLI, H_WRONG, H_MONAD_W, 1, 1],
            [H_MONAD_W, TAG_MONAD, H_PRODUCED, 0, 1, 1],
        ],
        &[[H_LOLI_W, 1, 1]],
    );
}

// ---------------------------------------------------------------------------
// Adversarial: wrong produced hash → CONTEXT_BUS imbalance
// Step produces H_WRONG but final expects H_PRODUCED
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_flat_wrong_produced_fails() {
    const H_WRONG: u32 = 25;
    const H_MONAD_W: u32 = 36;
    const H_LOLI_W: u32 = 46;

    // Step claims to produce H_WRONG
    let step = compiled_step(H_CONSUMED, H_WRONG, H_LOLI_W, H_MONAD_W);

    run_flat_test(
        &[H_CONSUMED],
        &[step],
        &[0],
        &[[1, H_PRODUCED]], // final expects H_PRODUCED (but step sends H_WRONG)
        &[
            [H_LOLI_W, TAG_LOLI, H_CONSUMED, H_MONAD_W, 1, 1],
            [H_MONAD_W, TAG_MONAD, H_WRONG, 0, 1, 1],
        ],
        &[[H_LOLI_W, 1, 1]],
    );
}
