//! Phase 2: Adversarial flat path tests.
//!
//! Tests FlatStepChip soundness for compiled rules:
//! - Wrong consumed hash → CONTEXT_BUS imbalance
//! - Wrong tensor spine → FORMULA_BUS mismatch

mod common;

use std::sync::Arc;

use p3_baby_bear::BabyBear;
use openvm_stark_backend::{p3_field::PrimeCharacteristicRing, p3_matrix::dense::RowMajorMatrix, AirRef};
use sequent_certifier::chips::{
    canon_cons_rom::CanonConsRomAir,
    flat_final::FlatFinalChip,
    flat_init::FlatInitChip,
    flat_step::FlatStepChip,
    freevar_rom::FreevarRomAir,
    subst::SubstChip,
};
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
/// Width 43 (Phase 4a-5: includes canon_cons at index 42).
fn compiled_step(consumed: u32, produced: u32, loli: u32, monad: u32) -> [u32; 43] {
    let mut row = [0u32; 43];
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
    // row[42] = 0             // canon_cons (unused for compiled)
    row
}

/// Build a width-4 flat trace: [is_active, hash, acc_active, is_first]
fn build_flat_boundary_trace(rows: &[[u32; 2]], min_rows: usize) -> (RowMajorMatrix<BabyBear>, u32) {
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * 4);
    let mut acc: u32 = 0;
    for (i, row) in rows.iter().enumerate() {
        if row[0] == 1 { acc += 1; }
        data.push(BabyBear::from_u32(row[0]));
        data.push(BabyBear::from_u32(row[1]));
        data.push(BabyBear::from_u32(acc));
        data.push(if i == 0 { BabyBear::ONE } else { BabyBear::ZERO });
    }
    let final_acc = BabyBear::from_u32(acc);
    for _ in rows.len()..n {
        data.push(BabyBear::ZERO);
        data.push(BabyBear::ZERO);
        data.push(final_acc);
        data.push(BabyBear::ZERO);
    }
    (RowMajorMatrix::new(data, 4), acc)
}

/// Run flat path test with FlatStepChip (requires log_blowup=2 for degree-4 constraints).
fn run_flat_test(
    init_hashes: &[u32],
    step_rows: &[[u32; 43]],
    final_rows: &[[u32; 2]],
    formula_rom: &[[u32; 6]],
    gamma_rom: &[[u32; 3]],
) {
    let max_ctx_size = init_hashes.len();
    let init = FlatInitChip { ctx_hashes: init_hashes.to_vec(), max_ctx_size, min_rows: MIN };
    let init_row_data: Vec<[u32; 2]> = init_hashes.iter().map(|&h| [1u32, h]).collect();
    let (init_trace, init_active_count) = build_flat_boundary_trace(&init_row_data, MIN);

    // Init PVs: [hash_0, ..., hash_{max-1}, active_count]
    let mut init_pis: Vec<BabyBear> = init_hashes.iter()
        .map(|&h| BabyBear::from_u32(h)).collect();
    init_pis.resize(max_ctx_size, BabyBear::ZERO);
    init_pis.push(BabyBear::from_u32(init_active_count));

    let step_chip = FlatStepChip {
        loli_tag: TAG_LOLI, monad_tag: TAG_MONAD, tensor_tag: TAG_TENSOR,
        one_hash: ONE_HASH,
    };
    let step_trace = padded_trace::<43>(step_rows, MIN);

    let final_max_ctx = final_rows.iter().filter(|r| r[0] == 1).count();
    let final_max = final_max_ctx.max(max_ctx_size);
    let (final_trace, final_active_count) = build_flat_boundary_trace(final_rows, MIN);

    // Final PVs: [hash_0, ..., hash_{max-1}, active_count]
    let final_hashes: Vec<u32> = final_rows.iter()
        .filter(|r| r[0] == 1).map(|r| r[1]).collect();
    let mut final_pis: Vec<BabyBear> = final_hashes.iter()
        .map(|&h| BabyBear::from_u32(h)).collect();
    final_pis.resize(final_max, BabyBear::ZERO);
    final_pis.push(BabyBear::from_u32(final_active_count));

    let (rom_chip, rom_trace) = make_formula_rom(formula_rom, MIN);
    let (gamma_chip, gamma_trace) = make_gamma_rom(gamma_rom, MIN);

    // SubstChip always present (even if empty)
    let subst_trace = padded_trace::<16>(&[], MIN);

    // FreevarRomAir always present (empty)
    let freevar_trace = padded_trace::<1>(&[], MIN);

    // CanonConsRomAir always present (empty for compiled-only tests)
    let cc_trace = padded_trace::<1>(&[], MIN);

    let airs: Vec<AirRef<_>> = vec![
        Arc::new(init),
        Arc::new(step_chip),
        Arc::new(FlatFinalChip { max_ctx_size: final_max }),
        Arc::new(rom_chip),
        Arc::new(gamma_chip),
        Arc::new(SubstChip),
        Arc::new(FreevarRomAir { entries: vec![], min_rows: MIN }),
        Arc::new(CanonConsRomAir { entries: vec![], min_rows: MIN }),
    ];
    let traces = vec![init_trace, step_trace, final_trace, rom_trace, gamma_trace, subst_trace, freevar_trace, cc_trace];
    let pis = vec![init_pis, vec![], final_pis, vec![], vec![], vec![], vec![], vec![]];

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
        &[[1, H_PRODUCED]], // final expects H_PRODUCED (but step sends H_WRONG)
        &[
            [H_LOLI_W, TAG_LOLI, H_CONSUMED, H_MONAD_W, 1, 1],
            [H_MONAD_W, TAG_MONAD, H_WRONG, 0, 1, 1],
        ],
        &[[H_LOLI_W, 1, 1]],
    );
}
