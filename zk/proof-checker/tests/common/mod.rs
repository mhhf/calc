//! Shared test utilities for proof term verifier integration tests.

use std::collections::HashMap;

use proof_checker::bridge::WitnessJson;
use proof_checker::chips::{
    formula_rom::FormulaRomAir,
    freevar_rom::FreevarRomAir,
    gamma_rom::GammaRomAir,
    init::InitChip,
};
use proof_checker::rule::RuleSpec;
use openvm_stark_backend::p3_matrix::dense::RowMajorMatrix;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

/// Build a padded trace matrix from active rows.
///
/// Each row is `W` field elements. Pads to at least `min_rows` then
/// to the next power of 2 (required by stark-backend). Padding rows
/// are all zeros (is_active=0 → no bus contribution).
pub fn padded_trace<const W: usize>(
    active_rows: &[[u32; W]],
    min_rows: usize,
) -> RowMajorMatrix<BabyBear> {
    let n = active_rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * W);
    for row in active_rows {
        for &v in row {
            data.push(BabyBear::from_u32(v));
        }
    }
    for _ in active_rows.len()..n {
        for _ in 0..W {
            data.push(BabyBear::ZERO);
        }
    }
    RowMajorMatrix::new(data, W)
}

/// Build an InitChip + its width-1 main trace from old-style rows.
///
/// Input rows: `[ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]`
/// Preprocessed (in struct): `[ctx_hash, ctx_active, oblig_hash, oblig_active, lax]`
/// Main trace: `[nonce]`
pub fn make_init(rows: &[[u32; 6]], min_rows: usize) -> (InitChip, RowMajorMatrix<BabyBear>) {
    let prep: Vec<[u32; 5]> = rows
        .iter()
        .map(|r| [r[0], r[1], r[2], r[3], r[5]])
        .collect();
    let main: Vec<[u32; 1]> = rows.iter().map(|r| [r[4]]).collect();
    (InitChip { rows: prep, min_rows }, padded_trace(&main, min_rows))
}

/// Build a FormulaRomAir + its width-1 main trace from old-style rows.
///
/// Input rows: `[hash, tag, c0, c1, is_active, num_lookups]`
/// Preprocessed (in struct): `[hash, tag, c0, c1, is_active]`
/// Main trace: `[num_lookups]`
pub fn make_formula_rom(rows: &[[u32; 6]], min_rows: usize) -> (FormulaRomAir, RowMajorMatrix<BabyBear>) {
    let prep: Vec<[u32; 5]> = rows
        .iter()
        .map(|r| [r[0], r[1], r[2], r[3], r[4]])
        .collect();
    let main: Vec<[u32; 1]> = rows.iter().map(|r| [r[5]]).collect();
    (FormulaRomAir { entries: prep, min_rows }, padded_trace(&main, min_rows))
}

/// Build a GammaRomAir + its width-1 main trace from old-style rows.
///
/// Input rows: `[hash, is_active, num_lookups]`
/// Preprocessed (in struct): `[hash, is_active]`
/// Main trace: `[num_lookups]`
pub fn make_gamma_rom(rows: &[[u32; 3]], min_rows: usize) -> (GammaRomAir, RowMajorMatrix<BabyBear>) {
    let prep: Vec<[u32; 2]> = rows.iter().map(|r| [r[0], r[1]]).collect();
    let main: Vec<[u32; 1]> = rows.iter().map(|r| [r[2]]).collect();
    (GammaRomAir { entries: prep, min_rows }, padded_trace(&main, min_rows))
}

/// Build a FreevarRomAir + its width-1 main trace from rows.
///
/// Input rows: `[subst_id, freevar_hash, ground_value, is_active, num_lookups]`
/// Preprocessed (in struct): `[subst_id, freevar_hash, ground_value, is_active]`
/// Main trace: `[num_lookups]`
pub fn make_freevar_rom(rows: &[[u32; 5]], min_rows: usize) -> (FreevarRomAir, RowMajorMatrix<BabyBear>) {
    let prep: Vec<[u32; 4]> = rows.iter().map(|r| [r[0], r[1], r[2], r[3]]).collect();
    let main: Vec<[u32; 1]> = rows.iter().map(|r| [r[4]]).collect();
    (FreevarRomAir { entries: prep, min_rows }, padded_trace(&main, min_rows))
}

/// Load rule specs and tags from a fixture JSON file.
///
/// Every fixture contains the full set of rule_specs and tags
/// (derived from the calculus definition), so any fixture works.
pub fn load_test_specs() -> (HashMap<String, u32>, HashMap<String, RuleSpec>) {
    let json = include_str!("../fixtures/identity.json");
    let w: WitnessJson = serde_json::from_str(json).unwrap();
    (w.tags, w.rule_specs)
}
