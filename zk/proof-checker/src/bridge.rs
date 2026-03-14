//! Bridge: JSON witness → STARK trace matrices → prover.
//!
//! Two verification paths, selected by `format` field in witness JSON:
//!   - Tree (default): full ILL derivation, 13 chips, 7 buses
//!   - Flat ("flat"):  forward-only rewriting certificate, 5–7 chips, 5 buses
//!
//! Phase 3b: ROM chips and init chips are data-carrying structs with
//! preprocessed columns committed at keygen. `run_simple_test_fast`
//! handles keygen transparently.
//!
//! The witness JSON is fully self-describing: it carries `tags` (connective
//! tag mapping) and `rule_specs` (per-rule chip structure), both derived
//! from the calculus definition. The bridge reads these and constructs
//! chips entirely at runtime — zero calculus-specific code.

use std::collections::HashMap;
use std::sync::Arc;

use openvm_stark_backend::{
    p3_matrix::dense::RowMajorMatrix,
    AirRef,
};
use openvm_stark_sdk::{
    config::{baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine}, FriParameters},
    engine::{StarkFriEngine, VerificationDataWithFriParams},
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use serde::Deserialize;

use crate::chips::{
    discard::DiscardChip,
    dup::DupChip,
    flat_final::FlatFinalChip,
    flat_init::FlatInitChip,
    flat_step::FlatStepChip,
    formula_rom::FormulaRomAir,
    freevar_rom::FreevarRomAir,
    gamma_rom::GammaRomAir,
    init::InitChip,
    subst::SubstChip,
    zero_l::ZeroLChip,
};
use crate::rule::{RuleChip, RuleSpec};

/// JSON witness format produced by `lib/zk/witness.js`.
#[derive(Deserialize, Debug)]
pub struct WitnessJson {
    pub tags: HashMap<String, u32>,
    pub rule_specs: HashMap<String, RuleSpec>,
    pub chips: HashMap<String, Vec<Vec<u32>>>,
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
    #[serde(default)]
    pub freevar_rom: Vec<Vec<u32>>,
}

/// Known special chip names that are NOT generic RuleChips.
const SPECIAL_CHIPS: &[&str] = &["init", "dup", "zero_l", "discard", "subst"];

/// Build a padded RowMajorMatrix from dynamic-width rows.
fn build_trace(rows: &[Vec<u32>], width: usize, min_rows: usize) -> RowMajorMatrix<BabyBear> {
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * width);
    for (i, row) in rows.iter().enumerate() {
        assert_eq!(row.len(), width, "row {i} width mismatch: expected {width}, got {}", row.len());
        for &v in row {
            data.push(BabyBear::from_u32(v));
        }
    }
    for _ in rows.len()..n {
        for _ in 0..width {
            data.push(BabyBear::ZERO);
        }
    }
    RowMajorMatrix::new(data, width)
}

/// Build a padded trace for chips with zero active rows.
fn empty_trace(width: usize, min_rows: usize) -> RowMajorMatrix<BabyBear> {
    let n = min_rows.next_power_of_two();
    let data = vec![BabyBear::ZERO; n * width];
    RowMajorMatrix::new(data, width)
}

/// Build a width-1 trace from a column of u32 values, padded.
fn build_trace_1col(values: &[u32], min_rows: usize) -> RowMajorMatrix<BabyBear> {
    let n = values.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n);
    for &v in values {
        data.push(BabyBear::from_u32(v));
    }
    for _ in values.len()..n {
        data.push(BabyBear::ZERO);
    }
    RowMajorMatrix::new(data, 1)
}

/// Split formula ROM rows [hash, tag, c0, c1, is_active, num_lookups]
/// into preprocessed entries [hash, tag, c0, c1, is_active] and lookups [num_lookups].
fn split_formula_rom(rows: &[Vec<u32>]) -> (Vec<[u32; 5]>, Vec<u32>) {
    let mut entries = Vec::with_capacity(rows.len());
    let mut lookups = Vec::with_capacity(rows.len());
    for row in rows {
        entries.push([row[0], row[1], row[2], row[3], row[4]]);
        lookups.push(row[5]);
    }
    (entries, lookups)
}

/// Split gamma ROM rows [hash, is_active, num_lookups]
/// into preprocessed entries [hash, is_active] and lookups [num_lookups].
fn split_gamma_rom(rows: &[Vec<u32>]) -> (Vec<[u32; 2]>, Vec<u32>) {
    let mut entries = Vec::with_capacity(rows.len());
    let mut lookups = Vec::with_capacity(rows.len());
    for row in rows {
        entries.push([row[0], row[1]]);
        lookups.push(row[2]);
    }
    (entries, lookups)
}

/// Split freevar ROM rows [subst_id, freevar_hash, ground_value, is_active, num_lookups]
/// into preprocessed entries [subst_id, freevar_hash, ground_value, is_active] and lookups [num_lookups].
fn split_freevar_rom(rows: &[Vec<u32>]) -> (Vec<[u32; 4]>, Vec<u32>) {
    let mut entries = Vec::with_capacity(rows.len());
    let mut lookups = Vec::with_capacity(rows.len());
    for row in rows {
        entries.push([row[0], row[1], row[2], row[3]]);
        lookups.push(row[4]);
    }
    (entries, lookups)
}

/// Split init chip rows [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]
/// into preprocessed [ctx_hash, ctx_active, oblig_hash, oblig_active, lax] and main [nonce].
fn split_init_rows(rows: &[Vec<u32>]) -> (Vec<[u32; 5]>, Vec<u32>) {
    let mut prep = Vec::with_capacity(rows.len());
    let mut nonces = Vec::with_capacity(rows.len());
    for row in rows {
        prep.push([row[0], row[1], row[2], row[3], row[5]]); // lax is col 5
        nonces.push(row[4]); // nonce is col 4
    }
    (prep, nonces)
}

/// Build AIRs, traces, and PIs from a tree witness (shared by prove and vdata paths).
fn build_witness_inputs(witness: &WitnessJson) -> Result<(Vec<AirRef<BabyBearPoseidon2Config>>, Vec<RowMajorMatrix<BabyBear>>, Vec<Vec<BabyBear>>), String> {
    let min_rows = 4;
    let tags = &witness.tags;

    let zero_tag = tags.get("zero").copied().unwrap_or(0);

    let mut airs: Vec<AirRef<_>> = Vec::new();
    let mut traces: Vec<RowMajorMatrix<BabyBear>> = Vec::new();
    let mut pis: Vec<Vec<BabyBear>> = Vec::new();

    // 1. InitChip (data-carrying, preprocessed sequent)
    let init_rows = witness.chips.get("init").ok_or("missing init chip")?;
    let (init_prep, init_nonces) = split_init_rows(init_rows);
    airs.push(Arc::new(InitChip { rows: init_prep, min_rows }) as AirRef<_>);
    traces.push(build_trace_1col(&init_nonces, min_rows));
    pis.push(vec![]);

    // 2. DupChip (always present, may be empty)
    let dup_rows = witness.chips.get("dup");
    airs.push(Arc::new(DupChip) as AirRef<_>);
    traces.push(match dup_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 2, min_rows),
        _ => empty_trace(2, min_rows),
    });
    pis.push(vec![]);

    // 3. ZeroLChip
    let zero_rows = witness.chips.get("zero_l");
    airs.push(Arc::new(ZeroLChip::new(zero_tag)) as AirRef<_>);
    traces.push(match zero_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 6, min_rows),
        _ => empty_trace(6, min_rows),
    });
    pis.push(vec![]);

    // 4. DiscardChip
    let discard_rows = witness.chips.get("discard");
    airs.push(Arc::new(DiscardChip) as AirRef<_>);
    traces.push(match discard_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 3, min_rows),
        _ => empty_trace(3, min_rows),
    });
    pis.push(vec![]);

    // 5. SubstChip (width 16 — FORMULA_BUS lookups + unwrap rows)
    let subst_rows = witness.chips.get("subst");
    airs.push(Arc::new(SubstChip) as AirRef<_>);
    traces.push(match subst_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, crate::chips::subst::WIDTH, min_rows),
        _ => empty_trace(crate::chips::subst::WIDTH, min_rows),
    });
    pis.push(vec![]);

    // 6. Generic RuleChips — specs read from witness (fully generic)
    let mut rule_names: Vec<String> = witness.chips.keys()
        .filter(|name| !SPECIAL_CHIPS.contains(&name.as_str()))
        .cloned()
        .collect();
    rule_names.sort();

    for name in &rule_names {
        let spec = witness.rule_specs.get(name)
            .ok_or_else(|| format!("chip '{}' has no matching rule_spec in witness", name))?
            .clone();
        let chip = RuleChip::new(spec);
        let width = chip.layout.width;
        let rows = witness.chips.get(name).unwrap();
        if !rows.is_empty() && rows[0].len() != width {
            panic!("chip '{}': layout width={} but first row has {} columns", name, width, rows[0].len());
        }
        airs.push(Arc::new(chip) as AirRef<_>);
        traces.push(if rows.is_empty() {
            empty_trace(width, min_rows)
        } else {
            build_trace(rows, width, min_rows)
        });
        pis.push(vec![]);
    }

    // 7. FormulaRomAir (data-carrying, preprocessed)
    let (formula_entries, formula_lookups) = split_formula_rom(&witness.formula_rom);
    airs.push(Arc::new(FormulaRomAir { entries: formula_entries, min_rows }) as AirRef<_>);
    traces.push(if formula_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&formula_lookups, min_rows)
    });
    pis.push(vec![]);

    // 8. GammaRomAir (data-carrying, preprocessed)
    let (gamma_entries, gamma_lookups) = split_gamma_rom(&witness.gamma_rom);
    airs.push(Arc::new(GammaRomAir { entries: gamma_entries, min_rows }) as AirRef<_>);
    traces.push(if gamma_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&gamma_lookups, min_rows)
    });
    pis.push(vec![]);

    // 9. FreevarRomAir (data-carrying, preprocessed)
    if !witness.freevar_rom.is_empty() {
        let (freevar_entries, freevar_lookups) = split_freevar_rom(&witness.freevar_rom);
        airs.push(Arc::new(FreevarRomAir { entries: freevar_entries, min_rows }) as AirRef<_>);
        traces.push(build_trace_1col(&freevar_lookups, min_rows));
        pis.push(vec![]);
    }

    Ok((airs, traces, pis))
}

/// Prove a witness JSON, returning Ok(()) on success or Err on verification failure.
pub fn prove_witness(witness: &WitnessJson) -> Result<(), String> {
    let (airs, traces, pis) = build_witness_inputs(witness)?;
    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .map(|_| ())
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Prove a tree witness, returning the full verification data (proof + VK + FRI params).
/// Phase 4a: needed for recursive verification and IVC.
pub fn prove_witness_vdata(witness: &WitnessJson) -> Result<VerificationDataWithFriParams<BabyBearPoseidon2Config>, String> {
    let (airs, traces, pis) = build_witness_inputs(witness)?;
    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Flat witness format produced by `lib/zk/flat-witness.js`.
///
/// Phase 3b.7: uses CONTEXT_BUS + GAMMA_BUS + FORMULA_BUS + SUBST_TREE_BUS + FREEVAR_BUS.
/// Chips: FlatInitChip + FlatStepChip + FlatFinalChip + FormulaRomAir + GammaRomAir
///        + SubstChip (optional) + FreevarRomAir (optional).
#[derive(Deserialize, Debug)]
pub struct FlatWitnessJson {
    pub format: String,
    pub chips: HashMap<String, Vec<Vec<u32>>>,
    /// Preprocessed per-step data for FlatStepChip: canon_cons (canonical body hash).
    #[serde(default)]
    pub flat_step_prep: Vec<u32>,
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
    #[serde(default)]
    pub freevar_rom: Vec<Vec<u32>>,
    /// Connective name → ZK tag integer (needed for FlatStepChip struct fields).
    pub tags: HashMap<String, u32>,
    /// Constants: { one_hash: Store.put('one', []) }.
    #[serde(default)]
    pub constants: HashMap<String, u32>,
}

/// Build AIRs, traces, and PIs from a flat witness (shared by prove and vdata paths).
fn build_flat_witness_inputs(witness: &FlatWitnessJson) -> Result<(Vec<AirRef<BabyBearPoseidon2Config>>, Vec<RowMajorMatrix<BabyBear>>, Vec<Vec<BabyBear>>), String> {
    let min_rows = 4;

    let loli_tag = witness.tags.get("loli").copied().unwrap_or(0);
    let monad_tag = witness.tags.get("monad").copied().unwrap_or(0);
    let tensor_tag = witness.tags.get("tensor").copied().unwrap_or(0);
    let one_hash = witness.constants.get("one_hash").copied().unwrap_or(0);

    let mut airs: Vec<AirRef<_>> = Vec::new();
    let mut traces: Vec<RowMajorMatrix<BabyBear>> = Vec::new();
    let mut pis: Vec<Vec<BabyBear>> = Vec::new();

    // 1. FlatInitChip (Phase 4a: main trace + public values, no preprocessed)
    let init_rows = witness.chips.get("flat_init").ok_or("missing flat_init chip")?;
    let ctx_hashes: Vec<u32> = init_rows.iter()
        .filter(|r| r.len() >= 2 && r[0] == 1) // is_active=1
        .map(|r| r[1])
        .collect();
    let max_ctx_size = ctx_hashes.len();
    airs.push(Arc::new(FlatInitChip { ctx_hashes: ctx_hashes.clone(), max_ctx_size, min_rows }) as AirRef<_>);
    // Main trace: [is_active, hash] (was dummy width-1 column before Phase 4a)
    traces.push(if init_rows.is_empty() {
        empty_trace(2, min_rows)
    } else {
        build_trace(init_rows, 2, init_rows.len().max(min_rows))
    });
    // Public values: context hashes padded to max_ctx_size
    let init_pis: Vec<BabyBear> = ctx_hashes.iter()
        .map(|&h| BabyBear::from_u32(h))
        .collect();
    pis.push(init_pis);

    // 2. FlatStepChip (data-carrying, with tag constants + preprocessed canon_cons)
    let step_rows = witness.chips.get("flat_step").ok_or("missing flat_step chip")?;
    let step_min = step_rows.len().max(min_rows);
    airs.push(Arc::new(FlatStepChip {
        loli_tag, monad_tag, tensor_tag, one_hash,
        canon_cons: witness.flat_step_prep.clone(),
        min_rows: step_min,
    }) as AirRef<_>);
    traces.push(if step_rows.is_empty() {
        empty_trace(crate::chips::flat_step::WIDTH, min_rows)
    } else {
        build_trace(step_rows, crate::chips::flat_step::WIDTH, step_min)
    });
    pis.push(vec![]);

    // 3. FlatFinalChip (Phase 4a: with public values for final context)
    let final_rows = witness.chips.get("flat_final").ok_or("missing flat_final chip")?;
    let final_hashes: Vec<u32> = final_rows.iter()
        .filter(|r| r.len() >= 2 && r[0] == 1)
        .map(|r| r[1])
        .collect();
    let final_max_ctx = final_hashes.len();
    airs.push(Arc::new(FlatFinalChip { max_ctx_size: final_max_ctx }) as AirRef<_>);
    traces.push(if final_rows.is_empty() {
        empty_trace(2, min_rows)
    } else {
        build_trace(final_rows, 2, min_rows)
    });
    let final_pis: Vec<BabyBear> = final_hashes.iter()
        .map(|&h| BabyBear::from_u32(h))
        .collect();
    pis.push(final_pis);

    // 4. FormulaRomAir (data-carrying, preprocessed)
    let (formula_entries, formula_lookups) = split_formula_rom(&witness.formula_rom);
    airs.push(Arc::new(FormulaRomAir { entries: formula_entries, min_rows }) as AirRef<_>);
    traces.push(if formula_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&formula_lookups, min_rows)
    });
    pis.push(vec![]);

    // 5. GammaRomAir (data-carrying, preprocessed)
    let (gamma_entries, gamma_lookups) = split_gamma_rom(&witness.gamma_rom);
    airs.push(Arc::new(GammaRomAir { entries: gamma_entries, min_rows }) as AirRef<_>);
    traces.push(if gamma_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&gamma_lookups, min_rows)
    });
    pis.push(vec![]);

    // 6. SubstChip (optional — present when loli matches exist)
    let subst_rows = witness.chips.get("subst");
    airs.push(Arc::new(SubstChip) as AirRef<_>);
    traces.push(match subst_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, crate::chips::subst::WIDTH, min_rows),
        _ => empty_trace(crate::chips::subst::WIDTH, min_rows),
    });
    pis.push(vec![]);

    // 7. FreevarRomAir (optional — present when loli matches have freevars)
    if !witness.freevar_rom.is_empty() {
        let (freevar_entries, freevar_lookups) = split_freevar_rom(&witness.freevar_rom);
        airs.push(Arc::new(FreevarRomAir { entries: freevar_entries, min_rows }) as AirRef<_>);
        traces.push(build_trace_1col(&freevar_lookups, min_rows));
        pis.push(vec![]);
    }

    Ok((airs, traces, pis))
}

/// Prove a flat witness, returning Ok(()) on success.
pub fn prove_flat_witness(witness: &FlatWitnessJson) -> Result<(), String> {
    let (airs, traces, pis) = build_flat_witness_inputs(witness)?;
    // FlatStepChip has degree-4 constraints (spine boundary checks), requiring
    // log_blowup >= 2 so the LDE has enough evaluations for the quotient domain.
    let engine = BabyBearPoseidon2Engine::new(
        FriParameters::standard_with_100_bits_security(2),
    );
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .map(|_| ())
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Prove a flat witness, returning the full verification data.
/// Phase 4a: needed for recursive verification and IVC.
pub fn prove_flat_witness_vdata(witness: &FlatWitnessJson) -> Result<VerificationDataWithFriParams<BabyBearPoseidon2Config>, String> {
    let (airs, traces, pis) = build_flat_witness_inputs(witness)?;
    let engine = BabyBearPoseidon2Engine::new(
        FriParameters::standard_with_100_bits_security(2),
    );
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Prove a chunked flat witness (array of FlatWitnessJson), returning
/// verification data for each chunk. Each chunk is proved independently.
/// Phase 4a-4: per-chunk proving for batch recursive composition.
pub fn prove_chunked_flat_witness(
    chunks: &[FlatWitnessJson],
) -> Result<Vec<VerificationDataWithFriParams<BabyBearPoseidon2Config>>, String> {
    let mut results = Vec::with_capacity(chunks.len());
    for (i, chunk) in chunks.iter().enumerate() {
        let vdata = prove_flat_witness_vdata(chunk)
            .map_err(|e| format!("chunk {i} failed: {e}"))?;
        results.push(vdata);
    }
    Ok(results)
}

/// Parse a JSON string and prove it. Dispatches based on `format` field.
pub fn prove_json(json: &str) -> Result<(), String> {
    let value: serde_json::Value = serde_json::from_str(json)
        .map_err(|e| format!("JSON parse error: {e}"))?;

    if value.get("format").and_then(|v| v.as_str()) == Some("flat") {
        let witness: FlatWitnessJson = serde_json::from_value(value)
            .map_err(|e| format!("Flat witness parse error: {e}"))?;
        prove_flat_witness(&witness)
    } else {
        let witness: WitnessJson = serde_json::from_value(value)
            .map_err(|e| format!("Tree witness parse error: {e}"))?;
        prove_witness(&witness)
    }
}
