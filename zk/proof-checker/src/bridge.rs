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

use rayon::prelude::*;

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
    byte_check_rom::ByteCheckRomAir,
    canon_cons_rom::CanonConsRomAir,
    ctx_boundary::CtxBoundaryChip,
    discard::DiscardChip,
    dup::DupChip,
    fact_axiom::FactAxiomChip,
    fact_rom::fact_rom_air,
    flat_final::FlatFinalChip,
    flat_init::FlatInitChip,
    flat_step::FlatStepChip,
    formula_rom::FormulaRomAir,
    freevar_rom::FreevarRomAir,
    gamma_rom::gamma_rom_air,
    init::InitChip,
    oblig_boundary::ObligBoundaryChip,
    pred_rom::PredicateRomAir,
    subst::SubstChip,
    uint256_arith::Uint256ArithChip,
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
    /// Phase 6-4: verified fact ROM [goal_hash, is_active, num_lookups].
    /// Contains predicate hashes for custom-chip-verified facts (arr_get, inc, etc.).
    #[serde(default)]
    pub fact_rom: Vec<Vec<u32>>,
    /// Phase 6-6a: predicate verification ROM.
    /// [pred_hash, is_active, num_lookups, is_plus, is_mul, is_inc, arg0, arg1, arg2]
    /// PredicateRomAir constrains arithmetic semantics in preprocessed trace.
    #[serde(default)]
    pub pred_rom: Vec<Vec<u32>>,
    /// Phase 6-6b: 256-bit arithmetic verification rows.
    /// Each row is 166 columns: [prep (101 cols), main (65 cols)].
    /// Prep: [pred_hash, is_active, is_plus_256, is_inc_256, is_mul_256, a_limbs(32), b_limbs(32), c_limbs(32)]
    /// Main: [num_lookups, carry_lo(32), carry_hi(32)]
    #[serde(default)]
    pub uint256_arith: Vec<Vec<u32>>,
    /// Phase 6-6b: byte range check lookup counts.
    /// 256 entries: byte_check_rom[i] = num_lookups for byte value i.
    #[serde(default)]
    pub byte_check_rom: Vec<u32>,
    /// Phase 6-7: max obligation count for boundary chip PV normalization.
    #[serde(default)]
    pub max_oblig_count: Option<usize>,
    /// Phase 6-7: max context size for boundary chip PV normalization.
    #[serde(default)]
    pub max_boundary_ctx_size: Option<usize>,
}

/// Known special chip names that are NOT generic RuleChips.
const SPECIAL_CHIPS: &[&str] = &["init", "dup", "zero_l", "discard", "subst", "fact_axiom", "oblig_boundary", "ctx_boundary"];

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

/// Split canon_cons ROM rows [cons_hash, canon_cons, is_active, num_lookups]
/// into preprocessed entries [cons_hash, canon_cons, is_active] and lookups [num_lookups].
fn split_canon_cons_rom(rows: &[Vec<u32>]) -> (Vec<[u32; 3]>, Vec<u32>) {
    let mut entries = Vec::with_capacity(rows.len());
    let mut lookups = Vec::with_capacity(rows.len());
    for row in rows {
        entries.push([row[0], row[1], row[2]]);
        lookups.push(row[3]);
    }
    (entries, lookups)
}

/// Split predicate ROM rows
/// [pred_hash, is_active, num_lookups, is_plus, is_mul, is_inc,
///  is_arr_get, is_arr_set, is_mem_read, is_mem_expand, arg0, arg1, arg2, arg3]
/// into preprocessed entries [pred_hash, is_active, is_plus, is_mul, is_inc,
///  is_arr_get, is_arr_set, is_mem_read, is_mem_expand, arg0, arg1, arg2, arg3]
/// and lookups [num_lookups].
fn split_pred_rom(rows: &[Vec<u32>]) -> (Vec<[u32; 13]>, Vec<u32>) {
    let mut entries = Vec::with_capacity(rows.len());
    let mut lookups = Vec::with_capacity(rows.len());
    for row in rows {
        entries.push([
            row[0],  // pred_hash
            row[1],  // is_active
            row[3],  // is_plus
            row[4],  // is_mul
            row[5],  // is_inc
            row[6],  // is_arr_get
            row[7],  // is_arr_set
            row[8],  // is_mem_read
            row[9],  // is_mem_expand
            row[10], // arg0
            row[11], // arg1
            row[12], // arg2
            row[13], // arg3
        ]);
        lookups.push(row[2]); // num_lookups is at index 2
    }
    (entries, lookups)
}

/// Split uint256_arith rows (133 cols each) into:
/// - Preprocessed (100 cols): [pred_hash, is_active, is_plus_256, is_inc_256, a_0..31, b_0..31, c_0..31]
/// - Main (33 cols): [num_lookups, carry_0..31]
fn split_uint256_arith(rows: &[Vec<u32>]) -> (Vec<Vec<u32>>, Vec<Vec<u32>>) {
    let prep_width = crate::chips::uint256_arith::PREP_WIDTH; // 100
    let main_width = crate::chips::uint256_arith::WIDTH;      // 33
    let mut prep = Vec::with_capacity(rows.len());
    let mut main = Vec::with_capacity(rows.len());
    for row in rows {
        assert_eq!(row.len(), prep_width + main_width,
            "uint256_arith row width mismatch: expected {}, got {}", prep_width + main_width, row.len());
        prep.push(row[..prep_width].to_vec());
        main.push(row[prep_width..].to_vec());
    }
    (prep, main)
}

/// Split init chip rows into preprocessed [ctx_hash, ctx_active, oblig_hash, oblig_active, lax]
/// and main [is_active, nonce].
///
/// Accepts two formats:
/// - Legacy (6 cols): [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax] → is_active=1
/// - New (7 cols):    [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax, is_active]
fn split_init_rows(rows: &[Vec<u32>]) -> (Vec<[u32; 5]>, Vec<Vec<u32>>, u32) {
    let mut prep = Vec::with_capacity(rows.len());
    let mut main = Vec::with_capacity(rows.len());
    let mut acc: u32 = 0;
    for row in rows {
        prep.push([row[0], row[1], row[2], row[3], row[5]]); // lax is col 5
        let is_active = if row.len() >= 7 { row[6] } else { 1 };
        acc += is_active;
        main.push(vec![is_active, row[4], acc]); // [is_active, nonce, acc_active]
    }
    (prep, main, acc)
}

/// Build AIRs, traces, and PIs from a tree witness (shared by prove and vdata paths).
/// Public for tamper testing: tests can call this, modify PIs, and re-prove.
pub fn build_witness_inputs(witness: &WitnessJson) -> Result<(Vec<AirRef<BabyBearPoseidon2Config>>, Vec<RowMajorMatrix<BabyBear>>, Vec<Vec<BabyBear>>), String> {
    let min_rows = 4;
    let tags = &witness.tags;

    let zero_tag = tags.get("zero").copied().unwrap_or(0);

    let mut airs: Vec<AirRef<_>> = Vec::new();
    let mut traces: Vec<RowMajorMatrix<BabyBear>> = Vec::new();
    let mut pis: Vec<Vec<BabyBear>> = Vec::new();

    // 1. InitChip (data-carrying, preprocessed sequent, with sequent identity PVs)
    let init_rows = witness.chips.get("init").ok_or("missing init chip")?;
    let (init_prep, init_main, init_active_count) = split_init_rows(init_rows);

    // Extract sequent components for PVs: [ctx_hash_1..n, succedent_hash, lax, init_active_count]
    let mut ctx_hashes: Vec<u32> = Vec::new();
    let mut succedent_hash: u32 = 0;
    let mut lax_flag: u32 = 0;
    for row in &init_prep {
        // row = [ctx_hash, ctx_active, oblig_hash, oblig_active, lax]
        if row[1] == 1 { ctx_hashes.push(row[0]); }
        if row[3] == 1 { succedent_hash = row[2]; lax_flag = row[4]; }
    }
    let max_ctx_size = ctx_hashes.len();
    let num_pvs = max_ctx_size + 3; // ctx hashes + succedent + lax + init_active_count
    let mut init_pis: Vec<BabyBear> = ctx_hashes.iter()
        .map(|&h| BabyBear::from_u32(h)).collect();
    init_pis.push(BabyBear::from_u32(succedent_hash));
    init_pis.push(BabyBear::from_u32(lax_flag));
    init_pis.push(BabyBear::from_u32(init_active_count));

    airs.push(Arc::new(InitChip { rows: init_prep, min_rows, num_pvs }) as AirRef<_>);
    // Build init main trace with acc_active padding (can't use build_trace — padding
    // rows need acc_active = final_sum, not 0, to satisfy running-sum constraint)
    traces.push({
        let w = crate::chips::init::WIDTH;
        let n = init_main.len().max(min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * w);
        for row in &init_main {
            for &v in row { data.push(BabyBear::from_u32(v)); }
        }
        let final_acc = BabyBear::from_u32(init_active_count);
        for _ in init_main.len()..n {
            data.push(BabyBear::ZERO); // is_active = 0
            data.push(BabyBear::ZERO); // nonce = 0
            data.push(final_acc);       // acc_active = final_sum (carry forward)
        }
        RowMajorMatrix::new(data, w)
    });
    pis.push(init_pis);

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

    // 6. FactAxiomChip (Phase 6-4: custom chip for clause proof replacement)
    // Always present (like other special chips) to maintain constant AIR count.
    let fact_axiom_rows = witness.chips.get("fact_axiom");
    airs.push(Arc::new(FactAxiomChip) as AirRef<_>);
    traces.push(match fact_axiom_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, crate::chips::fact_axiom::WIDTH, min_rows),
        _ => empty_trace(crate::chips::fact_axiom::WIDTH, min_rows),
    });
    pis.push(vec![]);

    // 7. Generic RuleChips — specs read from witness (fully generic)
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

    // 8. FormulaRomAir (data-carrying, preprocessed)
    let (formula_entries, formula_lookups) = split_formula_rom(&witness.formula_rom);
    airs.push(Arc::new(FormulaRomAir { entries: formula_entries, min_rows }) as AirRef<_>);
    traces.push(if formula_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&formula_lookups, min_rows)
    });
    pis.push(vec![]);

    // 9. GammaRomAir (data-carrying, preprocessed)
    let (gamma_entries, gamma_lookups) = split_gamma_rom(&witness.gamma_rom);
    airs.push(Arc::new(gamma_rom_air(gamma_entries, min_rows)) as AirRef<_>);
    traces.push(if gamma_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&gamma_lookups, min_rows)
    });
    pis.push(vec![]);

    // 10. FreevarRomAir (data-carrying, preprocessed)
    if !witness.freevar_rom.is_empty() {
        let (freevar_entries, freevar_lookups) = split_freevar_rom(&witness.freevar_rom);
        airs.push(Arc::new(FreevarRomAir { entries: freevar_entries, min_rows }) as AirRef<_>);
        traces.push(build_trace_1col(&freevar_lookups, min_rows));
        pis.push(vec![]);
    }

    // 11. FactRomAir (Phase 6-4: custom chip verified facts)
    // Always present when fact_rom is non-empty; absent when empty
    // (backward compat: old fixtures without fact_rom still work).
    if !witness.fact_rom.is_empty() {
        let (fact_entries, fact_lookups) = split_gamma_rom(&witness.fact_rom);
        airs.push(Arc::new(fact_rom_air(fact_entries, min_rows)) as AirRef<_>);
        traces.push(build_trace_1col(&fact_lookups, min_rows));
        pis.push(vec![]);
    }

    // 12. PredicateRomAir (Phase 6-6a: in-circuit predicate verification)
    // Always present when pred_rom is non-empty. Constrains arithmetic
    // semantics (plus, mul, inc) in preprocessed trace. Absent when empty
    // (backward compat: old fixtures without pred_rom still work).
    if !witness.pred_rom.is_empty() {
        let (pred_entries, pred_lookups) = split_pred_rom(&witness.pred_rom);
        airs.push(Arc::new(PredicateRomAir { entries: pred_entries, min_rows }) as AirRef<_>);
        traces.push(build_trace_1col(&pred_lookups, min_rows));
        pis.push(vec![]);
    }

    // 13. ByteCheckRomAir + Uint256ArithChip (Phase 6-6b: 256-bit arithmetic)
    // Present when uint256_arith is non-empty. ByteCheckRomAir must come first
    // (supplies BYTE_CHECK_BUS that Uint256ArithChip demands).
    if !witness.uint256_arith.is_empty() {
        // ByteCheckRomAir: 256 entries [0..255], main trace = [num_lookups]
        let byte_min = 256usize.max(min_rows); // at least 256 rows
        airs.push(Arc::new(ByteCheckRomAir { min_rows: byte_min }) as AirRef<_>);
        traces.push(if witness.byte_check_rom.is_empty() {
            empty_trace(1, byte_min)
        } else {
            build_trace_1col(&witness.byte_check_rom, byte_min)
        });
        pis.push(vec![]);

        // Uint256ArithChip: preprocessed + main from split
        let (u256_prep, u256_main) = split_uint256_arith(&witness.uint256_arith);
        airs.push(Arc::new(Uint256ArithChip { entries: u256_prep, min_rows }) as AirRef<_>);
        traces.push(build_trace(&u256_main, crate::chips::uint256_arith::WIDTH, min_rows));
        pis.push(vec![]);
    }

    // 14. ObligBoundaryChip (Phase 6-7: tree path chunking)
    // Present when oblig_boundary chip data exists (chunked tree witnesses).
    if witness.chips.contains_key("oblig_boundary") {
        let max_oblig_count = witness.max_oblig_count.unwrap_or(1);
        let oblig_rows = witness.chips.get("oblig_boundary").unwrap();

        // Extract PVs: init obligs (is_send=1) and final obligs (is_send=0)
        let mut init_obligs: Vec<BabyBear> = Vec::new();
        let mut final_obligs: Vec<BabyBear> = Vec::new();
        let mut send_count: u32 = 0;
        let mut recv_count: u32 = 0;
        for row in oblig_rows {
            if row[0] == 1 { // is_active
                let goal = BabyBear::from_u32(row[3]);
                let lax = BabyBear::from_u32(row[4]);
                if row[1] == 1 { // is_send (init)
                    init_obligs.push(goal);
                    init_obligs.push(lax);
                    send_count += 1;
                } else { // receive (final)
                    final_obligs.push(goal);
                    final_obligs.push(lax);
                    recv_count += 1;
                }
            }
        }
        // Pad to max_oblig_count * 2
        init_obligs.resize(max_oblig_count * 2, BabyBear::ZERO);
        final_obligs.resize(max_oblig_count * 2, BabyBear::ZERO);
        let mut oblig_pvs = init_obligs;
        oblig_pvs.extend(final_obligs);
        oblig_pvs.push(BabyBear::from_u32(send_count));
        oblig_pvs.push(BabyBear::from_u32(recv_count));

        // Custom trace building: add acc_send_count + acc_recv_count columns,
        // padding rows carry forward final accumulated values.
        let width = crate::chips::oblig_boundary::WIDTH;
        let n = oblig_rows.len().max(min_rows).next_power_of_two();
        let mut oblig_trace_data = Vec::with_capacity(n * width);
        let mut acc_send: u32 = 0;
        let mut acc_recv: u32 = 0;
        for (i, row) in oblig_rows.iter().enumerate() {
            let is_active = row[0];
            let is_send = row[1];
            if is_active == 1 {
                if is_send == 1 { acc_send += 1; }
                else { acc_recv += 1; }
            }
            for &v in row { oblig_trace_data.push(BabyBear::from_u32(v)); }
            oblig_trace_data.push(BabyBear::from_u32(acc_send));
            oblig_trace_data.push(BabyBear::from_u32(acc_recv));
            oblig_trace_data.push(if i == 0 { BabyBear::ONE } else { BabyBear::ZERO }); // is_first
        }
        let final_acc_send = BabyBear::from_u32(acc_send);
        let final_acc_recv = BabyBear::from_u32(acc_recv);
        for _ in oblig_rows.len()..n {
            for _ in 0..5 { oblig_trace_data.push(BabyBear::ZERO); } // is_active..lax = 0
            oblig_trace_data.push(final_acc_send);
            oblig_trace_data.push(final_acc_recv);
            oblig_trace_data.push(BabyBear::ZERO); // is_first = 0
        }

        airs.push(Arc::new(ObligBoundaryChip { max_oblig_count }) as AirRef<_>);
        traces.push(if oblig_rows.is_empty() {
            empty_trace(width, min_rows)
        } else {
            RowMajorMatrix::new(oblig_trace_data, width)
        });
        pis.push(oblig_pvs);
    }

    // 15. CtxBoundaryChip (Phase 6-7: tree path chunking)
    if witness.chips.contains_key("ctx_boundary") {
        let max_ctx = witness.max_boundary_ctx_size.unwrap_or(0);
        let ctx_rows = witness.chips.get("ctx_boundary").unwrap();

        let mut init_ctx: Vec<BabyBear> = Vec::new();
        let mut final_ctx: Vec<BabyBear> = Vec::new();
        let mut send_count: u32 = 0;
        let mut recv_count: u32 = 0;
        for row in ctx_rows {
            if row[0] == 1 { // is_active
                let hash = BabyBear::from_u32(row[2]);
                if row[1] == 1 { // is_send (init)
                    init_ctx.push(hash);
                    send_count += 1;
                } else {
                    final_ctx.push(hash);
                    recv_count += 1;
                }
            }
        }
        init_ctx.resize(max_ctx, BabyBear::ZERO);
        final_ctx.resize(max_ctx, BabyBear::ZERO);
        let mut ctx_pvs = init_ctx;
        ctx_pvs.extend(final_ctx);
        ctx_pvs.push(BabyBear::from_u32(send_count));
        ctx_pvs.push(BabyBear::from_u32(recv_count));

        // Custom trace building: add acc_send_count + acc_recv_count columns,
        // padding rows carry forward final accumulated values.
        let width = crate::chips::ctx_boundary::WIDTH;
        let n = ctx_rows.len().max(min_rows).next_power_of_two();
        let mut ctx_trace_data = Vec::with_capacity(n * width);
        let mut acc_send: u32 = 0;
        let mut acc_recv: u32 = 0;
        for (i, row) in ctx_rows.iter().enumerate() {
            let is_active = row[0];
            let is_send = row[1];
            if is_active == 1 {
                if is_send == 1 { acc_send += 1; }
                else { acc_recv += 1; }
            }
            for &v in row { ctx_trace_data.push(BabyBear::from_u32(v)); }
            ctx_trace_data.push(BabyBear::from_u32(acc_send));
            ctx_trace_data.push(BabyBear::from_u32(acc_recv));
            ctx_trace_data.push(if i == 0 { BabyBear::ONE } else { BabyBear::ZERO }); // is_first
        }
        let final_acc_send = BabyBear::from_u32(acc_send);
        let final_acc_recv = BabyBear::from_u32(acc_recv);
        for _ in ctx_rows.len()..n {
            for _ in 0..3 { ctx_trace_data.push(BabyBear::ZERO); } // is_active..hash = 0
            ctx_trace_data.push(final_acc_send);
            ctx_trace_data.push(final_acc_recv);
            ctx_trace_data.push(BabyBear::ZERO); // is_first = 0
        }

        airs.push(Arc::new(CtxBoundaryChip { max_ctx_size: max_ctx }) as AirRef<_>);
        traces.push(if ctx_rows.is_empty() {
            empty_trace(width, min_rows)
        } else {
            RowMajorMatrix::new(ctx_trace_data, width)
        });
        pis.push(ctx_pvs);
    }

    Ok((airs, traces, pis))
}

/// Prove a witness JSON, returning Ok(()) on success or Err on verification failure.
///
/// Respects `OPENVM_FAST_TEST=1` for insecure-but-fast FRI parameters.
/// Without it, uses 100-bit provable security (193 queries + 20-bit PoW).
pub fn prove_witness(witness: &WitnessJson) -> Result<(), String> {
    prove_witness_vdata(witness).map(|_| ())
}

/// Prove a tree witness, returning the full verification data (proof + VK + FRI params).
/// Phase 4a: needed for recursive verification and IVC.
///
/// Respects `OPENVM_FAST_TEST=1` for insecure-but-fast FRI parameters.
pub fn prove_witness_vdata(witness: &WitnessJson) -> Result<VerificationDataWithFriParams<BabyBearPoseidon2Config>, String> {
    let (airs, traces, pis) = build_witness_inputs(witness)?;
    let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(1));
    StarkFriEngine::run_simple_test_impl(&engine, airs, traces, pis)
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Prove a chunked tree witness (array of WitnessJson), returning
/// verification data for each chunk. Each chunk is proved independently.
/// Phase 6-7: per-chunk proving for tree path batch recursive composition.
pub fn prove_chunked_tree_witness(
    chunks: &[WitnessJson],
) -> Result<Vec<VerificationDataWithFriParams<BabyBearPoseidon2Config>>, String> {
    chunks.par_iter().enumerate()
        .map(|(i, chunk)| {
            prove_witness_vdata(chunk)
                .map_err(|e| format!("tree chunk {i} failed: {e}"))
        })
        .collect()
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
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
    #[serde(default)]
    pub freevar_rom: Vec<Vec<u32>>,
    /// Canon-cons ROM: [cons_hash, canon_cons, is_active, num_lookups].
    /// Phase 4a-5: extracted from FlatStepChip preprocessed trace.
    #[serde(default)]
    pub canon_cons_rom: Vec<Vec<u32>>,
    /// Connective name → ZK tag integer (needed for FlatStepChip struct fields).
    pub tags: HashMap<String, u32>,
    /// Constants: { one_hash: Store.put('one', []) }.
    #[serde(default)]
    pub constants: HashMap<String, u32>,
    /// Max context size for PV normalization (Phase 4a-5).
    /// When set, FlatInitChip and FlatFinalChip pad PVs to this size,
    /// ensuring constant PV count across chunks → constant VK contribution.
    #[serde(default)]
    pub max_ctx_size: Option<usize>,
}

/// Build AIRs, traces, and PIs from a flat witness (shared by prove and vdata paths).
/// Public for tamper testing: tests can call this, modify PIs, and re-prove.
pub fn build_flat_witness_inputs(witness: &FlatWitnessJson) -> Result<(Vec<AirRef<BabyBearPoseidon2Config>>, Vec<RowMajorMatrix<BabyBear>>, Vec<Vec<BabyBear>>), String> {
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
    let max_ctx_size = witness.max_ctx_size.unwrap_or(ctx_hashes.len());
    let init_active_count = ctx_hashes.len() as u32;
    airs.push(Arc::new(FlatInitChip { ctx_hashes: ctx_hashes.clone(), max_ctx_size, min_rows }) as AirRef<_>);
    // Custom trace building: [is_active, hash, acc_active, is_first]
    traces.push({
        let width = crate::chips::flat_init::WIDTH;
        let n = init_rows.len().max(min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * width);
        let mut acc: u32 = 0;
        for (i, row) in init_rows.iter().enumerate() {
            let is_active = row[0];
            if is_active == 1 { acc += 1; }
            data.push(BabyBear::from_u32(row[0])); // is_active
            data.push(BabyBear::from_u32(row[1])); // hash
            data.push(BabyBear::from_u32(acc));     // acc_active
            data.push(if i == 0 { BabyBear::ONE } else { BabyBear::ZERO }); // is_first
        }
        let final_acc = BabyBear::from_u32(acc);
        for _ in init_rows.len()..n {
            data.push(BabyBear::ZERO); // is_active
            data.push(BabyBear::ZERO); // hash
            data.push(final_acc);       // acc_active (carry forward)
            data.push(BabyBear::ZERO); // is_first
        }
        RowMajorMatrix::new(data, width)
    });
    // Public values: context hashes padded to max_ctx_size + active_count
    let mut init_pis: Vec<BabyBear> = ctx_hashes.iter()
        .map(|&h| BabyBear::from_u32(h))
        .collect();
    init_pis.resize(max_ctx_size, BabyBear::ZERO);
    init_pis.push(BabyBear::from_u32(init_active_count));
    pis.push(init_pis);

    // 2. FlatStepChip (tag constants only — no preprocessed trace since Phase 4a-5)
    let step_rows = witness.chips.get("flat_step").ok_or("missing flat_step chip")?;
    airs.push(Arc::new(FlatStepChip {
        loli_tag, monad_tag, tensor_tag, one_hash,
    }) as AirRef<_>);
    traces.push(if step_rows.is_empty() {
        empty_trace(crate::chips::flat_step::WIDTH, min_rows)
    } else {
        build_trace(step_rows, crate::chips::flat_step::WIDTH, min_rows)
    });
    pis.push(vec![]);

    // 3. FlatFinalChip (Phase 4a: with public values for final context)
    let final_rows = witness.chips.get("flat_final").ok_or("missing flat_final chip")?;
    let final_hashes: Vec<u32> = final_rows.iter()
        .filter(|r| r.len() >= 2 && r[0] == 1)
        .map(|r| r[1])
        .collect();
    let final_max_ctx = witness.max_ctx_size.unwrap_or(final_hashes.len());
    let final_active_count = final_hashes.len() as u32;
    airs.push(Arc::new(FlatFinalChip { max_ctx_size: final_max_ctx }) as AirRef<_>);
    // Custom trace building: [is_active, hash, acc_active, is_first]
    traces.push({
        let width = crate::chips::flat_final::WIDTH;
        let n = final_rows.len().max(min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * width);
        let mut acc: u32 = 0;
        for (i, row) in final_rows.iter().enumerate() {
            let is_active = row[0];
            if is_active == 1 { acc += 1; }
            data.push(BabyBear::from_u32(row[0])); // is_active
            data.push(BabyBear::from_u32(row[1])); // hash
            data.push(BabyBear::from_u32(acc));     // acc_active
            data.push(if i == 0 { BabyBear::ONE } else { BabyBear::ZERO }); // is_first
        }
        let final_acc = BabyBear::from_u32(acc);
        for _ in final_rows.len()..n {
            data.push(BabyBear::ZERO); // is_active
            data.push(BabyBear::ZERO); // hash
            data.push(final_acc);       // acc_active (carry forward)
            data.push(BabyBear::ZERO); // is_first
        }
        RowMajorMatrix::new(data, width)
    });
    let mut final_pis: Vec<BabyBear> = final_hashes.iter()
        .map(|&h| BabyBear::from_u32(h))
        .collect();
    final_pis.resize(final_max_ctx, BabyBear::ZERO);
    final_pis.push(BabyBear::from_u32(final_active_count));
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
    airs.push(Arc::new(gamma_rom_air(gamma_entries, min_rows)) as AirRef<_>);
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

    // 7. FreevarRomAir (always present — empty when no loli freevars)
    // Unconditional inclusion ensures constant AIR count across all chunks,
    // reducing VK variation to PV sizes only (Phase 4a-4 finding 12).
    let (freevar_entries, freevar_lookups) = if !witness.freevar_rom.is_empty() {
        split_freevar_rom(&witness.freevar_rom)
    } else {
        (vec![], vec![])
    };
    airs.push(Arc::new(FreevarRomAir { entries: freevar_entries, min_rows }) as AirRef<_>);
    traces.push(if freevar_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&freevar_lookups, min_rows)
    });
    pis.push(vec![]);

    // 8. CanonConsRomAir (always present — empty when no loli matches)
    // Phase 4a-5: extracted from FlatStepChip preprocessed trace.
    let (cc_entries, cc_lookups) = if !witness.canon_cons_rom.is_empty() {
        split_canon_cons_rom(&witness.canon_cons_rom)
    } else {
        (vec![], vec![])
    };
    airs.push(Arc::new(CanonConsRomAir { entries: cc_entries, min_rows }) as AirRef<_>);
    traces.push(if cc_lookups.is_empty() {
        empty_trace(1, min_rows)
    } else {
        build_trace_1col(&cc_lookups, min_rows)
    });
    pis.push(vec![]);

    Ok((airs, traces, pis))
}

/// Prove a flat witness, returning Ok(()) on success.
///
/// FlatStepChip has degree-4 constraints requiring log_blowup >= 2.
/// Respects `OPENVM_FAST_TEST=1` for insecure-but-fast FRI parameters.
pub fn prove_flat_witness(witness: &FlatWitnessJson) -> Result<(), String> {
    prove_flat_witness_vdata(witness).map(|_| ())
}

/// Prove a flat witness, returning the full verification data.
/// Phase 4a: needed for recursive verification and IVC.
pub fn prove_flat_witness_vdata(witness: &FlatWitnessJson) -> Result<VerificationDataWithFriParams<BabyBearPoseidon2Config>, String> {
    let (airs, traces, pis) = build_flat_witness_inputs(witness)?;
    // FlatStepChip has degree-4 constraints (spine boundary checks), requiring
    // log_blowup >= 2 so the LDE has enough evaluations for the quotient domain.
    let engine = BabyBearPoseidon2Engine::new(
        FriParameters::new_for_testing(2),
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
    chunks.par_iter().enumerate()
        .map(|(i, chunk)| {
            prove_flat_witness_vdata(chunk)
                .map_err(|e| format!("chunk {i} failed: {e}"))
        })
        .collect()
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
