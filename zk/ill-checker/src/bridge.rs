//! Bridge: JSON witness → STARK trace matrices → prover.
//!
//! Deserializes the JSON output of `lib/zk/witness.js` into typed
//! trace matrices for each AIR chip, then runs the STARK prover.
//! This is the JS → Rust integration layer for Phase 1f.
//!
//! The witness JSON is self-describing: it carries a `tags` field
//! with the connective→integer mapping derived from the calculus
//! definition. The bridge reads this and uses it when constructing
//! RuleChips, so the Rust verifier adapts automatically when
//! connective definitions change.

use std::collections::HashMap;
use std::sync::Arc;

use openvm_stark_backend::{
    p3_matrix::dense::RowMajorMatrix,
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine,
    engine::StarkFriEngine,
};
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;
use serde::Deserialize;

use crate::chips::{
    discard::DiscardChip,
    dup::DupChip,
    formula_rom::FormulaRomAir,
    gamma_rom::GammaRomAir,
    init::InitChip,
    zero_l::ZeroLChip,
};
use crate::rule::{ill, RuleChip, RuleSpec};

/// JSON witness format produced by `lib/zk/witness.js`.
#[derive(Deserialize, Debug)]
pub struct WitnessJson {
    /// Connective name → ZK tag integer, derived from the calculus definition.
    pub tags: HashMap<String, u32>,
    pub chips: HashMap<String, Vec<Vec<u32>>>,
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
}

/// Get the base RuleSpec (structural layout) for a rule name.
/// Tags are overridden from the witness — these are just for structure.
fn base_rule_spec(name: &str) -> Option<RuleSpec> {
    match name {
        "id" => Some(ill::ID),
        "tensor_r" => Some(ill::TENSOR_R),
        "tensor_l" => Some(ill::TENSOR_L),
        "loli_r" => Some(ill::LOLI_R),
        "loli_l" => Some(ill::LOLI_L),
        "with_r" => Some(ill::WITH_R),
        "with_l1" => Some(ill::WITH_L1),
        "with_l2" => Some(ill::WITH_L2),
        "oplus_r1" => Some(ill::OPLUS_R1),
        "oplus_r2" => Some(ill::OPLUS_R2),
        "oplus_l" => Some(ill::OPLUS_L),
        "one_r" => Some(ill::ONE_R),
        "one_l" => Some(ill::ONE_L),
        "bang_r" => Some(ill::BANG_R),
        "bang_l" => Some(ill::BANG_L),
        "absorption" => Some(ill::ABSORPTION),
        "copy" => Some(ill::COPY),
        "monad_r" => Some(ill::MONAD_R),
        "monad_l" => Some(ill::MONAD_L),
        "exists_r" => Some(ill::EXISTS_R),
        "exists_l" => Some(ill::EXISTS_L),
        "forall_r" => Some(ill::FORALL_R),
        "forall_l" => Some(ill::FORALL_L),
        _ => None,
    }
}

/// Map from rule name to the connective it operates on.
fn connective_for_rule(name: &str) -> Option<&str> {
    match name {
        "tensor_r" | "tensor_l" => Some("tensor"),
        "loli_r" | "loli_l" => Some("loli"),
        "with_r" | "with_l1" | "with_l2" => Some("with"),
        "oplus_r1" | "oplus_r2" | "oplus_l" => Some("oplus"),
        "bang_r" | "bang_l" | "absorption" => Some("bang"),
        "monad_r" | "monad_l" => Some("monad"),
        "one_r" | "one_l" => Some("one"),
        "exists_r" | "exists_l" => Some("exists"),
        "forall_r" | "forall_l" => Some("forall"),
        // id, copy — no connective tag
        _ => None,
    }
}

/// Build a RuleSpec for a rule name, overriding the tag from the witness's tag mapping.
fn rule_spec_with_tags(name: &str, tags: &HashMap<String, u32>) -> Option<RuleSpec> {
    let mut spec = base_rule_spec(name)?;
    if let Some(conn) = connective_for_rule(name) {
        spec.tag = tags.get(conn).copied();
    }
    Some(spec)
}

/// Known special chip names that are NOT generic RuleChips.
const SPECIAL_CHIPS: &[&str] = &["init", "dup", "zero_l", "discard"];

/// Build a padded RowMajorMatrix from dynamic-width rows.
fn build_trace(rows: &[Vec<u32>], width: usize, min_rows: usize) -> RowMajorMatrix<BabyBear> {
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * width);
    for row in rows {
        assert_eq!(row.len(), width, "row width mismatch: expected {width}, got {}", row.len());
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

/// Prove a witness JSON, returning Ok(()) on success or Err on verification failure.
pub fn prove_witness(witness: &WitnessJson) -> Result<(), String> {
    let min_rows = 4; // stark-backend minimum
    let tags = &witness.tags;

    // Resolve the zero tag from the witness for ZeroLChip
    let zero_tag = tags.get("zero").copied()
        .ok_or("missing 'zero' tag in witness")?;

    let mut airs: Vec<AirRef<_>> = Vec::new();
    let mut traces: Vec<RowMajorMatrix<BabyBear>> = Vec::new();
    let mut pis: Vec<Vec<BabyBear>> = Vec::new();

    // 1. InitChip (always present)
    let init_rows = witness.chips.get("init").ok_or("missing init chip")?;
    airs.push(Arc::new(InitChip) as AirRef<_>);
    traces.push(build_trace(init_rows, 6, min_rows));
    pis.push(vec![]);

    // 2. DupChip (always present, may be empty)
    let dup_rows = witness.chips.get("dup");
    airs.push(Arc::new(DupChip) as AirRef<_>);
    traces.push(match dup_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 2, min_rows),
        _ => empty_trace(2, min_rows),
    });
    pis.push(vec![]);

    // 3. ZeroLChip (parameterized with the zero tag from the witness)
    let zero_rows = witness.chips.get("zero_l");
    airs.push(Arc::new(ZeroLChip::new(zero_tag)) as AirRef<_>);
    traces.push(match zero_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 6, min_rows),
        _ => empty_trace(6, min_rows),
    });
    pis.push(vec![]);

    // 4. DiscardChip (always present, may be empty)
    let discard_rows = witness.chips.get("discard");
    airs.push(Arc::new(DiscardChip) as AirRef<_>);
    traces.push(match discard_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 3, min_rows),
        _ => empty_trace(3, min_rows),
    });
    pis.push(vec![]);

    // 5. Generic RuleChips — tags overridden from the witness
    let mut rule_names: Vec<String> = witness.chips.keys()
        .filter(|name| !SPECIAL_CHIPS.contains(&name.as_str()))
        .cloned()
        .collect();
    rule_names.sort(); // deterministic order

    for name in &rule_names {
        let spec = rule_spec_with_tags(name, tags)
            .ok_or_else(|| format!("unknown rule chip: {name}"))?;
        let chip = RuleChip::new(spec);
        let width = chip.layout.width;
        let rows = witness.chips.get(name).unwrap();
        airs.push(Arc::new(chip) as AirRef<_>);
        traces.push(if rows.is_empty() {
            empty_trace(width, min_rows)
        } else {
            build_trace(rows, width, min_rows)
        });
        pis.push(vec![]);
    }

    // 6. FormulaRomAir
    airs.push(Arc::new(FormulaRomAir) as AirRef<_>);
    traces.push(if witness.formula_rom.is_empty() {
        empty_trace(6, min_rows)
    } else {
        build_trace(&witness.formula_rom, 6, min_rows)
    });
    pis.push(vec![]);

    // 7. GammaRomAir
    airs.push(Arc::new(GammaRomAir) as AirRef<_>);
    traces.push(if witness.gamma_rom.is_empty() {
        empty_trace(3, min_rows)
    } else {
        build_trace(&witness.gamma_rom, 3, min_rows)
    });
    pis.push(vec![]);

    // Run the STARK prover + verifier
    BabyBearPoseidon2Engine::run_simple_test_fast(airs, traces, pis)
        .map(|_| ())
        .map_err(|e| format!("STARK verification failed: {e:?}"))
}

/// Parse a JSON string and prove it.
pub fn prove_json(json: &str) -> Result<(), String> {
    let witness: WitnessJson = serde_json::from_str(json)
        .map_err(|e| format!("JSON parse error: {e}"))?;
    prove_witness(&witness)
}
