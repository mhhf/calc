//! Bridge: JSON witness → STARK trace matrices → prover.
//!
//! Deserializes the JSON output of `lib/zk/witness.js` into typed
//! trace matrices for each AIR chip, then runs the STARK prover.
//!
//! The witness JSON is fully self-describing: it carries `tags` (connective
//! tag mapping) and `rule_specs` (per-rule chip structure), both derived
//! from the calculus definition. The bridge reads these and constructs
//! chips entirely at runtime — zero calculus-specific code. The same Rust
//! binary verifies proofs from any calculus defined in CALC.

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
    subst::SubstChip,
    zero_l::ZeroLChip,
};
use crate::rule::{RuleChip, RuleSpec};

/// JSON witness format produced by `lib/zk/witness.js`.
///
/// Fully self-describing: `tags` and `rule_specs` are derived from the
/// calculus definition, so the Rust verifier adapts automatically.
#[derive(Deserialize, Debug)]
pub struct WitnessJson {
    /// Connective name → ZK tag integer, derived from the calculus definition.
    pub tags: HashMap<String, u32>,
    /// Rule name → ZK RuleSpec, derived from the calculus rule descriptors.
    pub rule_specs: HashMap<String, RuleSpec>,
    pub chips: HashMap<String, Vec<Vec<u32>>>,
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
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

    // 5. SubstChip (substitution bridge for loli bodies with freevars)
    let subst_rows = witness.chips.get("subst");
    airs.push(Arc::new(SubstChip) as AirRef<_>);
    traces.push(match subst_rows {
        Some(rows) if !rows.is_empty() => build_trace(rows, 3, min_rows),
        _ => empty_trace(3, min_rows),
    });
    pis.push(vec![]);

    // 6. Generic RuleChips — specs read from witness (fully generic)
    let mut rule_names: Vec<String> = witness.chips.keys()
        .filter(|name| !SPECIAL_CHIPS.contains(&name.as_str()))
        .cloned()
        .collect();
    rule_names.sort(); // deterministic order

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
