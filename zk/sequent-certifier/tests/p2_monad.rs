//! Phase 2: Lax monad tests.
//!
//! Tests monad_r (guided mode, lax=1 override) and monad_l (strip {}).
//! Validates: lax flag propagation through obligation bus,
//! PremiseSpec.lax override in monad_r.

mod common;

use std::sync::Arc;

use sequent_certifier::rule::RuleChip;
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::{make_init, make_formula_rom};

fn dyn_trace(rows: &[&[u32]], width: usize, min_rows: usize) -> openvm_stark_backend::p3_matrix::dense::RowMajorMatrix<p3_baby_bear::BabyBear> {
    use p3_field::PrimeCharacteristicRing;
    let n = rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * width);
    for row in rows {
        assert_eq!(row.len(), width);
        for &v in *row { data.push(p3_baby_bear::BabyBear::from_u32(v)); }
    }
    for _ in rows.len()..n {
        for _ in 0..width { data.push(p3_baby_bear::BabyBear::ZERO); }
    }
    openvm_stark_backend::p3_matrix::dense::RowMajorMatrix::new(data, width)
}

const H_A: u32 = 42;
const H_UNIT: u32 = 5;      // unit grade node (binlit 0 — D6 graded monad)
const H_MONAD_A: u32 = 600; // hash({A}) = monad(H_UNIT, H_A)

// ---------------------------------------------------------------------------
// monad_r + monad_l + id: {A} ⊢ {A}
// ---------------------------------------------------------------------------

#[test]
fn p2_monad_roundtrip() {
    let (tags, specs) = common::load_test_specs();
    let monad_l_chip = RuleChip::new(specs["monad_l"].clone());
    let monad_r_chip = RuleChip::new(specs["monad_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    // arity 2 since the D6 merge-back: [active, hash, grade, body, ...]
    assert_eq!(monad_l_chip.layout.width, 4);
    assert_eq!(monad_r_chip.layout.width, 7);

    let (init_chip, init_trace, init_pis) = make_init(&[[H_MONAD_A, 1, H_MONAD_A, 1, 0, 0]], 4);
    let ml_trace = dyn_trace(&[&[1, H_MONAD_A, H_UNIT, H_A]], 4, 4);
    let mr_trace = dyn_trace(&[&[1, H_MONAD_A, H_UNIT, H_A, 0, 0, 1]], 7, 4);
    let id_trace = dyn_trace(&[&[1, H_A, 1, 1]], 4, 4);
    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_MONAD_A, tags["monad"], H_UNIT, H_A, 1, 2]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(monad_l_chip) as AirRef<_>,
            Arc::new(monad_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, ml_trace, mr_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![], vec![]],
    )
    .expect("monad: {A} ⊢ {A}");
}

// ---------------------------------------------------------------------------
// Failure: monad_r output consumed with wrong lax
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_monad_r_lax_mismatch_fails() {
    let (tags, specs) = common::load_test_specs();
    let monad_l_chip = RuleChip::new(specs["monad_l"].clone());
    let monad_r_chip = RuleChip::new(specs["monad_r"].clone());
    let id_chip = RuleChip::new(specs["id"].clone());

    let (init_chip, init_trace, init_pis) = make_init(&[[H_MONAD_A, 1, H_MONAD_A, 1, 0, 0]], 4);
    let ml_trace = dyn_trace(&[&[1, H_MONAD_A, H_UNIT, H_A]], 4, 4);
    let mr_trace = dyn_trace(&[&[1, H_MONAD_A, H_UNIT, H_A, 0, 0, 1]], 7, 4);

    // WRONG: lax=0 instead of lax=1
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let (rom_chip, rom_trace) = make_formula_rom(
        &[[H_MONAD_A, tags["monad"], H_UNIT, H_A, 1, 2]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(init_chip) as AirRef<_>,
            Arc::new(monad_l_chip) as AirRef<_>,
            Arc::new(monad_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(rom_chip) as AirRef<_>,
        ],
        vec![init_trace, ml_trace, mr_trace, id_trace, rom_trace],
        vec![init_pis, vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: lax mismatch in monad_r");
}
