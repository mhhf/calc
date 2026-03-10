//! Phase 2: Lax monad tests.
//!
//! Tests monad_r (guided mode, lax=1 override) and monad_l (strip {}).
//! Validates: lax flag propagation through obligation bus,
//! PremiseSpec.lax override in monad_r.

mod common;

use std::sync::Arc;

use ill_checker::{
    chips::{formula_rom::FormulaRomAir, init::InitChip},
    rule::{ill, RuleChip},
    tags,
};
use openvm_stark_backend::AirRef;
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};

use common::padded_trace;

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
const H_MONAD_A: u32 = 600; // hash({A})

// ---------------------------------------------------------------------------
// monad_r + monad_l + id: {A} ⊢ {A}
// ---------------------------------------------------------------------------

#[test]
fn p2_monad_roundtrip() {
    // {A} ⊢ {A}
    // Proof: monad_l({A}, monad_r(id(A)))
    //
    // Bus flow:
    //   Init:    ctx={A}, oblig=(0, {A}, 0)
    //   monad_l: ctx receive {A}, ctx send A, formula lookup
    //   monad_r: oblig receive (0, {A}, 0), oblig send (1, A, lax=1),
    //            formula lookup ({A}, MONAD, A, 0)
    //   id:      oblig receive (1, A, 1), ctx receive A

    let monad_l_chip = RuleChip::new(ill::monad_l());
    let monad_r_chip = RuleChip::new(ill::monad_r());
    let id_chip = RuleChip::new(ill::id());

    // monad_l layout: [active=0, hash=1, child0=2] width=3
    assert_eq!(monad_l_chip.layout.width, 3);
    // monad_r layout: [active=0, hash=1, child0=2, nonce_in=3, lax=4, nonce_out0=5] width=6
    assert_eq!(monad_r_chip.layout.width, 6);

    // Init: ctx={A}, oblig=(0, {A}, 0)
    let init_trace = padded_trace(&[[H_MONAD_A, 1, H_MONAD_A, 1, 0, 0]], 4);

    // monad_l: [active, hash, child0]
    let ml_trace = dyn_trace(&[&[1, H_MONAD_A, H_A]], 3, 4);

    // monad_r: [active, hash, child0, nonce_in, lax, nonce_out0]
    // Input lax=0, but output lax is overridden to 1
    let mr_trace = dyn_trace(&[&[1, H_MONAD_A, H_A, 0, 0, 1]], 6, 4);

    // id: [active, hash, nonce_in, lax]
    // Must receive with lax=1 (monad_r forced lax=1)
    let id_trace = dyn_trace(&[&[1, H_A, 1, 1]], 4, 4);

    // ROM: {A} — looked up twice (monad_l + monad_r both do formula lookup)
    let rom_trace = padded_trace(
        &[[H_MONAD_A, tags::MONAD, H_A, 0, 1, 2]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(monad_l_chip) as AirRef<_>,
            Arc::new(monad_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, ml_trace, mr_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("monad: {A} ⊢ {A}");
}

// ---------------------------------------------------------------------------
// Failure: monad_r output consumed with wrong lax
// ---------------------------------------------------------------------------

#[test]
#[should_panic]
fn p2_monad_r_lax_mismatch_fails() {
    // monad_r produces lax=1, but id tries to consume with lax=0
    let monad_l_chip = RuleChip::new(ill::monad_l());
    let monad_r_chip = RuleChip::new(ill::monad_r());
    let id_chip = RuleChip::new(ill::id());

    let init_trace = padded_trace(&[[H_MONAD_A, 1, H_MONAD_A, 1, 0, 0]], 4);
    let ml_trace = dyn_trace(&[&[1, H_MONAD_A, H_A]], 3, 4);
    let mr_trace = dyn_trace(&[&[1, H_MONAD_A, H_A, 0, 0, 1]], 6, 4);

    // WRONG: lax=0 instead of lax=1
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    let rom_trace = padded_trace(
        &[[H_MONAD_A, tags::MONAD, H_A, 0, 1, 2]],
        4,
    );

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(monad_l_chip) as AirRef<_>,
            Arc::new(monad_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, ml_trace, mr_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("should fail: lax mismatch in monad_r");
}
