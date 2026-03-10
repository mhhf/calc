//! Phase 2: Quantifier tests (exists, forall).
//!
//! Tests exists_r, exists_l, forall_r, forall_l.
//! Quantifiers use arity=1 with child0 = instantiated body hash.
//! Substitution correctness lives in the formula ROM (Phase 3 concern).

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

const H_A: u32 = 42;       // hash of some proposition A (or instantiated body)
const H_EXISTS_A: u32 = 700; // hash(∃x.A)
const H_FORALL_A: u32 = 800; // hash(∀x.A)

// ---------------------------------------------------------------------------
// exists_r: A ⊢ ∃x.A  (instantiation with witness)
// ---------------------------------------------------------------------------

#[test]
fn p2_exists_r_basic() {
    // A ⊢ ∃x.A
    // Proof: exists_r(id(A))
    //   exists_r: oblig receive (0, ∃A, 0), formula lookup, oblig send (1, A, 0)
    //   id:       oblig receive (1, A, 0), ctx receive A

    let exists_r_chip = RuleChip::new(ill::EXISTS_R);
    let id_chip = RuleChip::new(ill::ID);

    // exists_r layout: [active=0, hash=1, c0=2, nonce_in=3, lax=4, nonce_out0=5] width=6
    assert_eq!(exists_r_chip.layout.width, 6);

    let init_trace = padded_trace(&[[H_A, 1, H_EXISTS_A, 1, 0, 0]], 4);

    // exists_r: [active, hash, c0, nonce_in, lax, nonce_out0]
    let er_trace = dyn_trace(&[&[1, H_EXISTS_A, H_A, 0, 0, 1]], 6, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    // ROM: ∃A with child0=A
    let rom_trace = padded_trace(&[[H_EXISTS_A, tags::EXISTS, H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(exists_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, er_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("exists_r: A ⊢ ∃x.A");
}

// ---------------------------------------------------------------------------
// exists_l: ∃x.A ⊢ A  (open with eigenvariable)
// ---------------------------------------------------------------------------

#[test]
fn p2_exists_l_basic() {
    // ∃x.A ⊢ A
    // Proof: exists_l(∃A, id(A))
    //   exists_l: ctx receive ∃A, ctx send A (child0), formula lookup
    //   id:       oblig receive (0, A, 0), ctx receive A

    let exists_l_chip = RuleChip::new(ill::EXISTS_L);
    let id_chip = RuleChip::new(ill::ID);

    // exists_l: context-only left, [active=0, hash=1, c0=2] width=3
    assert_eq!(exists_l_chip.layout.width, 3);

    let init_trace = padded_trace(&[[H_EXISTS_A, 1, H_A, 1, 0, 0]], 4);

    // exists_l: [active, hash, c0]
    let el_trace = dyn_trace(&[&[1, H_EXISTS_A, H_A]], 3, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // ROM: ∃A
    let rom_trace = padded_trace(&[[H_EXISTS_A, tags::EXISTS, H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(exists_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, el_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("exists_l: ∃x.A ⊢ A");
}

// ---------------------------------------------------------------------------
// forall_r: A ⊢ ∀x.A  (abstraction)
// ---------------------------------------------------------------------------

#[test]
fn p2_forall_r_basic() {
    // A ⊢ ∀x.A  (vacuous; A doesn't depend on x)
    // Proof: forall_r(id(A))

    let forall_r_chip = RuleChip::new(ill::FORALL_R);
    let id_chip = RuleChip::new(ill::ID);

    // forall_r layout: [active=0, hash=1, c0=2, nonce_in=3, lax=4, nonce_out0=5] width=6
    assert_eq!(forall_r_chip.layout.width, 6);

    let init_trace = padded_trace(&[[H_A, 1, H_FORALL_A, 1, 0, 0]], 4);

    // forall_r: [active, hash, c0, nonce_in, lax, nonce_out0]
    let fr_trace = dyn_trace(&[&[1, H_FORALL_A, H_A, 0, 0, 1]], 6, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    // ROM: ∀A with child0=A
    let rom_trace = padded_trace(&[[H_FORALL_A, tags::FORALL, H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(forall_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, fr_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("forall_r: A ⊢ ∀x.A");
}

// ---------------------------------------------------------------------------
// forall_l: ∀x.A ⊢ A  (instantiation)
// ---------------------------------------------------------------------------

#[test]
fn p2_forall_l_basic() {
    // ∀x.A ⊢ A
    // Proof: forall_l(∀A, id(A))

    let forall_l_chip = RuleChip::new(ill::FORALL_L);
    let id_chip = RuleChip::new(ill::ID);

    // forall_l: context-only left, [active=0, hash=1, c0=2] width=3
    assert_eq!(forall_l_chip.layout.width, 3);

    let init_trace = padded_trace(&[[H_FORALL_A, 1, H_A, 1, 0, 0]], 4);

    // forall_l: [active, hash, c0]
    let fl_trace = dyn_trace(&[&[1, H_FORALL_A, H_A]], 3, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 0, 0]], 4, 4);

    // ROM: ∀A
    let rom_trace = padded_trace(&[[H_FORALL_A, tags::FORALL, H_A, 0, 1, 1]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(forall_l_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, fl_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![]],
    )
    .expect("forall_l: ∀x.A ⊢ A");
}

// ---------------------------------------------------------------------------
// Roundtrip: ∃x.A ⊢ ∃x.A (exists_l + exists_r)
// ---------------------------------------------------------------------------

#[test]
fn p2_exists_roundtrip() {
    // ∃x.A ⊢ ∃x.A
    // Proof: exists_l(∃A, exists_r(id(A)))

    let exists_l_chip = RuleChip::new(ill::EXISTS_L);
    let exists_r_chip = RuleChip::new(ill::EXISTS_R);
    let id_chip = RuleChip::new(ill::ID);

    let init_trace = padded_trace(&[[H_EXISTS_A, 1, H_EXISTS_A, 1, 0, 0]], 4);

    // exists_l: [active, hash, c0]
    let el_trace = dyn_trace(&[&[1, H_EXISTS_A, H_A]], 3, 4);

    // exists_r: [active, hash, c0, nonce_in, lax, nonce_out0]
    let er_trace = dyn_trace(&[&[1, H_EXISTS_A, H_A, 0, 0, 1]], 6, 4);

    // id: [active, hash, nonce_in, lax]
    let id_trace = dyn_trace(&[&[1, H_A, 1, 0]], 4, 4);

    // ROM: ∃A — looked up twice (exists_l + exists_r)
    let rom_trace = padded_trace(&[[H_EXISTS_A, tags::EXISTS, H_A, 0, 1, 2]], 4);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(InitChip) as AirRef<_>,
            Arc::new(exists_l_chip) as AirRef<_>,
            Arc::new(exists_r_chip) as AirRef<_>,
            Arc::new(id_chip) as AirRef<_>,
            Arc::new(FormulaRomAir) as AirRef<_>,
        ],
        vec![init_trace, el_trace, er_trace, id_trace, rom_trace],
        vec![vec![], vec![], vec![], vec![], vec![]],
    )
    .expect("exists roundtrip: ∃x.A ⊢ ∃x.A");
}
