//! Spike S4: Preprocessed columns (fixed ROM data)
//!
//! Validates: FormulaROM as preprocessed trace, committed once at keygen.
//! Tests: LookupBus for formula decomposition lookups, preprocessed columns via keygen.

use std::sync::Arc;

use openvm_stark_backend::{
    interaction::{InteractionBuilder, LookupBus},
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};
use p3_baby_bear::BabyBear;

const FORMULA_BUS: LookupBus = LookupBus::new(0);

// ---- SimpleRomAir: ROM as main trace (for run_simple_test_fast) ----

struct SimpleRomAir;

impl<F> BaseAir<F> for SimpleRomAir {
    fn width(&self) -> usize { 6 } // hash, tag, child0, child1, is_active, num_lookups
}
impl<F> BaseAirWithPublicValues<F> for SimpleRomAir {}
impl<F> PartitionedBaseAir<F> for SimpleRomAir {}

impl<AB: InteractionBuilder> Air<AB> for SimpleRomAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let hash: AB::Expr = local[0].clone().into();
        let tag: AB::Expr = local[1].clone().into();
        let child0: AB::Expr = local[2].clone().into();
        let child1: AB::Expr = local[3].clone().into();
        let is_active: AB::Expr = local[4].clone().into();
        let num_lookups: AB::Expr = local[5].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        FORMULA_BUS.add_key_with_lookups(
            builder,
            [hash, tag, child0, child1],
            is_active * num_lookups,
        );
    }
}

// ---- CheckerAir: looks up formula decompositions ----

struct CheckerAir;

impl<F> BaseAir<F> for CheckerAir {
    fn width(&self) -> usize { 5 }
}
impl<F> BaseAirWithPublicValues<F> for CheckerAir {}
impl<F> PartitionedBaseAir<F> for CheckerAir {}

impl<AB: InteractionBuilder> Air<AB> for CheckerAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let hash: AB::Expr = local[0].clone().into();
        let tag: AB::Expr = local[1].clone().into();
        let child0: AB::Expr = local[2].clone().into();
        let child1: AB::Expr = local[3].clone().into();
        let needs_decompose: AB::Expr = local[4].clone().into();

        builder.assert_zero(
            needs_decompose.clone() * (needs_decompose.clone() - AB::Expr::ONE),
        );

        FORMULA_BUS.lookup_key(builder, [hash, tag, child0, child1], needs_decompose);
    }
}

// --- Tests with SimpleRomAir ---

#[test]
fn s4_formula_rom_lookup() {
    let rom_data: Vec<BabyBear> = vec![
        100, 1, 42, 43, 1, 1, // hash=100 → (tensor, 42, 43), looked up 1x
        200, 2, 42, 43, 1, 1, // hash=200 → (loli, 42, 43), looked up 1x
        0, 0, 0, 0, 0, 0,     // pad
        0, 0, 0, 0, 0, 0,     // pad
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    let checker_data: Vec<BabyBear> = vec![
        100, 1, 42, 43, 1,
        200, 2, 42, 43, 1,
        0, 0, 0, 0, 0,
        0, 0, 0, 0, 0,
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(SimpleRomAir) as AirRef<_>, Arc::new(CheckerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(rom_data, 6), RowMajorMatrix::new(checker_data, 5)],
        vec![vec![], vec![]],
    )
    .expect("S4: formula ROM lookup");
}

#[test]
fn s4_multiple_lookups() {
    let rom_data: Vec<BabyBear> = vec![100, 1, 42, 43, 1, 3]
        .into_iter().map(BabyBear::from_u32).collect();

    let checker_data: Vec<BabyBear> = vec![
        100, 1, 42, 43, 1,
        100, 1, 42, 43, 1,
        100, 1, 42, 43, 1,
        0, 0, 0, 0, 0,
    ]
    .into_iter().map(BabyBear::from_u32).collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(SimpleRomAir) as AirRef<_>, Arc::new(CheckerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(rom_data, 6), RowMajorMatrix::new(checker_data, 5)],
        vec![vec![], vec![]],
    )
    .expect("S4: multiple lookups same entry");
}

#[test]
#[should_panic]
fn s4_wrong_decomposition_fails() {
    let rom_data: Vec<BabyBear> = vec![100, 1, 42, 43, 1, 1]
        .into_iter().map(BabyBear::from_u32).collect();

    let checker_data: Vec<BabyBear> = vec![100, 1, 99, 43, 1] // WRONG child0
        .into_iter().map(BabyBear::from_u32).collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(SimpleRomAir) as AirRef<_>, Arc::new(CheckerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(rom_data, 6), RowMajorMatrix::new(checker_data, 5)],
        vec![vec![], vec![]],
    )
    .expect("should fail");
}

// --- Test with PREPROCESSED columns (keygen pipeline) ---

#[test]
fn s4_preprocessed_columns_via_keygen() {
    use openvm_stark_backend::{
        engine::StarkEngine,
        prover::types::{AirProvingContext, ProvingContext},
    };
    use openvm_stark_sdk::config::baby_bear_poseidon2::default_engine;

    // ROM AIR with preprocessed columns — following FibonacciSelectorAir pattern
    struct PrepRomAir {
        entries: Vec<[u32; 5]>, // [hash, tag, child0, child1, is_active]
    }

    impl<F: Field> BaseAir<F> for PrepRomAir {
        fn width(&self) -> usize { 1 } // witness: num_lookups only

        fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
            let n = self.entries.len().next_power_of_two();
            let mut data = Vec::with_capacity(n * 5);
            for row in &self.entries {
                for &v in row {
                    data.push(F::from_u32(v));
                }
            }
            for _ in self.entries.len()..n {
                data.extend([F::ZERO; 5]);
            }
            Some(RowMajorMatrix::new(data, 5))
        }
    }
    impl<F: Field> BaseAirWithPublicValues<F> for PrepRomAir {}
    impl<F: Field> PartitionedBaseAir<F> for PrepRomAir {}

    impl<AB: InteractionBuilder + PairBuilder> Air<AB> for PrepRomAir
    where
        AB::F: Field,
    {
        fn eval(&self, builder: &mut AB) {
            let prep = builder.preprocessed();
            let prep_local = prep.row_slice(0).unwrap();
            let hash: AB::Expr = prep_local[0].clone().into();
            let tag: AB::Expr = prep_local[1].clone().into();
            let child0: AB::Expr = prep_local[2].clone().into();
            let child1: AB::Expr = prep_local[3].clone().into();
            let is_active: AB::Expr = prep_local[4].clone().into();

            let main = builder.main();
            let local = main.row_slice(0).unwrap();
            let num_lookups: AB::Expr = local[0].clone().into();

            FORMULA_BUS.add_key_with_lookups(
                builder,
                [hash, tag, child0, child1],
                is_active * num_lookups,
            );
        }
    }

    let rom = PrepRomAir {
        entries: vec![
            [100, 1, 42, 43, 1],
            [200, 2, 42, 43, 1],
        ],
    };

    let engine = default_engine();
    let mut kb = engine.keygen_builder();
    let rom_id = kb.add_air(Arc::new(rom) as AirRef<_>);
    let checker_id = kb.add_air(Arc::new(CheckerAir) as AirRef<_>);
    let pk = kb.generate_pk();

    // ROM witness: each entry looked up once (2 active + 0 padding = degree 2)
    let rom_witness = RowMajorMatrix::new(
        vec![BabyBear::from_u32(1), BabyBear::from_u32(1)],
        1,
    );

    let checker_trace = RowMajorMatrix::new(
        vec![100, 1, 42, 43, 1, 200, 2, 42, 43, 1]
            .into_iter().map(BabyBear::from_u32).collect(),
        5,
    );

    let ctx = ProvingContext {
        per_air: vec![
            (rom_id, AirProvingContext::simple_no_pis(Arc::new(rom_witness))),
            (checker_id, AirProvingContext::simple_no_pis(Arc::new(checker_trace))),
        ],
    };

    engine.prove_then_verify(&pk, ctx)
        .expect("S4: preprocessed ROM via keygen pipeline");
}
