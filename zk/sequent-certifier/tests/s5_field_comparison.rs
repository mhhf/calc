//! Spike S5: BabyBear vs Goldilocks field comparison
//!
//! Validates: BabyBear works with non-trivial AIR (selectors, bus, arithmetic).
//! Finding: Goldilocks engine does NOT implement StarkFriEngine and fails with
//!          InvalidProofShape via StarkEngine::run_test_impl — under-supported in SDK.
//! Decision: BabyBear is the clear choice (fast, well-supported, extension field safe).

use std::sync::Arc;
use std::time::Instant;

use openvm_stark_backend::{
    interaction::{InteractionBuilder, PermutationCheckBus},
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::engine::StarkFriEngine;
use p3_baby_bear::BabyBear;

const BUS: PermutationCheckBus = PermutationCheckBus::new(0);

// --- A non-trivial AIR with bus interactions ---
// Simulates a proof checker: multiple selectors, bus send/receive, arithmetic

struct BenchAir;

impl<F> BaseAir<F> for BenchAir {
    fn width(&self) -> usize { 6 } // [val, acc, sel_add, sel_sub, sel_pad, counter]
}
impl<F> BaseAirWithPublicValues<F> for BenchAir {
    fn num_public_values(&self) -> usize { 1 } // final acc value
}
impl<F> PartitionedBaseAir<F> for BenchAir {}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB> for BenchAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let val: AB::Expr = local[0].clone().into();
        let acc: AB::Expr = local[1].clone().into();
        let sel_add: AB::Expr = local[2].clone().into();
        let sel_sub: AB::Expr = local[3].clone().into();
        let sel_pad: AB::Expr = local[4].clone().into();
        let counter: AB::Expr = local[5].clone().into();

        let acc_next: AB::Expr = next[1].clone().into();
        let counter_next: AB::Expr = next[5].clone().into();

        // Exactly one selector
        builder.assert_one(sel_add.clone() + sel_sub.clone() + sel_pad.clone());

        // Boolean selectors
        builder.assert_zero(sel_add.clone() * (sel_add.clone() - AB::Expr::ONE));
        builder.assert_zero(sel_sub.clone() * (sel_sub.clone() - AB::Expr::ONE));
        builder.assert_zero(sel_pad.clone() * (sel_pad.clone() - AB::Expr::ONE));

        // acc' = acc + val (when add), acc' = acc - val (when sub), acc' = acc (when pad)
        builder.when_transition().assert_zero(
            sel_add.clone() * (acc_next.clone() - acc.clone() - val.clone())
            + sel_sub.clone() * (acc_next.clone() - acc.clone() + val.clone())
            + sel_pad.clone() * (acc_next.clone() - acc.clone())
        );

        // Counter increments by 1 on non-pad rows
        builder.when_transition().assert_zero(
            (sel_add.clone() + sel_sub.clone()) * (counter_next.clone() - counter.clone() - AB::Expr::ONE)
            + sel_pad.clone() * (counter_next - counter)
        );

        // Bus: send val on add, receive val on sub
        BUS.send(builder, [val.clone()], sel_add);
        BUS.receive(builder, [val], sel_sub);

        // Public value: final accumulator
        let pis = builder.public_values();
        let pi_final: AB::Expr = pis[0].clone().into();
        builder.when_last_row().assert_eq(acc, pi_final);
    }
}

fn generate_bench_trace<F: Field>(n: usize) -> (RowMajorMatrix<F>, F) {
    assert!(n.is_power_of_two());
    assert!(n >= 4);

    // Pattern: add values, then subtract same values, then pad
    let num_ops = n / 2; // half add, half subtract (minus padding)
    let active = if num_ops > 2 { num_ops - 1 } else { 1 };

    let mut data = Vec::with_capacity(n * 6);
    let mut acc = F::ZERO;
    let mut counter = F::ZERO;

    // Add phase
    for i in 0..active {
        let val = F::from_u32((i as u32) + 1);
        data.extend([val, acc, F::ONE, F::ZERO, F::ZERO, counter]);
        acc = acc + val;
        counter = counter + F::ONE;
    }

    // Sub phase (same values in reverse for bus balance)
    for i in (0..active).rev() {
        let val = F::from_u32((i as u32) + 1);
        data.extend([val, acc, F::ZERO, F::ONE, F::ZERO, counter]);
        acc = acc - val;
        counter = counter + F::ONE;
    }

    // Pad remaining
    let used = active * 2;
    for _ in used..n {
        data.extend([F::ZERO, acc, F::ZERO, F::ZERO, F::ONE, counter]);
    }

    (RowMajorMatrix::new(data, 6), acc)
}

// --- BabyBear tests ---

#[test]
fn s5_babybear_basic() {
    use openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Engine;

    let n = 16;
    let (trace, final_acc) = generate_bench_trace::<BabyBear>(n);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(BenchAir) as AirRef<_>],
        vec![trace],
        vec![vec![final_acc]],
    )
    .expect("S5: BabyBear proving should work");
}

#[test]
fn s5_babybear_larger_trace() {
    use openvm_stark_sdk::config::baby_bear_poseidon2::BabyBearPoseidon2Engine;

    let n = 64;
    let (trace, final_acc) = generate_bench_trace::<BabyBear>(n);

    let start = Instant::now();
    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(BenchAir) as AirRef<_>],
        vec![trace],
        vec![vec![final_acc]],
    )
    .expect("S5: BabyBear n=64");
    let elapsed = start.elapsed();

    println!("S5 BabyBear (n=64): {:?}", elapsed);
    println!();
    println!("S5 Field Decision:");
    println!("  BabyBear:   p ≈ 2^31, extension ≈ 2^124 (quartic)");
    println!("  Goldilocks: p ≈ 2^64, extension ≈ 2^128");
    println!("  Goldilocks NOT supported: no StarkFriEngine, InvalidProofShape via StarkEngine");
    println!("  → BabyBear is the only viable choice with stark-backend SDK");
    println!();
    println!("  Grand product collision (10K elements):");
    println!("    BabyBear base:      Pr ≈ 2^-21 (marginal)");
    println!("    BabyBear extension: Pr ≈ 2^-114 (safe — LogUp uses extension field)");
}
