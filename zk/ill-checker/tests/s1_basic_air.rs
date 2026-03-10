//! Spike S1: Basic AIR chip + prove/verify
//!
//! Validates: stark-backend API, Plonky3 integration, basic constraint system.
//! Test: Fibonacci AIR — constrains a[i+1] = b[i], b[i+1] = a[i] + b[i].

use std::sync::Arc;

use openvm_stark_backend::{
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};
use p3_baby_bear::BabyBear;

// --- AIR ---

struct FibAir;

impl<F> BaseAir<F> for FibAir {
    fn width(&self) -> usize { 2 }
}

impl<F> BaseAirWithPublicValues<F> for FibAir {
    fn num_public_values(&self) -> usize { 3 }
}

impl<F> PartitionedBaseAir<F> for FibAir {}

impl<AB: AirBuilderWithPublicValues> Air<AB> for FibAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let a: AB::Expr = local[0].clone().into();
        let b: AB::Expr = local[1].clone().into();
        let a_next: AB::Expr = next[0].clone().into();
        let b_next: AB::Expr = next[1].clone().into();

        let pis = builder.public_values();
        let pi_a: AB::Expr = pis[0].clone().into();
        let pi_b: AB::Expr = pis[1].clone().into();
        let pi_x: AB::Expr = pis[2].clone().into();

        builder.when_first_row().assert_eq(a.clone(), pi_a);
        builder.when_first_row().assert_eq(b.clone(), pi_b);

        builder.when_transition().assert_eq(a_next, b.clone());
        builder.when_transition().assert_eq(b_next, a + b.clone());

        builder.when_last_row().assert_eq(b, pi_x);
    }
}

// --- Trace generation ---

fn generate_fib_trace(a: u32, b: u32, n: usize) -> (RowMajorMatrix<BabyBear>, BabyBear) {
    assert!(n.is_power_of_two());
    let mut vals = Vec::with_capacity(n * 2);
    let (mut x, mut y) = (a, b);
    for _ in 0..n {
        vals.push(BabyBear::from_u32(x));
        vals.push(BabyBear::from_u32(y));
        let tmp = x.wrapping_add(y);
        x = y;
        y = tmp;
    }
    let last_b = vals[(n - 1) * 2 + 1];
    (RowMajorMatrix::new(vals, 2), last_b)
}

// --- Tests ---

#[test]
fn s1_fibonacci_prove_verify() {
    let n = 8;
    let (a, b) = (1u32, 1u32);
    let (trace, last_val) = generate_fib_trace(a, b, n);

    let pis = vec![BabyBear::from_u32(a), BabyBear::from_u32(b), last_val];

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(FibAir) as AirRef<_>],
        vec![trace],
        vec![pis],
    )
    .expect("S1: basic AIR prove/verify should succeed");
}

#[test]
#[should_panic]
fn s1_fibonacci_bad_witness_fails() {
    let n = 8;
    let (a, b) = (1u32, 1u32);
    let (_, last_val) = generate_fib_trace(a, b, n);

    let bad_trace = RowMajorMatrix::new(vec![BabyBear::ZERO; n * 2], 2);
    let pis = vec![BabyBear::from_u32(a), BabyBear::from_u32(b), last_val];

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(FibAir) as AirRef<_>],
        vec![bad_trace],
        vec![pis],
    )
    .expect("should fail");
}
