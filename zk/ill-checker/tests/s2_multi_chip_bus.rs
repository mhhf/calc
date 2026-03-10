//! Spike S2: Multi-chip with LogUp bus interactions
//!
//! Validates: InteractionBuilder send/receive across chips, multi-chip proving.
//! Test: SenderAir sends values 0..N on a bus, ReceiverAir receives same values.
//! Bus balance must hold across the two chips.

use std::sync::Arc;

use openvm_stark_backend::{
    interaction::PermutationCheckBus,
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};
use p3_baby_bear::BabyBear;

const BUS: PermutationCheckBus = PermutationCheckBus::new(0);

// --- Sender AIR: sends (value) on each active row ---

struct SenderAir;

impl<F> BaseAir<F> for SenderAir {
    fn width(&self) -> usize { 2 } // [value, is_active]
}
impl<F> BaseAirWithPublicValues<F> for SenderAir {}
impl<F> PartitionedBaseAir<F> for SenderAir {}

impl<AB: AirBuilder> Air<AB> for SenderAir
where
    AB: openvm_stark_backend::interaction::InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let value: AB::Expr = local[0].clone().into();
        let is_active: AB::Expr = local[1].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Send value on the bus when active
        BUS.send(builder, [value], is_active);
    }
}

// --- Receiver AIR: receives (value) on each active row ---

struct ReceiverAir;

impl<F> BaseAir<F> for ReceiverAir {
    fn width(&self) -> usize { 2 } // [value, is_active]
}
impl<F> BaseAirWithPublicValues<F> for ReceiverAir {}
impl<F> PartitionedBaseAir<F> for ReceiverAir {}

impl<AB: AirBuilder> Air<AB> for ReceiverAir
where
    AB: openvm_stark_backend::interaction::InteractionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let value: AB::Expr = local[0].clone().into();
        let is_active: AB::Expr = local[1].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        BUS.receive(builder, [value], is_active);
    }
}

// --- Trace generation ---

fn make_trace(values: &[u32], n: usize) -> RowMajorMatrix<BabyBear> {
    assert!(n.is_power_of_two());
    assert!(values.len() <= n);
    let mut data = Vec::with_capacity(n * 2);
    for i in 0..n {
        if i < values.len() {
            data.push(BabyBear::from_u32(values[i]));
            data.push(BabyBear::ONE); // active
        } else {
            data.push(BabyBear::ZERO);
            data.push(BabyBear::ZERO); // padding (inactive)
        }
    }
    RowMajorMatrix::new(data, 2)
}

// --- Tests ---

#[test]
fn s2_send_receive_balance() {
    let values: Vec<u32> = (0..4).collect();
    let n = 4; // power of 2

    let sender_trace = make_trace(&values, n);
    let receiver_trace = make_trace(&values, n);

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(SenderAir) as AirRef<_>,
            Arc::new(ReceiverAir) as AirRef<_>,
        ],
        vec![sender_trace, receiver_trace],
        vec![vec![], vec![]], // no public values
    )
    .expect("S2: balanced send/receive should succeed");
}

#[test]
fn s2_multi_value_tuple() {
    // Test with multi-field tuples on the bus
    const TUPLE_BUS: PermutationCheckBus = PermutationCheckBus::new(1);

    struct TupleSenderAir;

    impl<F> BaseAir<F> for TupleSenderAir {
        fn width(&self) -> usize { 3 } // [field0, field1, is_active]
    }
    impl<F> BaseAirWithPublicValues<F> for TupleSenderAir {}
    impl<F> PartitionedBaseAir<F> for TupleSenderAir {}

    impl<AB: AirBuilder> Air<AB> for TupleSenderAir
    where
        AB: openvm_stark_backend::interaction::InteractionBuilder,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.row_slice(0).unwrap();
            let f0: AB::Expr = local[0].clone().into();
            let f1: AB::Expr = local[1].clone().into();
            let active: AB::Expr = local[2].clone().into();
            TUPLE_BUS.send(builder, [f0, f1], active);
        }
    }

    struct TupleReceiverAir;

    impl<F> BaseAir<F> for TupleReceiverAir {
        fn width(&self) -> usize { 3 }
    }
    impl<F> BaseAirWithPublicValues<F> for TupleReceiverAir {}
    impl<F> PartitionedBaseAir<F> for TupleReceiverAir {}

    impl<AB: AirBuilder> Air<AB> for TupleReceiverAir
    where
        AB: openvm_stark_backend::interaction::InteractionBuilder,
    {
        fn eval(&self, builder: &mut AB) {
            let main = builder.main();
            let local = main.row_slice(0).unwrap();
            let f0: AB::Expr = local[0].clone().into();
            let f1: AB::Expr = local[1].clone().into();
            let active: AB::Expr = local[2].clone().into();
            TUPLE_BUS.receive(builder, [f0, f1], active);
        }
    }

    // Send tuples: (10,20), (30,40), (50,60), (70,80)
    let send_data: Vec<BabyBear> = vec![
        10, 20, 1, 30, 40, 1, 50, 60, 1, 70, 80, 1,
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    // Receive same tuples (different row order is fine — bus is multiset)
    let recv_data: Vec<BabyBear> = vec![
        70, 80, 1, 50, 60, 1, 30, 40, 1, 10, 20, 1,
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(TupleSenderAir) as AirRef<_>,
            Arc::new(TupleReceiverAir) as AirRef<_>,
        ],
        vec![
            RowMajorMatrix::new(send_data, 3),
            RowMajorMatrix::new(recv_data, 3),
        ],
        vec![vec![], vec![]],
    )
    .expect("S2: multi-field tuple bus should work");
}

#[test]
#[should_panic]
fn s2_unbalanced_bus_fails() {
    let n = 4;
    // Send 4 values but only receive 3
    let sender_trace = make_trace(&[1, 2, 3, 4], n);
    let receiver_trace = make_trace(&[1, 2, 3], n); // missing value 4!

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![
            Arc::new(SenderAir) as AirRef<_>,
            Arc::new(ReceiverAir) as AirRef<_>,
        ],
        vec![sender_trace, receiver_trace],
        vec![vec![], vec![]],
    )
    .expect("should fail: bus unbalanced");
}
