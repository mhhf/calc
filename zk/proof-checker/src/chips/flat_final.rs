//! FlatFinalChip: consumes remaining linear context for flat certificates.
//!
//! Each row receives one fact hash from CONTEXT_BUS. Paired with
//! FlatInitChip — init sends, final receives, steps consume/produce.
//! CONTEXT_BUS balance verifies: init = steps_consumed + final.
//!
//! Columns (width 2): [is_active, hash]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

pub const WIDTH: usize = 2;

pub struct FlatFinalChip;

impl<F> BaseAir<F> for FlatFinalChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for FlatFinalChip {}
impl<F> PartitionedBaseAir<F> for FlatFinalChip {}

impl<AB: InteractionBuilder> Air<AB> for FlatFinalChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[0].clone().into();
        let hash: AB::Expr = local[1].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        CONTEXT_BUS.receive(builder, [hash], is_active);
    }
}
