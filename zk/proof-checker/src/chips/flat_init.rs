//! FlatInitChip: introduces initial linear context for flat certificates.
//!
//! Each row sends one fact hash on CONTEXT_BUS. Simpler than InitChip —
//! no OBLIG_BUS interaction (flat certificates don't use obligations).
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

pub struct FlatInitChip;

impl<F> BaseAir<F> for FlatInitChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for FlatInitChip {}
impl<F> PartitionedBaseAir<F> for FlatInitChip {}

impl<AB: InteractionBuilder> Air<AB> for FlatInitChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[0].clone().into();
        let hash: AB::Expr = local[1].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        CONTEXT_BUS.send(builder, [hash], is_active);
    }
}
