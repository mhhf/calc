//! DiscardChip: consumes a linear resource authorized by zero_l.
//!
//! Each active row consumes one resource from CONTEXT_BUS and one
//! discard permit from DISCARD_BUS. The permit must match a nonce
//! from a ZeroLChip row — this ensures only zero_l can authorize
//! context discarding (ILL soundness).
//!
//! Without the DISCARD_BUS check, a malicious witness could freely
//! discard linear resources, breaking linearity.
//!
//! Columns (width 3): [hash, is_active, permit]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, DISCARD_BUS};

pub const COL_HASH: usize = 0;
pub const COL_IS_ACTIVE: usize = 1;
pub const COL_PERMIT: usize = 2;
pub const WIDTH: usize = 3;

pub struct DiscardChip;

impl<F> BaseAir<F> for DiscardChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for DiscardChip {}
impl<F> PartitionedBaseAir<F> for DiscardChip {}

impl<AB: InteractionBuilder> Air<AB> for DiscardChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let permit: AB::Expr = local[COL_PERMIT].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume resource from context
        CONTEXT_BUS.receive(builder, [hash], is_active.clone());

        // Verify discard permit (must match a zero_l nonce)
        DISCARD_BUS.lookup_key(builder, [permit], is_active);
    }
}
