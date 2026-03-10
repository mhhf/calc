//! DupChip: context duplication for additive rules (with_r, oplus_l).
//!
//! Each active row receives one resource from CONTEXT_BUS and sends
//! it back twice — one copy for each additive branch. The witness
//! generator emits one DupChip row per live context element at each
//! additive branching point.
//!
//! Net effect per row: +1 on CONTEXT_BUS (receive 1, send 2).
//!
//! Columns (width 2): [hash, is_active]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

pub const COL_HASH: usize = 0;
pub const COL_IS_ACTIVE: usize = 1;
pub const WIDTH: usize = 2;

pub struct DupChip;

impl<F> BaseAir<F> for DupChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for DupChip {}
impl<F> PartitionedBaseAir<F> for DupChip {}

impl<AB: InteractionBuilder> Air<AB> for DupChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume original resource
        CONTEXT_BUS.receive(builder, [hash.clone()], is_active.clone());

        // Send two copies (one per additive branch)
        CONTEXT_BUS.send(builder, [hash.clone()], is_active.clone());
        CONTEXT_BUS.send(builder, [hash], is_active);
    }
}
