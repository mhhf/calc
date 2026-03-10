//! IdentityChip: consumes an obligation and a matching context resource.
//!
//! The identity rule (axiom): the proof term `id(A)` proves A ⊢ A by
//! consuming the obligation for A and consuming A from the linear context.
//!
//! Columns (width 4): [principal, is_active, nonce, lax]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, OBLIG_BUS};

pub const COL_PRINCIPAL: usize = 0;
pub const COL_IS_ACTIVE: usize = 1;
pub const COL_NONCE: usize = 2;
pub const COL_LAX: usize = 3;
pub const WIDTH: usize = 4;

pub struct IdentityChip;

impl<F> BaseAir<F> for IdentityChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for IdentityChip {}
impl<F> PartitionedBaseAir<F> for IdentityChip {}

impl<AB: InteractionBuilder> Air<AB> for IdentityChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let principal: AB::Expr = local[COL_PRINCIPAL].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let nonce: AB::Expr = local[COL_NONCE].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume obligation from OBLIG_BUS
        OBLIG_BUS.receive(builder, [nonce, principal.clone(), lax], is_active.clone());

        // Consume resource from CONTEXT_BUS
        CONTEXT_BUS.receive(builder, [principal], is_active);
    }
}
