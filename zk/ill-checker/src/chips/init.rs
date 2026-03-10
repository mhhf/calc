//! InitChip: introduces the initial context and root obligation.
//!
//! Each row independently controls whether it sends on CONTEXT_BUS
//! and/or OBLIG_BUS. This allows the initial sequent's context
//! elements and obligation to use different hashes.
//!
//! Example: for A, B ⊢ A⊗B (2 context elements, 1 obligation):
//!   Row 0: ctx_hash=A, ctx_active=1, oblig_hash=A⊗B, oblig_active=1, nonce=0, lax=0
//!   Row 1: ctx_hash=B, ctx_active=1, oblig_hash=0,   oblig_active=0, nonce=0, lax=0
//!
//! Columns (width 6): [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, OBLIG_BUS};

pub const COL_CTX_HASH: usize = 0;
pub const COL_CTX_ACTIVE: usize = 1;
pub const COL_OBLIG_HASH: usize = 2;
pub const COL_OBLIG_ACTIVE: usize = 3;
pub const COL_NONCE: usize = 4;
pub const COL_LAX: usize = 5;
pub const WIDTH: usize = 6;

pub struct InitChip;

impl<F> BaseAir<F> for InitChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for InitChip {}
impl<F> PartitionedBaseAir<F> for InitChip {}

impl<AB: InteractionBuilder> Air<AB> for InitChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let ctx_hash: AB::Expr = local[COL_CTX_HASH].clone().into();
        let ctx_active: AB::Expr = local[COL_CTX_ACTIVE].clone().into();
        let oblig_hash: AB::Expr = local[COL_OBLIG_HASH].clone().into();
        let oblig_active: AB::Expr = local[COL_OBLIG_ACTIVE].clone().into();
        let nonce: AB::Expr = local[COL_NONCE].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();

        // Boolean constraints
        builder.assert_zero(ctx_active.clone() * (ctx_active.clone() - AB::Expr::ONE));
        builder.assert_zero(oblig_active.clone() * (oblig_active.clone() - AB::Expr::ONE));

        // Introduce context element on CONTEXT_BUS (when ctx_active=1)
        CONTEXT_BUS.send(builder, [ctx_hash], ctx_active);

        // Produce obligation on OBLIG_BUS (when oblig_active=1)
        OBLIG_BUS.send(builder, [nonce, oblig_hash, lax], oblig_active);
    }
}
