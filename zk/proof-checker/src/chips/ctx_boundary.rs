//! CtxBoundaryChip: context handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs linear context at chunk boundaries for tree path chunking.
//! Reuses the FlatInitChip/FlatFinalChip pattern for CONTEXT_BUS.
//!
//! At chunk start (is_send=1): sends context hashes on CONTEXT_BUS.
//! At chunk end (is_send=0): receives remaining context from CONTEXT_BUS.
//!
//! Main trace (width 3): [is_active, is_send, hash]
//! Public values: [init_hash_0, ..., init_hash_N, final_hash_0, ..., final_hash_N]
//!   padded to max_ctx_size per side (init + final).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

pub const WIDTH: usize = 3;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_HASH: usize = 2;

/// CtxBoundaryChip for tree-path inter-chunk context handoff.
///
/// `max_ctx_size` determines PV size: max_ctx_size per side (init/final).
/// Total PVs = 2 * max_ctx_size.
pub struct CtxBoundaryChip {
    pub max_ctx_size: usize,
}

impl<F> BaseAir<F> for CtxBoundaryChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for CtxBoundaryChip {
    fn num_public_values(&self) -> usize {
        self.max_ctx_size * 2
    }
}

impl<F> PartitionedBaseAir<F> for CtxBoundaryChip {}

impl<AB: InteractionBuilder> Air<AB> for CtxBoundaryChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let is_send: AB::Expr = local[COL_IS_SEND].clone().into();
        let hash: AB::Expr = local[COL_HASH].clone().into();

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));

        // is_send=1: CONTEXT_BUS.send (chunk start — inject context)
        CONTEXT_BUS.send(
            builder,
            [hash.clone()],
            is_active.clone() * is_send.clone(),
        );

        // is_send=0: CONTEXT_BUS.receive (chunk end — absorb remaining context)
        CONTEXT_BUS.receive(
            builder,
            [hash],
            is_active * (AB::Expr::ONE - is_send),
        );
    }
}
