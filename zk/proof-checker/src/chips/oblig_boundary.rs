//! ObligBoundaryChip: obligation handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs obligations at chunk boundaries for tree path chunking.
//!
//! At chunk start (is_send=1): sends obligations on OBLIG_BUS (re-introduces
//! obligations from previous chunk's boundary snapshot).
//! At chunk end (is_send=0): receives obligations from OBLIG_BUS (absorbs
//! outstanding obligations that cross the chunk boundary).
//!
//! Main trace (width 5): [is_active, is_send, nonce, goal_hash, lax]
//! Public values: [init_goal_0, init_lax_0, ..., final_goal_0, final_lax_0, ...]
//!   padded to max_oblig_count * 2 per side (init + final).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::OBLIG_BUS;

pub const WIDTH: usize = 5;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_NONCE: usize = 2;
const COL_GOAL: usize = 3;
const COL_LAX: usize = 4;

/// ObligBoundaryChip for tree-path inter-chunk obligation handoff.
///
/// `max_oblig_count` determines PV size: 2 * max_oblig_count per side (init/final).
/// Total PVs = 4 * max_oblig_count.
pub struct ObligBoundaryChip {
    pub max_oblig_count: usize,
}

impl<F> BaseAir<F> for ObligBoundaryChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for ObligBoundaryChip {
    fn num_public_values(&self) -> usize {
        // init: [goal, lax] * max_oblig_count + final: [goal, lax] * max_oblig_count
        self.max_oblig_count * 4
    }
}

impl<F> PartitionedBaseAir<F> for ObligBoundaryChip {}

impl<AB: InteractionBuilder> Air<AB> for ObligBoundaryChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let is_send: AB::Expr = local[COL_IS_SEND].clone().into();
        let nonce: AB::Expr = local[COL_NONCE].clone().into();
        let goal: AB::Expr = local[COL_GOAL].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));
        builder.assert_zero(lax.clone() * (lax.clone() - AB::Expr::ONE));

        // is_send=1: OBLIG_BUS.send (chunk start — inject obligations)
        OBLIG_BUS.send(
            builder,
            [nonce.clone(), goal.clone(), lax.clone()],
            is_active.clone() * is_send.clone(),
        );

        // is_send=0: OBLIG_BUS.receive (chunk end — absorb obligations)
        OBLIG_BUS.receive(
            builder,
            [nonce, goal, lax],
            is_active * (AB::Expr::ONE - is_send),
        );
    }
}
