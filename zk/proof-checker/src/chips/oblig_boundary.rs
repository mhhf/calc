//! ObligBoundaryChip: obligation handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs obligations at chunk boundaries for tree path chunking.
//!
//! At chunk start (is_send=1): sends obligations on OBLIG_BUS (re-introduces
//! obligations from previous chunk's boundary snapshot).
//! At chunk end (is_send=0): receives obligations from OBLIG_BUS (absorbs
//! outstanding obligations that cross the chunk boundary).
//!
//! Main trace (width 7): [is_active, is_send, nonce, goal_hash, lax, acc_send_count, acc_recv_count]
//! Public values: [init_goal_0, init_lax_0, ..., final_goal_0, final_lax_0, ...,
//!                 send_active_count, recv_active_count]
//!   padded to max_oblig_count * 2 per side (init + final), plus 2 count PVs.
//!
//! The running-sum count columns bind PV counts to actual trace row counts,
//! preventing a malicious prover from adding/removing boundary rows without detection.

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::OBLIG_BUS;

pub const WIDTH: usize = 7;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_NONCE: usize = 2;
const COL_GOAL: usize = 3;
const COL_LAX: usize = 4;
const COL_ACC_SEND: usize = 5;
const COL_ACC_RECV: usize = 6;

/// ObligBoundaryChip for tree-path inter-chunk obligation handoff.
///
/// `max_oblig_count` determines PV size: 2 * max_oblig_count per side (init/final).
/// Total PVs = 4 * max_oblig_count + 2 (send_active_count + recv_active_count).
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
        // + send_active_count + recv_active_count
        self.max_oblig_count * 4 + 2
    }
}

impl<F> PartitionedBaseAir<F> for ObligBoundaryChip {}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB> for ObligBoundaryChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let is_send: AB::Expr = local[COL_IS_SEND].clone().into();
        let nonce: AB::Expr = local[COL_NONCE].clone().into();
        let goal: AB::Expr = local[COL_GOAL].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();
        let acc_send: AB::Expr = local[COL_ACC_SEND].clone().into();
        let acc_recv: AB::Expr = local[COL_ACC_RECV].clone().into();

        let is_active_next: AB::Expr = next[COL_ACTIVE].clone().into();
        let is_send_next: AB::Expr = next[COL_IS_SEND].clone().into();
        let acc_send_next: AB::Expr = next[COL_ACC_SEND].clone().into();
        let acc_recv_next: AB::Expr = next[COL_ACC_RECV].clone().into();

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));
        builder.assert_zero(lax.clone() * (lax.clone() - AB::Expr::ONE));

        // Running-sum count constraints: bind PV counts to actual trace row counts
        let send_contrib = is_active.clone() * is_send.clone();
        let recv_contrib = is_active.clone() * (AB::Expr::ONE - is_send.clone());

        // First row: acc = contribution
        builder.when_first_row().assert_eq(acc_send.clone(), send_contrib.clone());
        builder.when_first_row().assert_eq(acc_recv.clone(), recv_contrib.clone());

        // Transition: acc_next = acc + next_contribution
        let send_contrib_next = is_active_next.clone() * is_send_next.clone();
        let recv_contrib_next = is_active_next * (AB::Expr::ONE - is_send_next);
        builder.when_transition().assert_eq(acc_send_next, acc_send.clone() + send_contrib_next);
        builder.when_transition().assert_eq(acc_recv_next, acc_recv.clone() + recv_contrib_next);

        // Last row: acc = PV count (last 2 PVs)
        let num_pvs = self.max_oblig_count * 4 + 2;
        let pv_send_count: AB::Expr = builder.public_values()[num_pvs - 2].clone().into();
        let pv_recv_count: AB::Expr = builder.public_values()[num_pvs - 1].clone().into();
        builder.when_last_row().assert_eq(acc_send, pv_send_count);
        builder.when_last_row().assert_eq(acc_recv, pv_recv_count);

        // is_send=1: OBLIG_BUS.send (chunk start — inject obligations)
        OBLIG_BUS.send(
            builder,
            [nonce.clone(), goal.clone(), lax.clone()],
            send_contrib,
        );

        // is_send=0: OBLIG_BUS.receive (chunk end — absorb obligations)
        OBLIG_BUS.receive(
            builder,
            [nonce, goal, lax],
            recv_contrib,
        );
    }
}
