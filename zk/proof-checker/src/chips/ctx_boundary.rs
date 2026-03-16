//! CtxBoundaryChip: context handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs linear context at chunk boundaries for tree path chunking.
//! Reuses the FlatInitChip/FlatFinalChip pattern for CONTEXT_BUS.
//!
//! At chunk start (is_send=1): sends context hashes on CONTEXT_BUS.
//! At chunk end (is_send=0): receives remaining context from CONTEXT_BUS.
//!
//! Main trace (width 5): [is_active, is_send, hash, acc_send_count, acc_recv_count]
//! Public values: [init_hash_0, ..., init_hash_N, final_hash_0, ..., final_hash_N,
//!                 send_active_count, recv_active_count]
//!   padded to max_ctx_size per side (init + final), plus 2 count PVs.
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

use crate::buses::CONTEXT_BUS;

pub const WIDTH: usize = 5;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_HASH: usize = 2;
const COL_ACC_SEND: usize = 3;
const COL_ACC_RECV: usize = 4;

/// CtxBoundaryChip for tree-path inter-chunk context handoff.
///
/// `max_ctx_size` determines PV size: max_ctx_size per side (init/final).
/// Total PVs = 2 * max_ctx_size + 2 (send_active_count + recv_active_count).
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
        self.max_ctx_size * 2 + 2
    }
}

impl<F> PartitionedBaseAir<F> for CtxBoundaryChip {}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB> for CtxBoundaryChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let is_send: AB::Expr = local[COL_IS_SEND].clone().into();
        let hash: AB::Expr = local[COL_HASH].clone().into();
        let acc_send: AB::Expr = local[COL_ACC_SEND].clone().into();
        let acc_recv: AB::Expr = local[COL_ACC_RECV].clone().into();

        let is_active_next: AB::Expr = next[COL_ACTIVE].clone().into();
        let is_send_next: AB::Expr = next[COL_IS_SEND].clone().into();
        let acc_send_next: AB::Expr = next[COL_ACC_SEND].clone().into();
        let acc_recv_next: AB::Expr = next[COL_ACC_RECV].clone().into();

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));

        // Running-sum count constraints
        let send_contrib = is_active.clone() * is_send.clone();
        let recv_contrib = is_active.clone() * (AB::Expr::ONE - is_send.clone());

        builder.when_first_row().assert_eq(acc_send.clone(), send_contrib.clone());
        builder.when_first_row().assert_eq(acc_recv.clone(), recv_contrib.clone());

        let send_contrib_next = is_active_next.clone() * is_send_next.clone();
        let recv_contrib_next = is_active_next * (AB::Expr::ONE - is_send_next);
        builder.when_transition().assert_eq(acc_send_next, acc_send.clone() + send_contrib_next);
        builder.when_transition().assert_eq(acc_recv_next, acc_recv.clone() + recv_contrib_next);

        let num_pvs = self.max_ctx_size * 2 + 2;
        let pv_send_count: AB::Expr = builder.public_values()[num_pvs - 2].clone().into();
        let pv_recv_count: AB::Expr = builder.public_values()[num_pvs - 1].clone().into();
        builder.when_last_row().assert_eq(acc_send, pv_send_count);
        builder.when_last_row().assert_eq(acc_recv, pv_recv_count);

        // is_send=1: CONTEXT_BUS.send (chunk start — inject context)
        CONTEXT_BUS.send(
            builder,
            [hash.clone()],
            send_contrib,
        );

        // is_send=0: CONTEXT_BUS.receive (chunk end — absorb remaining context)
        CONTEXT_BUS.receive(
            builder,
            [hash],
            recv_contrib,
        );
    }
}
