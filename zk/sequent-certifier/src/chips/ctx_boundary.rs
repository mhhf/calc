//! CtxBoundaryChip: context handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs linear context at chunk boundaries for tree path chunking.
//! Reuses the FlatInitChip/FlatFinalChip pattern for CONTEXT_BUS.
//!
//! At chunk start (is_send=1): sends context hashes on CONTEXT_BUS.
//! At chunk end (is_send=0): receives remaining context from CONTEXT_BUS.
//!
//! Main trace (width 6): [is_active, is_send, hash, acc_send_count, acc_recv_count, is_first]
//! Public values: [init_hash_0, ..., init_hash_N, final_hash_0, ..., final_hash_N,
//!                 send_active_count, recv_active_count]
//!   padded to max_ctx_size per side (init + final), plus 2 count PVs.
//!
//! ## Soundness layers
//!
//! 1. **Bus balance (CONTEXT_BUS):** trace values participate in LogUp multiset
//!    equality — internal consistency within each chunk.
//! 2. **Running-sum count binding:** acc_send/acc_recv constrain PV counts against
//!    actual trace row counts — prevents adding/removing boundary rows.
//! 3. **PV value binding (CTX_PV_BIND_BUS):** on the first row, receive all PV
//!    values on a binding bus; active rows send their trace values on the same bus.
//!    LogUp multiset equality ensures PV values match trace values (as a set).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, CTX_PV_BIND_BUS};

pub const WIDTH: usize = 6;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_HASH: usize = 2;
const COL_ACC_SEND: usize = 3;
const COL_ACC_RECV: usize = 4;
const COL_IS_FIRST: usize = 5;

/// CtxBoundaryChip for tree-path inter-chunk context handoff.
///
/// `max_ctx_size` determines PV size: max_ctx_size per side (init/final).
/// Total PVs = 2 * max_ctx_size + 2 (send_active_count + recv_active_count).
pub struct CtxBoundaryChip {
    pub max_ctx_size: usize,
}

/// PV layout accessors — centralized offset computation.
impl CtxBoundaryChip {
    pub fn num_pvs(&self) -> usize {
        self.max_ctx_size * 2 + 2
    }
    pub fn init_hash_idx(&self, k: usize) -> usize { k }
    pub fn final_hash_idx(&self, k: usize) -> usize { self.max_ctx_size + k }
    pub fn send_count_idx(&self) -> usize { self.num_pvs() - 2 }
    pub fn recv_count_idx(&self) -> usize { self.num_pvs() - 1 }
}

impl<F> BaseAir<F> for CtxBoundaryChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for CtxBoundaryChip {
    fn num_public_values(&self) -> usize {
        self.num_pvs()
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
        let is_first: AB::Expr = local[COL_IS_FIRST].clone().into();

        let is_active_next: AB::Expr = next[COL_ACTIVE].clone().into();
        let is_send_next: AB::Expr = next[COL_IS_SEND].clone().into();
        let acc_send_next: AB::Expr = next[COL_ACC_SEND].clone().into();
        let acc_recv_next: AB::Expr = next[COL_ACC_RECV].clone().into();
        let is_first_next: AB::Expr = next[COL_IS_FIRST].clone().into();

        // Extract all PV values into locals before any mutable builder calls
        let pv_send_count: AB::Expr = {
            let pvs = builder.public_values();
            pvs[self.send_count_idx()].clone().into()
        };
        let pv_recv_count: AB::Expr = {
            let pvs = builder.public_values();
            pvs[self.recv_count_idx()].clone().into()
        };
        let mut pv_init_hashes: Vec<AB::Expr> = Vec::with_capacity(self.max_ctx_size);
        let mut pv_final_hashes: Vec<AB::Expr> = Vec::with_capacity(self.max_ctx_size);
        for k in 0..self.max_ctx_size {
            let pvs = builder.public_values();
            pv_init_hashes.push(pvs[self.init_hash_idx(k)].clone().into());
            pv_final_hashes.push(pvs[self.final_hash_idx(k)].clone().into());
        }

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));
        builder.assert_zero(is_first.clone() * (is_first.clone() - AB::Expr::ONE));

        // is_first: 1 on row 0, 0 elsewhere
        builder.when_first_row().assert_one(is_first.clone());
        builder.when_transition().assert_zero(is_first_next);

        // Running-sum count constraints
        let send_contrib = is_active.clone() * is_send.clone();
        let recv_contrib = is_active.clone() * (AB::Expr::ONE - is_send.clone());

        builder.when_first_row().assert_eq(acc_send.clone(), send_contrib.clone());
        builder.when_first_row().assert_eq(acc_recv.clone(), recv_contrib.clone());

        let send_contrib_next = is_active_next.clone() * is_send_next.clone();
        let recv_contrib_next = is_active_next * (AB::Expr::ONE - is_send_next);
        builder.when_transition().assert_eq(acc_send_next, acc_send.clone() + send_contrib_next);
        builder.when_transition().assert_eq(acc_recv_next, acc_recv.clone() + recv_contrib_next);

        builder.when_last_row().assert_eq(acc_send, pv_send_count.clone());
        builder.when_last_row().assert_eq(acc_recv, pv_recv_count.clone());

        // --- CONTEXT_BUS: actual context transfer ---

        CONTEXT_BUS.send(
            builder,
            [hash.clone()],
            send_contrib.clone(),
        );

        CONTEXT_BUS.receive(
            builder,
            [hash.clone()],
            recv_contrib.clone(),
        );

        // --- CTX_PV_BIND_BUS: bind PV values to trace values ---

        // Init side (is_send=1): discriminator = 0
        for k in 0..self.max_ctx_size {
            CTX_PV_BIND_BUS.receive(
                builder,
                [AB::Expr::ZERO, pv_init_hashes[k].clone()],
                is_first.clone(),
            );
        }
        CTX_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, hash.clone()],
            send_contrib,
        );
        let max_ctx_expr = AB::Expr::from_u32(self.max_ctx_size as u32);
        let init_padding = max_ctx_expr.clone() - pv_send_count;
        CTX_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, AB::Expr::ZERO],
            is_first.clone() * init_padding,
        );

        // Final side (is_send=0): discriminator = 1
        for k in 0..self.max_ctx_size {
            CTX_PV_BIND_BUS.receive(
                builder,
                [AB::Expr::ONE, pv_final_hashes[k].clone()],
                is_first.clone(),
            );
        }
        CTX_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ONE, hash],
            recv_contrib,
        );
        let recv_padding = max_ctx_expr - pv_recv_count;
        CTX_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ONE, AB::Expr::ZERO],
            is_first * recv_padding,
        );
    }
}
