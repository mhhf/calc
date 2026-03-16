//! ObligBoundaryChip: obligation handoff at tree-path chunk boundaries.
//!
//! Phase 6-7: injects/absorbs obligations at chunk boundaries for tree path chunking.
//!
//! At chunk start (is_send=1): sends obligations on OBLIG_BUS (re-introduces
//! obligations from previous chunk's boundary snapshot).
//! At chunk end (is_send=0): receives obligations from OBLIG_BUS (absorbs
//! outstanding obligations that cross the chunk boundary).
//!
//! Main trace (width 8): [is_active, is_send, nonce, goal_hash, lax,
//!                         acc_send_count, acc_recv_count, is_first]
//! Public values: [init_goal_0, init_lax_0, ..., final_goal_0, final_lax_0, ...,
//!                 send_active_count, recv_active_count]
//!   padded to max_oblig_count * 2 per side (init + final), plus 2 count PVs.
//!
//! ## Soundness layers
//!
//! 1. **Bus balance (OBLIG_BUS):** trace values participate in LogUp multiset
//!    equality — internal consistency within each chunk.
//! 2. **Running-sum count binding:** acc_send/acc_recv constrain PV counts against
//!    actual trace row counts — prevents adding/removing boundary rows.
//! 3. **PV value binding (OBLIG_PV_BIND_BUS):** on the first row, receive all PV
//!    values on a binding bus; active rows send their trace values on the same bus.
//!    LogUp multiset equality ensures PV values match trace values (as a set).
//!    This prevents declaring one set of obligations in PVs while actually
//!    transferring a different set in the trace.

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{OBLIG_BUS, OBLIG_PV_BIND_BUS};

pub const WIDTH: usize = 8;

const COL_ACTIVE: usize = 0;
const COL_IS_SEND: usize = 1;
const COL_NONCE: usize = 2;
const COL_GOAL: usize = 3;
const COL_LAX: usize = 4;
const COL_ACC_SEND: usize = 5;
const COL_ACC_RECV: usize = 6;
const COL_IS_FIRST: usize = 7;

/// ObligBoundaryChip for tree-path inter-chunk obligation handoff.
///
/// `max_oblig_count` determines PV size: 2 * max_oblig_count per side (init/final).
/// Total PVs = 4 * max_oblig_count + 2 (send_active_count + recv_active_count).
pub struct ObligBoundaryChip {
    pub max_oblig_count: usize,
}

/// PV layout accessors — centralized offset computation.
impl ObligBoundaryChip {
    pub fn num_pvs(&self) -> usize {
        self.max_oblig_count * 4 + 2
    }
    pub fn init_goal_idx(&self, k: usize) -> usize { k * 2 }
    pub fn init_lax_idx(&self, k: usize) -> usize { k * 2 + 1 }
    pub fn final_goal_idx(&self, k: usize) -> usize { self.max_oblig_count * 2 + k * 2 }
    pub fn final_lax_idx(&self, k: usize) -> usize { self.max_oblig_count * 2 + k * 2 + 1 }
    pub fn send_count_idx(&self) -> usize { self.num_pvs() - 2 }
    pub fn recv_count_idx(&self) -> usize { self.num_pvs() - 1 }
    /// Number of PV elements per side (init or final).
    pub fn pvs_per_side(&self) -> usize { self.max_oblig_count * 2 }
}

impl<F> BaseAir<F> for ObligBoundaryChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for ObligBoundaryChip {
    fn num_public_values(&self) -> usize {
        self.num_pvs()
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
        let is_first: AB::Expr = local[COL_IS_FIRST].clone().into();

        let is_active_next: AB::Expr = next[COL_ACTIVE].clone().into();
        let is_send_next: AB::Expr = next[COL_IS_SEND].clone().into();
        let acc_send_next: AB::Expr = next[COL_ACC_SEND].clone().into();
        let acc_recv_next: AB::Expr = next[COL_ACC_RECV].clone().into();
        let is_first_next: AB::Expr = next[COL_IS_FIRST].clone().into();

        // Extract all PV values into locals before any mutable builder calls.
        // (builder.public_values() borrows immutably; bus interactions borrow mutably)
        let pv_send_count: AB::Expr = {
            let pvs = builder.public_values();
            pvs[self.send_count_idx()].clone().into()
        };
        let pv_recv_count: AB::Expr = {
            let pvs = builder.public_values();
            pvs[self.recv_count_idx()].clone().into()
        };
        let mut pv_init_goals: Vec<AB::Expr> = Vec::with_capacity(self.max_oblig_count);
        let mut pv_init_laxs: Vec<AB::Expr> = Vec::with_capacity(self.max_oblig_count);
        let mut pv_final_goals: Vec<AB::Expr> = Vec::with_capacity(self.max_oblig_count);
        let mut pv_final_laxs: Vec<AB::Expr> = Vec::with_capacity(self.max_oblig_count);
        for k in 0..self.max_oblig_count {
            let pvs = builder.public_values();
            pv_init_goals.push(pvs[self.init_goal_idx(k)].clone().into());
            pv_init_laxs.push(pvs[self.init_lax_idx(k)].clone().into());
            pv_final_goals.push(pvs[self.final_goal_idx(k)].clone().into());
            pv_final_laxs.push(pvs[self.final_lax_idx(k)].clone().into());
        }

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_send.clone() * (is_send.clone() - AB::Expr::ONE));
        builder.assert_zero(lax.clone() * (lax.clone() - AB::Expr::ONE));
        builder.assert_zero(is_first.clone() * (is_first.clone() - AB::Expr::ONE));

        // is_first: 1 on row 0, 0 elsewhere
        builder.when_first_row().assert_one(is_first.clone());
        builder.when_transition().assert_zero(is_first_next);

        // Running-sum count constraints: bind PV counts to actual trace row counts
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

        // --- OBLIG_BUS: actual obligation transfer ---

        OBLIG_BUS.send(
            builder,
            [nonce.clone(), goal.clone(), lax.clone()],
            send_contrib.clone(),
        );

        OBLIG_BUS.receive(
            builder,
            [nonce, goal.clone(), lax.clone()],
            recv_contrib.clone(),
        );

        // --- OBLIG_PV_BIND_BUS: bind PV values to trace values ---
        // On the first row, receive all PV obligation values (init + final).
        // Active rows send their trace values. Zero-padding compensates for
        // unused PV slots. LogUp multiset equality ensures PVs match trace.

        // Init side (is_send=1): discriminator = 0
        for k in 0..self.max_oblig_count {
            OBLIG_PV_BIND_BUS.receive(
                builder,
                [AB::Expr::ZERO, pv_init_goals[k].clone(), pv_init_laxs[k].clone()],
                is_first.clone(),
            );
        }
        // Active send rows supply trace values
        OBLIG_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, goal.clone(), lax.clone()],
            send_contrib.clone(),
        );
        // Zero-padding for unused init slots
        let max_oblig_expr = AB::Expr::from_u32(self.max_oblig_count as u32);
        let init_padding = max_oblig_expr.clone() - pv_send_count;
        OBLIG_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, AB::Expr::ZERO, AB::Expr::ZERO],
            is_first.clone() * init_padding,
        );

        // Final side (is_send=0): discriminator = 1
        for k in 0..self.max_oblig_count {
            OBLIG_PV_BIND_BUS.receive(
                builder,
                [AB::Expr::ONE, pv_final_goals[k].clone(), pv_final_laxs[k].clone()],
                is_first.clone(),
            );
        }
        OBLIG_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ONE, goal, lax],
            recv_contrib,
        );
        let recv_padding = max_oblig_expr - pv_recv_count;
        OBLIG_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ONE, AB::Expr::ZERO, AB::Expr::ZERO],
            is_first * recv_padding,
        );
    }
}
