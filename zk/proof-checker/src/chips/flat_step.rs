//! FlatStepChip: per-step resource accounting for flat rewriting certificates.
//!
//! Each row represents one forward execution step. Consumed facts are
//! received from CONTEXT_BUS, produced facts are sent to CONTEXT_BUS.
//! For compiled rules (is_loli=0), ground_loli is looked up in GAMMA_BUS
//! to verify the rule is a valid persistent clause.
//!
//! Verification model:
//!   - Resource consistency: CONTEXT_BUS balance (sound)
//!   - Rule membership: GAMMA_BUS lookup (sound with committed gamma)
//!   - Rule application: NOT verified in circuit — JS checkRewriteTrace
//!     handles full pattern matching. Adding tensor decomposition via
//!     FORMULA_BUS is a planned enhancement (see TODO_0084 §Phase 3).
//!
//! Layout (width 27):
//!   [0]     active           — boolean, row is active
//!   [1]     is_loli          — boolean, 1 = loli match (no gamma lookup)
//!   [2]     ground_loli      — ground loli hash for gamma lookup
//!   [3..8]  consumed_0..5    — consumed fact hashes (0 = unused)
//!   [9..14] consumed_active  — per-slot boolean flags
//!   [15..20] produced_0..5   — produced fact hashes (0 = unused)
//!   [21..26] produced_active — per-slot boolean flags

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, GAMMA_BUS};

pub const MAX_CONSUMED: usize = 6;
pub const MAX_PRODUCED: usize = 6;

const COL_ACTIVE: usize = 0;
const COL_IS_LOLI: usize = 1;
const COL_GROUND_LOLI: usize = 2;
const COL_CONSUMED: usize = 3;
const COL_CONSUMED_ACTIVE: usize = COL_CONSUMED + MAX_CONSUMED;
const COL_PRODUCED: usize = COL_CONSUMED_ACTIVE + MAX_CONSUMED;
const COL_PRODUCED_ACTIVE: usize = COL_PRODUCED + MAX_PRODUCED;
pub const WIDTH: usize = COL_PRODUCED_ACTIVE + MAX_PRODUCED; // 27

pub struct FlatStepChip;

impl<F> BaseAir<F> for FlatStepChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for FlatStepChip {}
impl<F> PartitionedBaseAir<F> for FlatStepChip {}

impl<AB: InteractionBuilder> Air<AB> for FlatStepChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let active: AB::Expr = local[COL_ACTIVE].clone().into();
        let is_loli: AB::Expr = local[COL_IS_LOLI].clone().into();
        let ground_loli: AB::Expr = local[COL_GROUND_LOLI].clone().into();

        // Boolean constraints
        builder.assert_zero(active.clone() * (active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_loli.clone() * (is_loli.clone() - AB::Expr::ONE));

        // Consumed facts: receive from CONTEXT_BUS
        for i in 0..MAX_CONSUMED {
            let fact: AB::Expr = local[COL_CONSUMED + i].clone().into();
            let slot_active: AB::Expr = local[COL_CONSUMED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            CONTEXT_BUS.receive(builder, [fact], active.clone() * slot_active);
        }

        // Produced facts: send to CONTEXT_BUS
        for i in 0..MAX_PRODUCED {
            let fact: AB::Expr = local[COL_PRODUCED + i].clone().into();
            let slot_active: AB::Expr = local[COL_PRODUCED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            CONTEXT_BUS.send(builder, [fact], active.clone() * slot_active);
        }

        // Rule lookup: GAMMA_BUS for compiled rules (is_loli=0)
        let rule_mult = active * (AB::Expr::ONE - is_loli);
        GAMMA_BUS.lookup_key(builder, [ground_loli], rule_mult);
    }
}
