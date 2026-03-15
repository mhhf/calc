//! FactAxiomChip: custom chip for clause proof replacement.
//!
//! Phase 6-4: replaces full clause proof subtrees with a single row per step.
//! Each row receives an obligation from OBLIG_BUS, verifies the goal type
//! against FACT_BUS (ROM-backed), performs CONTEXT_BUS interactions for the
//! consumed (antecedent) and produced (consequent) facts, and sends a new
//! obligation for the continuation (next step or terminal axiom).
//!
//! Phase 6-6a: added pred_hash column (col 30) + PRED_BUS lookup to verify
//! predicate semantics via PredicateRomAir. Closes the soundness gap where
//! FACT_BUS only checked ROM membership without verifying predicate arithmetic.
//!
//! Layout (width 32):
//!   [0]     active
//!   [1]     goal_hash      — obligation type (OBLIG_BUS.receive + FACT_BUS.lookup)
//!   [2]     nonce_in       — obligation nonce (OBLIG_BUS.receive)
//!   [3]     lax            — lax flag (OBLIG_BUS.receive + send)
//!   [4]     goal_out       — continuation obligation type (OBLIG_BUS.send)
//!   [5]     nonce_out      — continuation obligation nonce (OBLIG_BUS.send)
//!   [6..11]  consumed_0..5  — consumed fact hashes (CONTEXT_BUS.receive)
//!   [12..17] ca_0..5        — consumed slot active flags
//!   [18..23] produced_0..5  — produced fact hashes (CONTEXT_BUS.send)
//!   [24..29] pa_0..5        — produced slot active flags
//!   [30]    pred_hash      — predicate application hash (PRED_BUS.lookup)
//!   [31]    pred_active    — boolean: 1 if pred_hash should be verified

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, FACT_BUS, OBLIG_BUS, PRED_BUS};

pub const MAX_CONSUMED: usize = 6;
pub const MAX_PRODUCED: usize = 6;

const COL_ACTIVE: usize = 0;
const COL_GOAL: usize = 1;
const COL_NONCE_IN: usize = 2;
const COL_LAX: usize = 3;
const COL_GOAL_OUT: usize = 4;
const COL_NONCE_OUT: usize = 5;
const COL_CONSUMED: usize = 6;
const COL_CONSUMED_ACTIVE: usize = COL_CONSUMED + MAX_CONSUMED;     // 12
const COL_PRODUCED: usize = COL_CONSUMED_ACTIVE + MAX_CONSUMED;     // 18
const COL_PRODUCED_ACTIVE: usize = COL_PRODUCED + MAX_PRODUCED;     // 24
const COL_PRED_HASH: usize = COL_PRODUCED_ACTIVE + MAX_PRODUCED;   // 30
const COL_PRED_ACTIVE: usize = COL_PRED_HASH + 1;                 // 31
pub const WIDTH: usize = COL_PRED_ACTIVE + 1;                     // 32

pub struct FactAxiomChip;

impl<F: Field> BaseAir<F> for FactAxiomChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for FactAxiomChip {}
impl<F: Field> PartitionedBaseAir<F> for FactAxiomChip {}

impl<AB: InteractionBuilder> Air<AB> for FactAxiomChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let active: AB::Expr = local[COL_ACTIVE].clone().into();
        let goal: AB::Expr = local[COL_GOAL].clone().into();
        let nonce_in: AB::Expr = local[COL_NONCE_IN].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();
        let goal_out: AB::Expr = local[COL_GOAL_OUT].clone().into();
        let nonce_out: AB::Expr = local[COL_NONCE_OUT].clone().into();

        // Boolean constraints
        builder.assert_zero(active.clone() * (active.clone() - AB::Expr::ONE));
        builder.assert_zero(lax.clone() * (lax.clone() - AB::Expr::ONE));

        // Read consumed slots
        let mut c = Vec::with_capacity(MAX_CONSUMED);
        let mut ca = Vec::with_capacity(MAX_CONSUMED);
        for i in 0..MAX_CONSUMED {
            c.push(local[COL_CONSUMED + i].clone().into());
            let slot_active: AB::Expr = local[COL_CONSUMED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            ca.push(slot_active);
        }

        // Read produced slots
        let mut p = Vec::with_capacity(MAX_PRODUCED);
        let mut pa = Vec::with_capacity(MAX_PRODUCED);
        for i in 0..MAX_PRODUCED {
            p.push(local[COL_PRODUCED + i].clone().into());
            let slot_active: AB::Expr = local[COL_PRODUCED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            pa.push(slot_active);
        }

        // --- OBLIG_BUS: receive incoming, send continuation ---
        // Field order: [nonce, type, lax] — matches InitChip and RuleChip.
        OBLIG_BUS.receive(builder, [nonce_in, goal.clone(), lax.clone()], active.clone());
        OBLIG_BUS.send(builder, [nonce_out, goal_out, lax], active.clone());

        // --- CONTEXT_BUS: consume antecedent facts, produce consequent facts ---
        for i in 0..MAX_CONSUMED {
            CONTEXT_BUS.receive(builder, [c[i].clone()], active.clone() * ca[i].clone());
        }
        for i in 0..MAX_PRODUCED {
            CONTEXT_BUS.send(builder, [p[i].clone()], active.clone() * pa[i].clone());
        }

        // --- FACT_BUS: verify goal type against ROM ---
        FACT_BUS.lookup_key(builder, [goal], active.clone());

        // --- PRED_BUS: verify predicate semantics (Phase 6-6a) ---
        // pred_active gates the lookup: 1 when predicate verification is needed,
        // 0 for steps without persistent predicate goals (e.g., linear-only steps).
        let pred_hash: AB::Expr = local[COL_PRED_HASH].clone().into();
        let pred_active: AB::Expr = local[COL_PRED_ACTIVE].clone().into();
        builder.assert_zero(pred_active.clone() * (pred_active.clone() - AB::Expr::ONE));
        PRED_BUS.lookup_key(builder, [pred_hash], active * pred_active);
    }
}
