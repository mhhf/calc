//! FlatStepChip: per-step resource accounting + rule verification for flat
//! rewriting certificates.
//!
//! Each row represents one forward execution step. Consumed facts are
//! received from CONTEXT_BUS, produced facts are sent to CONTEXT_BUS.
//! For compiled rules (is_loli=0), ground_loli is looked up in GAMMA_BUS.
//! For loli matches (is_loli=1), ground_loli is consumed from CONTEXT_BUS.
//!
//! Phase 3b: FORMULA_BUS tensor spine verification for compiled rules.
//! For compiled rules: ground_loli = loli(ant_hash, monad(cons_hash)) and
//! ant_hash/cons_hash are right-associated tensor trees matching the
//! consumed/produced slots.
//! For loli matches: ant_hash/cons_hash are the original loli's pattern
//! (may have metavariables). The antecedent uses ground_ant (right-associated
//! tensor of consumed) with spine verification + SUBST_TREE_BUS demand.
//! The body uses per-leaf SUBST_TREE_BUS demands: each produced fact is
//! paired with its corresponding body leaf pattern (from flattening the
//! consHash tensor tree). This avoids tensor association mismatches since
//! body leaves and produced facts always have matching tree structure.
//!
//! Layout (width 48):
//!   [0]     active
//!   [1]     is_loli          — 1 = loli match (consume from ctx, no gamma)
//!   [2]     ground_loli      — ground loli hash
//!   [3..8]  consumed_0..5    — consumed fact hashes (trigger facts only)
//!   [9..14] consumed_active  — per-slot boolean flags
//!   [15..20] produced_0..5   — produced fact hashes
//!   [21..26] produced_active — per-slot boolean flags
//!   [27]    ant_hash         — antecedent tensor tree root (pattern, may have freevars)
//!   [28..31] ant_i1..ant_i4  — antecedent spine intermediates
//!   [32]    cons_hash        — consequent tensor tree root (pattern, may have freevars)
//!   [33..36] cons_i1..cons_i4 — consequent spine intermediates
//!   [37]    monad_hash       — monad(cons_hash)
//!   [38]    compiled         — active * (1 - is_loli), auxiliary for degree reduction
//!   [39]    ground_ant       — ground antecedent hash = tensor(consumed slots)
//!   [40]    ground_cons      — (unused for loli, used for compiled spine)
//!   [41]    subst_id         — substitution instance ID for SUBST_TREE_BUS
//!   [42..47] body_leaf_0..5  — body leaf pattern hashes for per-leaf SubstChip verification
//!   [48..53] body_diff_0..5  — boolean: 1 when body_leaf differs from produced AND structurally compatible

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, FORMULA_BUS, GAMMA_BUS, SUBST_TREE_BUS};

pub const MAX_CONSUMED: usize = 6;
pub const MAX_PRODUCED: usize = 6;

const COL_ACTIVE: usize = 0;
const COL_IS_LOLI: usize = 1;
const COL_GROUND_LOLI: usize = 2;
const COL_CONSUMED: usize = 3;
const COL_CONSUMED_ACTIVE: usize = COL_CONSUMED + MAX_CONSUMED;     // 9
const COL_PRODUCED: usize = COL_CONSUMED_ACTIVE + MAX_CONSUMED;     // 15
const COL_PRODUCED_ACTIVE: usize = COL_PRODUCED + MAX_PRODUCED;     // 21
const COL_ANT_HASH: usize = COL_PRODUCED_ACTIVE + MAX_PRODUCED;     // 27
const COL_ANT_I1: usize = COL_ANT_HASH + 1;                        // 28
const COL_CONS_HASH: usize = COL_ANT_I1 + (MAX_CONSUMED - 2);      // 32
const COL_CONS_I1: usize = COL_CONS_HASH + 1;                       // 33
const COL_MONAD_HASH: usize = COL_CONS_I1 + (MAX_PRODUCED - 2);     // 37
const COL_COMPILED: usize = COL_MONAD_HASH + 1;                     // 38
const COL_GROUND_ANT: usize = COL_COMPILED + 1;                     // 39
const COL_GROUND_CONS: usize = COL_GROUND_ANT + 1;                  // 40
const COL_SUBST_ID: usize = COL_GROUND_CONS + 1;                    // 41
const COL_BODY_LEAF: usize = COL_SUBST_ID + 1;                      // 42
const COL_BODY_DIFF: usize = COL_BODY_LEAF + MAX_PRODUCED;          // 48
pub const WIDTH: usize = COL_BODY_DIFF + MAX_PRODUCED;               // 54

/// FlatStepChip with tag constants for FORMULA_BUS lookups.
pub struct FlatStepChip {
    pub loli_tag: u32,
    pub monad_tag: u32,
    pub tensor_tag: u32,
    pub one_hash: u32,
}

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
        let ant_hash: AB::Expr = local[COL_ANT_HASH].clone().into();
        let cons_hash: AB::Expr = local[COL_CONS_HASH].clone().into();
        let monad_hash: AB::Expr = local[COL_MONAD_HASH].clone().into();

        let compiled: AB::Expr = local[COL_COMPILED].clone().into();
        let ground_ant: AB::Expr = local[COL_GROUND_ANT].clone().into();
        let _ground_cons: AB::Expr = local[COL_GROUND_CONS].clone().into();
        let subst_id: AB::Expr = local[COL_SUBST_ID].clone().into();

        let loli_tag: AB::Expr = AB::Expr::from_u32(self.loli_tag);
        let monad_tag: AB::Expr = AB::Expr::from_u32(self.monad_tag);
        let tensor_tag: AB::Expr = AB::Expr::from_u32(self.tensor_tag);
        let one_hash: AB::Expr = AB::Expr::from_u32(self.one_hash);

        // Boolean constraints
        builder.assert_zero(active.clone() * (active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_loli.clone() * (is_loli.clone() - AB::Expr::ONE));
        // `compiled` is a product of two booleans, so already boolean by construction.
        // Explicit check retained as defense-in-depth against witness generation bugs.
        builder.assert_zero(compiled.clone() * (compiled.clone() - AB::Expr::ONE));

        // compiled = active * (1 - is_loli): stored as a trace column to keep max
        // constraint degree at 4 (vs 5 if computed inline in spine boundary checks)
        builder.assert_zero(
            compiled.clone() - active.clone() * (AB::Expr::ONE - is_loli.clone()),
        );

        // Read consumed/produced slots + actives
        let mut c = Vec::with_capacity(MAX_CONSUMED);
        let mut ca = Vec::with_capacity(MAX_CONSUMED);
        for i in 0..MAX_CONSUMED {
            c.push(local[COL_CONSUMED + i].clone().into());
            let slot_active: AB::Expr = local[COL_CONSUMED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            ca.push(slot_active);
        }

        let mut p = Vec::with_capacity(MAX_PRODUCED);
        let mut pa = Vec::with_capacity(MAX_PRODUCED);
        for i in 0..MAX_PRODUCED {
            p.push(local[COL_PRODUCED + i].clone().into());
            let slot_active: AB::Expr = local[COL_PRODUCED_ACTIVE + i].clone().into();
            builder.assert_zero(slot_active.clone() * (slot_active.clone() - AB::Expr::ONE));
            pa.push(slot_active);
        }

        // Read spine intermediates
        let mut ant_intermediates: Vec<AB::Expr> = Vec::with_capacity(MAX_CONSUMED - 2);
        for i in 0..(MAX_CONSUMED - 2) {
            ant_intermediates.push(local[COL_ANT_I1 + i].clone().into());
        }
        let mut cons_intermediates: Vec<AB::Expr> = Vec::with_capacity(MAX_PRODUCED - 2);
        for i in 0..(MAX_PRODUCED - 2) {
            cons_intermediates.push(local[COL_CONS_I1 + i].clone().into());
        }

        // --- CONTEXT_BUS interactions ---

        // Consumed facts: receive from CONTEXT_BUS (trigger facts only)
        for i in 0..MAX_CONSUMED {
            CONTEXT_BUS.receive(builder, [c[i].clone()], active.clone() * ca[i].clone());
        }

        // Loli match: consume the loli itself from context (separate from consumed slots)
        CONTEXT_BUS.receive(builder, [ground_loli.clone()], active.clone() * is_loli.clone());

        // Produced facts: send to CONTEXT_BUS
        for i in 0..MAX_PRODUCED {
            CONTEXT_BUS.send(builder, [p[i].clone()], active.clone() * pa[i].clone());
        }

        // --- GAMMA_BUS: compiled rules only ---
        GAMMA_BUS.lookup_key(builder, [ground_loli.clone()], compiled.clone());

        // --- FORMULA_BUS: rule structure verification ---

        // 1. Loli decomposition: ground_loli = loli(ant_hash, monad_hash)
        //    Fires for ALL active rows. For compiled rules, ant_hash/monad_hash are
        //    computed from consumed/produced. For loli matches, they come from the
        //    original loli's Store decomposition.
        FORMULA_BUS.lookup_key(
            builder,
            [ground_loli, loli_tag, ant_hash.clone(), monad_hash.clone()],
            active.clone(),
        );

        // 2. Monad unwrap: monad_hash = monad(cons_hash, 0)
        FORMULA_BUS.lookup_key(
            builder,
            [monad_hash, monad_tag, cons_hash.clone(), AB::Expr::ZERO],
            active.clone(),
        );

        // 3. Antecedent tensor spine verification — COMPILED RULES ONLY
        //    (Loli matches skip spine verification since the original loli's
        //    antecedent may contain metavariables that don't match ground triggers.)

        // When consumed_count == 0: ant_hash must equal one_hash
        builder.assert_zero(
            compiled.clone() * (AB::Expr::ONE - ca[0].clone()) * (ant_hash.clone() - one_hash.clone()),
        );
        // When consumed_count == 1: ant_hash must equal c0
        builder.assert_zero(
            compiled.clone() * ca[0].clone() * (AB::Expr::ONE - ca[1].clone()) * (ant_hash.clone() - c[0].clone()),
        );
        // Spine lookups for consumed_count >= 2:
        FORMULA_BUS.lookup_key(
            builder,
            [ant_hash.clone(), tensor_tag.clone(), c[0].clone(), ant_intermediates[0].clone()],
            compiled.clone() * ca[1].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[0].clone(), tensor_tag.clone(), c[1].clone(), ant_intermediates[1].clone()],
            compiled.clone() * ca[2].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[1].clone(), tensor_tag.clone(), c[2].clone(), ant_intermediates[2].clone()],
            compiled.clone() * ca[3].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[2].clone(), tensor_tag.clone(), c[3].clone(), ant_intermediates[3].clone()],
            compiled.clone() * ca[4].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[3].clone(), tensor_tag.clone(), c[4].clone(), c[5].clone()],
            compiled.clone() * ca[5].clone(),
        );
        // Boundary equality: last intermediate = last consumed fact
        builder.assert_zero(
            compiled.clone() * ca[1].clone() * (AB::Expr::ONE - ca[2].clone())
                * (ant_intermediates[0].clone() - c[1].clone()),
        );
        builder.assert_zero(
            compiled.clone() * ca[2].clone() * (AB::Expr::ONE - ca[3].clone())
                * (ant_intermediates[1].clone() - c[2].clone()),
        );
        builder.assert_zero(
            compiled.clone() * ca[3].clone() * (AB::Expr::ONE - ca[4].clone())
                * (ant_intermediates[2].clone() - c[3].clone()),
        );
        builder.assert_zero(
            compiled.clone() * ca[4].clone() * (AB::Expr::ONE - ca[5].clone())
                * (ant_intermediates[3].clone() - c[4].clone()),
        );

        // 4. Consequent tensor spine verification — COMPILED RULES ONLY
        builder.assert_zero(
            compiled.clone() * (AB::Expr::ONE - pa[0].clone()) * (cons_hash.clone() - one_hash.clone()),
        );
        builder.assert_zero(
            compiled.clone() * pa[0].clone() * (AB::Expr::ONE - pa[1].clone()) * (cons_hash.clone() - p[0].clone()),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [cons_hash.clone(), tensor_tag.clone(), p[0].clone(), cons_intermediates[0].clone()],
            compiled.clone() * pa[1].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [cons_intermediates[0].clone(), tensor_tag.clone(), p[1].clone(), cons_intermediates[1].clone()],
            compiled.clone() * pa[2].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [cons_intermediates[1].clone(), tensor_tag.clone(), p[2].clone(), cons_intermediates[2].clone()],
            compiled.clone() * pa[3].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [cons_intermediates[2].clone(), tensor_tag.clone(), p[3].clone(), cons_intermediates[3].clone()],
            compiled.clone() * pa[4].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [cons_intermediates[3].clone(), tensor_tag.clone(), p[4].clone(), p[5].clone()],
            compiled.clone() * pa[5].clone(),
        );
        builder.assert_zero(
            compiled.clone() * pa[1].clone() * (AB::Expr::ONE - pa[2].clone())
                * (cons_intermediates[0].clone() - p[1].clone()),
        );
        builder.assert_zero(
            compiled.clone() * pa[2].clone() * (AB::Expr::ONE - pa[3].clone())
                * (cons_intermediates[1].clone() - p[2].clone()),
        );
        builder.assert_zero(
            compiled.clone() * pa[3].clone() * (AB::Expr::ONE - pa[4].clone())
                * (cons_intermediates[2].clone() - p[3].clone()),
        );
        builder.assert_zero(
            compiled.clone() * pa[4].clone() * (AB::Expr::ONE - pa[5].clone())
                * (cons_intermediates[3].clone() - p[4].clone()),
        );

        // 5. Loli antecedent spine: ground_ant = tensor(c[0], tensor(c[1], ...))
        //    Same pattern as compiled spine (sections 3-4) but:
        //    - Gated on loli_active instead of compiled
        //    - Targets ground_ant/ground_cons instead of ant_hash/cons_hash
        //    Uses (active - compiled) = active * is_loli without adding a column.
        let loli_active = active.clone() - compiled;

        // Antecedent spine boundary + lookups (loli rows)
        builder.assert_zero(
            loli_active.clone() * (AB::Expr::ONE - ca[0].clone()) * (ground_ant.clone() - one_hash.clone()),
        );
        builder.assert_zero(
            loli_active.clone() * ca[0].clone() * (AB::Expr::ONE - ca[1].clone()) * (ground_ant.clone() - c[0].clone()),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ground_ant.clone(), tensor_tag.clone(), c[0].clone(), ant_intermediates[0].clone()],
            loli_active.clone() * ca[1].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[0].clone(), tensor_tag.clone(), c[1].clone(), ant_intermediates[1].clone()],
            loli_active.clone() * ca[2].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[1].clone(), tensor_tag.clone(), c[2].clone(), ant_intermediates[2].clone()],
            loli_active.clone() * ca[3].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[2].clone(), tensor_tag.clone(), c[3].clone(), ant_intermediates[3].clone()],
            loli_active.clone() * ca[4].clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [ant_intermediates[3].clone(), tensor_tag.clone(), c[4].clone(), c[5].clone()],
            loli_active.clone() * ca[5].clone(),
        );
        builder.assert_zero(
            loli_active.clone() * ca[1].clone() * (AB::Expr::ONE - ca[2].clone())
                * (ant_intermediates[0].clone() - c[1].clone()),
        );
        builder.assert_zero(
            loli_active.clone() * ca[2].clone() * (AB::Expr::ONE - ca[3].clone())
                * (ant_intermediates[1].clone() - c[2].clone()),
        );
        builder.assert_zero(
            loli_active.clone() * ca[3].clone() * (AB::Expr::ONE - ca[4].clone())
                * (ant_intermediates[2].clone() - c[3].clone()),
        );
        builder.assert_zero(
            loli_active.clone() * ca[4].clone() * (AB::Expr::ONE - ca[5].clone())
                * (ant_intermediates[3].clone() - c[4].clone()),
        );

        // 6. Loli body verification: per-leaf SUBST_TREE_BUS demands.
        //    Each produced fact is paired with its corresponding body leaf pattern
        //    (extracted by flattening the consHash tensor tree in the witness).
        //    body_diff[i] is 1 when body_leaf[i] differs from p[i] AND is
        //    structurally compatible for SubstChip verification.
        let mut body_leaf: Vec<AB::Expr> = Vec::with_capacity(MAX_PRODUCED);
        let mut body_diff: Vec<AB::Expr> = Vec::with_capacity(MAX_PRODUCED);
        for i in 0..MAX_PRODUCED {
            body_leaf.push(local[COL_BODY_LEAF + i].clone().into());
            let bd: AB::Expr = local[COL_BODY_DIFF + i].clone().into();
            builder.assert_zero(bd.clone() * (bd.clone() - AB::Expr::ONE));
            body_diff.push(bd);
        }

        // 7. SUBST_TREE_BUS: demand matching verification for loli rows.
        //    Antecedent: single demand for ant_hash → ground_ant.
        SUBST_TREE_BUS.send(
            builder,
            [subst_id.clone(), ant_hash, ground_ant],
            loli_active.clone(),
        );
        //    Body: per-leaf demands, gated by body_diff (only when structurally verifiable).
        for i in 0..MAX_PRODUCED {
            SUBST_TREE_BUS.send(
                builder,
                [subst_id.clone(), body_leaf[i].clone(), p[i].clone()],
                loli_active.clone() * body_diff[i].clone(),
            );
        }
    }
}
