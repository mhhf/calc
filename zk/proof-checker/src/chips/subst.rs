//! SubstChip: substitution bridge for loli bodies with freevars.
//!
//! When a loli fact contains unresolved freevars in its body (e.g., sha3's
//! `_Bytes`), the Store.child decomposition yields different hashes than the
//! ground values produced by the forward engine. The SubstChip bridges this
//! gap via per-node tree verification rows.
//!
//! Phase 3b.6: recursive tree matching verification.
//!
//! Each substitution instance produces multiple rows — one per syntax tree
//! node in the old/new formula pair. The root is always a loli node; only
//! the antecedent child (c0) is recursively verified. The body child (c1)
//! is NOT verified here — it's separately validated by loli_l/monad_l/tensor_l
//! chips, since the body structure may differ between pattern and ground.
//!
//! Row types:
//! - **Root row** (is_root=1): CONTEXT_BUS receive old, send new.
//!   FORMULA_BUS decomposes both. Only c0 (antecedent) gets tree-verified.
//! - **Non-root internal** (is_root=0, is_freevar=0): FORMULA_BUS decompose
//!   both sides (same tag), SUBST_TREE_BUS for all differing children.
//! - **Freevar leaf** (is_freevar=1): FORMULA_BUS verify old is freevar,
//!   FREEVAR_BUS lookup for consistency.
//!
//! Columns (width 15):
//!   [0]  is_active
//!   [1]  hash_old
//!   [2]  hash_new
//!   [3]  is_root
//!   [4]  is_freevar
//!   [5]  subst_id
//!   [6]  tag
//!   [7]  c0_old
//!   [8]  c1_old
//!   [9]  c0_new
//!   [10] c1_new
//!   [11] c0_eq
//!   [12] c1_eq
//!   [13] is_internal     — precomputed: is_active * (1 - is_freevar)
//!   [14] non_root_int    — precomputed: is_internal * (1 - is_root)

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, FORMULA_BUS, FREEVAR_BUS, SUBST_TREE_BUS};

pub const WIDTH: usize = 15;

const COL_ACTIVE: usize = 0;
const COL_HASH_OLD: usize = 1;
const COL_HASH_NEW: usize = 2;
const COL_IS_ROOT: usize = 3;
const COL_IS_FREEVAR: usize = 4;
const COL_SUBST_ID: usize = 5;
const COL_TAG: usize = 6;
const COL_C0_OLD: usize = 7;
const COL_C1_OLD: usize = 8;
const COL_C0_NEW: usize = 9;
const COL_C1_NEW: usize = 10;
const COL_C0_EQ: usize = 11;
const COL_C1_EQ: usize = 12;
const COL_IS_INTERNAL: usize = 13;
const COL_NON_ROOT_INT: usize = 14;

pub struct SubstChip;

impl<F> BaseAir<F> for SubstChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for SubstChip {}
impl<F> PartitionedBaseAir<F> for SubstChip {}

impl<AB: InteractionBuilder> Air<AB> for SubstChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let hash_old: AB::Expr = local[COL_HASH_OLD].clone().into();
        let hash_new: AB::Expr = local[COL_HASH_NEW].clone().into();
        let is_root: AB::Expr = local[COL_IS_ROOT].clone().into();
        let is_freevar: AB::Expr = local[COL_IS_FREEVAR].clone().into();
        let subst_id: AB::Expr = local[COL_SUBST_ID].clone().into();
        let tag: AB::Expr = local[COL_TAG].clone().into();
        let c0_old: AB::Expr = local[COL_C0_OLD].clone().into();
        let c1_old: AB::Expr = local[COL_C1_OLD].clone().into();
        let c0_new: AB::Expr = local[COL_C0_NEW].clone().into();
        let c1_new: AB::Expr = local[COL_C1_NEW].clone().into();
        let c0_eq: AB::Expr = local[COL_C0_EQ].clone().into();
        let c1_eq: AB::Expr = local[COL_C1_EQ].clone().into();
        let is_internal: AB::Expr = local[COL_IS_INTERNAL].clone().into();
        let non_root_int: AB::Expr = local[COL_NON_ROOT_INT].clone().into();

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_root.clone() * (is_root.clone() - AB::Expr::ONE));
        builder.assert_zero(is_freevar.clone() * (is_freevar.clone() - AB::Expr::ONE));
        builder.assert_zero(c0_eq.clone() * (c0_eq.clone() - AB::Expr::ONE));
        builder.assert_zero(c1_eq.clone() * (c1_eq.clone() - AB::Expr::ONE));
        builder.assert_zero(is_internal.clone() * (is_internal.clone() - AB::Expr::ONE));
        builder.assert_zero(non_root_int.clone() * (non_root_int.clone() - AB::Expr::ONE));

        // Mutual exclusions
        builder.assert_zero(is_root.clone() * is_freevar.clone());

        // Precomputed column correctness
        // is_internal = is_active * (1 - is_freevar)
        builder.assert_zero(
            is_internal.clone() - is_active.clone() * (AB::Expr::ONE - is_freevar.clone()),
        );
        // non_root_int = is_internal * (1 - is_root)
        builder.assert_zero(
            non_root_int.clone() - is_internal.clone() * (AB::Expr::ONE - is_root.clone()),
        );

        // --- c0_eq / c1_eq correctness ---
        // c0_eq: checked for ALL internal nodes (root and non-root)
        builder.assert_zero(
            is_internal.clone() * c0_eq.clone() * (c0_old.clone() - c0_new.clone()),
        );
        // c1_eq: checked only for NON-ROOT internal nodes
        // At root (loli node), c1 is the body which may have different structure
        builder.assert_zero(
            non_root_int.clone() * c1_eq.clone() * (c1_old.clone() - c1_new.clone()),
        );

        // --- CONTEXT_BUS: root rows swap old→new ---
        CONTEXT_BUS.receive(builder, [hash_old.clone()], is_active.clone() * is_root.clone());
        CONTEXT_BUS.send(builder, [hash_new.clone()], is_active.clone() * is_root.clone());

        // --- SUBST_TREE_BUS ---
        // Non-root rows: receive demand from parent
        SUBST_TREE_BUS.receive(
            builder,
            [subst_id.clone(), hash_old.clone(), hash_new.clone()],
            is_active.clone() * (AB::Expr::ONE - is_root.clone()),
        );

        // c0: ALL internal nodes send for differing child0
        SUBST_TREE_BUS.send(
            builder,
            [subst_id.clone(), c0_old.clone(), c0_new.clone()],
            is_internal.clone() * (AB::Expr::ONE - c0_eq.clone()),
        );
        // c1: only NON-ROOT internal nodes send for differing child1
        // Root nodes skip c1 verification (body has different structure)
        SUBST_TREE_BUS.send(
            builder,
            [subst_id.clone(), c1_old.clone(), c1_new.clone()],
            non_root_int.clone() * (AB::Expr::ONE - c1_eq.clone()),
        );

        // --- FORMULA_BUS: structural verification ---
        // Internal nodes: both old and new must decompose with the same tag
        FORMULA_BUS.lookup_key(
            builder,
            [hash_old.clone(), tag.clone(), c0_old, c1_old],
            is_internal.clone(),
        );
        FORMULA_BUS.lookup_key(
            builder,
            [hash_new.clone(), tag.clone(), c0_new, c1_new],
            is_internal,
        );

        // Freevar leaf: verify old_hash is a freevar in FORMULA_BUS
        FORMULA_BUS.lookup_key(
            builder,
            [hash_old.clone(), tag, local[COL_C0_OLD].clone().into(), AB::Expr::ZERO],
            is_active.clone() * is_freevar.clone(),
        );

        // --- FREEVAR_BUS: consistency check ---
        FREEVAR_BUS.lookup_key(
            builder,
            [subst_id, hash_old, hash_new],
            is_active * is_freevar,
        );
    }
}
