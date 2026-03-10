//! ILL rule table — all ILL inference rules as RuleSpec constants.
//!
//! Each constant describes one rule's ZK chip behavior. Instantiate
//! with `RuleChip::new(ill::TENSOR_R)` to get a working AIR chip.
//!
//! Rule semantics match the CALC rule descriptors in calculus/ill/ill.rules.
//! The mapping is: descriptor fields → RuleSpec fields:
//!   - side="r", premises with succedent → oblig_receive + premises
//!   - side="l", 1 premise, context-only → ctx_receive + ctx_sends
//!   - side="l", 2 premises → oblig_receive + ctx_receive + premises
//!   - connective + arity → tag + formula_lookup
//!   - structural (copy) → gamma_lookup
//!
//! zero_l is excluded — it needs a specialized chip (ZeroLChip) for
//! context discarding via DISCARD_BUS. See chips/zero_l.rs.

use super::{CtxSend, PremiseSpec, RuleSpec, TypeRef};
use crate::tags;

/// All generic ILL rule specs (excludes zero_l which is specialized).
pub const ALL: &[RuleSpec] = &[
    ID, TENSOR_R, TENSOR_L, LOLI_R, LOLI_L, WITH_R, WITH_L1, WITH_L2,
    OPLUS_R1, OPLUS_R2, OPLUS_L, ONE_R, ONE_L, BANG_R, BANG_L,
    ABSORPTION, COPY, MONAD_R, MONAD_L, EXISTS_R, EXISTS_L, FORALL_R,
    FORALL_L,
];

// ---------------------------------------------------------------------------
// Identity axiom
// ---------------------------------------------------------------------------

/// id: A ⊢ A — consume obligation and context resource with same hash.
pub const ID: RuleSpec = RuleSpec {
    name: "id",
    tag: None,
    arity: 0,
    oblig_receive: true,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[],
    formula_lookup: false,
    gamma_lookup: false,
    is_identity: true,
};

// ---------------------------------------------------------------------------
// Multiplicative conjunction (tensor, ⊗)
// ---------------------------------------------------------------------------

/// tensor_r: G ; D, D' ⊢ A ⊗ B ← G ; D ⊢ A, G ; D' ⊢ B
/// Right intro, context split, 2 premises.
pub const TENSOR_R: RuleSpec = RuleSpec {
    name: "tensor_r",
    tag: Some(tags::TENSOR),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        PremiseSpec { succedent: TypeRef::Child(1), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// tensor_l: G ; D, A ⊗ B ⊢ C ← G ; D, A, B ⊢ C
/// Left decomposition, context-only. Receives compound, sends children.
pub const TENSOR_L: RuleSpec = RuleSpec {
    name: "tensor_l",
    tag: Some(tags::TENSOR),
    arity: 2,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0), CtxSend::Child(1)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Linear implication (loli, ⊸)
// ---------------------------------------------------------------------------

/// loli_r: G ; D ⊢ A ⊸ B ← G ; D, A ⊢ B
/// Right intro, adds child0 (A) to context, changes succedent to child1 (B).
pub const LOLI_R: RuleSpec = RuleSpec {
    name: "loli_r",
    tag: Some(tags::LOLI),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(1), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// loli_l: G ; D, D', A ⊸ B ⊢ C ← G ; D ⊢ A, G ; D', B ⊢ C
/// Left focus, context split, 2 premises. Consumes obligation + principal.
/// Premise 0: prove A (child0). Premise 1: prove C with B (child1) added.
pub const LOLI_L: RuleSpec = RuleSpec {
    name: "loli_l",
    tag: Some(tags::LOLI),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        PremiseSpec { succedent: TypeRef::Inherited, lax: None },
    ],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(1)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Additive conjunction (with, &)
// ---------------------------------------------------------------------------

/// with_r: G ; D ⊢ A & B ← G ; D ⊢ A, G ; D ⊢ B
/// Right intro, context copy, 2 premises. DupChip handles context duplication.
pub const WITH_R: RuleSpec = RuleSpec {
    name: "with_r",
    tag: Some(tags::WITH),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        PremiseSpec { succedent: TypeRef::Child(1), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// with_l1: G ; D, A & B ⊢ C ← G ; D, A ⊢ C
/// Left projection (first component). Context-only.
pub const WITH_L1: RuleSpec = RuleSpec {
    name: "with_l1",
    tag: Some(tags::WITH),
    arity: 2,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// with_l2: G ; D, A & B ⊢ C ← G ; D, B ⊢ C
/// Left projection (second component). Context-only.
pub const WITH_L2: RuleSpec = RuleSpec {
    name: "with_l2",
    tag: Some(tags::WITH),
    arity: 2,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(1)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Additive disjunction (oplus, ⊕)
// ---------------------------------------------------------------------------

/// oplus_r1: G ; D ⊢ A ⊕ B ← G ; D ⊢ A
/// Right injection (first). 1 premise, succedent becomes child0.
pub const OPLUS_R1: RuleSpec = RuleSpec {
    name: "oplus_r1",
    tag: Some(tags::OPLUS),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// oplus_r2: G ; D ⊢ A ⊕ B ← G ; D ⊢ B
/// Right injection (second). 1 premise, succedent becomes child1.
pub const OPLUS_R2: RuleSpec = RuleSpec {
    name: "oplus_r2",
    tag: Some(tags::OPLUS),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(1), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// oplus_l: G ; D, A ⊕ B ⊢ C ← G ; D, A ⊢ C, G ; D, B ⊢ C
/// Left case analysis, context copy, 2 premises. DupChip handles duplication.
/// Both premises inherit the goal. Adds child0 and child1 to respective branches.
pub const OPLUS_L: RuleSpec = RuleSpec {
    name: "oplus_l",
    tag: Some(tags::OPLUS),
    arity: 2,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Inherited, lax: None },
        PremiseSpec { succedent: TypeRef::Inherited, lax: None },
    ],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0), CtxSend::Child(1)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Multiplicative unit (one, I)
// ---------------------------------------------------------------------------

/// one_r: G ; · ⊢ I
/// Axiom, 0 premises. Consumes obligation for I. No context interaction
/// (emptyLinear enforced by bus balance — unmatched context sends fail).
pub const ONE_R: RuleSpec = RuleSpec {
    name: "one_r",
    tag: Some(tags::ONE),
    arity: 0,
    oblig_receive: true,
    premises: &[],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// one_l: G ; D, I ⊢ C ← G ; D ⊢ C
/// Left removal, context-only. Consumes I from context, nothing added.
pub const ONE_L: RuleSpec = RuleSpec {
    name: "one_l",
    tag: Some(tags::ONE),
    arity: 0,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Exponential (bang, !)
// ---------------------------------------------------------------------------

/// bang_r (promotion): G ; · ⊢ !A ← G ; · ⊢ A
/// Right intro, emptyLinear. 1 premise, succedent becomes child0.
pub const BANG_R: RuleSpec = RuleSpec {
    name: "bang_r",
    tag: Some(tags::BANG),
    arity: 1,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// bang_l (dereliction): G ; D, !A ⊢ C ← G ; D, A ⊢ C
/// Left decomposition, context-only. Strips ! and adds A to linear context.
pub const BANG_L: RuleSpec = RuleSpec {
    name: "bang_l",
    tag: Some(tags::BANG),
    arity: 1,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// absorption: G ; D, !A ⊢ C ← G, A ; D ⊢ C
/// Left decomposition, moves A to cartesian zone (gamma). Context-only.
/// Does NOT send A back to CONTEXT — A becomes available via gamma ROM + copy.
pub const ABSORPTION: RuleSpec = RuleSpec {
    name: "absorption",
    tag: Some(tags::BANG),
    arity: 1,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// copy: G, A ; D ⊢ C ← G, A ; D, A ⊢ C
/// Structural rule. Copies A from gamma zone to linear context.
/// GAMMA lookup verifies membership, CONTEXT send introduces copy.
pub const COPY: RuleSpec = RuleSpec {
    name: "copy",
    tag: None,
    arity: 0,
    oblig_receive: false,
    premises: &[],
    ctx_receive: false,
    ctx_sends: &[CtxSend::Hash],
    formula_lookup: false,
    gamma_lookup: true,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Lax monad ({_})
// ---------------------------------------------------------------------------

/// monad_r (guided): G ; D ⊢ {A} — mode shift, produces inner obligation with lax=1.
/// Consumes obligation for {A}, produces obligation for A with lax=1.
pub const MONAD_R: RuleSpec = RuleSpec {
    name: "monad_r",
    tag: Some(tags::MONAD),
    arity: 1,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: Some(1) },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// monad_l: G ; D, {A} ⊢ {C} ← G ; D, A ⊢ {C}
/// Left decomposition, context-only. Strips {} and adds A to linear context.
/// requiresSuccedentTag="monad" is a prover hint, not a circuit constraint —
/// bus balance enforces correctness regardless.
pub const MONAD_L: RuleSpec = RuleSpec {
    name: "monad_l",
    tag: Some(tags::MONAD),
    arity: 1,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

// ---------------------------------------------------------------------------
// Quantifiers (exists, forall)
// ---------------------------------------------------------------------------

/// exists_r: G ; D ⊢ ∃A ← G ; D ⊢ A[t/x]
/// Right intro, 1 premise, succedent becomes instantiated body (child0).
/// Substitution correctness embedded in formula ROM (Phase 3: committed).
pub const EXISTS_R: RuleSpec = RuleSpec {
    name: "exists_r",
    tag: Some(tags::EXISTS),
    arity: 1,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// exists_l: G ; D, ∃A ⊢ C ← G ; D, A[a/x] ⊢ C
/// Left decomposition, context-only. Opens body with eigenvariable.
pub const EXISTS_L: RuleSpec = RuleSpec {
    name: "exists_l",
    tag: Some(tags::EXISTS),
    arity: 1,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// forall_r: G ; D ⊢ ∀A ← G ; D ⊢ A[a/x]
/// Right intro, 1 premise, succedent becomes instantiated body (child0).
pub const FORALL_R: RuleSpec = RuleSpec {
    name: "forall_r",
    tag: Some(tags::FORALL),
    arity: 1,
    oblig_receive: true,
    premises: &[
        PremiseSpec { succedent: TypeRef::Child(0), lax: None },
    ],
    ctx_receive: false,
    ctx_sends: &[],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};

/// forall_l: G ; D, ∀A ⊢ C ← G ; D, A[t/x] ⊢ C
/// Left decomposition, context-only. Opens body with metavariable.
pub const FORALL_L: RuleSpec = RuleSpec {
    name: "forall_l",
    tag: Some(tags::FORALL),
    arity: 1,
    oblig_receive: false,
    premises: &[],
    ctx_receive: true,
    ctx_sends: &[CtxSend::Child(0)],
    formula_lookup: true,
    gamma_lookup: false,
    is_identity: false,
};
