//! ILL rule table — all ILL inference rules as RuleSpec values.
//!
//! Each function returns a RuleSpec describing one rule's ZK chip behavior.
//! Instantiate with `RuleChip::new(ill::tensor_r())` to get a working AIR chip.
//!
//! These definitions use hardcoded tag constants from `tags.rs` and are
//! intended for Phase 2 unit tests. The e2e path (bridge.rs) reads rule
//! specs from the witness JSON — no ILL-specific code in the verification path.
//!
//! zero_l is excluded — it needs a specialized chip (ZeroLChip) for
//! context discarding via DISCARD_BUS. See chips/zero_l.rs.

use super::{CtxSend, PremiseSpec, RuleSpec, TypeRef};
use crate::tags;

/// All generic ILL rule specs (excludes zero_l which is specialized).
pub fn all() -> Vec<RuleSpec> {
    vec![
        id(), tensor_r(), tensor_l(), loli_r(), loli_l(), with_r(), with_l1(), with_l2(),
        oplus_r1(), oplus_r2(), oplus_l(), one_r(), one_l(), bang_r(), bang_l(),
        absorption(), copy(), monad_r(), monad_l(), exists_r(), exists_l(), forall_r(),
        forall_l(),
    ]
}

// ---------------------------------------------------------------------------
// Identity axiom
// ---------------------------------------------------------------------------

/// id: A ⊢ A — consume obligation and context resource with same hash.
pub fn id() -> RuleSpec {
    RuleSpec {
        name: "id".into(),
        tag: None,
        arity: 0,
        oblig_receive: true,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![],
        formula_lookup: false,
        gamma_lookup: false,
        is_identity: true,
    }
}

// ---------------------------------------------------------------------------
// Multiplicative conjunction (tensor, ⊗)
// ---------------------------------------------------------------------------

/// tensor_r: G ; D, D' ⊢ A ⊗ B ← G ; D ⊢ A, G ; D' ⊢ B
pub fn tensor_r() -> RuleSpec {
    RuleSpec {
        name: "tensor_r".into(),
        tag: Some(tags::TENSOR),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
            PremiseSpec { succedent: TypeRef::Child(1), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// tensor_l: G ; D, A ⊗ B ⊢ C ← G ; D, A, B ⊢ C
pub fn tensor_l() -> RuleSpec {
    RuleSpec {
        name: "tensor_l".into(),
        tag: Some(tags::TENSOR),
        arity: 2,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0), CtxSend::Child(1)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Linear implication (loli, ⊸)
// ---------------------------------------------------------------------------

/// loli_r: G ; D ⊢ A ⊸ B ← G ; D, A ⊢ B
pub fn loli_r() -> RuleSpec {
    RuleSpec {
        name: "loli_r".into(),
        tag: Some(tags::LOLI),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(1), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// loli_l: G ; D, D', A ⊸ B ⊢ C ← G ; D ⊢ A, G ; D', B ⊢ C
pub fn loli_l() -> RuleSpec {
    RuleSpec {
        name: "loli_l".into(),
        tag: Some(tags::LOLI),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
            PremiseSpec { succedent: TypeRef::Inherited, lax: None },
        ],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(1)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Additive conjunction (with, &)
// ---------------------------------------------------------------------------

/// with_r: G ; D ⊢ A & B ← G ; D ⊢ A, G ; D ⊢ B
pub fn with_r() -> RuleSpec {
    RuleSpec {
        name: "with_r".into(),
        tag: Some(tags::WITH),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
            PremiseSpec { succedent: TypeRef::Child(1), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// with_l1: G ; D, A & B ⊢ C ← G ; D, A ⊢ C
pub fn with_l1() -> RuleSpec {
    RuleSpec {
        name: "with_l1".into(),
        tag: Some(tags::WITH),
        arity: 2,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// with_l2: G ; D, A & B ⊢ C ← G ; D, B ⊢ C
pub fn with_l2() -> RuleSpec {
    RuleSpec {
        name: "with_l2".into(),
        tag: Some(tags::WITH),
        arity: 2,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(1)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Additive disjunction (oplus, ⊕)
// ---------------------------------------------------------------------------

/// oplus_r1: G ; D ⊢ A ⊕ B ← G ; D ⊢ A
pub fn oplus_r1() -> RuleSpec {
    RuleSpec {
        name: "oplus_r1".into(),
        tag: Some(tags::OPLUS),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// oplus_r2: G ; D ⊢ A ⊕ B ← G ; D ⊢ B
pub fn oplus_r2() -> RuleSpec {
    RuleSpec {
        name: "oplus_r2".into(),
        tag: Some(tags::OPLUS),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(1), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// oplus_l: G ; D, A ⊕ B ⊢ C ← G ; D, A ⊢ C, G ; D, B ⊢ C
pub fn oplus_l() -> RuleSpec {
    RuleSpec {
        name: "oplus_l".into(),
        tag: Some(tags::OPLUS),
        arity: 2,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Inherited, lax: None },
            PremiseSpec { succedent: TypeRef::Inherited, lax: None },
        ],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0), CtxSend::Child(1)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Multiplicative unit (one, I)
// ---------------------------------------------------------------------------

/// one_r: G ; · ⊢ I
pub fn one_r() -> RuleSpec {
    RuleSpec {
        name: "one_r".into(),
        tag: Some(tags::ONE),
        arity: 0,
        oblig_receive: true,
        premises: vec![],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// one_l: G ; D, I ⊢ C ← G ; D ⊢ C
pub fn one_l() -> RuleSpec {
    RuleSpec {
        name: "one_l".into(),
        tag: Some(tags::ONE),
        arity: 0,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Exponential (bang, !)
// ---------------------------------------------------------------------------

/// bang_r (promotion): G ; · ⊢ !A ← G ; · ⊢ A
pub fn bang_r() -> RuleSpec {
    RuleSpec {
        name: "bang_r".into(),
        tag: Some(tags::BANG),
        arity: 1,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// bang_l (dereliction): G ; D, !A ⊢ C ← G ; D, A ⊢ C
pub fn bang_l() -> RuleSpec {
    RuleSpec {
        name: "bang_l".into(),
        tag: Some(tags::BANG),
        arity: 1,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// absorption: G ; D, !A ⊢ C ← G, A ; D ⊢ C
pub fn absorption() -> RuleSpec {
    RuleSpec {
        name: "absorption".into(),
        tag: Some(tags::BANG),
        arity: 1,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// copy: G, A ; D ⊢ C ← G, A ; D, A ⊢ C
pub fn copy() -> RuleSpec {
    RuleSpec {
        name: "copy".into(),
        tag: None,
        arity: 0,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: false,
        ctx_sends: vec![CtxSend::Hash],
        formula_lookup: false,
        gamma_lookup: true,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Lax monad ({_})
// ---------------------------------------------------------------------------

/// monad_r (guided): G ; D ⊢ {A} — produces inner obligation with lax=1.
pub fn monad_r() -> RuleSpec {
    RuleSpec {
        name: "monad_r".into(),
        tag: Some(tags::MONAD),
        arity: 1,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: Some(1) },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// monad_l: G ; D, {A} ⊢ {C} ← G ; D, A ⊢ {C}
pub fn monad_l() -> RuleSpec {
    RuleSpec {
        name: "monad_l".into(),
        tag: Some(tags::MONAD),
        arity: 1,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

// ---------------------------------------------------------------------------
// Quantifiers (exists, forall)
// ---------------------------------------------------------------------------

/// exists_r: G ; D ⊢ ∃A ← G ; D ⊢ A[t/x]
pub fn exists_r() -> RuleSpec {
    RuleSpec {
        name: "exists_r".into(),
        tag: Some(tags::EXISTS),
        arity: 1,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// exists_l: G ; D, ∃A ⊢ C ← G ; D, A[a/x] ⊢ C
pub fn exists_l() -> RuleSpec {
    RuleSpec {
        name: "exists_l".into(),
        tag: Some(tags::EXISTS),
        arity: 1,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// forall_r: G ; D ⊢ ∀A ← G ; D ⊢ A[a/x]
pub fn forall_r() -> RuleSpec {
    RuleSpec {
        name: "forall_r".into(),
        tag: Some(tags::FORALL),
        arity: 1,
        oblig_receive: true,
        premises: vec![
            PremiseSpec { succedent: TypeRef::Child(0), lax: None },
        ],
        ctx_receive: false,
        ctx_sends: vec![],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}

/// forall_l: G ; D, ∀A ⊢ C ← G ; D, A[t/x] ⊢ C
pub fn forall_l() -> RuleSpec {
    RuleSpec {
        name: "forall_l".into(),
        tag: Some(tags::FORALL),
        arity: 1,
        oblig_receive: false,
        premises: vec![],
        ctx_receive: true,
        ctx_sends: vec![CtxSend::Child(0)],
        formula_lookup: true,
        gamma_lookup: false,
        is_identity: false,
    }
}
