//! Generic rule chip — a single parameterized AIR for any sequent calculus rule.
//!
//! A `RuleSpec` describes a rule's bus interactions declaratively:
//! which obligations it consumes/produces, which context elements it
//! moves, which formula lookups it performs. The `RuleChip` implements
//! the Air trait by reading the spec and emitting appropriate constraints.
//!
//! Adding a new rule = adding a `RuleSpec` value.
//! Adding a new calculus = deriving rule specs from `.rules` descriptors.
//!
//! Column layout is computed automatically from the spec — no manual
//! column index bookkeeping. The layout assigns columns in a fixed
//! order: [is_active, hash, child0, child1, nonce_in, lax, nonce_outs..., goal].

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};
use serde::Deserialize;

use crate::buses::{CONTEXT_BUS, FORMULA_BUS, GAMMA_BUS, OBLIG_BUS};

// ---------------------------------------------------------------------------
// Spec types
// ---------------------------------------------------------------------------

/// How a premise references a type for its obligation output.
#[derive(Clone, Copy, Debug, PartialEq, Deserialize)]
pub enum TypeRef {
    /// Use child[i] of the principal formula.
    Child(u8),
    /// Keep the parent obligation's type (succedent preserved).
    Inherited,
}

/// What gets sent to CONTEXT_BUS.
#[derive(Clone, Copy, Debug, PartialEq, Deserialize)]
pub enum CtxSend {
    /// Send child[i] of the principal formula.
    Child(u8),
    /// Send the hash column itself (e.g., copy rule).
    Hash,
}

/// A premise that creates a new obligation on OBLIG_BUS.
#[derive(Clone, Copy, Debug, PartialEq, Deserialize)]
pub struct PremiseSpec {
    /// What type to assign to the produced obligation.
    pub succedent: TypeRef,
    /// Override lax flag (None = inherit from input, Some(1) = force lax=1).
    pub lax: Option<u32>,
}

/// Complete specification for one inference rule's ZK chip.
///
/// Describes which buses the rule interacts with and how.
/// The generic `RuleChip` reads this spec and emits appropriate
/// AIR constraints. No code generation needed — just instantiate
/// with different specs.
///
/// Specs can be constructed statically (see `ill` module) or
/// deserialized from the witness JSON for fully generic verification.
#[derive(Clone, Debug, Deserialize)]
pub struct RuleSpec {
    pub name: String,
    /// Connective tag for FORMULA_BUS lookup (None for id, copy).
    pub tag: Option<u32>,
    /// Number of children of the principal formula (0, 1, or 2).
    pub arity: u8,

    // -- Obligation bus --
    /// OBLIG_BUS.receive — consume an obligation.
    pub oblig_receive: bool,
    /// OBLIG_BUS.send per premise — produce new obligations.
    pub premises: Vec<PremiseSpec>,

    // -- Context bus --
    /// CONTEXT_BUS.receive — consume principal from linear context.
    pub ctx_receive: bool,
    /// CONTEXT_BUS.send — introduce elements to context.
    pub ctx_sends: Vec<CtxSend>,

    // -- Formula bus --
    /// FORMULA_BUS.lookup_key — verify connective decomposition.
    pub formula_lookup: bool,

    // -- Gamma bus --
    /// GAMMA_BUS.lookup_key — look up gamma zone membership (copy rule).
    pub gamma_lookup: bool,

    // -- Special flags --
    /// Identity rule: principal = obligation type = context resource.
    /// When true, a single `hash` column serves both OBLIG and CONTEXT,
    /// and no separate `goal` column is allocated.
    pub is_identity: bool,
}

// ---------------------------------------------------------------------------
// Column layout
// ---------------------------------------------------------------------------

/// Column indices computed from a RuleSpec.
///
/// Allocation order: active, hash, child0, child1, nonce_in, lax,
/// nonce_outs..., goal. This order is deterministic and stable —
/// changing a spec field only adds/removes columns at the end.
pub struct ColumnLayout {
    pub width: usize,
    pub active: usize,
    pub hash: Option<usize>,
    pub child0: Option<usize>,
    pub child1: Option<usize>,
    pub nonce_in: Option<usize>,
    pub lax: Option<usize>,
    pub nonce_outs: Vec<usize>,
    pub goal: Option<usize>,
}

impl ColumnLayout {
    /// Compute column layout from a rule spec.
    pub fn compute(spec: &RuleSpec) -> Self {
        let mut col = 0usize;

        // is_active: always present
        let active = col;
        col += 1;

        // hash: principal formula hash, identity principal, gamma key, or context resource
        let needs_hash = spec.tag.is_some() || spec.is_identity || spec.gamma_lookup
            || spec.ctx_receive || spec.ctx_sends.iter().any(|s| matches!(s, CtxSend::Hash));
        let hash = if needs_hash {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };

        // children: only allocated when arity > 0
        let child0 = if spec.arity >= 1 {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };
        let child1 = if spec.arity >= 2 {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };

        // nonce_in: only when receiving an obligation
        let nonce_in = if spec.oblig_receive {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };

        // lax: present when any obligation interaction exists
        let has_oblig = spec.oblig_receive || !spec.premises.is_empty();
        let lax = if has_oblig {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };

        // nonce_outs: one per premise
        let mut nonce_outs = Vec::with_capacity(spec.premises.len());
        for _ in &spec.premises {
            nonce_outs.push(col);
            col += 1;
        }

        // goal: separate succedent type column for left focus rules
        // (where obligation type ≠ principal hash)
        let goal = if spec.oblig_receive && spec.ctx_receive && !spec.is_identity {
            let c = col;
            col += 1;
            Some(c)
        } else {
            None
        };

        ColumnLayout {
            width: col,
            active,
            hash,
            child0,
            child1,
            nonce_in,
            lax,
            nonce_outs,
            goal,
        }
    }
}

// ---------------------------------------------------------------------------
// Generic rule chip
// ---------------------------------------------------------------------------

/// A generic AIR chip for any inference rule, parameterized by `RuleSpec`.
///
/// Implements the `Air` trait by reading the spec and emitting bus
/// interaction constraints. Column layout is computed at construction
/// time from the spec.
///
/// Usage:
/// ```ignore
/// let chip = RuleChip::new(ill::tensor_r());
/// // chip.width() == 8, same bus interactions as hand-written BinaryRChip
/// ```
pub struct RuleChip {
    pub spec: RuleSpec,
    pub layout: ColumnLayout,
}

impl RuleChip {
    pub fn new(spec: RuleSpec) -> Self {
        Self {
            layout: ColumnLayout::compute(&spec),
            spec,
        }
    }

    /// The spec's name (for debug/display).
    pub fn name(&self) -> &str {
        &self.spec.name
    }
}

impl<F> BaseAir<F> for RuleChip {
    fn width(&self) -> usize {
        self.layout.width
    }
}

impl<F> BaseAirWithPublicValues<F> for RuleChip {}
impl<F> PartitionedBaseAir<F> for RuleChip {}

impl<AB: InteractionBuilder> Air<AB> for RuleChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let layout = &self.layout;
        let spec = &self.spec;

        // Helper: read a trace column as an AB::Expr.
        macro_rules! col {
            ($idx:expr) => {{
                let expr: AB::Expr = local[$idx].clone().into();
                expr
            }};
        }

        let active = col!(layout.active);

        // is_active must be boolean
        builder.assert_zero(active.clone() * (active.clone() - AB::Expr::ONE));

        // Obligation type: goal column (left focus rules) or hash column
        let oblig_type = if let Some(g) = layout.goal {
            col!(g)
        } else if let Some(h) = layout.hash {
            col!(h)
        } else {
            AB::Expr::ZERO
        };

        // --- OBLIG_BUS.receive ---
        if spec.oblig_receive {
            OBLIG_BUS.receive(
                builder,
                [
                    col!(layout.nonce_in.unwrap()),
                    oblig_type.clone(),
                    col!(layout.lax.unwrap()),
                ],
                active.clone(),
            );
        }

        // --- OBLIG_BUS.send per premise ---
        for (i, premise) in spec.premises.iter().enumerate() {
            let prem_type = match premise.succedent {
                TypeRef::Child(0) => col!(layout.child0.unwrap()),
                TypeRef::Child(1) => col!(layout.child1.unwrap()),
                TypeRef::Child(j) => panic!("unsupported child index {j}"),
                TypeRef::Inherited => oblig_type.clone(),
            };
            let prem_lax = match premise.lax {
                Some(v) => AB::Expr::from_u32(v),
                None => col!(layout.lax.unwrap()),
            };
            OBLIG_BUS.send(
                builder,
                [col!(layout.nonce_outs[i]), prem_type, prem_lax],
                active.clone(),
            );
        }

        // --- CONTEXT_BUS.receive ---
        if spec.ctx_receive {
            CONTEXT_BUS.receive(builder, [col!(layout.hash.unwrap())], active.clone());
        }

        // --- CONTEXT_BUS.send ---
        for send in &spec.ctx_sends {
            let val = match send {
                CtxSend::Child(0) => col!(layout.child0.unwrap()),
                CtxSend::Child(1) => col!(layout.child1.unwrap()),
                CtxSend::Child(j) => panic!("unsupported child index {j}"),
                CtxSend::Hash => col!(layout.hash.unwrap()),
            };
            CONTEXT_BUS.send(builder, [val], active.clone());
        }

        // --- FORMULA_BUS.lookup_key ---
        if spec.formula_lookup {
            let tag = AB::Expr::from_u32(spec.tag.unwrap());
            let c0 = layout.child0.map(|c| col!(c)).unwrap_or(AB::Expr::ZERO);
            let c1 = layout.child1.map(|c| col!(c)).unwrap_or(AB::Expr::ZERO);
            FORMULA_BUS.lookup_key(
                builder,
                [col!(layout.hash.unwrap()), tag, c0, c1],
                active.clone(),
            );
        }

        // --- GAMMA_BUS.lookup_key ---
        if spec.gamma_lookup {
            GAMMA_BUS.lookup_key(builder, [col!(layout.hash.unwrap())], active);
        }
    }
}
