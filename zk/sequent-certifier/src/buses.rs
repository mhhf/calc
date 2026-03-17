//! Shared bus definitions for the proof term verifier.
//!
//! Buses are the composability primitive: chips are swappable, buses are
//! the stable contract. The tree path (13 chips) and flat path (5–7 chips)
//! both balance on the same bus definitions — see bridge.rs for dispatch.
//!
//! Universal buses (any sequent calculus):
//!   OBLIG_BUS   — type obligation tracking (produce/consume)
//!   FORMULA_BUS — formula decomposition lookups
//!
//! Structural buses (substructural logics, derived from .calc):
//!   CONTEXT_BUS — linear resource tracking (send/receive)
//!   GAMMA_BUS   — cartesian zone membership (exponential/bang)
//!   DISCARD_BUS — zero_l discard permits (links zero_l to DiscardChip)
//!
//! Substitution buses (freevar resolution):
//!   SUBST_TREE_BUS — per-node tree matching demands
//!   FREEVAR_BUS    — freevar consistency (ROM-backed)
//!
//! Soundness: PermutationCheckBus enforces multiset equality via LogUp.
//! LookupBus enforces that every demand has a matching supply entry.
//! False positive ≤ n/|F_ext| where F_ext is quartic BabyBear (~2^124).
//!
//! Tree path: OBLIG + CONTEXT + FORMULA + DISCARD + GAMMA + SUBST_TREE + FREEVAR (7 buses).
//! Flat path: CONTEXT + GAMMA + FORMULA + SUBST_TREE + FREEVAR (5 of 7).

use openvm_stark_backend::interaction::{LookupBus, PermutationCheckBus};

/// Type obligation bus. Send = produce obligation, receive = consume obligation.
/// Tuple: (nonce, type_hash, lax)
pub const OBLIG_BUS: PermutationCheckBus = PermutationCheckBus::new(0);

/// Linear context bus. Send = introduce resource, receive = consume resource.
/// Tuple: (hash)
pub const CONTEXT_BUS: PermutationCheckBus = PermutationCheckBus::new(1);

/// Formula decomposition bus. ROM provides (hash, tag, child0, child1) entries;
/// rule chips look up decompositions to verify connective structure.
pub const FORMULA_BUS: LookupBus = LookupBus::new(2);

/// Discard permit bus. ZeroLChip provides permits (nonce) with multiplicity;
/// DiscardChip looks up permits to authorize context element discarding.
/// Ensures only zero_l can discard linear resources (soundness).
pub const DISCARD_BUS: LookupBus = LookupBus::new(3);

/// Gamma (cartesian) zone bus. GammaRomAir provides (hash) entries;
/// copy rule looks up membership to verify formula is in gamma zone.
pub const GAMMA_BUS: LookupBus = LookupBus::new(4);

/// Substitution tree bus. Links parent SubstChip rows to child rows:
/// parent demands child verification, child supplies it.
/// Tuple: (subst_id, old_hash, new_hash)
pub const SUBST_TREE_BUS: PermutationCheckBus = PermutationCheckBus::new(5);

/// Free variable consistency bus. FreevarRomAir provides (subst_id, freevar_hash)
/// → ground_value entries; SubstChip freevar-leaf rows look up to verify that
/// the same freevar maps to the same ground value within a substitution instance.
pub const FREEVAR_BUS: LookupBus = LookupBus::new(6);

/// Canon-cons bus. CanonConsRomAir provides (cons_hash, canon_cons) entries;
/// FlatStepChip loli rows look up to verify the canonical body form is correct.
/// Phase 4a-5: moved from FlatStepChip preprocessed trace to ROM for constant VK.
pub const CANON_CONS_BUS: LookupBus = LookupBus::new(7);

/// Verified fact bus. FactRomAir provides (goal_hash) entries for predicates
/// verified by custom chips (arr_get, arr_set, mem_read, mem_expand, plus, inc, mul). The fact_axiom
/// rule looks up membership to discharge obligations without clause proof
/// subtrees. Phase 6-4: same trust model as GAMMA_BUS (ROM committed in VK).
pub const FACT_BUS: LookupBus = LookupBus::new(8);

/// Predicate verification bus. PredicateRomAir provides (pred_hash) entries
/// with in-circuit arithmetic constraints (plus: a+b=c, mul: a*b=c, inc: a+1=b).
/// The fact_axiom chip demands pred_hash membership, ensuring every custom-chip
/// clause proof has its predicate semantics verified.
/// Phase 6-6a: closes the soundness gap where fact_axiom only checked ROM
/// membership without verifying predicate semantics.
pub const PRED_BUS: LookupBus = LookupBus::new(9);

/// Byte range-check bus. ByteCheckRomAir provides entries [0..255];
/// Uint256ArithChip looks up each limb to prove it lies in [0, 256).
/// Phase 6-6b: supports 256-bit arithmetic verification.
pub const BYTE_CHECK_BUS: LookupBus = LookupBus::new(10);

/// Obligation PV value binding bus. LogUp multiset equality ensures
/// PV obligation values match actual trace values. Prevents declaring
/// one set of obligations in PVs while transferring a different set.
/// Tuple: (discriminator, goal_hash, lax) — discriminator 0=init, 1=final.
/// Phase 6-7: closes PV→trace binding gap for ObligBoundaryChip.
pub const OBLIG_PV_BIND_BUS: PermutationCheckBus = PermutationCheckBus::new(11);

/// Context PV value binding bus. LogUp multiset equality ensures
/// PV context hashes match actual trace values. Same pattern as
/// OBLIG_PV_BIND_BUS but for CtxBoundaryChip.
/// Tuple: (discriminator, hash) — discriminator 0=init, 1=final.
/// Phase 6-7: closes PV→trace binding gap for CtxBoundaryChip.
pub const CTX_PV_BIND_BUS: PermutationCheckBus = PermutationCheckBus::new(12);

/// Flat path PV value binding bus. LogUp multiset equality ensures
/// FlatInitChip/FlatFinalChip PV context hashes match actual trace values.
/// Tuple: (discriminator, hash) — discriminator 0=init, 1=final.
/// Phase 4a→6-7: closes PV→trace binding gap for flat path.
pub const FLAT_PV_BIND_BUS: PermutationCheckBus = PermutationCheckBus::new(13);
