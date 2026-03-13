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
