//! Shared bus definitions for the proof term verifier.
//!
//! Universal buses (any sequent calculus):
//!   OBLIG_BUS   — type obligation tracking (produce/consume)
//!   FORMULA_BUS — formula decomposition lookups
//!
//! Structural buses (substructural logics, derived from .calc):
//!   CONTEXT_BUS — linear resource tracking (send/receive)
//!   GAMMA_BUS   — cartesian zone membership (exponential/bang)
//!   DISCARD_BUS — zero_l discard permits (links zero_l to DiscardChip)

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
