//! Connective tags for FORMULA_BUS decomposition lookups.
//!
//! Each binary connective has a unique tag. The formula ROM stores
//! (hash, tag, child0, child1) tuples. Rule chips include the tag
//! in their FORMULA_BUS lookup to verify the correct connective.
//!
//! Phase 2 will auto-generate these from .calc connective definitions.

pub const TENSOR: u32 = 1;
pub const LOLI: u32 = 2;
pub const WITH: u32 = 3;
pub const OPLUS: u32 = 4;
pub const BANG: u32 = 5;
pub const MONAD: u32 = 6;
