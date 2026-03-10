//! Connective tags for FORMULA_BUS decomposition lookups.
//!
//! Each connective has a unique tag. The formula ROM stores
//! (hash, tag, child0, child1) tuples. Rule chips include the tag
//! in their FORMULA_BUS lookup to verify the correct connective.
//!
//! Tags derived from ILL .calc connective definitions.
//! Nullary connectives (ONE, ZERO) use child0=child1=0 in the ROM.
//! Unary connectives (BANG, MONAD, EXISTS, FORALL) use child1=0.

pub const TENSOR: u32 = 1;
pub const LOLI: u32 = 2;
pub const WITH: u32 = 3;
pub const OPLUS: u32 = 4;
pub const BANG: u32 = 5;
pub const MONAD: u32 = 6;
pub const ONE: u32 = 7;
pub const ZERO: u32 = 8;
pub const EXISTS: u32 = 9;
pub const FORALL: u32 = 10;
