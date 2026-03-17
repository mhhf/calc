//! FactRomAir: verified fact ROM for FACT_BUS.
//!
//! Stores goal hashes of predicates verified by custom chips
//! (arr_get, arr_set, mem_read, mem_expand, plus, inc, mul). The fact_axiom
//! rule looks up membership to discharge obligations without walking full
//! clause proof subtrees.
//!
//! Now a type alias for SimpleRomAir. Use `fact_rom_air()` to construct.

use crate::buses::FACT_BUS;
use super::simple_rom::SimpleRomAir;

pub use super::simple_rom::{WIDTH, PREP_WIDTH};

/// Type alias — FactRomAir is a SimpleRomAir wired to FACT_BUS.
pub type FactRomAir = SimpleRomAir;

/// Convenience constructor: creates a SimpleRomAir wired to FACT_BUS.
pub fn fact_rom_air(entries: Vec<[u32; 2]>, min_rows: usize) -> FactRomAir {
    SimpleRomAir { bus: FACT_BUS, entries, min_rows }
}
