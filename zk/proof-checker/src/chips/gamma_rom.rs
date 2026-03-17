//! GammaRomAir: cartesian zone (Γ) membership ROM for GAMMA_BUS.
//!
//! Stores formulas available in the cartesian/gamma zone. The copy rule
//! looks up membership to verify a formula can be freely duplicated.
//!
//! Now a type alias for SimpleRomAir. Use `gamma_rom_air()` to construct.

use crate::buses::GAMMA_BUS;
use super::simple_rom::SimpleRomAir;

pub use super::simple_rom::{WIDTH, PREP_WIDTH};

/// Type alias — GammaRomAir is a SimpleRomAir wired to GAMMA_BUS.
pub type GammaRomAir = SimpleRomAir;

/// Convenience constructor: creates a SimpleRomAir wired to GAMMA_BUS.
pub fn gamma_rom_air(entries: Vec<[u32; 2]>, min_rows: usize) -> GammaRomAir {
    SimpleRomAir { bus: GAMMA_BUS, entries, min_rows }
}
