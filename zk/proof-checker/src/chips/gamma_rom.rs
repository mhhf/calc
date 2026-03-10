//! GammaRomAir: cartesian zone (Γ) membership ROM for GAMMA_BUS.
//!
//! Stores formulas available in the cartesian/gamma zone. The copy rule
//! looks up membership to verify a formula can be freely duplicated.
//! Entries are created by absorption (!A consumed → A enters gamma).
//!
//! Similar to FormulaRomAir but simpler — only tracks hash, not structure.
//!
//! Phase 2: main-trace columns (committed with witness).
//! Phase 3: preprocessed + Poseidon commitment.
//!
//! Columns (width 3): [hash, is_active, num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::GAMMA_BUS;

pub const COL_HASH: usize = 0;
pub const COL_IS_ACTIVE: usize = 1;
pub const COL_NUM_LOOKUPS: usize = 2;
pub const WIDTH: usize = 3;

pub struct GammaRomAir;

impl<F> BaseAir<F> for GammaRomAir {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for GammaRomAir {}
impl<F> PartitionedBaseAir<F> for GammaRomAir {}

impl<AB: InteractionBuilder> Air<AB> for GammaRomAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let num_lookups: AB::Expr = local[COL_NUM_LOOKUPS].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Provide gamma zone entries with multiplicity
        GAMMA_BUS.add_key_with_lookups(builder, [hash], is_active * num_lookups);
    }
}
