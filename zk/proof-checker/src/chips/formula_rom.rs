//! FormulaRomAir: formula decomposition ROM for FORMULA_BUS.
//!
//! Stores (hash, tag, child0, child1) tuples. Rule chips look up
//! decompositions to verify connective structure. The ROM's
//! `add_key_with_lookups` interaction provides the supply side of
//! the LookupBus; rule chips' `lookup_key` calls provide the demand.
//!
//! Phase 1: main-trace columns (committed with the witness).
//! Phase 3: preprocessed columns (committed at keygen, Poseidon hash).
//!
//! Columns (width 6): [hash, tag, child0, child1, is_active, num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::FORMULA_BUS;

pub const COL_HASH: usize = 0;
pub const COL_TAG: usize = 1;
pub const COL_CHILD0: usize = 2;
pub const COL_CHILD1: usize = 3;
pub const COL_IS_ACTIVE: usize = 4;
pub const COL_NUM_LOOKUPS: usize = 5;
pub const WIDTH: usize = 6;

pub struct FormulaRomAir;

impl<F> BaseAir<F> for FormulaRomAir {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for FormulaRomAir {}
impl<F> PartitionedBaseAir<F> for FormulaRomAir {}

impl<AB: InteractionBuilder> Air<AB> for FormulaRomAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let tag: AB::Expr = local[COL_TAG].clone().into();
        let child0: AB::Expr = local[COL_CHILD0].clone().into();
        let child1: AB::Expr = local[COL_CHILD1].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let num_lookups: AB::Expr = local[COL_NUM_LOOKUPS].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Provide formula entries on FORMULA_BUS
        FORMULA_BUS.add_key_with_lookups(
            builder,
            [hash, tag, child0, child1],
            is_active * num_lookups,
        );
    }
}
