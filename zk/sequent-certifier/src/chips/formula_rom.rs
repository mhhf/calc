//! FormulaRomAir: formula decomposition ROM for FORMULA_BUS.
//!
//! Stores (hash, tag, child0, child1) tuples. Rule chips look up
//! decompositions to verify connective structure. The ROM's
//! `add_key_with_lookups` interaction provides the supply side of
//! the LookupBus; rule chips' `lookup_key` calls provide the demand.
//!
//! Phase 3b: preprocessed columns (committed at keygen via Poseidon2).
//! ROM data is immutable — only num_lookups is witness-dependent.
//!
//! Preprocessed (width 5): [hash, tag, child0, child1, is_active]
//! Main trace (width 1): [num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::FORMULA_BUS;

/// Width of the main trace (witness-dependent): just num_lookups.
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace (committed at keygen).
pub const PREP_WIDTH: usize = 5;

/// FormulaRomAir with data committed at keygen.
///
/// `entries` contains [hash, tag, child0, child1, is_active] per row.
/// These become preprocessed columns via `preprocessed_trace()`.
/// The main trace carries only `num_lookups` (1 column).
/// `min_rows` ensures preprocessed trace height matches main trace height.
pub struct FormulaRomAir {
    pub entries: Vec<[u32; 5]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for FormulaRomAir {
    fn width(&self) -> usize {
        WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = self.entries.len().max(self.min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * PREP_WIDTH);
        for row in &self.entries {
            for &v in row {
                data.push(F::from_u32(v));
            }
        }
        for _ in self.entries.len()..n {
            for _ in 0..PREP_WIDTH {
                data.push(F::ZERO);
            }
        }
        Some(RowMajorMatrix::new(data, PREP_WIDTH))
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for FormulaRomAir {}
impl<F: Field> PartitionedBaseAir<F> for FormulaRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for FormulaRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let hash: AB::Expr = prep_local[0].clone().into();
        let tag: AB::Expr = prep_local[1].clone().into();
        let child0: AB::Expr = prep_local[2].clone().into();
        let child1: AB::Expr = prep_local[3].clone().into();
        let is_active: AB::Expr = prep_local[4].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // Provide formula entries on FORMULA_BUS
        FORMULA_BUS.add_key_with_lookups(
            builder,
            [hash, tag, child0, child1],
            is_active * num_lookups,
        );
    }
}
