//! FreevarRomAir: free variable consistency ROM for FREEVAR_BUS.
//!
//! Stores (subst_id, freevar_hash, ground_value) entries that define
//! the substitution mapping for each SubstChip instance. Freevar-leaf
//! rows in SubstChip look up their (subst_id, freevar_hash) to verify
//! that the ground value is consistent across all occurrences.
//!
//! Preprocessed (width 4): [subst_id, freevar_hash, ground_value, is_active]
//! Main trace (width 1): [num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::FREEVAR_BUS;

/// Width of the main trace (witness-dependent): just num_lookups.
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace (committed at keygen).
pub const PREP_WIDTH: usize = 4;

/// FreevarRomAir with data committed at keygen.
///
/// `entries` contains [subst_id, freevar_hash, ground_value, is_active] per row.
/// The main trace carries only `num_lookups` (1 column).
pub struct FreevarRomAir {
    pub entries: Vec<[u32; 4]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for FreevarRomAir {
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

impl<F: Field> BaseAirWithPublicValues<F> for FreevarRomAir {}
impl<F: Field> PartitionedBaseAir<F> for FreevarRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for FreevarRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let subst_id: AB::Expr = prep_local[0].clone().into();
        let freevar_hash: AB::Expr = prep_local[1].clone().into();
        let ground_value: AB::Expr = prep_local[2].clone().into();
        let is_active: AB::Expr = prep_local[3].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // Provide freevar mapping entries with multiplicity
        FREEVAR_BUS.add_key_with_lookups(
            builder,
            [subst_id, freevar_hash, ground_value],
            is_active * num_lookups,
        );
    }
}
