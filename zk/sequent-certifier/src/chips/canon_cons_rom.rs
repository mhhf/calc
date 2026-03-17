//! CanonConsRomAir: canonical body form ROM for CANON_CONS_BUS.
//!
//! Maps cons_hash → canon_cons for loli body pattern verification.
//! FlatStepChip loli rows look up their (cons_hash, canon_cons) pair
//! to verify the canonical body form is correct.
//!
//! Phase 4a-5: extracted from FlatStepChip preprocessed trace to enable
//! program-static preprocessed data → constant VK across chunks.
//!
//! Preprocessed (width 3): [cons_hash, canon_cons, is_active]
//! Main trace (width 1): [num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CANON_CONS_BUS;

/// Width of the main trace: just num_lookups.
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace.
pub const PREP_WIDTH: usize = 3;

/// CanonConsRomAir with data committed at keygen.
///
/// `entries` contains [cons_hash, canon_cons, is_active] per row.
/// The main trace carries only `num_lookups` (1 column).
pub struct CanonConsRomAir {
    pub entries: Vec<[u32; 3]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for CanonConsRomAir {
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

impl<F: Field> BaseAirWithPublicValues<F> for CanonConsRomAir {}
impl<F: Field> PartitionedBaseAir<F> for CanonConsRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for CanonConsRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let cons_hash: AB::Expr = prep_local[0].clone().into();
        let canon_cons: AB::Expr = prep_local[1].clone().into();
        let is_active: AB::Expr = prep_local[2].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // Provide canon_cons mapping entries with multiplicity
        CANON_CONS_BUS.add_key_with_lookups(
            builder,
            [cons_hash, canon_cons],
            is_active * num_lookups,
        );
    }
}
