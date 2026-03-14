//! FactRomAir: verified fact ROM for FACT_BUS.
//!
//! Stores goal hashes of predicates verified by custom chips
//! (arr_get, plus, inc, mul, neq). The fact_axiom rule looks up
//! membership to discharge obligations without walking full clause
//! proof subtrees.
//!
//! Phase 6-4: same pattern as GammaRomAir but for computed facts
//! instead of persistent context membership.
//!
//! Preprocessed (width 2): [goal_hash, is_active]
//! Main trace (width 1): [num_lookups]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::FACT_BUS;

/// Width of the main trace (witness-dependent): just num_lookups.
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace (committed at keygen).
pub const PREP_WIDTH: usize = 2;

/// FactRomAir with data committed at keygen.
///
/// `entries` contains [goal_hash, is_active] per row.
/// The main trace carries only `num_lookups` (1 column).
pub struct FactRomAir {
    pub entries: Vec<[u32; 2]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for FactRomAir {
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

impl<F: Field> BaseAirWithPublicValues<F> for FactRomAir {}
impl<F: Field> PartitionedBaseAir<F> for FactRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for FactRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let hash: AB::Expr = prep_local[0].clone().into();
        let is_active: AB::Expr = prep_local[1].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // Provide verified fact entries on FACT_BUS
        FACT_BUS.add_key_with_lookups(builder, [hash], is_active * num_lookups);
    }
}
