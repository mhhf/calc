//! SimpleRomAir: generic key-lookup ROM chip parameterized by bus.
//!
//! Provides a single preprocessed key column with an is_active flag.
//! Main trace carries num_lookups (multiplicity). Used for both
//! GammaRomAir (GAMMA_BUS) and FactRomAir (FACT_BUS).
//!
//! Preprocessed (width 2): [key_hash, is_active]
//! Main trace (width 1): [num_lookups]

use openvm_stark_backend::{
    interaction::{InteractionBuilder, LookupBus},
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

/// Width of the main trace: just num_lookups.
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace.
pub const PREP_WIDTH: usize = 2;

/// Generic ROM chip: preprocessed [key_hash, is_active], main [num_lookups].
///
/// `entries` contains [key_hash, is_active] per row.
/// `bus` determines which LookupBus this ROM supplies on.
pub struct SimpleRomAir {
    pub bus: LookupBus,
    pub entries: Vec<[u32; 2]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for SimpleRomAir {
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

impl<F: Field> BaseAirWithPublicValues<F> for SimpleRomAir {}
impl<F: Field> PartitionedBaseAir<F> for SimpleRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for SimpleRomAir
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

        self.bus.add_key_with_lookups(builder, [hash], is_active * num_lookups);
    }
}
