//! FlatInitChip: introduces initial linear context for flat certificates.
//!
//! Phase 3b: context data in preprocessed columns (committed at keygen).
//! Main trace is width 1 (dummy — OpenVM requires width ≥ 1).
//!
//! Preprocessed (width 2): [is_active, hash]
//! Main trace (width 1): [dummy]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

/// Width of the main trace (dummy column).
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace.
pub const PREP_WIDTH: usize = 2;

/// FlatInitChip with context data committed at keygen.
///
/// `ctx_hashes` contains the initial linear context fact hashes.
/// The main trace carries only a dummy column (always 0).
/// `min_rows` ensures preprocessed trace height matches main trace height.
pub struct FlatInitChip {
    pub ctx_hashes: Vec<u32>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for FlatInitChip {
    fn width(&self) -> usize {
        WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = self.ctx_hashes.len().max(self.min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * PREP_WIDTH);
        for &h in &self.ctx_hashes {
            data.push(F::ONE);          // is_active
            data.push(F::from_u32(h));  // hash
        }
        for _ in self.ctx_hashes.len()..n {
            data.push(F::ZERO); // is_active = 0
            data.push(F::ZERO); // hash = 0
        }
        Some(RowMajorMatrix::new(data, PREP_WIDTH))
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for FlatInitChip {}
impl<F: Field> PartitionedBaseAir<F> for FlatInitChip {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for FlatInitChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = prep.row_slice(0).unwrap();
        let is_active: AB::Expr = p[0].clone().into();
        let hash: AB::Expr = p[1].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        CONTEXT_BUS.send(builder, [hash], is_active);
    }
}
