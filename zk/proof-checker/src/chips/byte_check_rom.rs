//! ByteCheckRomAir: byte-level range check table.
//!
//! Phase 6-6b: ensures that limbs used in Uint256ArithChip are valid bytes [0, 256).
//!
//! Preprocessed (width 1): [byte_value] — 256 entries [0..255]
//! Main trace (width 1):   [num_lookups]
//!
//! Supplies BYTE_CHECK_BUS: each limb in Uint256ArithChip looks up its value
//! to prove it lies in [0, 256).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::Field,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::BYTE_CHECK_BUS;

/// Width of the main trace: [num_lookups].
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace: [byte_value].
pub const PREP_WIDTH: usize = 1;

/// ByteCheckRomAir: preprocessed table of byte values [0..255].
pub struct ByteCheckRomAir {
    pub min_rows: usize,
}

impl ByteCheckRomAir {
    /// Number of entries in the ROM (always 256).
    pub const NUM_ENTRIES: usize = 256;
}

impl<F: Field> BaseAir<F> for ByteCheckRomAir {
    fn width(&self) -> usize {
        WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = Self::NUM_ENTRIES.max(self.min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * PREP_WIDTH);
        for i in 0..Self::NUM_ENTRIES {
            data.push(F::from_u32(i as u32));
        }
        for _ in Self::NUM_ENTRIES..n {
            data.push(F::ZERO);
        }
        Some(RowMajorMatrix::new(data, PREP_WIDTH))
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for ByteCheckRomAir {}
impl<F: Field> PartitionedBaseAir<F> for ByteCheckRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for ByteCheckRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let byte_value: AB::Expr = prep_local[0].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // Supply byte values on BYTE_CHECK_BUS
        BYTE_CHECK_BUS.add_key_with_lookups(builder, [byte_value], num_lookups);
    }
}
