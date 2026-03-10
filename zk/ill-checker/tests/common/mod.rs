//! Shared test utilities for proof term verifier integration tests.

use openvm_stark_backend::p3_matrix::dense::RowMajorMatrix;
use p3_baby_bear::BabyBear;
use p3_field::PrimeCharacteristicRing;

/// Build a padded trace matrix from active rows.
///
/// Each row is `W` field elements. Pads to at least `min_rows` then
/// to the next power of 2 (required by stark-backend). Padding rows
/// are all zeros (is_active=0 → no bus contribution).
pub fn padded_trace<const W: usize>(
    active_rows: &[[u32; W]],
    min_rows: usize,
) -> RowMajorMatrix<BabyBear> {
    let n = active_rows.len().max(min_rows).next_power_of_two();
    let mut data = Vec::with_capacity(n * W);
    for row in active_rows {
        for &v in row {
            data.push(BabyBear::from_u32(v));
        }
    }
    for _ in active_rows.len()..n {
        for _ in 0..W {
            data.push(BabyBear::ZERO);
        }
    }
    RowMajorMatrix::new(data, W)
}
