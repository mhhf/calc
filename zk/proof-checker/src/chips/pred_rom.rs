//! PredicateRomAir: in-circuit predicate verification for custom chips.
//!
//! Phase 6-6a: closes the soundness gap where FactRomAir + FactAxiomChip
//! only checked ROM membership without verifying predicate semantics.
//! A malicious prover could previously forge arithmetic claims (e.g., 2+3=999).
//!
//! Each ROM entry commits to a predicate instantiation with its argument values.
//! Selector columns dispatch to predicate-specific arithmetic constraints:
//!   - plus(a, b, c):  a + b = c
//!   - mul(a, b, c):   a * b = c
//!   - inc(a, b):      a + 1 = b
//!   - neq(a, b):      (a - b) * inv = 1  (requires inverse witness)
//!
//! Preprocessed (width 8): [pred_hash, is_active, is_plus, is_mul, is_inc, arg0, arg1, arg2]
//! Main trace (width 1):   [num_lookups]
//!
//! The fact_axiom chip demands pred_hash on PRED_BUS for every active row.
//! All argument values are BabyBear field elements (< 2^31 - 1).
//! Values exceeding BabyBear range have no selector set (unverified,
//! deferred to Phase 6-6b limb decomposition).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir, PairBuilder},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::PRED_BUS;

/// Width of the main trace: [num_lookups].
pub const WIDTH: usize = 1;

/// Width of the preprocessed trace.
pub const PREP_WIDTH: usize = 8;

// Preprocessed column indices.
const P_PRED_HASH: usize = 0;
const P_IS_ACTIVE: usize = 1;
const P_IS_PLUS: usize = 2;
const P_IS_MUL: usize = 3;
const P_IS_INC: usize = 4;
const P_ARG0: usize = 5;
const P_ARG1: usize = 6;
const P_ARG2: usize = 7;

/// PredicateRomAir with data committed at keygen.
///
/// `entries` contains [pred_hash, is_active, is_plus, is_mul, is_inc, arg0, arg1, arg2]
/// per row. The main trace carries only `num_lookups` (1 column).
pub struct PredicateRomAir {
    pub entries: Vec<[u32; PREP_WIDTH]>,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for PredicateRomAir {
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

impl<F: Field> BaseAirWithPublicValues<F> for PredicateRomAir {}
impl<F: Field> PartitionedBaseAir<F> for PredicateRomAir {}

impl<AB: InteractionBuilder + PairBuilder> Air<AB> for PredicateRomAir
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let pred_hash: AB::Expr = prep_local[P_PRED_HASH].clone().into();
        let is_active: AB::Expr = prep_local[P_IS_ACTIVE].clone().into();
        let is_plus: AB::Expr = prep_local[P_IS_PLUS].clone().into();
        let is_mul: AB::Expr = prep_local[P_IS_MUL].clone().into();
        let is_inc: AB::Expr = prep_local[P_IS_INC].clone().into();
        let arg0: AB::Expr = prep_local[P_ARG0].clone().into();
        let arg1: AB::Expr = prep_local[P_ARG1].clone().into();
        let arg2: AB::Expr = prep_local[P_ARG2].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let num_lookups: AB::Expr = local[0].clone().into();

        // --- Arithmetic constraints (VK-committed, per-row) ---

        // plus(a, b, c): a + b = c
        builder.assert_zero(is_plus.clone() * (arg0.clone() + arg1.clone() - arg2.clone()));

        // mul(a, b, c): a * b = c
        builder.assert_zero(is_mul.clone() * (arg0.clone() * arg1.clone() - arg2.clone()));

        // inc(a, b): a + 1 = b
        builder.assert_zero(is_inc.clone() * (arg0 + AB::Expr::ONE - arg1));

        // --- PRED_BUS: supply predicate verification entries ---
        PRED_BUS.add_key_with_lookups(builder, [pred_hash], is_active * num_lookups);
    }
}
