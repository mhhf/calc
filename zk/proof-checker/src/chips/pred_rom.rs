//! PredicateRomAir: in-circuit predicate verification for custom chips.
//!
//! Phase 6-6a: closes the soundness gap where FactRomAir + FactAxiomChip
//! only checked ROM membership without verifying predicate semantics.
//! A malicious prover could previously forge arithmetic claims (e.g., 2+3=999).
//!
//! Phase 6-6c/d: extended to 100% predicate coverage. ROM-based predicates
//! (arr_get, arr_set, mem_read, mem_expand) use selector columns with no
//! algebraic constraints — VK-committed ROM membership IS the verification.
//!
//! Each ROM entry commits to a predicate instantiation with its argument values.
//! Selector columns dispatch to predicate-specific arithmetic constraints:
//!   - plus(a, b, c):  a + b = c
//!   - mul(a, b, c):   a * b = c
//!   - inc(a, b):      a + 1 = b
//!   - arr_get/arr_set/mem_read/mem_expand: no constraint (ROM membership only)
//!
//! Preprocessed (width 13): [pred_hash, is_active, is_plus, is_mul, is_inc,
//!                           is_arr_get, is_arr_set, is_mem_read, is_mem_expand,
//!                           arg0, arg1, arg2, arg3]
//! Main trace (width 1):   [num_lookups]
//!
//! The fact_axiom chip demands pred_hash on PRED_BUS for every active row.
//! Arithmetic argument values are BabyBear field elements (< 2^31 - 1).
//! ROM-based arguments are Store IDs (u32 sequential indices, always < BabyBear).
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
pub const PREP_WIDTH: usize = 13;

// Preprocessed column indices.
const P_PRED_HASH: usize = 0;
const P_IS_ACTIVE: usize = 1;
const P_IS_PLUS: usize = 2;
const P_IS_MUL: usize = 3;
const P_IS_INC: usize = 4;
const P_IS_ARR_GET: usize = 5;
const P_IS_ARR_SET: usize = 6;
const P_IS_MEM_READ: usize = 7;
const P_IS_MEM_EXPAND: usize = 8;
const P_ARG0: usize = 9;
const P_ARG1: usize = 10;
const P_ARG2: usize = 11;
const P_ARG3: usize = 12;

/// PredicateRomAir with data committed at keygen.
///
/// `entries` contains [pred_hash, is_active, is_plus, is_mul, is_inc,
///                     is_arr_get, is_arr_set, is_mem_read, is_mem_expand,
///                     arg0, arg1, arg2, arg3]
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
        // ROM-based selectors: read but no constraints (ROM membership is verification)
        let _is_arr_get: AB::Expr = prep_local[P_IS_ARR_GET].clone().into();
        let _is_arr_set: AB::Expr = prep_local[P_IS_ARR_SET].clone().into();
        let _is_mem_read: AB::Expr = prep_local[P_IS_MEM_READ].clone().into();
        let _is_mem_expand: AB::Expr = prep_local[P_IS_MEM_EXPAND].clone().into();
        let arg0: AB::Expr = prep_local[P_ARG0].clone().into();
        let arg1: AB::Expr = prep_local[P_ARG1].clone().into();
        let arg2: AB::Expr = prep_local[P_ARG2].clone().into();
        // arg3 read for completeness but only used by arr_set/mem_expand (no constraint)
        let _arg3: AB::Expr = prep_local[P_ARG3].clone().into();

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

        // ROM-based predicates (arr_get, arr_set, mem_read, mem_expand):
        // No algebraic constraints — VK commits the preprocessed trace,
        // so ROM membership (via PRED_BUS) is sufficient verification.

        // --- PRED_BUS: supply predicate verification entries ---
        PRED_BUS.add_key_with_lookups(builder, [pred_hash], is_active * num_lookups);
    }
}
