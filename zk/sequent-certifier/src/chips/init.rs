//! InitChip: introduces the initial context and root obligation.
//!
//! Phase 3b: sequent data in preprocessed columns (committed at keygen).
//! Only nonce remains as main trace (proof-specific: nonce assignment
//! varies per proof term).
//!
//! Phase 6-2: public values expose the sequent identity so external verifiers
//! can determine WHAT sequent the proof certifies:
//!   PV layout: [ctx_hash_1, ..., ctx_hash_max, succedent_hash, lax_flag, init_active_count]
//!   - ctx hashes: initial linear context (padded with 0 to max_ctx_size)
//!   - succedent_hash: the root obligation formula hash
//!   - lax_flag: 1 if proving {C} (monadic), 0 if proving C
//!   - init_active_count: sum of is_active across all rows (soundness: recursive
//!     verifier checks this == 0 for non-first chunks to prevent re-injection)
//!
//! Preprocessed (width 5): [ctx_hash, ctx_active, oblig_hash, oblig_active, lax]
//! Main trace (width 3): [is_active, nonce, acc_active]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir, PairBuilder},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, OBLIG_BUS};

/// Width of the main trace: [is_active, nonce, acc_active].
pub const WIDTH: usize = 3;

/// Width of the preprocessed trace.
pub const PREP_WIDTH: usize = 5;

/// InitChip with sequent data committed at keygen.
///
/// `rows` contains [ctx_hash, ctx_active, oblig_hash, oblig_active, lax] per row.
/// The main trace carries `[is_active, nonce, acc_active]` (3 columns).
/// `min_rows` ensures preprocessed trace height matches main trace height.
/// `num_pvs` controls PV count: max_ctx_size + 3 (ctx hashes + succedent + lax + init_active_count).
pub struct InitChip {
    pub rows: Vec<[u32; 5]>,
    pub min_rows: usize,
    pub num_pvs: usize,
}

impl<F: Field> BaseAir<F> for InitChip {
    fn width(&self) -> usize {
        WIDTH
    }

    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        let n = self.rows.len().max(self.min_rows).next_power_of_two();
        let mut data = Vec::with_capacity(n * PREP_WIDTH);
        for row in &self.rows {
            for &v in row {
                data.push(F::from_u32(v));
            }
        }
        for _ in self.rows.len()..n {
            for _ in 0..PREP_WIDTH {
                data.push(F::ZERO);
            }
        }
        Some(RowMajorMatrix::new(data, PREP_WIDTH))
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for InitChip {
    fn num_public_values(&self) -> usize {
        self.num_pvs
    }
}
impl<F: Field> PartitionedBaseAir<F> for InitChip {}

impl<AB: InteractionBuilder + PairBuilder + AirBuilderWithPublicValues> Air<AB> for InitChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let p = prep.row_slice(0).unwrap();
        let ctx_hash: AB::Expr = p[0].clone().into();
        let ctx_active: AB::Expr = p[1].clone().into();
        let oblig_hash: AB::Expr = p[2].clone().into();
        let oblig_active: AB::Expr = p[3].clone().into();
        let lax: AB::Expr = p[4].clone().into();

        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();
        let is_active: AB::Expr = local[0].clone().into();
        let nonce: AB::Expr = local[1].clone().into();
        let acc_active: AB::Expr = local[2].clone().into();
        let is_active_next: AB::Expr = next[0].clone().into();
        let acc_active_next: AB::Expr = next[2].clone().into();

        // Boolean constraints
        builder.assert_zero(ctx_active.clone() * (ctx_active.clone() - AB::Expr::ONE));
        builder.assert_zero(oblig_active.clone() * (oblig_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Running sum: acc_active accumulates is_active across rows
        // First row: acc_active = is_active
        builder.when_first_row().assert_eq(acc_active.clone(), is_active.clone());
        // Transition: acc_active_next = acc_active + is_active_next
        builder.when_transition().assert_eq(acc_active_next, acc_active.clone() + is_active_next);
        // Last row: acc_active = init_active_count PV (last PV slot)
        let pv_active_count: AB::Expr = builder.public_values()[self.num_pvs - 1].clone().into();
        builder.when_last_row().assert_eq(acc_active, pv_active_count);

        // Gate bus sends by is_active (constant VK: preprocessed identical across chunks,
        // is_active=1 in chunk 0, is_active=0 in other chunks — now enforced via PV)
        CONTEXT_BUS.send(builder, [ctx_hash], ctx_active * is_active.clone());
        OBLIG_BUS.send(builder, [nonce, oblig_hash, lax], oblig_active * is_active);
    }
}
