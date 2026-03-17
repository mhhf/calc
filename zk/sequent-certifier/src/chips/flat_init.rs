//! FlatInitChip: introduces initial linear context for flat certificates.
//!
//! Phase 4a: context data in main trace (prover-provided), with public values
//! carrying the context hashes for cross-chunk IVC verification.
//!
//! Main trace (width 4): [is_active, hash, acc_active, is_first]
//! Public values: [hash_0, ..., hash_{max-1}, active_count]
//!   padded to max_ctx_size + 1 total PVs.
//!
//! ## Soundness layers
//!
//! 1. **Bus balance (CONTEXT_BUS):** trace values participate in LogUp multiset
//!    equality — within-proof consistency.
//! 2. **Running-sum count binding:** acc_active constrains PV active_count against
//!    actual trace row counts.
//! 3. **PV value binding (FLAT_PV_BIND_BUS):** on the first row, receive all PV
//!    hash values on a binding bus; active rows send their trace values on the same
//!    bus. LogUp multiset equality ensures PV values match trace values (as a set).

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, AirBuilder, AirBuilderWithPublicValues, BaseAir},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, FLAT_PV_BIND_BUS};

/// Width of the main trace.
pub const WIDTH: usize = 4;

const COL_ACTIVE: usize = 0;
const COL_HASH: usize = 1;
const COL_ACC_ACTIVE: usize = 2;
const COL_IS_FIRST: usize = 3;

/// FlatInitChip with context data in main trace and public values.
///
/// `ctx_hashes` contains the initial linear context fact hashes.
/// `max_ctx_size` determines the fixed number of hash PVs (for constant VK across chunks).
/// `min_rows` ensures trace height is at least this value.
pub struct FlatInitChip {
    pub ctx_hashes: Vec<u32>,
    pub max_ctx_size: usize,
    pub min_rows: usize,
}

/// PV layout accessors.
impl FlatInitChip {
    pub fn num_pvs(&self) -> usize { self.max_ctx_size + 1 }
    pub fn hash_idx(&self, k: usize) -> usize { k }
    pub fn active_count_idx(&self) -> usize { self.max_ctx_size }
}

impl<F: Field> BaseAir<F> for FlatInitChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for FlatInitChip {
    fn num_public_values(&self) -> usize {
        self.num_pvs()
    }
}

impl<F: Field> PartitionedBaseAir<F> for FlatInitChip {}

impl<AB: InteractionBuilder + AirBuilderWithPublicValues> Air<AB> for FlatInitChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next = main.row_slice(1).unwrap();

        let is_active: AB::Expr = local[COL_ACTIVE].clone().into();
        let hash: AB::Expr = local[COL_HASH].clone().into();
        let acc_active: AB::Expr = local[COL_ACC_ACTIVE].clone().into();
        let is_first: AB::Expr = local[COL_IS_FIRST].clone().into();

        let is_active_next: AB::Expr = next[COL_ACTIVE].clone().into();
        let acc_active_next: AB::Expr = next[COL_ACC_ACTIVE].clone().into();
        let is_first_next: AB::Expr = next[COL_IS_FIRST].clone().into();

        // Extract PV values before mutable builder calls
        let pv_active_count: AB::Expr = {
            let pvs = builder.public_values();
            pvs[self.active_count_idx()].clone().into()
        };
        let mut pv_hashes: Vec<AB::Expr> = Vec::with_capacity(self.max_ctx_size);
        for k in 0..self.max_ctx_size {
            let pvs = builder.public_values();
            pv_hashes.push(pvs[self.hash_idx(k)].clone().into());
        }

        // Boolean constraints
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        builder.assert_zero(is_first.clone() * (is_first.clone() - AB::Expr::ONE));

        // inactive rows must have hash = 0
        builder.assert_zero((AB::Expr::ONE - is_active.clone()) * hash.clone());

        // is_first: 1 on row 0, 0 elsewhere
        builder.when_first_row().assert_one(is_first.clone());
        builder.when_transition().assert_zero(is_first_next);

        // Running-sum count constraint
        builder.when_first_row().assert_eq(acc_active.clone(), is_active.clone());
        builder.when_transition().assert_eq(acc_active_next, acc_active.clone() + is_active_next);
        builder.when_last_row().assert_eq(acc_active, pv_active_count.clone());

        // --- CONTEXT_BUS: actual context injection ---
        CONTEXT_BUS.send(builder, [hash.clone()], is_active.clone());

        // --- FLAT_PV_BIND_BUS: bind PV values to trace values ---
        // Init side: discriminator = 0
        for k in 0..self.max_ctx_size {
            FLAT_PV_BIND_BUS.receive(
                builder,
                [AB::Expr::ZERO, pv_hashes[k].clone()],
                is_first.clone(),
            );
        }
        FLAT_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, hash],
            is_active,
        );
        let max_ctx_expr = AB::Expr::from_u32(self.max_ctx_size as u32);
        let padding = max_ctx_expr - pv_active_count;
        FLAT_PV_BIND_BUS.send(
            builder,
            [AB::Expr::ZERO, AB::Expr::ZERO],
            is_first * padding,
        );
    }
}
