//! ZeroLChip: additive false left rule (ex falso quodlibet).
//!
//! When zero (0) appears in the linear context, any goal is provable
//! and all remaining linear resources are discarded. This is the only
//! way to discard linear resources in ILL — soundness requires that
//! DiscardChip rows are linked to a ZeroLChip via DISCARD_BUS.
//!
//! The `num_discards` witness column tells the bus how many DiscardChip
//! rows this zero_l application authorizes. LookupBus ensures the
//! total discard count matches exactly.
//!
//! Columns (width 6): [hash, is_active, nonce_in, lax, goal, num_discards]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, DISCARD_BUS, FORMULA_BUS, OBLIG_BUS};
use crate::tags;

pub const COL_HASH: usize = 0;
pub const COL_IS_ACTIVE: usize = 1;
pub const COL_NONCE_IN: usize = 2;
pub const COL_LAX: usize = 3;
pub const COL_GOAL: usize = 4;
pub const COL_NUM_DISCARDS: usize = 5;
pub const WIDTH: usize = 6;

pub struct ZeroLChip;

impl<F> BaseAir<F> for ZeroLChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for ZeroLChip {}
impl<F> PartitionedBaseAir<F> for ZeroLChip {}

impl<AB: InteractionBuilder> Air<AB> for ZeroLChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let nonce_in: AB::Expr = local[COL_NONCE_IN].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();
        let goal: AB::Expr = local[COL_GOAL].clone().into();
        let num_discards: AB::Expr = local[COL_NUM_DISCARDS].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume obligation (any goal type)
        OBLIG_BUS.receive(
            builder,
            [nonce_in.clone(), goal, lax],
            is_active.clone(),
        );

        // Consume zero formula from context
        CONTEXT_BUS.receive(builder, [hash.clone()], is_active.clone());

        // Verify formula is actually zero
        let tag = AB::Expr::from_u32(tags::ZERO);
        FORMULA_BUS.lookup_key(
            builder,
            [hash, tag, AB::Expr::ZERO, AB::Expr::ZERO],
            is_active.clone(),
        );

        // Authorize discards: provide permits on DISCARD_BUS
        // Each DiscardChip row must look up this nonce_in as its permit.
        DISCARD_BUS.add_key_with_lookups(
            builder,
            [nonce_in],
            is_active * num_discards,
        );
    }
}
