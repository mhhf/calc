//! BinaryRChip: right rule for any binary connective.
//!
//! Consumes one parent obligation, produces two child obligations,
//! and verifies formula decomposition via FORMULA_BUS lookup.
//!
//! Parameterized by connective tag — the same chip struct serves
//! tensor_r (tag=TENSOR), with_r (tag=WITH), etc. The tag is
//! included in the FORMULA_BUS lookup to enforce the correct
//! connective. A prover cannot use a tensor_r chip to decompose
//! a with formula because the ROM lookup would fail.
//!
//! No CONTEXT_BUS interaction — right rules don't touch the linear
//! context directly. (Context duplication for additive right rules
//! like with_r is handled by a separate DupChip.)
//!
//! Columns (width 8): [hash, child0, child1, is_active, nonce_in, nonce_out0, nonce_out1, lax]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{FORMULA_BUS, OBLIG_BUS};

pub const COL_HASH: usize = 0;
pub const COL_CHILD0: usize = 1;
pub const COL_CHILD1: usize = 2;
pub const COL_IS_ACTIVE: usize = 3;
pub const COL_NONCE_IN: usize = 4;
pub const COL_NONCE_OUT0: usize = 5;
pub const COL_NONCE_OUT1: usize = 6;
pub const COL_LAX: usize = 7;
pub const WIDTH: usize = 8;

/// Right rule for a binary connective. Parameterized by connective tag.
pub struct BinaryRChip {
    pub tag: u32,
}

impl<F> BaseAir<F> for BinaryRChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for BinaryRChip {}
impl<F> PartitionedBaseAir<F> for BinaryRChip {}

impl<AB: InteractionBuilder> Air<AB> for BinaryRChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let child0: AB::Expr = local[COL_CHILD0].clone().into();
        let child1: AB::Expr = local[COL_CHILD1].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();
        let nonce_in: AB::Expr = local[COL_NONCE_IN].clone().into();
        let nonce_out0: AB::Expr = local[COL_NONCE_OUT0].clone().into();
        let nonce_out1: AB::Expr = local[COL_NONCE_OUT1].clone().into();
        let lax: AB::Expr = local[COL_LAX].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume parent obligation
        OBLIG_BUS.receive(builder, [nonce_in, hash.clone(), lax.clone()], is_active.clone());

        // Produce child obligations
        OBLIG_BUS.send(
            builder,
            [nonce_out0, child0.clone(), lax.clone()],
            is_active.clone(),
        );
        OBLIG_BUS.send(
            builder,
            [nonce_out1, child1.clone(), lax],
            is_active.clone(),
        );

        // Verify formula decomposition: hash must decompose as (tag, child0, child1)
        let tag: AB::Expr = AB::Expr::from_u32(self.tag);
        FORMULA_BUS.lookup_key(builder, [hash, tag, child0, child1], is_active);
    }
}
