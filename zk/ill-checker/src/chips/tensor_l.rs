//! TensorLChip: left decomposition rule for tensor (⊗).
//!
//! Receives A⊗B from the linear context, sends A and B back to the
//! context as separate resources. Verifies decomposition via FORMULA_BUS.
//!
//! No OBLIG_BUS interaction — left decomposition doesn't consume or
//! produce obligations. It only restructures the linear context.
//!
//! Columns (width 4): [hash, child0, child1, is_active]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::{CONTEXT_BUS, FORMULA_BUS};
use crate::tags;

pub const COL_HASH: usize = 0;
pub const COL_CHILD0: usize = 1;
pub const COL_CHILD1: usize = 2;
pub const COL_IS_ACTIVE: usize = 3;
pub const WIDTH: usize = 4;

pub struct TensorLChip;

impl<F> BaseAir<F> for TensorLChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for TensorLChip {}
impl<F> PartitionedBaseAir<F> for TensorLChip {}

impl<AB: InteractionBuilder> Air<AB> for TensorLChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let hash: AB::Expr = local[COL_HASH].clone().into();
        let child0: AB::Expr = local[COL_CHILD0].clone().into();
        let child1: AB::Expr = local[COL_CHILD1].clone().into();
        let is_active: AB::Expr = local[COL_IS_ACTIVE].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume compound resource from context
        CONTEXT_BUS.receive(builder, [hash.clone()], is_active.clone());

        // Introduce decomposed children into context
        CONTEXT_BUS.send(builder, [child0.clone()], is_active.clone());
        CONTEXT_BUS.send(builder, [child1.clone()], is_active.clone());

        // Verify decomposition via formula ROM
        let tag: AB::Expr = AB::Expr::from_u32(tags::TENSOR);
        FORMULA_BUS.lookup_key(builder, [hash, tag, child0, child1], is_active);
    }
}
