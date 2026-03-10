//! SubstChip: substitution bridge for loli bodies with freevars.
//!
//! When a loli fact contains unresolved freevars in its body (e.g., sha3's
//! `_Bytes`), the Store.child decomposition yields different hashes than the
//! ground values produced by the forward engine. The SubstChip bridges this
//! gap: it consumes the original (unresolved) hash from CONTEXT_BUS and
//! produces the ground (resolved) hash, allowing subsequent decomposition
//! chips (loli_l, monad_l, tensor_l) to operate on ground hashes.
//!
//! Columns (width 3): [is_active, hash_old, hash_new]

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

pub struct SubstChip;

impl<F> BaseAir<F> for SubstChip {
    fn width(&self) -> usize {
        3
    }
}

impl<F> BaseAirWithPublicValues<F> for SubstChip {}
impl<F> PartitionedBaseAir<F> for SubstChip {}

impl<AB: InteractionBuilder> Air<AB> for SubstChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[0].clone().into();
        let hash_old: AB::Expr = local[1].clone().into();
        let hash_new: AB::Expr = local[2].clone().into();

        // is_active must be boolean
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));

        // Consume old hash from context, produce new hash
        CONTEXT_BUS.receive(builder, [hash_old], is_active.clone());
        CONTEXT_BUS.send(builder, [hash_new], is_active);
    }
}
