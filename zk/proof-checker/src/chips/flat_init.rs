//! FlatInitChip: introduces initial linear context for flat certificates.
//!
//! Phase 4a: context data in main trace (prover-provided), with public values
//! carrying the context hashes for cross-chunk IVC verification.
//!
//! Main trace (width 2): [is_active, hash]
//! Public values: ctx_hashes padded to max_ctx_size with zeros
//!
//! Phase 3b→4a migration: previously used preprocessed trace (committed at
//! keygen, baked into VK). Now uses main trace so VK is constant across chunks
//! when max_ctx_size is fixed.
//!
//! **Soundness note (Phase 4a gap):** PVs are prover-declared and NOT constrained
//! against the main trace in-circuit. The CONTEXT_BUS ensures within-proof
//! correctness (init sends must balance step receives). Cross-chunk PV integrity
//! relies on collision-resistant hashing by the prover. In-circuit PV→trace
//! linkage via Poseidon2 commitment is deferred to Phase 4a-4/Phase 5.

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::{Field, PrimeCharacteristicRing},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

/// Width of the main trace.
pub const WIDTH: usize = 2;

/// FlatInitChip with context data in main trace and public values.
///
/// `ctx_hashes` contains the initial linear context fact hashes.
/// `max_ctx_size` determines the fixed number of public values (for constant VK across chunks).
/// `min_rows` ensures trace height is at least this value.
pub struct FlatInitChip {
    pub ctx_hashes: Vec<u32>,
    pub max_ctx_size: usize,
    pub min_rows: usize,
}

impl<F: Field> BaseAir<F> for FlatInitChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F: Field> BaseAirWithPublicValues<F> for FlatInitChip {
    fn num_public_values(&self) -> usize {
        self.max_ctx_size
    }
}

impl<F: Field> PartitionedBaseAir<F> for FlatInitChip {}

impl<AB: InteractionBuilder> Air<AB> for FlatInitChip
where
    AB::F: Field,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[0].clone().into();
        let hash: AB::Expr = local[1].clone().into();

        // is_active ∈ {0, 1}
        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        // inactive rows must have hash = 0
        builder.assert_zero((AB::Expr::ONE - is_active.clone()) * hash.clone());

        CONTEXT_BUS.send(builder, [hash], is_active);
    }
}
