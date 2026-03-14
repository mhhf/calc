//! FlatFinalChip: consumes remaining linear context for flat certificates.
//!
//! Each row receives one fact hash from CONTEXT_BUS. Paired with
//! FlatInitChip — init sends, final receives, steps consume/produce.
//! CONTEXT_BUS balance verifies: init = steps_consumed + final.
//!
//! Phase 4a: public values carry the final context hashes for cross-chunk
//! IVC verification. See FlatInitChip soundness note on PV gap.
//!
//! Columns (width 2): [is_active, hash]
//! Public values: final context hashes padded to max_ctx_size with zeros

use openvm_stark_backend::{
    interaction::InteractionBuilder,
    p3_air::{Air, BaseAir},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

use crate::buses::CONTEXT_BUS;

pub const WIDTH: usize = 2;

/// FlatFinalChip with public values for IVC context continuity.
///
/// `max_ctx_size` determines the number of public values (0 = no PVs, legacy mode).
pub struct FlatFinalChip {
    pub max_ctx_size: usize,
}

impl<F> BaseAir<F> for FlatFinalChip {
    fn width(&self) -> usize {
        WIDTH
    }
}

impl<F> BaseAirWithPublicValues<F> for FlatFinalChip {
    fn num_public_values(&self) -> usize {
        self.max_ctx_size
    }
}

impl<F> PartitionedBaseAir<F> for FlatFinalChip {}

impl<AB: InteractionBuilder> Air<AB> for FlatFinalChip {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();

        let is_active: AB::Expr = local[0].clone().into();
        let hash: AB::Expr = local[1].clone().into();

        builder.assert_zero(is_active.clone() * (is_active.clone() - AB::Expr::ONE));
        CONTEXT_BUS.receive(builder, [hash], is_active);
    }
}
