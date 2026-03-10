//! Spike S3: Context tracking via bus + challenge access exploration
//!
//! Tests:
//! a) Pure bus context tracking (no grand product accumulator)
//! b) Whether PermutationAirBuilder is accessible in Air::eval (compilation test)
//! c) Extension field challenge usage in constraints
//!
//! Key finding: stark-backend's LogUp operates in the extension field.
//! Delta_acc (grand product) also naturally lives in the extension field.
//! If we can constrain stage-0 columns against extension-field challenges,
//! we can implement delta_acc. Otherwise, we use the pure-bus approach.

use std::sync::Arc;

use openvm_stark_backend::{
    interaction::{InteractionBuilder, PermutationCheckBus},
    p3_air::{Air, BaseAir, ExtensionBuilder, PermutationAirBuilder},
    p3_field::PrimeCharacteristicRing,
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    AirRef,
};
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine, engine::StarkFriEngine,
};
use p3_baby_bear::BabyBear;

// ---- Test 3a: Pure bus context tracking ----

const DELTA_BUS: PermutationCheckBus = PermutationCheckBus::new(0);

/// ContextTrackerAir: models context operations via bus send/receive
/// Columns: [hash, sel_init, sel_id, sel_pad]
/// init: sends hash on DELTA_BUS (element enters context)
/// id: receives hash from DELTA_BUS (element consumed from context)
struct ContextTrackerAir;

impl<F> BaseAir<F> for ContextTrackerAir {
    fn width(&self) -> usize { 4 }
}
impl<F> BaseAirWithPublicValues<F> for ContextTrackerAir {}
impl<F> PartitionedBaseAir<F> for ContextTrackerAir {}

impl<AB: InteractionBuilder> Air<AB> for ContextTrackerAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let hash: AB::Expr = local[0].clone().into();
        let sel_init: AB::Expr = local[1].clone().into();
        let sel_id: AB::Expr = local[2].clone().into();
        let sel_pad: AB::Expr = local[3].clone().into();

        // Exactly one selector active
        builder.assert_one(sel_init.clone() + sel_id.clone() + sel_pad.clone());

        // Boolean checks
        builder.assert_zero(sel_init.clone() * (sel_init.clone() - AB::Expr::ONE));
        builder.assert_zero(sel_id.clone() * (sel_id.clone() - AB::Expr::ONE));
        builder.assert_zero(sel_pad.clone() * (sel_pad.clone() - AB::Expr::ONE));

        // Init sends formula to context bus
        DELTA_BUS.send(builder, [hash.clone()], sel_init);

        // Id receives (consumes) formula from context bus
        DELTA_BUS.receive(builder, [hash], sel_id);
    }
}

#[test]
fn s3a_identity_proof_via_bus() {
    // A ⊢ A: init sends A, id consumes A
    let h_a = 42u32;
    let data: Vec<BabyBear> = vec![
        h_a, 1, 0, 0, // init: send A
        h_a, 0, 1, 0, // id: consume A
        0, 0, 0, 1,   // pad
        0, 0, 0, 1,   // pad
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(ContextTrackerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(data, 4)],
        vec![vec![]],
    )
    .expect("S3a: A ⊢ A via bus context tracking");
}

#[test]
fn s3a_tensor_decompose_via_bus() {
    // A ⊗ B ⊢ B ⊗ A: init sends A⊗B, tensor_l decomposes, tensor_r recomposes
    // Modeled as: send A⊗B, receive A⊗B, send A, send B, receive B, receive A
    let h_ab = 100u32;
    let h_a = 42u32;
    let h_b = 43u32;
    let data: Vec<BabyBear> = vec![
        h_ab, 1, 0, 0, // init: send A⊗B
        h_ab, 0, 1, 0, // tensor_l: consume A⊗B
        h_a, 1, 0, 0,  // tensor_l: produce A
        h_b, 1, 0, 0,  // tensor_l: produce B
        h_b, 0, 1, 0,  // id(B): consume B
        h_a, 0, 1, 0,  // id(A): consume A
        0, 0, 0, 1,    // pad
        0, 0, 0, 1,    // pad
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(ContextTrackerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(data, 4)],
        vec![vec![]],
    )
    .expect("S3a: A⊗B ⊢ B⊗A via bus context tracking");
}

#[test]
#[should_panic]
fn s3a_unconsumed_context_fails() {
    // Send A and B, only consume A — bus unbalanced
    let data: Vec<BabyBear> = vec![
        42, 1, 0, 0, // init: send A
        43, 1, 0, 0, // init: send B
        42, 0, 1, 0, // id: consume A only
        0, 0, 0, 1,  // pad
    ]
    .into_iter()
    .map(BabyBear::from_u32)
    .collect();

    BabyBearPoseidon2Engine::run_simple_test_fast(
        vec![Arc::new(ContextTrackerAir) as AirRef<_>],
        vec![RowMajorMatrix::new(data, 4)],
        vec![vec![]],
    )
    .expect("should fail: unconsumed context");
}

// ---- Test 3b: Challenge access in extension field ----
// Explore whether we can write constraints that reference the LogUp challenge.
// This uses ExtensionBuilder + PermutationAirBuilder to access randomness.

struct ChallengeTestAir;

impl<F> BaseAir<F> for ChallengeTestAir {
    fn width(&self) -> usize { 2 } // [hash, dummy]
}
impl<F> BaseAirWithPublicValues<F> for ChallengeTestAir {}
impl<F> PartitionedBaseAir<F> for ChallengeTestAir {}

impl<AB> Air<AB> for ChallengeTestAir
where
    AB: InteractionBuilder + PermutationAirBuilder + ExtensionBuilder,
{
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let hash: AB::Expr = local[0].clone().into();
        let dummy: AB::Expr = local[1].clone().into();

        // Access the challenge — this is an extension field element
        let challenges = builder.permutation_randomness();
        if !challenges.is_empty() {
            // Convert hash to extension field expression
            let hash_ef: AB::ExprEF = hash.clone().into();
            let r: AB::ExprEF = challenges[0].clone().into();

            // We CAN compute (r - hash) in the extension field
            let _delta: AB::ExprEF = r - hash_ef;

            // NOTE: We can't easily constrain this against a base-field witness column
            // because delta is in ExprEF and witness is in Expr.
            // This is the fundamental issue: delta_acc lives in the extension field.
        }

        // Still need at least one interaction for the challenge to exist
        DELTA_BUS.send(builder, [hash], AB::Expr::ONE);
        DELTA_BUS.receive(builder, [dummy], AB::Expr::ONE);
    }
}

#[test]
fn s3b_challenge_access_panics_in_symbolic_phase() {
    // KEY FINDING: permutation_randomness() panics during SymbolicRapBuilder
    // phase with "Challenge phase not supported". This means we CANNOT access
    // the LogUp challenge in Air::eval() — it's only available during the
    // LogUp evaluation phase (eval_fri_log_up_phase) which runs AFTER Air::eval.
    //
    // Consequence for delta_acc:
    // - Cannot constrain stage-0 witness columns against the verifier challenge
    // - Delta grand product accumulator needs a different approach:
    //   1. Pure bus context tracking (extra rows for additives) ← validated in S3a
    //   2. Fork stark-backend for user stage-1 columns
    //   3. Implement custom Rap trait (bypass blanket impl)
    //   4. Use prover-committed "challenge" (weaker soundness)
    let data: Vec<BabyBear> = vec![42, 42, 43, 43, 44, 44, 45, 45]
        .into_iter()
        .map(BabyBear::from_u32)
        .collect();

    let result = std::panic::catch_unwind(|| {
        BabyBearPoseidon2Engine::run_simple_test_fast(
            vec![Arc::new(ChallengeTestAir) as AirRef<_>],
            vec![RowMajorMatrix::new(data, 2)],
            vec![vec![]],
        )
    });

    assert!(result.is_err(), "Expected panic: challenge phase not available in Air::eval");
}
