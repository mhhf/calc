//! Phase 6-7+: Recursive composition for symbolic exploration paths.
//!
//! Verifies N independent symbolic path proofs (each a tree-path STARK) under
//! a single shared VK in a recursive verifier program.
//!
//! Key differences from tree chunk composition:
//! - No PV continuity checks (paths are independent, not sequential chunks)
//! - Each path has its own init PVs (sequent identity)
//! - We commit: VK hash (program identity)
//!
//! Pipeline: normalize_tree_witnesses → prove_witnesses_shared_keygen
//!   → build composition DSL → execute/prove recursive STARK

use openvm_native_circuit::{NativeConfig, NativeCpuBuilder};
use openvm_native_compiler::{conversion::CompilerOptions, prelude::*};
use openvm_native_compiler::ir::DIGEST_SIZE;
use openvm_native_recursion::{
    challenger::duplex::DuplexChallengerVariable,
    fri::TwoAdicFriPcsVariable,
    hints::Hintable,
    stark::StarkVerifier,
    types::{new_from_inner_multi_vk, InnerConfig},
    utils::const_fri_config,
    vars::StarkProofVariable,
};
use openvm_stark_sdk::config::{
    baby_bear_poseidon2::{BabyBearPoseidon2Config, BabyBearPoseidon2Engine},
    FriParameters,
};
use openvm_stark_sdk::engine::StarkFriEngine;
use openvm_stark_backend::proof::Proof;
use openvm_circuit::arch::{instructions::exe::VmExe, Streams, VirtualMachine};
use openvm_circuit::utils::air_test_impl;
use p3_baby_bear::BabyBear;

use sequent_certifier::bridge::{
    normalize_tree_witnesses, prove_witnesses_shared_keygen, WitnessJson,
};

/// NativeConfig for recursive composition.
///
/// Uses aggregation config (no continuations, single segment).
/// With OPENVM_FAST_TEST=1, inner proofs are smaller and the composition
/// fits in one segment (~20M cells for 1 path, ~66M for 3 paths).
/// Standard FRI params produce larger inner proofs (~264M cells for 1 path)
/// that may OOM on <64GB machines.
fn composition_config(n_committed: usize) -> NativeConfig {
    NativeConfig::aggregation(n_committed, 3)
}

fn load_fixture(name: &str) -> String {
    let path = format!(
        "{}/tests/fixtures/{}.json",
        env!("CARGO_MANIFEST_DIR"),
        name
    );
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture {name}.json not found at {path}: {e}"))
}

fn parse_witness(json: &str) -> WitnessJson {
    serde_json::from_str(json).expect("parse WitnessJson")
}

/// Build a composition DSL program that verifies N proofs with shared VK.
///
/// The program:
/// 1. Reads Vec<Proof> from hint stream
/// 2. Verifies each proof against the shared MultiStarkVerificationAdvice
/// 3. Commits VK pre_hash as public values (program identity)
///
/// Returns (VmExe, n_committed_pvs).
fn build_symbolic_composition_program(
    vk: &openvm_stark_backend::keygen::types::MultiStarkVerifyingKey<BabyBearPoseidon2Config>,
    fri_params: FriParameters,
) -> (VmExe<BabyBear>, usize) {
    let m_advice = new_from_inner_multi_vk(vk);
    let mut builder = Builder::<InnerConfig>::default();

    let pcs = TwoAdicFriPcsVariable {
        config: const_fri_config(&mut builder, &fri_params),
    };

    // Read Vec<Proof> from hint stream
    let proof_vars: Array<InnerConfig, StarkProofVariable<InnerConfig>> =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::read(&mut builder);
    builder.assert_nonzero(&proof_vars.len());

    // Verify each proof against shared advice
    builder.range(0, proof_vars.len()).for_each(|i_vec, builder| {
        let i: RVar<_> = i_vec[0];
        let proof = builder.get(&proof_vars, i);

        StarkVerifier::verify::<DuplexChallengerVariable<InnerConfig>>(
            builder, &pcs, &m_advice, &proof,
        );
    });

    // Commit VK pre_hash (program identity)
    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();
    for &h in &vk_hash {
        let val: Felt<BabyBear> = builder.constant(h);
        builder.commit_public_value(val);
    }

    builder.halt();

    let program = builder.compile_isa_with_options(CompilerOptions::default());
    let n_instructions = program.instructions_and_debug_infos.len();
    println!("  composition program: {n_instructions} instructions, {DIGEST_SIZE} committed PVs");
    (VmExe::new(program), DIGEST_SIZE)
}

/// Basic composition test: verify 3 symbolic path proofs in a recursive verifier.
///
/// Uses metered interpreter (no outer STARK proving) — fast, tests DSL correctness.
#[test]
fn p6_symbolic_composition_3_paths() {
    // Spawn with 64MB stack for metered interpreter
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(p6_symbolic_composition_3_paths_inner)
        .unwrap();
    handle.join().unwrap();
}

fn p6_symbolic_composition_3_paths_inner() {
    let t0 = std::time::Instant::now();

    // --- 1. Prove 3 symbolic paths with shared keygen ---
    let jsons: Vec<String> = (0..3)
        .map(|i| load_fixture(&format!("solc_symbolic_{i:03}")))
        .collect();
    let mut witnesses: Vec<WitnessJson> = jsons.iter().map(|j| parse_witness(j)).collect();

    normalize_tree_witnesses(&mut witnesses);
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();

    println!("  inner proving: {:.2}s (3 paths)", t0.elapsed().as_secs_f64());

    // Confirm shared VK
    for (i, r) in results.iter().enumerate().skip(1) {
        assert_eq!(vk.pre_hash, r.data.vk.pre_hash, "VK mismatch at path {i}");
    }

    // --- 2. Build composition program ---
    let (exe, n_committed) = build_symbolic_composition_program(vk, fri_params);

    // --- 3. Execute composition via metered interpreter ---
    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);

    let config = openvm_native_circuit::NativeConfig::aggregation(n_committed, 3);
    let engine = BabyBearPoseidon2Engine::new(FriParameters::new_for_testing(1));
    let (vm, _) = VirtualMachine::<_, NativeCpuBuilder>::new_with_keygen(
        engine, NativeCpuBuilder, config,
    ).unwrap();
    let ctx = vm.build_metered_ctx(&exe);
    let (segments, _) = vm
        .metered_interpreter(&exe).unwrap()
        .execute_metered(Streams::from(input_stream), ctx).unwrap();
    println!("  composition executed: {} segment(s), {:.2}s total",
        segments.len(), t0.elapsed().as_secs_f64());
}

/// Full recursive STARK proof for symbolic composition with committed PVs.
///
/// Proves: "this symbolic path verifies under program VK."
/// Committed PVs: VK pre_hash (DIGEST_SIZE field elements).
///
/// Requires OPENVM_FAST_TEST=1 on <64GB machines (fast FRI reduces inner proof
/// size so the composition fits in one segment at ~20M cells).
#[test]
#[ignore] // OPENVM_FAST_TEST=1 cargo test --release -- --ignored p6_symbolic_composition_recursive_1
fn p6_symbolic_composition_recursive_1_path() {
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(p6_symbolic_composition_recursive_1_path_inner)
        .unwrap();
    handle.join().unwrap();
}

fn p6_symbolic_composition_recursive_1_path_inner() {
    let t0 = std::time::Instant::now();

    // --- 1. Prove 1 symbolic path ---
    let json = load_fixture("solc_symbolic_000");
    let mut witnesses: Vec<WitnessJson> = vec![parse_witness(&json)];

    normalize_tree_witnesses(&mut witnesses);
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();
    println!("  step 1: inner proving {:.2}s (1 path)", t0.elapsed().as_secs_f64());

    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();

    // --- 2. Build composition program ---
    let (exe, n_committed) = build_symbolic_composition_program(vk, fri_params);

    // --- 3. Generate recursive STARK proof via air_test_impl ---
    println!("  step 3: generating recursive STARK proof...");
    let t_outer = std::time::Instant::now();

    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);

    let config = composition_config(n_committed);
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
        NativeCpuBuilder,
        config,
        exe,
        input_stream,
        1,
        true,
    ).expect("symbolic composition recursive proof should succeed");

    println!("  outer STARK: {:.2}s ({} segment(s))", t_outer.elapsed().as_secs_f64(), vdata_vec.len());

    // --- 4. Verify committed PVs in last segment ---
    let vdata = vdata_vec.last().unwrap();

    // Find PV AIR by matching expected count
    let pv_counts: Vec<usize> = vdata.data.proof.per_air.iter()
        .map(|a| a.public_values.len()).collect();
    let pv_air_idx = pv_counts.iter().position(|&n| n == n_committed)
        .unwrap_or_else(|| panic!(
            "no AIR with {} PVs found; counts: {:?}", n_committed, pv_counts
        ));
    let pvs = &vdata.data.proof.per_air[pv_air_idx].public_values;

    for (k, &expected) in vk_hash.iter().enumerate() {
        assert_eq!(pvs[k], expected, "VK hash[{k}] mismatch");
    }

    let total = t0.elapsed().as_secs_f64();
    println!("  all committed PVs verified!");
    println!("  total: {total:.2}s (inner + outer)");
}

/// 3-path recursive STARK composition.
///
/// Verifies 3 symbolic paths in a single composition STARK.
/// With OPENVM_FAST_TEST=1: ~66M cells, single segment, ~30s.
#[test]
#[ignore] // OPENVM_FAST_TEST=1 cargo test --release -- --ignored p6_symbolic_composition_recursive_3
fn p6_symbolic_composition_recursive_3_paths() {
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(p6_symbolic_composition_recursive_3_paths_inner)
        .unwrap();
    handle.join().unwrap();
}

fn p6_symbolic_composition_recursive_3_paths_inner() {
    let t0 = std::time::Instant::now();

    // --- 1. Prove 3 symbolic paths with shared keygen ---
    let jsons: Vec<String> = (0..3)
        .map(|i| load_fixture(&format!("solc_symbolic_{i:03}")))
        .collect();
    let mut witnesses: Vec<WitnessJson> = jsons.iter().map(|j| parse_witness(j)).collect();

    normalize_tree_witnesses(&mut witnesses);
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();
    println!("  step 1: inner proving {:.2}s (3 paths)", t0.elapsed().as_secs_f64());

    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();

    // --- 2. Build composition program ---
    let (exe, n_committed) = build_symbolic_composition_program(vk, fri_params);

    // --- 3. Generate recursive STARK proof with segmented proving ---
    println!("  step 3: generating recursive STARK proof (3 paths, segmented)...");
    let t_outer = std::time::Instant::now();

    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);

    let config = composition_config(n_committed);
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
        NativeCpuBuilder,
        config,
        exe,
        input_stream,
        1,
        true,
    ).expect("3-path symbolic composition should succeed");

    println!("  outer STARK: {:.2}s ({} segment(s))", t_outer.elapsed().as_secs_f64(), vdata_vec.len());

    // Verify committed PVs in last segment
    let vdata = vdata_vec.last().unwrap();
    let pv_counts: Vec<usize> = vdata.data.proof.per_air.iter()
        .map(|a| a.public_values.len()).collect();
    let pv_air_idx = pv_counts.iter().position(|&n| n == n_committed)
        .unwrap_or_else(|| panic!(
            "no AIR with {} PVs found; counts: {:?}", n_committed, pv_counts
        ));
    let pvs = &vdata.data.proof.per_air[pv_air_idx].public_values;

    for (k, &expected) in vk_hash.iter().enumerate() {
        assert_eq!(pvs[k], expected, "VK hash[{k}] mismatch");
    }

    let total = t0.elapsed().as_secs_f64();
    println!("  all committed PVs verified! (3 paths)");
    println!("  total: {total:.2}s");
}

/// Full 31-path recursive composition.
///
/// End-to-end: normalize 31 paths → shared keygen → compose → recursive STARK.
/// Warning: ~600M cells with fast FRI, requires ~48GB+ RAM.
#[test]
#[ignore] // OPENVM_FAST_TEST=1 cargo test --release -- --ignored p6_symbolic_composition_all_31
fn p6_symbolic_composition_all_31_recursive() {
    let handle = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(p6_symbolic_composition_all_31_recursive_inner)
        .unwrap();
    handle.join().unwrap();
}

fn p6_symbolic_composition_all_31_recursive_inner() {
    let t0 = std::time::Instant::now();

    // --- 1. Prove all 31 symbolic paths with shared keygen ---
    let jsons: Vec<String> = (0..31)
        .map(|i| load_fixture(&format!("solc_symbolic_{i:03}")))
        .collect();
    let mut witnesses: Vec<WitnessJson> = jsons.iter().map(|j| parse_witness(j)).collect();

    normalize_tree_witnesses(&mut witnesses);
    let results = prove_witnesses_shared_keygen(&witnesses)
        .expect("shared keygen proving failed");

    let vk = &results[0].data.vk;
    let fri_params = results[0].fri_params;
    let proofs: Vec<Proof<BabyBearPoseidon2Config>> = results.iter()
        .map(|r| r.data.proof.clone())
        .collect();
    println!("  step 1: inner proving {:.2}s (31 paths)", t0.elapsed().as_secs_f64());

    let vk_hash: [BabyBear; DIGEST_SIZE] = vk.pre_hash.clone().into();

    // --- 2. Build composition program ---
    let (exe, n_committed) = build_symbolic_composition_program(vk, fri_params);

    // --- 3. Generate recursive STARK proof ---
    println!("  step 3: generating recursive STARK proof (31 paths)...");
    let t_outer = std::time::Instant::now();

    let input_stream =
        <Vec<Proof<BabyBearPoseidon2Config>> as Hintable<InnerConfig>>::write(&proofs);

    let config = composition_config(n_committed);
    let (_mem, vdata_vec) = air_test_impl::<BabyBearPoseidon2Engine, _>(
        FriParameters::new_for_testing(3),
        NativeCpuBuilder,
        config,
        exe,
        input_stream,
        1,
        true,
    ).expect("31-path symbolic composition should succeed");

    println!("  outer STARK: {:.2}s ({} segment(s))", t_outer.elapsed().as_secs_f64(), vdata_vec.len());

    // Verify committed PVs in last segment
    let vdata = vdata_vec.last().unwrap();
    let pv_counts: Vec<usize> = vdata.data.proof.per_air.iter()
        .map(|a| a.public_values.len()).collect();
    let pv_air_idx = pv_counts.iter().position(|&n| n == n_committed)
        .unwrap_or_else(|| panic!(
            "no AIR with {} PVs found; counts: {:?}", n_committed, pv_counts
        ));
    let pvs = &vdata.data.proof.per_air[pv_air_idx].public_values;

    for (k, &expected) in vk_hash.iter().enumerate() {
        assert_eq!(pvs[k], expected, "VK hash[{k}] mismatch");
    }

    let total = t0.elapsed().as_secs_f64();
    println!("  all 31 paths composed and verified!");
    println!("  total: {total:.2}s");
}
