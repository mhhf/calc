---
title: "IVC / Recursive STARK Verifier Circuits for Plonky3"
created: 2026-03-13
modified: 2026-03-13
summary: "Survey of options for STARK-in-STARK verifier circuits to enable IVC with a BabyBear + Poseidon2 Plonky3 backend."
tags: [zk, stark, recursion, ivc, plonky3, babybear, poseidon2, implementation]
category: "Implementation"
---

# IVC / Recursive STARK Verifier Circuits for Plonky3

Research question (OQ-1): which existing systems provide a STARK verifier circuit — a circuit that verifies a STARK proof *inside* another STARK proof — compatible with BabyBear + Poseidon2 and Plonky3's stark-backend?

Context: We use the OpenVM fork of Plonky3's stark-backend (BabyBear field, Poseidon2 hash). IVC requires chunking execution traces and recursively composing chunk proofs. The recursion primitive is a "verifier circuit": an AIR that constrains the verification of a prior proof.

---

## Option 1: Plonky3 Native (`p3-recursion`)

**Repo:** https://github.com/Plonky3/Plonky3 (separate `p3-recursion` crate, not yet in the main repo)

**What exists:** A `Plonky3-recursion` library (crates: `p3-recursion-circuit`, `p3-recursion-verifier`, `p3-test-utils`) provides:
- Fixed recursive verifier for both `p3-uni-stark` and `p3-batch-stark` proofs
- FRI PCS verification in-circuit
- Poseidon2 and Keccak in-circuit
- Modular circuit builder

**Field/hash:** BabyBear and Goldilocks fields; Poseidon2 and Keccak supported.

**Production-ready:** No. Explicitly "under active development and hasn't been audited yet." A Lita Foundation review (Oct 2024) found: FRI verifier unimplemented (`fri/src/verifier.rs`), univariate STARK verifier has a check commented out with TODO, multivariate STARK has no verifier module at all.

**Universal Verifier proposal (Issue #511):** An Oct 2024 proposal to build a cross-project universal verifier. Currently a draft specification. Proposes BabyBear + Keccak (not Poseidon2) for on-chain compatibility. Not implemented.

**Standalone reuse:** The library is designed as standalone. Once complete, it would be the natural choice for any Plonky3 project.

**Integration complexity:** Low conceptually (same ecosystem), but the verifier is not yet complete. Would require contributing to upstream or waiting.

**License:** MIT/Apache-2.0 (Polygon/Plonky3).

---

## Option 2: SP1 (`sp1-recursion-circuit`)

**Repo:** https://github.com/succinctlabs/sp1

**What exists:** SP1 has a dedicated recursion stack:
- `sp1-recursion-core`: Recursion-specific ISA and VM
- `sp1-recursion-compiler`: DSL that compiles to recursion VM ISA or Gnark circuit
- `sp1-recursion-circuit`: The actual verifier circuit (depends on `p3-baby-bear`, `p3-poseidon2`, Plonky3 AIR/FRI)
- Four recursive verifier variants: core verifier (RISC-V traces), compress verifier (recursion proofs), deferred verifier (compressed proofs), root verifier (full tree)

**Field/hash:** BabyBear + Poseidon2 (width 16, rate 8, SBOX degree 7, 8 external + 13 internal rounds). Matches our stack exactly.

**Production-ready:** Yes — SP1 is in production (v4+). Recursion is core functionality, audited. Final SNARK wrapper uses Groth16/PLONK over BN254 via Gnark for on-chain verification.

**Standalone reuse:** Theoretically open (MIT/Apache-2.0), but practically very hard. The recursion circuit is deeply entangled with SP1's RISC-V execution trace structure, SP1-specific chip interconnects, and the SP1 prover network. Extracting just the STARK verifier circuit would require significant surgery. Succinct has described the recursion DSL and compiler as "generally useful public goods," but no one has successfully used them outside SP1.

**Integration complexity:** Very high. The circuit verifies SP1-specific proof shapes (shard proofs, different trace widths per chip). Our proof shape would differ — the circuit would need to be re-parameterized or rebuilt from the SP1 DSL.

**License:** MIT/Apache-2.0.

---

## Option 3: OpenVM (`openvm-native-recursion`)

**Repo:** https://github.com/openvm-org/openvm
**Backend:** https://github.com/openvm-org/stark-backend (the same backend we use)

**What exists:** OpenVM has the most directly relevant implementation:
- `openvm-native-recursion`: standalone Rust eDSL with functions to verify arbitrary STARK proofs. Compiles to the native VM extension for OpenVM. Supports inner aggregation of arbitrary STARK proofs, outer aggregation via Halo2-based SNARKs.
- `openvm-continuations`: aggregation programs written using `openvm-native-recursion` to support continuations for all VMs in the framework.
- `openvm-circuit-primitives`: primitive chips/sub-chips for standalone circuit use.
- `openvm-poseidon2-air`: standalone Poseidon2 AIR implementation (configurable constraint degree).
- Required system chips in any VM: Program, Public Values, Connector, Range Checker, Memory chips, Poseidon2 — all available as AIR.

**Field/hash:** BabyBear + Poseidon2. Exact match.

**How continuations work:** Single execution trace → segments → per-segment STARK proofs → aggregation tree (parallelizable) → single final proof. The aggregation uses the native VM to execute the STARK verifier circuit over prior proofs, producing a new proof.

**Production-ready:** Yes — OpenVM v1.0 (released 2025) is in production with external audits (Cantina, Jan–Mar 2025). Proving Ethereum mainnet blocks at <$0.001/tx.

**OpenVM 2.0 / SWIRL (2026):** A newer proof system replacing the Plonky3 backend with WHIR (multilinear PCS). Uses write-once memory for fixed recursion circuits. However, the v1 (Plonky3-based) code remains available and is the relevant branch for our BabyBear + Plonky3 context.

**Standalone reuse:** The `openvm-native-recursion` crate is explicitly designed to be usable as a standalone library for writing arbitrary STARK verifier circuits in an eDSL. The eDSL compiles to OpenVM's native VM extension — so it requires adopting OpenVM's native VM as the recursion VM, but does not require adopting the full application VM. This is the most practical extraction path.

**Integration complexity:** Medium. The verifier circuit targets OpenVM's native VM extension. To use it standalone, you instantiate the native VM as the recursion layer (separate from your application VM). OpenVM's framework is explicitly modular and designed for this. The main cost is learning the eDSL and wiring the recursion VM alongside the application proof system.

**License:** MIT/Apache-2.0 (dual).

---

## Option 4: powdr

**Repo:** https://github.com/powdr-labs/powdr

**What exists:** powdrVM supports zk-continuations: chunked execution → per-chunk proofs → recursive combination into a single STARK. The recursion aggregation step compresses the recursion tree to a single STARK. powdr is a multi-prover SDK (Halo2, Plonky3, eSTARK, GKR, Stwo) and integrates with OpenVM for precompiles.

**Field/hash:** powdr is backend-agnostic. With Plonky3 backend: BabyBear + Poseidon2 is possible, but the recursion details (which verifier circuit, which field) depend on the backend selection. Not as deeply specified as OpenVM.

**Production-ready:** Partial. Continuations are implemented (`--continuations` flag). The recursive aggregation step ("a follow-up tutorial is coming soon") is less documented. Multi-prover is production for individual proofs; full recursion is more experimental.

**Standalone reuse:** powdr is an SDK/compiler layer, not a verifier circuit library. The recursion happens through the prover infrastructure, not an extractable circuit primitive.

**Integration complexity:** High relative to goal — powdr is designed for full zkVM development, not as a recursion primitive library.

**License:** MIT/Apache-2.0.

---

## Option 5: Custom Plonky3 STARK Verifier Circuit

Building a verifier circuit from scratch in the Plonky3 AIR framework.

**What it entails:**
1. FRI verification as AIR constraints: fold steps, Merkle path checks (Poseidon2 hashing), low-degree test
2. DEEP-ALI / quotient polynomial evaluation at out-of-domain point
3. Poseidon2 sponge in-circuit (already available as `openvm-poseidon2-air`)
4. AIR constraint evaluation (evaluating the original AIR's transition/boundary constraints on committed trace values)
5. LogUp/GKR lookup argument verification (for multi-table proofs)

**Complexity:** Very high. This is months of expert cryptographic engineering. The recursive verifier is the hardest part of any STARK system — FRI in-circuit alone involves hundreds of constraint rows per verification query. SP1 spent significant effort on this; OpenVM's native recursion is the result of 12+ months of engineering by the Axiom team.

**Field/hash:** Full control — can be BabyBear + Poseidon2.

**Production-ready:** Would require its own audit. Starting from scratch means inheriting all correctness risk.

**Recommendation:** Only if no existing option integrates. Use `openvm-poseidon2-air` as a starting primitive regardless.

---

## Summary Table

| Option | Exists | BabyBear+P2 | Production | Standalone | Complexity |
|---|---|---|---|---|---|
| Plonky3 native (p3-recursion) | Partial | Yes | No (unaudited, incomplete) | Yes (once done) | Low (same stack) |
| SP1 recursion circuit | Yes | Yes | Yes | No (RISC-V entangled) | Very high |
| OpenVM native-recursion | Yes | Yes | Yes (audited) | Yes (eDSL library) | Medium |
| powdr continuations | Yes | Partial | Partial | No (full SDK) | High |
| Custom | — | Yes | No | Yes | Very high |

---

## Recommendation

**OpenVM `openvm-native-recursion`** is the strongest match:
- Exact field/hash match (BabyBear + Poseidon2)
- Same stark-backend we already use
- Explicitly designed as a reusable STARK verifier eDSL library
- Production-audited (Cantina 2025)
- MIT/Apache-2.0

The integration path: use OpenVM's native VM extension as the recursion layer. Application proofs (our AIR chips) are proven with openvm-stark-backend. Chunk proofs are fed into `openvm-native-recursion` programs running on the native VM, which verify the chunk proofs and produce an aggregated proof.

Watch `p3-recursion` — once its FRI verifier is complete and audited, it will be the lighter-weight alternative within the same ecosystem.

---

## Sources

- Plonky3 universal verifier proposal: https://github.com/Plonky3/Plonky3/issues/511
- p3-recursion crate: https://lib.rs/crates/p3-test-utils
- Lita Foundation Plonky3 review: https://www.lita.foundation/blog/plonky-3-valida-october-review
- SP1 recursion circuit crate: https://docs.rs/crate/sp1-recursion-circuit/0.0.2-test
- SP1 security model (Poseidon2/BabyBear details): https://docs.succinct.xyz/docs/sp1/security/security-model
- OpenVM repo layout: https://github.com/openvm-org/openvm/blob/main/docs/repo/layout.md
- OpenVM v1 release: https://blog.openvm.dev/v1
- OpenVM distributed proving: https://docs.openvm.dev/specs/architecture/distributed-proving/
- OpenVM 2.0 / SWIRL: https://blog.openvm.dev/2.0
- powdr zk-continuations: https://docs.powdr.org/frontends/zk-continuations.html
