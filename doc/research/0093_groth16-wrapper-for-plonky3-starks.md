---
title: "Groth16 Wrapper for Plonky3 STARKs"
created: 2026-03-13
modified: 2026-03-13
summary: "Survey of approaches for wrapping Plonky3 BabyBear/KoalaBear STARKs into BN254 Groth16 or PLONK proofs for on-chain Ethereum verification."
tags: [blockchain, ethereum, verification, proof-systems, zk-proofs, groth16, plonky3]
category: "Implementation"
---

# Groth16 Wrapper for Plonky3 STARKs

## Problem

STARKs (e.g. Plonky3 over BabyBear/KoalaBear) are too large (~200 KB) for economical on-chain Ethereum verification. The standard workaround is to *wrap* the STARK proof inside a Groth16 SNARK, which is ~200 bytes and costs ~270k gas to verify on-chain via the `bn254` pairing precompile. The Groth16 circuit checks the STARK verification logic as its constraint system.

The field mismatch is the core difficulty: Plonky3 STARKs work over ~31-bit fields (BabyBear p=2^31-2^27+1, KoalaBear p=2^31-2^24+1), while BN254 Groth16 works over a ~254-bit scalar field. Encoding 31-bit arithmetic in 254-bit constraints is expensive but feasible.

---

## Option 1: SP1's Groth16 Wrapper (Succinct)

**Status:** Production, mainnet. Available now (2024–2025).

**Architecture:**

```
SP1 program (Rust/LLVM)
  → RISC-V execution trace
  → Plonky3 STARK (KoalaBear field, FRI, Poseidon2)
  → SP1 recursion: compress STARK → smaller STARK ("compressed" proof)
  → gnark circuit: interpret compressed proof as BN254 field arithmetic
  → Groth16 or PLONK proof over BN254
  → Solidity verifier contract on Ethereum
```

**Technical details (from source):**

- Lives in `crates/recursion/gnark-ffi/` in the SP1 repo.
- The gnark circuit (`sp1.go`) is a **bytecode interpreter**: it reads a constraint JSON file (encoding the verification of the compressed recursion proof) and replays field arithmetic opcodes (`AddF`, `MulE`, `AssertEqV`, etc.) inside the gnark `Define` method.
- Field arithmetic uses gnark's KoalaBear and Poseidon2 sub-circuits (in `koalabear/`, `poseidon2/` subdirs).
- Two backends: Groth16 and PLONK (KZG), both over BN254.
- The trusted setup for Groth16 uses a p0tion ceremony (April–May 2024), with R1CS and proving key stored externally (AWS S3).
- GPU acceleration via ICICLE library (`prove_groth16_icicle.go`).
- The Solidity side: `ISP1Verifier` interface, deployed verifiers `SP1VerifierGroth16` and `SP1VerifierPlonk`, routed by `SP1_VERIFIER_GATEWAY`.
- Public inputs to the on-chain verifier: `VkeyHash`, `CommittedValuesDigest`, `ExitCode`, `VkRoot`, `ProofNonce`.

**License:** Apache-2.0 / MIT (dual).

**Reusability for custom Plonky3 proofs:**
SP1's wrapper is tightly coupled to SP1's own recursion circuit and proof format. To use it for custom Plonky3-based proofs, you would need to:
1. Either run your computation through SP1 (write it as an SP1 guest program), OR
2. Reverse-engineer the constraint JSON format and produce compatible witnesses from your own Plonky3 proof—which would require substantial reverse-engineering effort.

Option (1) is feasible if your computation can be expressed as SP1 guest code. Option (2) is not currently practical without deep SP1 internals knowledge.

**Gas cost:** Not published in SP1 docs, but BN254 Groth16 is typically 260–280k gas (dominated by 2 pairings).

---

## Option 2: gnark-plonky2-verifier (Succinct Labs, MIT)

**Repo:** `github.com/succinctlabs/gnark-plonky2-verifier`

**Status:** Available (2023–2024), MIT licensed, 108 stars, 201 commits.

**What it is:** A gnark circuit that verifies **Plonky2** proofs (not Plonky3). Implements:
- Goldilocks field arithmetic (64-bit, p = 2^64 - 2^32 + 1)
- Poseidon hash over Goldilocks
- FRI protocol verification

**Plonky3 gap:** Plonky3 uses different fields (BabyBear/KoalaBear/Mersenne31 rather than Goldilocks) and has a different proof format. This verifier cannot be used directly for Plonky3 proofs. Extending it would require replacing the Goldilocks arithmetic circuits with BabyBear/KoalaBear circuits and adapting the FRI/Poseidon2 logic—a significant but not unbounded engineering effort.

**No gnark-plonky3:** As of early 2026, no public `gnark-plonky3` implementation exists.

---

## Option 3: RISC Zero's STARK→Groth16 Pipeline

**Status:** Production, available. License: Apache-2.0 / MIT.

**Architecture:**

```
RISC-V execution
  → RISC Zero STARK (DEEP-ALI + FRI, three-layer recursive system)
  → stark2snark: Circom circuit (stark_verify.circom, ~58 MB via Git LFS)
  → Groth16 proof via SnarkJS/Circom toolchain
  → on-chain Solidity verifier
```

**Technical details:**
- Uses **Circom** (not gnark) for the Groth16 circuit.
- The STARK verifier circuit is `stark_verify.circom` (~58 MB, suggesting large constraint count, likely tens of millions of R1CS constraints).
- Trusted setup via p0tion ceremony (same timeframe as SP1).
- The recommended API: `risc0-zkvm::Prover` trait (Docker-based workflow for Groth16).
- `risc0_groth16::Seal` is the compact output embedded in `InnerReceipt::Groth16`.

**Reusability:** RISC Zero uses its own STARKs (not Plonky3), so this is not directly reusable.

---

## Option 4: Custom Build

**What a custom Groth16 wrapper for Plonky3 would need:**

A gnark circuit verifying a Plonky3 FRI-based STARK must implement:

| Component | Constraint cost |
|---|---|
| BabyBear field arithmetic (emulated in BN254) | ~5–10 constraints per field op |
| Poseidon2 permutation (width 16, BabyBear) | ~1000–2000 R1CS constraints per call |
| FRI commit phase: Merkle tree hashing (log2(domain) levels) | O(log N) Poseidon2 calls |
| FRI query phase: per-query polynomial evaluations + interpolation | O(queries × depth) |
| PLONK/AIR constraint checks at query points | O(queries × constraints) |

Rough estimate for a Plonky3 STARK with 28 FRI queries, domain size 2^20, and moderate AIR constraints: **50–200 million R1CS constraints**. This is at the upper end of what Groth16 can handle practically (large proving key, multi-hour trusted setup ceremony).

**Comparison:** RISC Zero's `stark_verify.circom` is 58 MB source, implying tens of millions of constraints—consistent with this estimate.

**Feasibility:** Technically feasible, 6–18 months of engineering. The gnark-plonky2-verifier is a useful starting point for the FRI and hash circuit components, with BabyBear/KoalaBear field arithmetic replacing Goldilocks.

**Trusted setup requirement:** Groth16 requires a circuit-specific trusted setup ceremony. This is a one-time cost but requires coordination.

---

## Option 5: STARK on BN254 Field (Polygon/Miden approach)

Instead of emulating a small-field STARK inside Groth16, run a *final recursion STARK* over the BN254 scalar field (~254 bits). This makes the subsequent Groth16 circuit cheaper because BN254 arithmetic is "native."

**Polygon zkEVM approach:** Polygon uses STARKs internally (PIL/Pil2 language, C++ prover) with a recursion layer ending in FFLONK (not Groth16), verified on-chain. Their `stark-recurser` uses Circom.

**Miden/StarkWare approach:** StarkWare's STARKs use a prime field compatible with Ethereum. For their on-chain verifier, they can deploy a full STARK verifier in Solidity directly (the "SHARP verifier"), or wrap in a SNARK.

**Applicability:** To apply this to our Plonky3 proofs, we would add a final recursion step where a BN254-field STARK (e.g. using gnark-based PLONK/Groth16-friendly constraints) verifies the KoalaBear STARK. This is the architecture that systems like Polygon CDK use. Reduces Groth16 circuit size but adds a new recursion STARK layer.

---

## Option 6: PLONK with KZG on BN254

Instead of Groth16, use PLONK with KZG commitments over BN254. SP1 already offers this as `SP1ProofMode::Plonk`.

**Properties:**
- No circuit-specific trusted setup (KZG uses universal powers-of-tau, e.g. Hermez ceremony, ~8 MB for large circuits).
- Proof size slightly larger than Groth16 (~800 bytes vs ~200 bytes).
- Verification gas cost: typically **350–500k gas** vs ~270k for Groth16.
- Proving time: slower than Groth16 for the same circuit.

**gnark PLONK:** gnark supports PLONK over BN254 (Apache-2.0). This is what SP1 uses for its PLONK backend.

**Verdict:** PLONK is simpler to set up (no circuit-specific ceremony) but costs more gas and produces larger proofs. Reasonable alternative if trusted setup is a blocker.

---

## Summary Table

| Option | Available? | Open Source? | Integration Effort | Gas Cost |
|---|---|---|---|---|
| SP1 Groth16 wrapper (via SP1 as zkVM) | Yes (production) | Apache-2.0/MIT | Low if using SP1 as runtime; High for custom Plonky3 | ~270k |
| SP1 PLONK wrapper (via SP1) | Yes (production) | Apache-2.0/MIT | Same as above | ~400k |
| gnark-plonky2-verifier (extend to Plonky3) | Partial (Plonky2 only) | MIT | High (6–12 months, replace Goldilocks with KoalaBear) | ~270k |
| RISC Zero STARK→Groth16 | Yes (production) | Apache-2.0/MIT | Not applicable (different STARK system) | ~270k |
| Custom gnark Plonky3 verifier | Not yet | N/A | Very high (12–18 months) | ~270k |
| BN254-field final recursion layer | No ready impl | N/A | High (6–12 months) | ~270k |
| PLONK/KZG wrapper (gnark) | Yes (via SP1 or gnark directly) | Apache-2.0 | High for custom Plonky3 | ~400k |

---

## Key Findings

**Shortest path today:** If our Plonky3 proofs are generated inside SP1 (i.e. the computation runs as an SP1 guest), we get Groth16/PLONK wrapping for free via SP1's production pipeline. SP1 is Apache-2.0/MIT, actively maintained, audited, and has deployed Solidity verifiers.

**gnark-plonky2-verifier is the closest reusable building block** if we need a standalone gnark circuit for Plonky3. Porting from Goldilocks (64-bit) to KoalaBear (31-bit) is non-trivial but the FRI and circuit-interpreter architecture is directly applicable.

**No gnark-plonky3 exists** as a standalone library (as of 2026-03). SP1 embeds a gnark-based Plonky3 verifier internally but it is tightly coupled to SP1's recursion format, not published as a reusable library.

**Trusted setup for Groth16** is unavoidable and circuit-specific. SP1 and RISC Zero have both run ceremonies. A custom wrapper would need a new ceremony.

**PLONK/KZG** avoids the circuit-specific trusted setup (uses the universal BN254 powers-of-tau) at the cost of ~50% higher gas and larger proofs.

---

## References

- SP1 repo: `github.com/succinctlabs/sp1` (Apache-2.0/MIT)
- SP1 contracts: `github.com/succinctlabs/sp1-contracts`
- gnark-plonky2-verifier: `github.com/succinctlabs/gnark-plonky2-verifier` (MIT)
- gnark: `github.com/Consensys/gnark` (Apache-2.0)
- RISC Zero groth16_proof: `github.com/risc0/risc0/tree/main/groth16_proof`
- Polygon stark-recurser: `github.com/0xPolygonHermez/stark-recurser`
- Plonky3: `github.com/Plonky3/Plonky3`
