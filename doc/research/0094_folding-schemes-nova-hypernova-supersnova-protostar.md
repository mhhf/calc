---
title: "Folding Schemes for IVC: Nova, HyperNova, SuperNova, ProtoStar"
created: 2026-03-17
modified: 2026-03-17
summary: "Research survey of folding-based IVC schemes as potential replacements for STARK-in-STARK recursion in our BabyBear/Plonky3 stack. Covers mechanism, costs, library maturity, and integration feasibility."
tags: [zk, stark, recursion, ivc, plonky3, babybear, performance, implementation]
category: "Implementation"
---

# Folding Schemes for IVC: Nova, HyperNova, SuperNova, ProtoStar

Research question: can folding schemes (Nova / HyperNova / SuperNova / ProtoStar) replace our STARK-in-STARK recursion (~37 s per step via `openvm-native-recursion`) with lower-latency composition?

Current stack: Plonky3 `=0.4.1` + `openvm-stark-backend` v1.3.0 + BabyBear field + Poseidon2 hash. Our recursion is implemented in `zk/sequent-certifier/tests/p5_spike_recursive_proof.rs` using `openvm-native-recursion`; it executes a BabyBear-native STARK verifier program (`NativeCpuBuilder`) and then STARK-proves that verifier execution.

---

## 1. Nova

**Paper:** Kothapalli & Setty, "Nova: Recursive Zero-Knowledge Arguments from Folding Schemes," CRYPTO 2022. https://eprint.iacr.org/2021/370

**Mechanism — relaxed R1CS folding.**
Nova's IVC collapses the task of verifying two R1CS instances into verifying one "relaxed" R1CS instance. At each step, the prover folds the new instance into an accumulator using a Non-Interactive Folding Scheme (NIFS). The verifier circuit is constant-sized: ~10,000 multiplication gates — dominated by two elliptic-curve scalar multiplications. There is no SNARK at each step; the expensive final SNARK (Spartan) is applied only once at the end to compress the accumulated proof.

**Prover cost per step:** two multi-scalar multiplications (MSMs) of size O(|F|) where |F| is the number of constraints in the step function. This is the cheapest known per-step cost in the IVC literature.

**Proof size:** O(|F|) group elements (grows with steps), compressed to O(log |F|) by a final Spartan SNARK.

**Verifier cost:** constant — two elliptic-curve scalar multiplications.

**Recursive overhead:** The recursion verifier circuit is the smallest in the literature (~10,000 mult gates). Nova claims this is the fastest prover and simplest recursive argument known.

**Constraint system:** R1CS only. Nova does not natively fold AIR or Plonkish. Expressing our STARK verifier as an R1CS circuit is theoretically possible but would require translating the BabyBear-field Poseidon2 + FRI verifier into R1CS — a large and non-trivial circuit.

**Curves supported (nova-snark library):**
- Pallas / Vesta (IPA-based)
- BN254 / Grumpkin (HyperKZG / KZG)
- secp / secq

**No BabyBear support. No Plonky3 integration.**

---

## 2. HyperNova

**Paper:** Setty, Thaler & Wahby, "Customizable constraint systems for succinct arguments," https://eprint.iacr.org/2023/552 (introduces CCS) + HyperNova extension https://eprint.iacr.org/2023/573

**CCS — Customizable Constraint Systems.**
CCS is a unified constraint framework that simultaneously generalizes R1CS, Plonkish, and AIR without computational overhead. HyperNova applies multilinear sumcheck-based folding to CCS, enabling one MSM per step equal in size to the number of variables.

**AIR compatibility:** CCS explicitly captures AIR. The CCS paper shows SuperSpartan for AIR achieves: linear-time prover, transparent setup, polylogarithmic proof size, post-quantum plausible security — matching or exceeding STARK performance.

**Speedup over Nova:** The prover's cryptographic cost drops to a single MSM (vs. two in Nova). HyperNova also supports folding multiple instances simultaneously ("à la carte" cost proportional to instruction invoked).

**Relevance for our stack:** In principle HyperNova can fold AIR constraints directly. However, folding our specific Plonky3 AIRs would require:
1. Re-expressing chips as CCS instances (structurally feasible since CCS subsumes AIR).
2. Implementing HyperNova's sumcheck-based folding over BabyBear — no existing library does this.

**Libraries:** No standalone Rust HyperNova library for BabyBear. `sonobe` implements HyperNova over Pallas/BN254.

---

## 3. SuperNova

**Paper:** Kothapalli & Setty, "SuperNova: Proving universal machine executions without universal circuits," https://eprint.iacr.org/2022/1758

**Non-uniform IVC.**
SuperNova extends Nova to handle different circuit types at each step. Instead of a single monolithic circuit, SuperNova maintains one running folded instance per instruction type (NIVC — Non-uniform IVC). Proving cost at each step is proportional only to the circuit for the instruction actually invoked — not the sum of all instruction circuits.

**Relevance:** Directly applicable when different chip compositions appear per proof chunk (e.g., different ILL rules per step). SuperNova avoids paying for unused circuits.

**Library:** `lurk-lab/arecibo` implements SuperNova (currently ahead of the main `microsoft/nova` repo). Curves: Pallas/Vesta, BN254/Grumpkin, secp/secq. No BabyBear.

**Lurk 0.5 performance (Sphinx STARK backend):** 19.4 s for 1M-cycle Fibonacci. This is STARK-based, not SuperNova-IVC. SuperNova CPU prover for similar programs (argument.xyz benchmark, AWS r7iz.metal) runs comparably — ~10–20 s range for ~1M cycles depending on circuit complexity.

---

## 4. ProtoStar

**Paper:** Bünz & Chen, "ProtoStar: Generic Efficient Accumulation/Folding for Special Sound Protocols," https://eprint.iacr.org/2023/620

**Mechanism.**
ProtoStar is a generic folding compiler for any (2k-1)-move special-sound protocol whose verifier checks polynomial equations. Applied to Plonk, it produces a non-uniform IVC scheme for Plonkish constraint systems with:

- k+2 elliptic curve multiplications and k+d+O(1) field/hash operations per accumulation step (k = protocol rounds, d = verifier degree).
- The recursive circuit depends only on the protocol parameters, not the proof size or verifier time.
- No FFTs, no trusted setup, no pairings.
- Logarithmic prover complexity in the number of supported circuits.
- Supports high-degree gates and vector lookups.

**Constraint system:** Plonkish (not R1CS, not AIR directly). ProtoStar is not applicable to raw AIR/STARK without a Plonkish translation layer.

**Advantages over Nova/HyperNova:** Supports high-degree gates and lookup tables natively. The recursive verifier circuit is very small (3 group scalar mults + hash of d* field elements for Plonk). FFT-free prover.

**ProtoGalaxy:** A related scheme ("ProtoGalaxy: Efficient ProtoStar-style folding of multiple instances") by Eagen & Gabizon folds multiple instances efficiently — used in Aztec's HonkRecursion.

**Library:** `sonobe` implements a ProtoGalaxy variant. `aztec-packages` implements ProtoGalaxy for Honk/UltraHonk circuits in C++. No Rust BabyBear library.

---

## 5. Practical integration with Plonky3 / STARK

### Can folding schemes fold Plonky3 STARK proofs directly?

No, not with any existing library. The mismatch is fundamental:

| Dimension | Folding (Nova/HyperNova) | Our Stack |
|---|---|---|
| Field | Large prime / 256-bit (elliptic curve scalar) | BabyBear (31-bit prime) |
| Commitment | Pedersen / KZG (elliptic curve) | FRI over BabyBear |
| Constraint system | R1CS / CCS / Plonkish | AIR (Plonky3 chips) |
| Curves | Pallas, BN254, Grumpkin | None (hash-based) |

**Approach A: Express STARK verifier as R1CS/CCS, then fold.**
The STARK verifier (FRI + Poseidon2 in BabyBear) must be expressed as an R1CS or CCS circuit over the elliptic curve scalar field. This is what Nova-Scotia does for Circom-expressed circuits. For our verifier:
- FRI verification involves many field operations and Merkle paths in BabyBear (31-bit), but R1CS operates over a 255-bit field.
- Non-native field arithmetic (BabyBear in a 255-bit field circuit) is expensive: roughly 10–100× overhead per field operation.
- A single Poseidon2 BabyBear hash round as non-native R1CS constraints: estimated ~1,000–10,000 R1CS constraints per call. Our FRI verifier performs many such calls.
- This approach is theoretically sound but would likely produce a verifier circuit with millions of R1CS constraints — making per-step folding slower than our current 37 s STARK verifier.

**Approach B: Native BabyBear IVC via CCS + HyperNova.**
CCS captures AIR natively. If someone implemented HyperNova over BabyBear with FRI-based polynomial commitments (instead of elliptic-curve MSM), the per-step cost would be: 1 MSM-equivalent (field operations over BabyBear). No such implementation exists. This is a research project, not an engineering task.

**Approach C: STARK verifier as Plonkish + ProtoStar.**
Similar to Approach A but for Plonkish. Same non-native arithmetic problem.

**Key insight:** The elliptic-curve MSM that makes Nova fast has no direct analog in hash-based STARK systems. Nova's efficiency assumes you are working *on* the elliptic curve's scalar field. BabyBear is not that field.

### AIR vs CCS relationship

CCS subsumes AIR: an AIR with transition polynomial of degree d can be expressed as a CCS instance with s terms (one per monomial in the transition constraint). The CCS overhead for this translation is zero in theory — SuperSpartan for AIR achieves a linear-time prover with polylogarithmic proof. However, CCS/HyperNova requires polynomial commitments compatible with the multilinear sumcheck — FRI works here in principle, but the MSM-based commitment schemes in all current HyperNova implementations are elliptic-curve-based.

### SP1's approach (reference point for our stack)

SP1 v4.0 (Succinct Labs) uses Plonky3 (BabyBear) + STARK-in-STARK recursion, achieving Ethereum block proof in <40 s on a GPU cluster. SP1 does not use folding schemes; it uses multi-layer STARK compression: Core STARK → Compressed STARK → Groth16 wrapper. This confirms that STARK-in-STARK is the current art for BabyBear-based systems, not folding.

### Plonky2's recursive STARK performance (lower-bound reference)

Plonky2 (Goldilocks field) achieves recursive proof generation in 170 ms on a MacBook Pro. This uses a STARK verifier expressed as a PLONK circuit over the same Goldilocks field (native-field recursion). Plonky3 with BabyBear aims for similar efficiency when its planned recursion crate matures.

---

## 6. Existing libraries

| Library | Schemes | Curves | BabyBear | Plonky3 | Maturity |
|---|---|---|---|---|---|
| **nova-snark** (microsoft/Nova) | Nova | Pallas, BN254, secp | No | No | Active, ~production-ready |
| **arecibo** (argumentcomputer) | Nova + SuperNova | Pallas, BN254, secp | No | No | Active fork, experimental |
| **sonobe** (PSE) | Nova, CycleFold, HyperNova, ProtoGalaxy | Pallas, BN254 | No | No | Experimental, pre-audit |
| **bellpepper** | Nova frontend (Groth16-like API) | via nova-snark | No | No | Active |
| **Nova-Scotia** | Circom→Nova bridge | Pallas, BN254 | No | No | Proof-of-concept |
| **openvm-native-recursion** | STARK-in-STARK | BabyBear | Yes | Yes | v1.5.0, production |
| **p3-recursion** (Plonky3) | FRI-based recursive STARK | BabyBear, Goldilocks | Yes | Yes | Under development, unaudited |

**None of the folding libraries support BabyBear or Plonky3.**

---

## 7. Alternative approaches

### Plonky3's own recursion roadmap

Plonky3's roadmap lists multivariate STARK, PLONK, tensor PCS, and adapters (univariate↔multivariate) as incomplete. The `p3-recursion` crate exists but FRI verifier is unimplemented; a Lita Foundation review (Oct 2024) found the univariate STARK verifier has a commented-out check and the multivariate STARK has no verifier at all.

**Conclusion:** Not usable today; 6–18 month horizon at best.

### OpenVM recursion roadmap

OpenVM v1.5.0 (recommended production) uses STARK-in-STARK via `openvm-native-recursion`. The architecture is: inner STARK proof → verifier program in OpenVM ISA → outer STARK proof of verifier execution. No folding scheme support is planned in public roadmap. The 37 s cost in our setup is the verifier program execution time on `NativeCpuBuilder`.

**Optimization opportunities within the current approach:**
- `FriParameters::new_for_testing(3)` uses very low security (log-blowup=3); production would use higher, increasing time further.
- Reducing AIR complexity of inner proofs reduces verifier program size.
- Multi-chunk batching: one outer proof verifies N inner proofs (already our approach in `p5_composition`).

### STIR: better FRI

STIR (CRYPTO 2024) reduces FRI argument size by 1.25–2.46× versus optimized FRI with comparable prover/verifier cost. If integrated into Plonky3 it would shrink inner proofs (fewer Merkle branches to verify in the outer circuit), reducing outer proof cost proportionally.

### Proof aggregation (Groth16 / PLONK wrapper)

RISC Zero's approach: STARK (BabyBear-like) → recursive STARK → Groth16. The Groth16 step compresses the recursive STARK proof to a constant-size (~288 bytes) EVM-verifiable proof. SP1 uses the same pattern. This is the production path if we need a succinct final proof, and it is orthogonal to reducing the recursive STARK cost.

### LatticeFold

LatticeFold (2024) is a lattice-based folding scheme — post-quantum, operates over a 64-bit field, performs comparably to HyperNova. Supports R1CS and CCS. No production implementation; still academic.

### Jolt-b

Jolt-b replaces Jolt's KZG commitment with Basefold (FRI-like), achieving O(log² N) verifier for recursive IVC. Uses Goldilocks field. Prover is 2.47× slower than standard Jolt but is recursion-friendly. Not BabyBear.

---

## 8. Performance estimates and comparison

### Nova per-step folding cost (CPU, estimate)

Nova's per-step prover cost = 2 MSMs of size |F| (number of R1CS constraints). For a STARK verifier circuit expressed in R1CS, |F| would be in the millions. Representative MSM timing: 1M constraints on a modern CPU ≈ 0.5–2 s per MSM → 1–4 s per fold step. But the circuit itself (non-native BabyBear arithmetic in 255-bit R1CS) could push |F| to 10–100M constraints → 10–100 s per step. **Likely worse than our current 37 s.**

### Our current STARK-in-STARK cost

37 s per inner proof verification (via `openvm-native-recursion` in test mode with `FriParameters::new_for_testing(3)`). This is at low security. At production security (blowup=8–16), this scales roughly as O(blowup × log(trace_length)) — possibly 2–5× slower.

### HyperNova over BabyBear (hypothetical)

If someone implemented HyperNova natively over BabyBear with FRI commitments:
- Per-step cost: 1 multi-linear sumcheck + 1 FRI evaluation proof ≈ O(|W| log |W|) prover time where |W| is the witness size.
- This could plausibly be faster than STARK-in-STARK, but no implementation exists.

### Nova-Scotia (Circom circuits, actual benchmarks)

Nova-Scotia verifying 120 Bitcoin blocks: 55 s total for 120 steps = 0.46 s per step. This is for a small Bitcoin block header verification circuit (few thousand constraints). For a STARK verifier circuit the per-step cost would be orders of magnitude higher due to non-native arithmetic.

### STARK recursion (Plonky2 reference)

Plonky2 achieves 170 ms per recursive step on a MacBook Pro (Goldilocks field, native-field recursion). This is the gold standard for STARK-in-STARK. Our 37 s is much slower partly because: (a) we use testing parameters, (b) BabyBear vs Goldilocks FFT characteristics differ, (c) OpenVM's native-recursion adds overhead from the ISA execution layer.

---

## 9. Conclusion: feasibility assessment

| Option | BabyBear | Engineering effort | Timeline | Likely faster? |
|---|---|---|---|---|
| Nova (fold STARK verifier as R1CS) | No | Very high (non-native arith, huge circuit) | 6–12 months | Unlikely |
| HyperNova native (CCS over BabyBear + FRI) | Would need new library | Research-level | 12–24 months | Possibly, if done right |
| SuperNova (non-uniform IVC) | No | Very high | 6–12 months | Unlikely |
| ProtoStar (Plonkish) | No | High | 6–12 months | Unlikely |
| Plonky3 native recursion (p3-recursion) | Yes | Medium (wait for upstream) | 6–18 months | Yes (likely ~2–10× faster than current) |
| Optimize current STARK-in-STARK | Yes | Low | Immediate | Moderate gains (2–5×) |
| STIR integration | Yes | High | 12+ months | Smaller proof → faster outer |
| Groth16 wrapper (final compression) | Via BN254 | Medium | 3–6 months | Different goal: succinctness, not speed |

**Recommendation:** Folding schemes in their current form are not compatible with BabyBear/Plonky3. All production folding libraries use 255-bit prime fields and elliptic-curve MSMs. Integrating them would require either:
(a) Non-native BabyBear field arithmetic in R1CS — prohibitively expensive, or
(b) A new HyperNova/CCS implementation over BabyBear — a major research project.

The most tractable path to faster recursion within our stack is:
1. **Short term:** Optimize chunk sizes and batch more inner proofs per outer proof to amortize the 37 s cost.
2. **Medium term:** Monitor `p3-recursion` development — when Plonky3's native recursive verifier matures, it will provide native-field STARK recursion (similar to Plonky2's 170 ms target) without any field-mismatch overhead.
3. **Long term:** If a HyperNova/CCS implementation appears over BabyBear + FRI commitments, it would be the ideal drop-in since CCS subsumes AIR and our chips map to CCS instances with zero overhead.

---

## References

- Nova: https://eprint.iacr.org/2021/370
- HyperNova/CCS: https://eprint.iacr.org/2023/552, https://eprint.iacr.org/2023/573
- SuperNova: https://eprint.iacr.org/2022/1758
- ProtoStar: https://eprint.iacr.org/2023/620
- CycleFold (security fix): https://eprint.iacr.org/2023/969
- LatticeFold: https://eprint.iacr.org/2024/257
- STIR: https://eprint.iacr.org/2024/390
- nova-snark: https://github.com/microsoft/Nova
- arecibo/SuperNova: https://github.com/argumentcomputer/arecibo
- sonobe: https://github.com/privacy-scaling-explorations/sonobe
- Nova-Scotia: https://github.com/nalinbhardwaj/Nova-Scotia
- Plonky3: https://github.com/Plonky3/Plonky3
- SP1 v4 (Turbo): https://github.com/succinctlabs/sp1/releases/tag/v4.0.0
- OpenVM v1.5.0: https://github.com/openvm-org/openvm
