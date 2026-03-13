---
title: "LogUp Bus Accumulator Extraction for IVC Chunk Boundaries"
created: 2026-03-13
modified: 2026-03-13
summary: "Analysis of OpenVM stark-backend LogUp accumulator mechanics and the feasibility of extracting intermediate accumulator values for IVC chunk boundary chaining."
tags: [zk, stark, ivc, implementation, verification, plonky3]
category: "Implementation"
---

# LogUp Bus Accumulator Extraction for IVC Chunk Boundaries

Research question (OQ-2): Can we extract intermediate bus accumulator values from the OpenVM stark-backend for IVC chunk boundary chaining?

Sources: `github.com/openvm-org/stark-backend` (v1.3.0), `github.com/openvm-org/openvm` (continuations crate), `github.com/Plonky3/Plonky3` (lookup crate).

---

## 1. How the LogUp Accumulator Works

The FRI LogUp protocol in `crates/stark-backend/src/interaction/fri_log_up.rs` produces a **stage-1 (challenge-dependent) permutation trace** with layout:

```
Row: | perm_1 | perm_2 | ... | perm_s | phi |
```

- `perm_i`: LogUp reciprocal contribution for interaction chunk `i` at this row
- `phi`: running cumulative sum column

**Trace generation** (`generate_after_challenge_trace`):

```rust
// Phase 1: compute row sums into phi column
for row in 0..height {
    let row_sum = sum_of_reciprocals_for_row(row);
    perm_values[row * perm_width + (perm_width - 1)] = row_sum;
}

// Phase 2: convert to prefix sum
let mut phi = Challenge::ZERO;
for perm_chunk in perm_values.chunks_exact_mut(perm_width) {
    phi += *perm_chunk.last().unwrap();
    *perm_chunk.last_mut().unwrap() = phi;
}
```

So `phi[i] = sum of row_sums[0..=i]`. The phi column is a **strict prefix sum starting from zero**, with `phi[0] = row_sum[0]` and `phi[last] = total sum over all rows`.

**AIR constraints** (`eval_fri_log_up_phase`):

| Constraint | Expression |
|---|---|
| First row | `phi[0] == sum_of_perm_chunks_at_row_0` |
| Transition | `phi[next] - phi[local] == sum_of_perm_chunks_at_next_row` |
| Last row | `phi[last] == cumulative_sum` (the exposed value) |

The two challenge scalars (alpha, beta) are `ExtensionField<F>` elements — `STARK_LU_NUM_CHALLENGES = 2`.

**Exposed value**: `cumulative_sum` = `phi[last_row]` is stored in `AirProofData.exposed_values_after_challenge` as a single `Challenge` element.

**Verification**: `partially_verify` sums `cumulative_sum` across **all AIRs** and asserts the total equals `Challenge::ZERO`. This is a **global constraint** — individual AIR sums need not be zero, only the aggregate.

---

## 2. Where Challenges Come From

The Fiat-Shamir transcript order in `prover/coordinator.rs`:

1. Observe `vk_pre_hash`
2. Observe number of AIRs and AIR IDs
3. Observe public values per AIR
4. Observe preprocessed commitments
5. Observe main trace commitments
6. **Sample LogUp challenges (alpha, beta)** — happens inside `device.partially_prove()`
7. Observe after-challenge trace commitments
8. Observe quotient commitment
9. Sample DEEP evaluation point (zeta)
10. Sample FRI folding challenges

The LogUp challenges are derived from the entire prior Fiat-Shamir state: VK hash, all AIR IDs, all public values, all trace commitments. Two separate proofs would have **different challenges** unless they had identical transcript prefixes.

---

## 3. How OpenVM Handles Continuations (Without Bus Accumulator Chaining)

OpenVM's continuation system (`crates/continuations/`) does **not** chain bus accumulators across segments. It uses a different approach:

**Segment boundary state** (from `verifier/common/mod.rs`):

| State | Type | Invariant |
|---|---|---|
| Program counter | `initial_pc`, `final_pc` | `seg[i].final_pc == seg[i+1].initial_pc` |
| Memory Merkle root | `initial_root`, `final_root` | `seg[i].final_root == seg[i+1].initial_root` |
| Termination flag | `is_terminate` | Must be `0` for non-final segments |
| App commit | commitment hash | Same across all segments |

Each segment is a **complete, independent STARK proof** with its own LogUp instance. The bus (LogUp) constraint is globally satisfied **within each segment** — the cumulative sum of each segment's permutation trace sums to zero independently.

The continuations verifier (`verifier/leaf/mod.rs`) does **not** reference `cumulative_sum`, `logup`, `accumulator`, `bus`, `permutation`, or `exposed_values`. Bus soundness is handled entirely at the per-segment level.

**Implication**: OpenVM continuations work because the VM is designed so that each segment's multi-chip interactions are balanced within the segment. Memory state is threaded through Merkle roots (standard base-field public values), not through challenge-dependent accumulator values.

---

## 4. The Core Problem with LogUp and IVC

The key insight: LogUp accumulators are **challenge-dependent** (stage-1) columns. The challenges alpha, beta are derived from Fiat-Shamir applied to all of the current proof's commitments. Therefore:

1. **Different proofs have different challenges.** You cannot directly compare `phi[last]` from chunk k with a target value in chunk k+1, because they use different (alpha, beta).

2. **phi[i] is not committed.** Intermediate values of the phi column are never opened or exposed in the proof. Only `phi[last_row]` is exposed as `cumulative_sum`.

3. **phi[i] is not publicly accessible.** The prover computes the phi column internally; there is no API to extract or commit to intermediate phi values.

4. **The phi column has no natural "restart" mechanism.** The first-row constraint forces `phi[0] = row_sum[0]` (not zero), meaning phi does not have an initial value that can be set externally.

---

## 5. Could We Modify the Backend to Support IVC?

Two approaches:

### 5a. Expose intermediate phi value as a public value

The boundary phi value (phi at the last row of chunk k) could be extracted and placed into the public values of that proof, then a recursive verifier for chunk k+1 could check that its initial accumulator matches.

**Problem**: The challenges (alpha, beta) differ across proofs. The phi value from chunk k is computed with challenges (alpha_k, beta_k). Chunk k+1's phi is computed with (alpha_{k+1}, beta_{k+1}). These are incomparable.

**Solution that would work**: If all chunks are proven with the **same fixed (alpha, beta)** — i.e., challenges are fixed a priori and not derived from the trace — then phi values are comparable across chunks. But fixed challenges break soundness (no randomness means adversary can predict the challenge).

### 5b. Use a non-zero initial phi

Modify the AIR first-row constraint from `phi[0] == row_sum[0]` to `phi[0] == initial_phi + row_sum[0]` where `initial_phi` is a public input from the previous chunk.

**Problem**: Same as 5a — the phi values use different challenges across chunks. Even if you could pass `initial_phi` forward, the semantic meaning is different because the random challenges changed.

### 5c. Recursive STARK composition (the correct approach)

The correct approach (used by OpenVM and SP1) is to make the bus balance constraint hold **within each segment**, not across segments. This requires:

1. Designing each segment so that all chip interactions are fully balanced within the segment.
2. Any "open" state at segment boundaries (like memory) is handled via base-field public values (Merkle roots), not challenge-dependent accumulators.
3. The verifier circuit for chunk k verifies chunk k-1's STARK proof and carries forward only base-field state.

This is exactly the OpenVM continuations design.

---

## 6. What Is Extractable from the Backend

From `AirProofData` in a completed proof:

| Field | Accessible | Type |
|---|---|---|
| `exposed_values_after_challenge` | Yes | `Vec<Vec<Challenge>>` — contains `[cumulative_sum]` per AIR |
| `public_values` | Yes | `Vec<Val>` — base-field public values |
| Main trace commitments | Yes | PCS commitments |
| After-challenge trace commitments | Yes | PCS commitments |
| Intermediate phi values | No | Never exposed |
| phi at specific rows | No | Not committed or opened |

The `cumulative_sum` (= `phi[last_row]`) is in `exposed_values_after_challenge[0][0]` for each AIR that has interactions. For a valid proof this sums to zero across all AIRs.

---

## 7. Plonky3 Native LogUp

Plonky3's own `lookup/src/logup.rs` has an analogous design:
- Running sum `s[0] = 0`, `s[i+1] = s[i] + contribution[i]`
- First-row constraint: `s[0] == 0` (hardcoded)
- Global lookups: final value `expected_cumulated` is set per-lookup and then the verifier checks all `expected_cumulated` values sum to zero
- No mechanism to start `s[0]` at a non-zero value

This confirms the hardcoded-zero-initial-value design is uniform across Plonky3 and the stark-backend.

---

## 8. Conclusion

**Bus accumulator extraction for IVC chunk chaining is not directly feasible** with the current stark-backend design, for three compounding reasons:

1. Intermediate phi values are not exposed or accessible (only the final row's value is exposed).
2. Even if extracted, phi values are challenge-dependent: different chunks use different Fiat-Shamir challenges, making cross-chunk phi comparison semantically meaningless.
3. The existing API has no mechanism to initialize phi at a non-zero value (would require modifying both the trace generator and the AIR constraint).

**What OpenVM actually does**: continuations are handled by designing each segment so that bus interactions balance within the segment, and threading base-field state (PC, memory Merkle root) via public values. No bus accumulator state crosses segment boundaries.

**For our IVC design**: follow the same pattern. Each chunk must be bus-balanced internally. Chunk boundary state should be base-field values passed as public inputs. Use `openvm-native-recursion` or a recursive STARK verifier circuit (RES_0091) to compose chunk proofs.

---

## Sources

- stark-backend FriLogUp: https://github.com/openvm-org/stark-backend/blob/main/crates/stark-backend/src/interaction/fri_log_up.rs
- stark-backend RAP: https://github.com/openvm-org/stark-backend/blob/main/crates/stark-backend/src/interaction/rap.rs
- stark-backend proof types: https://github.com/openvm-org/stark-backend/blob/main/crates/stark-backend/src/proof.rs
- stark-backend coordinator (Fiat-Shamir order): https://github.com/openvm-org/stark-backend/blob/main/crates/stark-backend/src/prover/coordinator.rs
- OpenVM continuations verifier: https://github.com/openvm-org/openvm/blob/main/crates/continuations/src/verifier/common/mod.rs
- OpenVM leaf verifier: https://github.com/openvm-org/openvm/blob/main/crates/continuations/src/verifier/leaf/mod.rs
- Plonky3 logup: https://github.com/Plonky3/Plonky3/blob/main/lookup/src/logup.rs
- IVC recursive STARK verifier options: RES_0091
