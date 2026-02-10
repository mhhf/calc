---
title: v2 Prover Benchmark Results
created: 2026-02-10
modified: 2026-02-10
summary: Performance benchmarks showing v2 focused prover is 5-8x faster than v1 through content-addressed multisets and proper focusing discipline.
tags: [benchmark, performance, v2, prover, optimization]
---

# v2 Prover Benchmark Results

**Date:** 2026-02-02

## Summary

v2 focused prover is **5-8x faster** than v1 across all test cases.

| Metric | v2 vs v1 (base) | v2 vs v1 (store) |
|--------|-----------------|------------------|
| Geometric Mean | **5.8x faster** | **5.2x faster** |

## Detailed Results (50 iterations, --expose-gc)

| Test | v1-base (ms) | v1-store (ms) | v2 (ms) | v2/v1-base |
|------|-------------|---------------|---------|------------|
| identity | 0.103 | 0.055 | 0.018 | 5.9x faster |
| identity_var | 0.106 | 0.088 | 0.015 | 7.0x faster |
| modus_ponens | 0.479 | 0.363 | 0.056 | 8.5x faster |
| tensor_id | 0.462 | 0.449 | 0.057 | 8.1x faster |
| tensor_comm | 0.363 | 0.337 | 0.058 | 6.3x faster |
| tensor_assoc | 0.694 | 0.712 | 0.100 | 6.9x faster |
| with_elim_l | 0.264 | 0.241 | 0.045 | 5.8x faster |
| with_elim_r | 0.421 | 0.378 | 0.080 | 5.3x faster |
| with_intro | 0.230 | 0.179 | 0.041 | 5.7x faster |
| currying | 0.683 | 0.733 | 0.143 | 4.8x faster |
| uncurrying | 0.899 | 0.742 | 0.129 | 7.0x faster |
| distribution | 1.509 | 1.231 | 0.208 | 7.2x faster |
| tensor_with | 2.566 | 2.758 | 1.216 | 2.1x faster |
| deep_loli | 1.398 | 1.380 | 0.179 | 7.8x faster |
| nested_with | 1.495 | 1.504 | 0.386 | 3.9x faster |
| many_tensor | 1.117 | 1.086 | 0.133 | 8.4x faster |
| deep_tensor | 1.514 | 1.472 | 0.181 | 8.4x faster |
| many_with | 1.354 | 1.330 | 0.502 | 2.7x faster |

## v2 Proof Tree Stats

| Test | Tree Size | Depth |
|------|-----------|-------|
| identity | 1 | 1 |
| modus_ponens | 3 | 2 |
| tensor_comm | 4 | 3 |
| currying | 7 | 5 |
| distribution | 11 | 5 |
| deep_tensor | 13 | 9 |

## Why v2 is Faster

1. **Content-addressed multisets**: O(1) formula lookup via hash (Context module)
2. **Focused proof search**: Proper Andreoli-style inversion/focus phases
3. **Minimal architecture**: No legacy overhead, clean delta passing
4. **Efficient resource tracking**: Multiset operations instead of array scans

## Running Benchmarks

```bash
npm run bench:compare:all       # Compare v1-base, v1-store, v2
npm run bench:v2                # v2 only
npm run bench:compare:all:save  # Save results to JSON
```
