# MDE Forward Chaining - Performance Optimizations

## Final Performance (after all optimizations)

**5 EVM steps (JUMPDEST → PUSH1 → PUSH20 → CALLER → EQ):**
- Total time: ~10ms
- Per-step: ~2ms average
- Match calls: 24 total (5/step)
- Throughput: 0.5 steps/ms (~500 steps/sec)

## Optimization History

| Optimization | Match Calls | Time | Improvement |
|--------------|-------------|------|-------------|
| Baseline (no indexing) | 35,310 | ~50ms | - |
| State indexing | 22,145 | ~35ms | 37% fewer calls |
| Rule predicate filtering | 7,704 | ~28ms | 65% fewer calls |
| **EVM strategy + codeByPC** | **24** | **~10ms** | **321x fewer calls** |

## Current Profiling Breakdown

```
findMatch breakdown:
  unify.match:    3.8% (24 calls, 5/step)
  prove:         62.8% (12 calls, ~400µs/call)
  substitute:    24.1%
  overhead:      12.9%
```

**Bottleneck shifted from pattern matching to backward proving.**

## Key Optimizations

1. **State indexing by predicate**: `{pc: [...], code: [...], gas: [...]}`
2. **Rule filtering**: Only try rules where ALL trigger predicates exist in state
3. **EVM strategy**: PC→code→opcode for O(1) rule selection
4. **codeByPC index**: O(1) lookup for `code PC OPCODE` patterns

## Run Benchmarks
```bash
npm run bench:multisig         # Timing benchmark
npm run profile:multisig       # Detailed profiling (requires CALC_PROFILE=1)
```

## Limitations
1. **Additive conjunction (`&`)**: EQ rule produces `with` consequent not yet handled
2. **No `#trace`/`#import`**: Code facts must be loaded manually
3. **Symbolic equality**: Can't prove `eq member01 sender_addr`
