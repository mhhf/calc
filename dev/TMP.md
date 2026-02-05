# MDE Forward Chaining - Complete

## Performance Summary

**5 EVM steps to EQ instruction:**
- Total time: ~35ms (including warmup)
- Per-step: ~7ms average
- Throughput: 0.14 steps/ms (~140 steps/sec)

**Profiling breakdown (CALC_PROFILE=1):**
```
findMatch:    97.4% of execution
  unify.match:  57.9% (35,310 calls, 812ns/call)
  prove:         9.5% (12 calls, 392µs/call)
  substitute:    2.1%
  overhead:     30.5%
applyMatch:    2.6%
```

**Bottleneck: Pattern matching**
- 178 state facts × 44 rules = 7,832 potential matches/step
- ~7,000 unify calls per step
- Each unify call: 812 nanoseconds

## Execution Trace
```
[0] evm/jumpdest (23ms) - 10,681 match calls
[1] evm/push1    (10ms) - 10,815 match calls
[2] evm/push20   (9ms)  -  6,952 match calls
[3] evm/caller   (6ms)  -  4,857 match calls
[4] evm/eq       (2ms)  -  2,005 match calls
```

## Run Benchmarks
```bash
npm run bench:multisig     # Timing benchmark
npm run profile:multisig   # Detailed profiling
```

## Limitations
1. **Additive conjunction (`&`)**: EQ rule produces `with` consequent not yet handled
2. **No `#trace`/`#import`**: Code facts must be loaded manually
3. **Symbolic equality**: Can't prove `eq member01 sender_addr`
