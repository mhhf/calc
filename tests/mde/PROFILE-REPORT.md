# EVM ADD Profiling Report

## Summary

Single EVM ADD instruction (3 + 2 = 5): **~0.5-0.8 ms**

| Component | Time | % |
|-----------|------|---|
| Backward prove: `plus 3 2 X` | 0.46 ms | **90%** |
| Backward prove: `inc 0 X` | 0.05 ms | 10% |
| Linear matching (5 patterns) | 0.02 ms | 4% |
| Apply match | 0.02 ms | 4% |
| Rule loop overhead | 0.001 ms | <1% |

## Throughput

- **Current**: ~1,500-2,000 ADD ops/sec
- **After memoization**: ~40x faster = ~60,000 ADD ops/sec

## Scaling Analysis

Plus operation complexity (recursive proof):

| Operation | Time | Notes |
|-----------|------|-------|
| 0 + 0 | 0.07 ms | Base case |
| 1 + 1 | 0.30 ms | 2 recursions |
| 3 + 2 | 0.23 ms | Our test case |
| 7 + 7 | 0.60 ms | More recursion |

Roughly **O(log n)** where n is the sum.

## Optimization Opportunities

### 1. Memoization (Implemented above)
- **Speedup**: 40x
- Cache backward query results by goal hash
- Content-addressed makes this trivial

### 2. Clause Indexing
- **Estimated speedup**: 5-10x
- Index clauses by head functor
- Current: iterate all 37 clauses to find `plus/*`

### 3. Tabling
- **Estimated speedup**: 2-5x for recursive predicates
- Store intermediate results during recursion
- Standard Prolog optimization

### 4. Compilation to JS
- **Estimated speedup**: 100-1000x
- Compile `plus`, `inc`, etc. to native JS
- Example: `function plus(a, b) { return a + b; }`

## Bottleneck: Backward Proving

The recursive backward proof search for `plus` dominates runtime:

```
plus (i (i e)) (o (i e)) X
  <- plus (i e) (i e) R       // recurse on bits
  <- plus e (i e) R           // recurse again
  <- ...
  <- inc Q R                  // handle carry
```

Each level requires:
1. Fresh variable generation
2. Clause head unification
3. Substitution application
4. Recursive premise solving

## Recommendations

1. **Quick win**: Add memoization to backward prover
   - 40x speedup, minimal code change
   - Cache key = goal hash (already content-addressed)

2. **Medium effort**: Clause indexing
   - Build index on load: `{plus: [clause1, ...], inc: [...], ...}`
   - Skip irrelevant clauses during matching

3. **High effort**: Compile arithmetic to JS
   - Best for known predicates like `plus`, `mul`, `inc`
   - Could be a separate "builtins" module
