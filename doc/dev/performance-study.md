# Comprehensive Performance Study — Forward Engine (2026-02-15)

Workload: EVM multisig symbolic execution, 44 rules, 178 initial facts, 63-node tree.

## Current Performance

| Metric | Value |
|--------|-------|
| Median | 1.21ms |
| P10–P90 | 0.95–1.67ms |
| Per node | 19.2µs |
| Store ops/call | 575 (root state) |
| Theoretical min | ~7µs (Store-only) |
| Overhead ratio | 183× |

## Time Breakdown

```
findAllMatches     501µs  37%    63 calls    8.0µs/call
  getCandidateRules  24µs   2%    (fingerprint O(1) + disc-tree)
  tryMatch          477µs  35%    ~1 rule/step after strategy stack
mutateState        330µs  24%    62 calls    5.3µs/call
makeChildCtx        97µs   7%    62 calls    1.6µs/call
undoMutate          75µs   6%    62 calls    1.2µs/call
undoIndex           24µs   2%    62 calls    384ns/call
snapshotState       22µs   2%     7 calls    3.2µs/call
loop bookkeeping    50µs   4%    (Set ops, array alloc, matchAlts map)
JS overhead        160µs  12%    (function calls, GC, V8 internals)
─────────────────────────────────
              ≈  1210µs 100%
```

## V8 JIT Status

All hot functions compiled to TurboFan. Zero polymorphic/megamorphic ICs. Zero deoptimizations. GC impact negligible (sub-millisecond scavenges, no Mark-Compact during hot loop).

## Where Time Goes

### tryMatch (35% — the core work)

Per matching rule: 5–7µs. Includes:
- `matchIndexed`: walk antecedent patterns, bind metavars in theta slots
- FFI backward proving: `inc`, `plus`, `neq` — O(1) BigInt arithmetic
- `subCompiled`/`applyIndexed`: substitute theta into consequent patterns
- `consumed` object construction

The strategy stack eliminates 43/44 rules per step. Only ~1 tryMatch call per node. This is near-optimal — there's no way to avoid matching the winning rule.

Failing rules (when tried via micro-benchmark): ~29µs each, dominated by backward proving. But the strategy stack ensures these are never attempted during normal execution.

### mutateState + undoMutate (30% — object property operations)

`state.linear` is a plain object with ~178 numeric keys (content-addressed hashes). V8 stores these in dictionary mode (hash table internally). Each mutateState call does ~9 property operations (consume + produce). Each undoMutate restores them.

Object operation micro-benchmarks on the 178-key state:
- Property get/set: 108ns
- Property delete: 158ns
- `for-in` iteration (178 keys): 10.8µs
- Object spread (178 keys): 28.3µs

### makeChildCtx + undoIndex (9% — hash + index updates)

`for-in` over the undo log (~9 entries), `hashPair` calls, `indexAdd`/`indexRemove` array scans. Already O(delta) per step.

### Loop bookkeeping (4%)

`pathVisited.add/delete` (Set operations), `matches.map()` allocation, `children.push()`, cycle/bound checks. Negligible individually.

## Object Allocation

~960 objects per explore run. ~15 per node:
- theta array, consumed object, undo object (tryMatch/mutateState)
- ExploreContext, indexUndo array, {ctx, indexUndo} (makeChildCtx)
- matches array, candidates array, matchAlts (findAllMatches)
- children array, {rule, child} descriptors (explore loop)
- 7 leaf snapshots (2 object spreads each)

All short-lived except the returned tree. Heap delta per run: ~2KB retained.

## Remaining JS Optimizations

| Optimization | Estimated Impact | Effort |
|-------------|-----------------|--------|
| Eliminate `matches.map()` for matchAlts | ~0.5% | 2 lines |
| Pre-allocated reusable theta array | ~3–5% | ~20 LOC |
| `Map` for state.linear (vs object) | ~10–15% | ~50 LOC |
| Pool/reuse consumed and undo objects | ~3–5% | ~30 LOC |

**Combined ceiling: ~20% (1.2ms → ~1.0ms).** All are micro-optimizations with diminishing returns.

## What Won't Help in JS

- **More indexing**: Strategy stack already selects ~1 rule/step. getCandidateRules is 2% of total.
- **Compiled matching (Maranget)**: Only matters at 100+ rules where fingerprint can't discriminate. Current workload: 44 rules, 40 fingerprinted.
- **Semi-naive**: Only matters at 100K+ facts. Current: 178 facts.
- **Caching FFI results**: FFI (inc/plus/neq) changes every step (different PC values). No temporal reuse.
- **GC tuning**: GC is <1% of explore time.

## The 183× Overhead Gap

The theoretical minimum (2200 Store.tag/child/arity calls at 3–10ns each ≈ 7µs) vs actual 1210µs. Where does the 183× gap come from?

1. **Function call overhead**: Each node does ~8 function calls × 63 nodes = 504 calls. JS function call + return ≈ 20–50ns each. ~25µs.
2. **Object property operations**: 178-key dictionary-mode objects. Each property op: 100–160ns. ~9 ops × 62 nodes × 130ns = ~73µs. But `for-in` iteration and spread are much more: undoMutate does `for-in` over undo log (varies), makeChildCtx does `for-in` over undo log.
3. **Array operations**: `push`, `indexOf`, `sort` for index manipulation. ~100µs.
4. **Backward proving / FFI**: BigInt arithmetic (inc, plus, neq). ~200µs.
5. **V8 hidden class transitions**: Object creation with varying property sets. Dictionary-mode lookups instead of inline caches.
6. **General JS runtime**: Closure dispatch, prototype chain walks, boxing/unboxing numbers.

The gap is **fundamental to JavaScript**. Objects are the wrong abstraction for 178-key mutable multisets. A Zig/Rust port would use:
- `[MAX_FACTS]u32` flat arrays → O(1) lookup, zero allocation
- Stack-allocated theta/undo → zero GC pressure
- `comptime` rule dispatch → zero overhead

**Realistic native target: 50–100µs (10–20×).**

## Conclusion

The JS forward engine is well-optimized for JavaScript:
- TurboFan-compiled hot path, monomorphic ICs, zero deopts
- O(1) strategy stack (fingerprint) reducing 44→1 candidate/step
- Mutation+undo eliminating copies (state, index, pathVisited)
- De Bruijn indexed theta, compiled substitution, direct FFI
- O(delta) incremental context updates

The remaining ~20% of JS headroom (1.2ms → 1.0ms) comes from object pooling and Map conversions — diminishing returns. The real 10–20× jump requires a native runtime where state manipulation is struct field access, not dictionary-mode object operations.
