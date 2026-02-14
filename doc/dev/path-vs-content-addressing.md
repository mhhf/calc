# Hybrid Addressing for Forward Chaining Optimization

Optimizing forward chaining execution while keeping everything as plain linear logic. The engine detects patterns at compile time and applies transparent shortcuts at runtime.

## The Core Idea

Forward chaining rules like `f(X) * !plus(X, 2, X') -o f(X') * B()` preserve the predicate `f` — it appears on both sides of `-o` with a small change to its argument. The engine can detect this at compile time and, instead of full match + consume + substitute + produce, just navigate to the changed argument, apply the transform, and swap the hash.

For deeply nested types like `a(b(c(X), d(...)), e(f(Y, g(...))))` where a rule changes X and Y but preserves the structure — paths `[0,0,0]` and `[1,0,0]` identify the changed positions. Only nodes along those paths need new hashes (incremental Merkle update). Everything else keeps its content-addressed hash.

The hybrid: **content-addressed values everywhere, path-based access for navigating to what changes.**

## Quantified: Where the Waste Is

Analysis of all 44 EVM rules (`evm.ill`):

| Category | Facts | % of LHS | Description |
|----------|-------|----------|-------------|
| **Preserved** | 57 | 27% | Same predicate, identical args both sides |
| **Delta** | 97 | 46% | Same predicate, arg(s) change. In-place update possible |
| **Consumed** | 56 | 27% | Left-only, truly removed |
| **Produced** | 32 | — | Right-only, truly new |

**73.4% of all antecedent patterns** (154 of 210) could be optimized away or reduced to cheap field access.

Top preserved predicates:
- `code PC (opcode)` — **42 of 44 rules**. Every step consumes+reproduces the SAME bytecode fact.
- `address`, `sender`, `callvalue`, `timestamp`, `gaslimit`, `calldatasize` — environment singletons, read-only lookups disguised as consume+produce.

Top delta predicates:
- `pc` — 38 rules. arg0: PC → PC' (via `!inc` or jump target)
- `sh` — 34 rules. arg0: unwrap `s()` constructor (functionally `-1`)
- `gas` — 19 rules. arg0: GAS → GAS' (via `!inc` or `!plus`)

## Three Optimization Levels

All three are transparent — rules don't change, the engine just gets smarter.

### Level 1: Preserved Predicate Optimization

At compile time, detect predicates that appear identically on both sides of `-o`.

**IMPORTANT: Preserved predicates still need matching/unification.** We must verify the fact exists in state with the correct values and bind variables for use by other patterns. What we skip is the consume/reproduce/index-update cycle.

Two sub-cases:
1. **All vars already bound** (by non-preserved patterns): verification-only — "does state contain this fully-ground fact?" → O(1) index check. Skip consume/produce/index-update.
2. **Some vars not yet bound**: must match to bind variables, but still skip consume/produce/index-update.

Currently:
```
1. match(code_pattern, candidate)     — Store.get × 3-5
2. consume code fact from state       — delete from multiset
3. subApply(code_pattern, theta)      — Store.get × 3-5, Store.put
4. produce code fact into state       — insert into multiset
5. update index (remove + add)        — 2 index ops
```

With preserved detection:
```
1. match(code_pattern, candidate)     — still needed for variable binding
(steps 2-5 eliminated — fact stays in state unchanged)
```

**Saving per rule:** 2 multiset ops + 2 index ops + ~5 Store.get/put (substitute) per preserved predicate. With 1.3 preserved facts per rule average, significant savings on steps 2-5 but match cost remains.

**Note:** For `code PC OPCODE` specifically, the opcodeLayer strategy already handles the existence verification via `codeByPC` index. The remaining saving is eliminating the consume/reproduce cycle.

### Level 2: Delta Application

At compile time, compare antecedent and consequent patterns for same-predicate facts. Extract which arguments change and what transforms them.

Example — rule `evm/add` has `pc PC` → `pc PC'` where `!inc PC PC'`:
```
Delta: pc.arg0 changes via inc
```

Currently:
```
1. match pc pattern against state     — Store.get, unify
2. consume pc fact                    — delete from multiset
3. subApply(pc(PC'), theta)           — Store.get, Store.put
4. produce new pc fact                — insert into multiset
```

With delta:
```
1. find pc fact in state              — O(1) index lookup
2. read arg0 (current PC value)      — Store.child (flat store: 4ns)
3. apply inc                          — FFI, O(1)
4. create pc(PC')                     — Store.put('pc', [newPC])
5. swap in state: old hash → new hash — O(1)
```

Steps 1-5 are all O(1). No full pattern matching, no unification, no full substitution.

**`sh` as delta:** The `sh` predicate appears to be a structural change (`s(s(SH)) → s(SH)`) but is functionally `-1` — it unwraps one `s()` constructor. As a delta: `arg0 → Store.child(arg0, 0)`, which is O(1). The match still verifies the precondition (stack height >= N required by the opcode).

### Level 3: Path-Based Access for Nested Types

For deeply nested linear terms where a rule preserves the outer structure but changes values at specific paths.

Given a term `a(b(c(X), d(Y)), e(Z))` and a rule that changes X→X' and Z→Z':

**Paths (precomputed at compile time):**
- `[0, 0, 0]` — navigates a→b→c→X
- `[1, 0]` — navigates a→e→Z

**Incremental update (runtime):**
```
1. Navigate path [0,0,0]: read X     — 3 array lookups (flat store: 12ns)
2. Compute X' = transform(X)         — FFI / arithmetic
3. Navigate path [1,0]: read Z       — 2 array lookups (8ns)
4. Compute Z' = transform(Z)         — FFI / arithmetic
5. Rebuild bottom-up along changed paths:
   new_c = put('c', [X'])            — reuse d(Y) unchanged
   new_b = put('b', [new_c, d_hash]) — reuse d's hash
   new_e = put('e', [Z'])
   new_a = put('a', [new_b, new_e])
```

Only 4 `Store.put` calls instead of walking+rebuilding the entire term. Unchanged subtrees (d, Y, g) keep their content-addressed hashes — zero work.

For term size N with K changes at depth D: O(K*D) vs O(N).

## Flat Array Store: The Foundation

All three optimization levels benefit from replacing `Map<hash, {tag, children}>` with TypedArray arena.

### Benchmarked Performance (this machine, Node 22, V8 12.4)

```
Store access (1M lookups, median of 20 runs):

Map.get + .tag:                   32.1 ms   1.0x  (current)
TypedArray tags[id]:               2.0 ms  16.0x
TypedArray tags[id] + child0[id]:  2.7 ms  11.9x
```

**16x faster reads.** Content-addressing preserved via dedup Map on `put()` (cold path only). Tag comparison becomes integer `===`. String interning makes all children homogeneous uint32.

### Integer Width: Uint32Array (decided)

**BigUint64Array is NOT viable for the hot path.**

Benchmarked (10M elements, same machine):

| Operation | Uint32Array | BigUint64Array | Ratio |
|-----------|-------------|----------------|-------|
| Write     | 6.0 ms      | 189.6 ms       | **31.6x slower** |
| Read+sum  | 8.6 ms      | 57.5 ms        | **6.7x slower** |

Root cause: BigUint64Array stores/returns `BigInt` values. `BigInt` is heap-allocated in V8, not an inline value. Every read allocates. Every comparison is slower than `Number ===`.

**Zig compatibility:** Zig has `u32` natively. On WASM32 (the target for Zig→browser), `usize` = u32. Using u64 on wasm32 requires two instructions per operation. u32 crosses the JS↔WASM boundary as plain `Number` with zero marshaling overhead. u64 requires `BigInt` at the boundary (18% slower per V8 benchmarks).

**Index capacity:** Uint32 addresses 4.3 billion terms. At ~12 bytes/term (tag + 2 children), that's ~51GB. Memory exhaustion will happen long before index exhaustion.

**Decision: Uint32Array everywhere.** BigInt only in the `binlit` side table (see below).

### Scaling: Pre-Allocate Large + OS Lazy Paging (decided)

**The problem:** User expects programs to grow 1000x+ beyond current ~2000 terms.

**Benchmarked memory behavior (Linux, Node 22):**

```
100M Uint32Array (400MB logical):
  RSS at allocation:     0.1 MB   ← OS does NOT allocate physical memory
  RSS after touching 1M: 12.5 MB  ← only pages touched get allocated
  RSS after touching all: 390 MB  ← full physical allocation
```

The Linux kernel uses demand paging (mmap zero-page optimization). `new Uint32Array(N)` reserves virtual address space but allocates near-zero physical memory. Physical 4KB pages materialize only on first write (page fault).

**Strategy:**
- Pre-allocate **4M entries** per array at startup (~96MB virtual for 6 arrays, ~0 RSS)
- Covers up to 4 million terms with zero growth overhead
- If exceeded (rare): double via `ArrayBuffer.transfer()` (creates new fixed buffer, O(n) copy, old buffer detached)
- Resizable ArrayBuffer has **2.3x read overhead** due to bounds checking — NOT used for the hot path

**Growth cost if needed (benchmarked):**

```
TypedArray.set() copy cost:
  1K entries:   0.001ms
  10K entries:  0.007ms
  100K entries: 0.064ms
  1M entries:   2.0ms (worst case, one-time)
```

Doubling from 4M→8M costs ~8ms one-time. Amortized over millions of operations: negligible.

**Why not Resizable ArrayBuffer?** Resizable ArrayBuffer (ES2024) is available and resize is fast (0.03ms), but every element access has a generalized bounds check, causing **2.3x slower reads** in steady state. Not acceptable for the hot path.

**Decision:** Pre-allocate 4M entries, grow via `transfer()` if needed. Zero overhead in steady state.

### Layout: SoA (Struct-of-Arrays)

```javascript
const CAPACITY = 4_000_000;  // 4M terms, ~0 RSS until touched

// Core SoA arrays
const tags    = new Uint8Array(CAPACITY);    // tag enum (0-255)
const arities = new Uint8Array(CAPACITY);    // children count (0-4)
const child0  = new Uint32Array(CAPACITY);   // first child (term index or string/bigint table index)
const child1  = new Uint32Array(CAPACITY);   // second child
const child2  = new Uint32Array(CAPACITY);   // third child (rare: seq, deriv)
const child3  = new Uint32Array(CAPACITY);   // fourth child (very rare)

let nextId = 0;
```

SoA is better than AoS (interleaved) because:
1. Tag-only scans (the most common pattern: check tag, bail) touch only `tags` array — better cache
2. Each array has the right element size (Uint8 for tags, Uint32 for children)
3. V8 optimizes monomorphic TypedArray access to near-native speed

Zig equivalent (direct memory mapping for WASM):
```zig
const Store = struct {
    tags:     []u8,
    arities:  []u8,
    child0:   []u32,
    child1:   []u32,
    child2:   []u32,
    child3:   []u32,
    len:      u32,
};
```

### Tag Encoding

Dynamic tag registry, pre-register known tags:

```javascript
const TAG = Object.create(null);
const TAG_NAMES = [];
let nextTag = 0;

function registerTag(name) {
  if (TAG[name] !== undefined) return TAG[name];
  const id = nextTag++;
  TAG[name] = id;
  TAG_NAMES[id] = name;
  return id;
}

// Pre-register all known tags
['atom','freevar','tensor','loli','with','bang','one','type',
 'arrow','monad','app','binlit','strlit','charlit',
 'var','any','hyp','comma','empty','seq','deriv'].forEach(registerTag);
// Predicate tags registered dynamically as encountered
```

Benefits:
- `tags[id] === TAG.tensor` is integer comparison vs string `===`
- Tag fits in Uint8 (256 possible, ~25 used currently)
- Switch on integer tags compiles to jump tables in V8

### String Interning

All atom names, variable names stored once, referenced by uint32 index:

```javascript
const STRING_TO_ID = new Map();
const ID_TO_STRING = [];
let nextStringId = 0;

function internString(s) {
  let id = STRING_TO_ID.get(s);
  if (id === undefined) {
    id = nextStringId++;
    STRING_TO_ID.set(s, id);
    ID_TO_STRING.push(s);
  }
  return id;
}

function getString(id) { return ID_TO_STRING[id]; }
```

This makes ALL children in TypedArrays be uint32 — either a term index or a string table index. Discrimination is by tag (see below).

### Child Type Discrimination: Tag-Based Inference (decided)

**Problem:** `child0[id]` is always a uint32. How do we know if it's a term reference or a string table index?

**Solution:** The tag determines the child types. No per-node bitmask needed.

```javascript
// Tags whose children are string table indices (not term refs)
const STRING_CHILD_TAGS = new Uint8Array(256);
STRING_CHILD_TAGS[TAG.atom] = 1;     // child0 = atom name (string)
STRING_CHILD_TAGS[TAG.freevar] = 1;  // child0 = variable name (string)
STRING_CHILD_TAGS[TAG.strlit] = 1;   // child0 = string literal value (string)

// Tags whose children are raw numbers (not term refs, not strings)
const RAW_CHILD_TAGS = new Uint8Array(256);
RAW_CHILD_TAGS[TAG.charlit] = 1;     // child0 = codepoint (raw uint32)

// Tags whose children are bigint table indices
const BIGINT_CHILD_TAGS = new Uint8Array(256);
BIGINT_CHILD_TAGS[TAG.binlit] = 1;   // child0 = bigint table index

// isTermChild(id, childIdx):
function isTermChild(id, childIdx) {
  const t = tags[id];
  return !STRING_CHILD_TAGS[t] && !RAW_CHILD_TAGS[t] && !BIGINT_CHILD_TAGS[t];
}
```

**Benchmarked:** Tag-based inference (7.0ms/1M) vs bitmask (6.3ms/1M) — comparable. Tag-based is cleaner: no extra storage, no bitmask maintenance, handles `charlit` correctly.

**charlit fix:** Currently `isTermChild(97)` returns `true` (it's a number), but 97 is a codepoint, not a term ref. With tag-based inference, `charlit` is recognized by its tag → child is raw number, not a term ref. This fixes a latent bug.

### BigInt Side Table

`binlit` nodes store BigInt values (up to 256-bit for EVM). Cannot fit in Uint32Array.

```javascript
const BIGINT_TABLE = [];
let nextBigIntId = 0;

function storeBigInt(value) {
  const id = nextBigIntId++;
  BIGINT_TABLE.push(value);
  return id;
}

function getBigInt(id) { return BIGINT_TABLE[id]; }
```

`binlit` child0 stores the bigint table index. When reading a binlit's value: `getBigInt(child0[id])`.

Count is small: EVM multisig has ~50 unique BigInt values. Side table lookup is O(1).

### Content-Address Dedup

Same FNV-1a hash as current, used only on `put()` (cold path):

```javascript
const DEDUP = new Map();  // content hash → sequential index

function put(tagName, children) {
  const h = computeHash(tagName, children);
  const existing = DEDUP.get(h);
  if (existing !== undefined) return existing;

  const id = nextId++;
  DEDUP.set(h, id);
  tags[id] = TAG[tagName] ?? registerTag(tagName);
  arities[id] = children.length;
  // ... store children (intern strings, store bigints, etc.)
  return id;
}
```

**Identity preserved:** `put('tensor', [a, b]) === put('tensor', [a, b])` still returns the same index. `a === b` equality still works.

### Store.clear() Reset

```javascript
function clear() {
  nextId = 0;
  DEDUP.clear();
  STRING_TO_ID.clear();
  ID_TO_STRING.length = 0;
  nextStringId = 0;
  BIGINT_TABLE.length = 0;
  nextBigIntId = 0;
  // TypedArrays: no need to zero — nextId=0 means old data is unreachable
}
```

No need to zero the TypedArrays — slots beyond `nextId` are never read.

### isTerm() Migration

Current `isTerm(v)` does `typeof v === 'number' && STORE.has(v)`. With flat store:

```javascript
function isTerm(v) {
  return typeof v === 'number' && v >= 0 && v < nextId;
}
```

O(1) range check instead of Map.has. Faster.

### Backward-Compatible API

During migration, `Store.get()` still works for cold-path callers:

```javascript
function get(id) {
  if (id < 0 || id >= nextId) return undefined;
  const t = TAG_NAMES[tags[id]];
  const a = arities[id];
  const ch = [];
  for (let i = 0; i < a; i++) {
    const raw = getChildRaw(id, i);
    if (STRING_CHILD_TAGS[tags[id]]) ch.push(getString(raw));
    else if (BIGINT_CHILD_TAGS[tags[id]]) ch.push(getBigInt(raw));
    else if (RAW_CHILD_TAGS[tags[id]]) ch.push(raw);
    else ch.push(raw); // term index
  }
  return { tag: t, children: ch };
}
```

Allocates an object — fine for cold path. Hot path uses `tags[id]`, `child0[id]` directly.

## Resolved Research Questions

### 1. Full Theta Elimination for Deltas

**Answer: Yes, conditionally safe. Decidable at compile time.**

A delta predicate's transform reads inputs from the matched state fact and computes outputs via FFI. If the delta's variables don't flow to other unprocessed patterns, no theta is needed.

**Compile-time check:** For each delta predicate D in a rule:
1. Collect all variables in D's antecedent pattern: `vars(D)`
2. Check if those variables appear in any non-delta, non-preserved pattern (consumed or produced)
3. If NO: theta-free. Read inputs via `Store.child()`, apply FFI, produce output directly.
4. If YES: must still bind variables into theta for use by other patterns.

**Example — `evm/add` rule:**
```
pc PC * sh SH * stack SH (tensor X (tensor Y REST)) * code PC add * gas GAS
  * !inc PC PC' * !plus X Y Z * !plus GAS (o(i e)) GAS'
  -o pc PC' * sh SH * stack SH (tensor Z REST) * code PC add * gas GAS'
```

- `pc`: delta, var `PC` appears in `code PC add` (preserved) and `!inc PC PC'` (FFI). PC is bound by matching `pc` first. `PC'` flows to consequent `pc PC'`. Since `!inc PC PC'` is FFI and `PC` is bound, `PC'` = `inc(PC)` directly. **Theta-free for pc.**
- `code`: preserved, vars `PC` and `add` already bound by `pc` and opcodeLayer. **Verification only.**
- `sh`: preserved, var `SH` flows to consumed `stack SH ...`. **Must bind SH into theta.**
- `gas`: delta, var `GAS` bound by matching gas. `GAS'` = `plus(GAS, ...)` via FFI. **Theta-free for gas.**
- `stack`: consumed pattern, needs `SH`, `X`, `Y`, `REST` from theta. **Full match needed.**

**Conclusion:** Per-predicate theta elimination is possible and useful. Most deltas (pc, gas) are theta-free. Some (sh) still need binding. Compile-time analysis determines which.

### 2. sh/Stack Representation

**Answer: Keep Peano encoding. No change needed.**

The delta optimization already handles Peano efficiently: `arg0 → Store.child(arg0, 0)` is O(1) in the flat store. Converting to native uint32 would break the pure linear logic representation and require changes to the rule format.

The only cost of Peano is the initial construction (`s(s(s(...)))` during convert). This is cold path. Runtime access is O(1) per delta step regardless of encoding.

### 3. When Are Preserved Predicates Truly Free?

**Answer: Yes, determinable at compile time via variable dependency analysis.**

For each preserved predicate P in a rule:
1. Collect `vars(P)` — all variables in P's pattern
2. For each variable V in `vars(P)`, check if V is bound by an earlier (non-preserved) pattern in the match order
3. If ALL variables are already bound: P reduces to an existence check. O(1) via state index.
4. If SOME variables are unbound: P must match to bind them. But still skip consume/produce.

**Example:** `code PC OPCODE` is preserved. `PC` is bound by matching `pc PC` (delta). `OPCODE` is bound by the opcodeLayer index lookup (`codeByPC[pc] → hash`). Both variables bound before `code` is checked. **Truly free — no match needed, just verify hash exists in state.**

This analysis produces, per preserved predicate:
```javascript
{ pred: 'code', freeVars: false }  // all vars bound → existence check only
{ pred: 'sh',   freeVars: true }   // SH unbound → must match to bind
```

## How Delta Extraction Works

At compile time, for each forward rule:

```
For each linear predicate P in antecedent:
  If P also in consequent with same predicate head and arity:
    Compare argument patterns pairwise:
      For position i:
        If ante.args[i] === cons.args[i] (same metavar):
          → invariant at position i
        If ante.args[i] is metavar V and cons.args[i] is metavar V':
          Look for persistent fact linking V to V' (e.g. !inc V V'):
          → delta: position i, transform = inc
        If both have same tag but differ in subtrees:
          → recurse: compute sub-deltas with paths
        Else:
          → full recomputation at position i

    Classification:
      All positions invariant → PRESERVED (match for vars, skip consume/produce)
      Some positions have deltas → DELTA (in-place update)
      Structure changes (different arity/tag) → FULL (regular match)
```

Output per rule:
```javascript
{
  preserved: [{ pred: 'code', freeVars: false }],
  deltas: [
    { pred: 'pc', position: 0, transform: 'inc', thetaFree: true },
    { pred: 'sh', position: 0, structural: 'unwrap_s', thetaFree: false },
    { pred: 'gas', position: 0, transform: 'plus', args: ['gas_cost'], thetaFree: true },
  ],
  consumed: ['stack'],
  produced: ['stack'],
}
```

This metadata is stored alongside compiled rules — zero overhead at runtime.

## Staged Implementation Plan

**Process for EVERY stage:**
1. Clean git (no uncommitted changes)
2. All tests pass (523 tests)
3. Benchmark BEFORE implementing (baseline measurement)
4. Implement the change
5. Verify all tests still pass
6. Benchmark AFTER (measure improvement)
7. Assess code complexity change
8. Commit with clear message
9. Wait for approval before next stage

**Benchmark note:** Separate precomputation time (constant, amortized) from execution time (scales with input). We optimize for execution.

### Stage 1: Flat Array Store

Replace `lib/kernel/store.js` internals with TypedArray SoA arena.

**Sub-phases (to minimize risk):**
- **1a:** Internal TypedArray storage. `put()` writes to arrays AND Map. `get()` still reads from Map. All callers unchanged. All tests pass. No perf change yet (proves correctness of dual-write).
- **1b:** Switch `get()` to read from TypedArrays (allocates wrapper). Remove Map reads. `tag()`, `child()` read TypedArrays directly. All callers still use `Store.get()` API. Tests pass. Marginal perf improvement.
- **1c:** Remove Map storage entirely. Only dedup Map remains (for `put()` content-addressing). `get()` allocates wrapper from arrays. `tag()`, `child()`, `arity()` are O(1) array reads. Tests pass. Measure Store-level improvement.
- **1d:** Migrate hot-path callers from `Store.get(h).tag` → `Store.tag(h)` / `Store.child(h, i)`:
  - `unify.js match()` — ~12 Store.get calls per match
  - `forward.js tryMatch()` — ~8 Store.get calls per tryMatch
  - `substitute.js apply()` — ~5 Store.get calls per substitution
  - Other cold-path callers keep `Store.get()` wrapper. Tests pass. Benchmark full pipeline.

**What changes:**
- `Store.put()` returns sequential index instead of content hash
- Internal storage: `Map<hash, {tag, children}>` → TypedArray SoA + dedup Map
- Tag comparison: string `===` → integer `===` (via `Store.TAG` export)
- String interning for atom/variable names
- BigInt side table for `binlit` values
- Content-address dedup Map on `put()` only (cold path)

**What doesn't change:**
- `a === b` equality still works (same content → same index via dedup)
- Hashes as object keys in state (`state.linear[hash]`) still works — just numbers
- Hashes in Maps/Sets still works — sequential indices are still numbers
- `Number(h)` string→number conversions in context/state: unchanged
- No changes to rule format, prover, or engine logic

**Call site migration (from code audit):**

| Pattern | Sites | Action |
|---------|-------|--------|
| `Store.get(h).tag` | 41 | Hot path → `tags[h]`; cold path → keep `Store.get()` |
| `node.children.map(fn)` | 12 | Add `Store.mapChildren(h, fn)` accessor |
| `node.children.length` | 8 | Add `Store.arity(h)` accessor → `arities[h]` |
| `node.children.some(fn)` | 3 | Add `Store.someChild(h, fn)` accessor |
| `node.children[i]` | 20+ | → `Store.child(h, i)` (already exists) |
| `Store.clear()` | 5 (tests) | Reset all structures |
| `Store.isTerm(v)` | 3 | Range check `v >= 0 && v < nextId` |
| `Store.isTermChild(c)` | 14 | `typeof c === 'number'` unchanged (all children are uint32 now, but callers only see mixed types via `get()` wrapper or `child()` accessor) |

**Scope:** ~300 LOC (new store internals + accessor additions + hot-path migration)
**Benefit:** 12-16x faster Store reads on hot path
**Risk:** Low. Sub-phases ensure each step is independently testable.

### Stage 2: Preserved/Delta Detection (compile-time analysis)

Add analysis pass in `compileRule()` (forward.js) or a new module `lib/prover/strategy/rule-analysis.js`.

**What changes:**
- Each compiled rule gets `preserved: [...]`, `deltas: [...]`, metadata
- Analysis compares antecedent vs consequent patterns
- Classification: preserved (match-only), delta (in-place update), full (unchanged)
- Variable dependency analysis: which preserved predicates are truly free
- No execution changes yet — just metadata generation

**What doesn't change:**
- Execution still uses full match/consume/produce
- Rules unchanged
- No API changes

**Scope:** ~200 LOC analysis code
**Benefit:** None yet (just metadata). Validates the approach — can inspect which rules have what optimizations.
**Risk:** Very low. Pure addition.

### Stage 3: Optimized Execution (preserved skip + delta apply)

Modify `tryMatch` and `applyMatch` to use the metadata from Stage 2.

**What changes:**
- `tryMatch`: for preserved predicates with all vars bound, verify existence only. For preserved with unbound vars, match normally but mark as non-consumed. For delta predicates, read+transform+swap.
- `applyMatch`: skip consume/produce for preserved. Apply deltas for delta predicates. Full substitute for unclassified.
- Fallback to full match/substitute for non-optimizable predicates.

**What doesn't change:**
- Rules unchanged
- Exploration tree unchanged
- Cycle detection, depth bounds, choice expansion unchanged
- General prover (backward chaining, manual proving) unchanged

**Scope:** ~200 LOC modifications to forward.js hot path
**Benefit:** ~2-5x on forward chaining (73% of antecedent patterns optimized). Combined with Stage 1: ~15-30x total.
**Risk:** Medium. Must ensure correctness — the optimized path must produce identical state as the full path. Test by running both and comparing.

### Stage 4: Path-Based Nested Access (future)

For rules with deeply nested preserved types, precompute paths to changed leaves and use incremental Merkle update.

**Prerequisite:** Rules must actually USE deeply nested types. Current EVM rules use flat predicates (depth 1-2). This stage becomes valuable when:
- EVM facts are merged into one `evm(...)` type, or
- Other calculi use deeply nested linear types

**Scope:** ~300 LOC
**Benefit:** O(K*D) instead of O(N) per preserved nested term.
**Risk:** Low (additive optimization).

## Complexity Summary

| Stage | Code Change | Performance Impact | Risk |
|-------|-----------|-------------------|------|
| 1: Flat store | ~300 LOC (new store + migrations) | 12-16x on Store reads | Low |
| 2: Detection | ~200 LOC (analysis pass) | None (metadata only) | Very low |
| 3: Optimized exec | ~200 LOC (hot path mods) | 2-5x on forward chaining | Medium |
| 4: Nested paths | ~300 LOC (path navigation) | O(K*D) vs O(N) per nested term | Low |

**Cumulative estimate:**
- After Stage 1: ~0.3ms (from 3.1ms)
- After Stage 3: ~0.1-0.2ms
- After Stage 4 (with merged types): ~0.05-0.1ms

## Relation to Content vs Path Addressing

The original question: should CALC use path-addressed trees instead of content-addressed trees?

**Answer:** Both, at different levels.

- **Content-addressed:** All values (symbolic expressions, binary numbers, formulas). Essential for O(1) equality, structural sharing, multiset keys. This does NOT change.
- **Path-addressed:** Access patterns within preserved terms. The engine knows WHERE in a term to read/write, without searching. Paths are precomputed at compile time from rule structure.

This IS the hybrid. Content-addressing answers "WHAT is this value?" Path-addressing answers "WHERE in this term do I find the value that changes?"

The incremental Merkle update along changed paths is exactly where the original intuition ("hash changes propagate from leaf to root") is correct and useful — within a single preserved term, updating a leaf DOES require rehashing up to the root, and doing it incrementally (only the changed path) is cheaper than rebuilding everything.

## References

- Baader & Nipkow (1998) — Term rewriting positions and paths
- Stickel (1989) — Path indexing for theorem provers
- Conchon & Filliatre (2006) — Type-safe modular hash-consing
- Sampson (2019) — Flattening ASTs (arena allocation)
- BitECS — SoA TypedArray architecture for JS
- See also: `doc/research/flat-array-store.md`, `doc/research/path-addressed-trees.md`
