# TODO_0063: arrlit — compact array literals

## Problem

EVM bytecode is encoded as individual `code PC V` linear facts — one per byte. A 1040-byte Solidity contract produces 764 Store nodes, 764 FactSet entries, and a 764-entry fingerprint index. The stack uses individual `stack HEIGHT VALUE` facts plus an `sh` height counter. This encoding is:

- **Wasteful**: 764 × 18 bytes SoA = ~14KB for data that's a 1040-byte flat array
- **Parse-heavy**: 764 `Store.put` calls + 764 FactSet insertions at load time
- **Clone-heavy**: symexec branching clones all code facts (even though they never change)
- **Verbose in rules**: DUP8 unrolls 8 nested `(s ...)` wrappers for stack height

The `binlit` precedent shows how a compact Store node with a side table + ephemeral expansion gives O(1) storage for data that would otherwise require O(n) nodes.

See also: [RES_0070 — Compact Array/Sequence Representations](../research/0070_compact-array-representations.md) for survey of array representations across SMT solvers, proof assistants, CHR, EVM symbolic executors, and functional languages.

## Design: `arrlit` — array literal with ephemeral expansion

### Logical theory

```
arr: type.
ae: arr.                        % empty array
acons: bin -> arr -> arr.      % cons element onto array
```

Logically, `acons 0x60 (acons 0x80 (acons 0x60 (acons 0x40 ae)))` represents `[0x60, 0x80, 0x60, 0x40]`. This is never materialized — the Store holds a single `arrlit` node backed by a flat typed array.

### Store representation

```
Tag: arrlit (new pre-registered tag)
Arity: 1
Child0: index into ARRAY_TABLE (new side table)

ARRAY_TABLE[id] = Uint32Array of Store hashes
  (each element is a content-addressed hash, not a raw value)
```

For bytecode: elements are `binlit` hashes (one per byte).
For stack: elements are arbitrary term hashes (binlit, freevar, compound).

### No polymorphism needed

The type system is first-order: `bin` is the universal value type. `code: bin -> bin -> type`, `stack: nat -> bin -> type` — bytes, words, addresses, symbolic freevars all inhabit `bin`. So `arr: type` with `acons: bin -> arr -> arr` is monomorphic but universal. The same `arr` type works for bytecode (ground bytes), stack (mixed symbolic/ground), and future uses (memory regions).

Parametric arrays (`arr: type -> type`, e.g. `arr(byte)` vs `arr(w256)`) would require type constructors — LF/CLF dependent types territory. Not needed here: element-type discipline is enforced by the rules, not the type system. A `!get B PC V` on bytecode always yields a ground byte because the bytecode arrlit was constructed ground; the type system doesn't need to prove that.

### Ephemeral expansion (unify.js)

Pattern matching against `arrlit` follows the `binlit` blueprint:

| Pattern | arrlit([h0, h1, ...]) | Action |
|---|---|---|
| `ae` | `arrlit([])` | succeed iff empty |
| `acons(H, T)` | `arrlit([h0, h1, ...])` | bind H = h0, T = arrlit([h1, ...]) |
| `arrlit` (direct) | compare array identity | succeed iff same table id |

The critical operation is `acons(H, T)` decomposition:
1. Extract array from ARRAY_TABLE: O(1)
2. Head = array[0]: O(1)
3. Tail = new arrlit(array.slice(1)): O(n) copy — but see Sub-array Sharing below

### Sub-array sharing

For stack operations (PUSH/POP decompose frequently), O(n) slice on every pattern match is expensive. Two approaches:

**Option A: Offset arrays.** ARRAY_TABLE stores `{ data: Uint32Array, offset: u32, length: u32 }`. Tail creates a view: `{ data: same, offset: offset+1, length: length-1 }`. O(1) decomposition, shared backing.

**Option B: Copy-on-match.** Accept O(n) copy. Stacks are small (≤16 in practice). 16 × 4 = 64 bytes per copy. At ~300 execution steps: ~19KB total. Acceptable.

Recommendation: **Option A** (offset arrays). Cleaner, and the same data structure works for both small stacks and large bytecode.

### Persistent accessor: `!get`

```
get: arr -> bin -> bin -> type.
```

`!get A I V` — element at index I of array A is V. Backward-chained via FFI:

```javascript
// lib/engine/ffi/array.js
function get(args) {
  const [arrHash, idxHash, valHash] = args;
  const arr = Store.getArray(arrHash);   // ARRAY_TABLE lookup
  const idx = binToInt(idxHash);         // binlit → BigInt → Number
  if (arr === null || idx === null) return { success: null }; // non-ground
  if (idx < 0n || idx >= BigInt(arr.length)) return { success: false };
  return { success: true, theta: [[valHash, arr.data[arr.offset + Number(idx)]]] };
}
```

This gives O(1) random access, needed for:
- PUSH rules: read opcode data bytes at arbitrary PC offsets
- DUP rules: read stack element at depth N
- SWAP rules: read + replace at depth N

### Persistent mutator: `!set`

```
set: arr -> bin -> bin -> arr -> type.
```

`!set A I V A'` — A' is A with element I replaced by V. For SWAP operations:

```javascript
function set(args) {
  const [arrHash, idxHash, valHash, resultHash] = args;
  const arr = Store.getArray(arrHash);
  const idx = binToInt(idxHash);
  if (arr === null || idx === null) return { success: null };
  if (idx < 0n || idx >= BigInt(arr.length)) return { success: false };
  // Create new array with element replaced
  const newArr = arr.slice();  // copy
  newArr[Number(idx)] = valHash;
  const newHash = Store.put('arrlit', [newArr]);
  return { success: true, theta: [[resultHash, newHash]] };
}
```

### Persistent length: `!alen`

```
alen: arr -> bin -> type.
```

Replaces `sh` height counter for stacks:

```javascript
function alen(args) {
  const [arrHash, lenHash] = args;
  const arr = Store.getArray(arrHash);
  if (arr === null) return { success: null };
  return { success: true, theta: [[lenHash, intToBin(BigInt(arr.length))]] };
}
```

## Hex as first-class

### Current state

Hex is a text preprocessor: `N_FF` → `(i (i (i (i (i (i (i (i e))))))))` in source, then parsed to `binlit(255n)`. The `0x` prefix in the Pratt parser directly produces `binlit`. No hex representation survives past parsing.

### New: hex byte-string literals

Syntax: `0x6080604052...` (even-length hex string, any length).

When used as an argument to an `arr`-typed position, the parser produces an `arrlit` where each pair of hex digits becomes one `binlit` element:

```
bytecode 0x60806040
```

Parses to: `arrlit([binlit(0x60), binlit(0x80), binlit(0x60), binlit(0x40)])`

This eliminates `tools/bytecode-to-ill.js` and `lib/engine/hex.js` (`expandHexNotation`). Bytecode files shrink from 764 lines to 1 line.

### Parser changes (builders.js)

The Pratt parser already handles `0x...` → `binlit`. Extended behavior:
- Short hex (≤ 64 hex chars = 32 bytes): stays `binlit` (a single number)
- Long hex (> 64 hex chars) OR in `arr` type context: becomes `arrlit` of bytes

Alternative (simpler): introduce explicit `hex"..."` or `bytes"..."` syntax for byte arrays. Keep `0x...` as `binlit`.

Decision: use context-free `0x` prefix. Parser uses length heuristic: if > 64 hex chars, it's an arrlit. If ≤ 64, it's binlit. Explicit `bytes` keyword available for disambiguation.

## EVM rule rewrites

### Bytecode

Current (764 facts):
```
code   0  0x60  *
code   1  0x80  *
...
```

New (1 fact):
```
bytecode 0x608060405260043610...
```

### Rule: evm/add (before)

```
evm/add:
  pc PC *
  code PC 0x01 *
  !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) A *
  stack SH B
  -o {
    exists C. exists C'. (
      code PC 0x01 *
      pc PC' *
      sh (s SH) *
      stack SH C' *
      !plus A B C * !to256 C C')
  }.
```

### Rule: evm/add (after)

```
evm/add:
  pc PC *
  bytecode B *
  !get B PC 0x01 *
  !inc PC PC' *
  stack (acons A (acons B_val REST))
  -o {
    exists C. exists C'. (
      bytecode B *
      pc PC' *
      stack (acons C' REST) *
      !plus A B_val C * !to256 C C')
  }.
```

Changes:
- `code PC 0x01` → `bytecode B * !get B PC 0x01` (persistent lookup, ground opcode for discrimination)
- `sh` eliminated — it was purely internal accounting (no EVM opcode reads stack depth). It served two roles: (1) addressing `stack` facts by position, (2) guarding minimum stack depth. With arrlit, both are subsumed: `acons` decomposition addresses elements directly, and `acons(A, acons(B, REST))` inherently fails on a 1-element arrlit (structural guard). For DUP/SWAP, `!get S N V` returns `{ success: false }` on out-of-bounds — equivalent to the current pattern-match failure on insufficient `sh` depth. Value-level guards (`!to256`, `!trim`) are orthogonal to container representation and remain unchanged. No stack overflow guard (1024 max depth) exists in the current rules, and none is added here.
- `stack (s SH) A * stack SH B` → `stack (acons A (acons B_val REST))` (ephemeral expansion)
- Re-production: `bytecode B` reproduced (linear), `stack (acons C' REST)` reconstructed

### Rule: evm/push1 (before)

```
evm/push1:
  pc PC *
  code PC 0x60 *
  code PC' V *
  !inc PC PC' *
  !inc PC' PC'' *
  sh SH
  -o {
    pc PC'' * code PC 0x60 * code PC' V *
    sh (s SH) * stack SH V
  }.
```

### Rule: evm/push1 (after)

```
evm/push1:
  pc PC *
  bytecode B *
  !get B PC 0x60 *
  !inc PC PC' *
  !get B PC' V *
  !inc PC' PC'' *
  stack S
  -o {
    bytecode B *
    pc PC'' *
    stack (acons V S)
  }.
```

Cleaner: no `sh`, no reproducing data code facts, no separate code fact for push data.

### Rule: evm/dup3 (before)

```
evm/dup3:
  pc PC * code PC 0x82 * !inc PC PC' *
  sh (s (s (s SH))) *
  stack SH V
  -o {
    code PC 0x82 * pc PC' *
    sh (s (s (s (s SH)))) *
    stack SH V * stack (s (s (s SH))) V
  }.
```

### Rule: evm/dup3 (after)

```
evm/dup3:
  pc PC *
  bytecode B *
  !get B PC 0x82 *
  !inc PC PC' *
  stack S *
  !get S 2 V
  -o {
    bytecode B *
    pc PC' *
    stack (acons V S)
  }.
```

Dramatically simpler. One DUP rule template parameterized by depth.

### Rule: evm/swap1 (after)

```
evm/swap1:
  pc PC *
  bytecode B *
  !get B PC 0x90 *
  !inc PC PC' *
  stack (acons X (acons Y REST))
  -o {
    bytecode B *
    pc PC' *
    stack (acons Y (acons X REST))
  }.
```

### Rule: evm/pop (after)

```
evm/pop:
  pc PC *
  bytecode B *
  !get B PC 0x50 *
  !inc PC PC' *
  stack (acons _ REST)
  -o {
    bytecode B *
    pc PC' *
    stack REST
  }.
```

### Predicate declarations

```
bytecode: arr -> type.           % replaces code: bin -> bin -> type.
stack: arr -> type.              % replaces stack: nat -> bin -> type.
% sh: nat -> type.              % eliminated
```

For deeper swaps (swap3+), use `!get` + `!set`:

```
evm/swap4:
  pc PC *
  bytecode B *
  !get B PC 0x93 *
  !inc PC PC' *
  stack (acons X REST) *
  !get REST 3 Y *
  !set REST 3 X REST'
  -o {
    bytecode B *
    pc PC' *
    stack (acons Y REST')
  }.
```

## Fingerprint indexing impact

### Current: O(1) via ground opcode in `code PC OPCODE`

The fingerprint discriminator detects that `code` has a ground child (the opcode byte), giving O(1) rule selection.

### New: O(1) via `!get B PC OPCODE` with ground OPCODE

The persistent antecedent `!get B PC 0x01` still contains a ground opcode. The compiled matcher can:
1. Evaluate `!get B PC V` via FFI (O(1) array lookup)
2. Check `V == 0x01` (the ground value in the rule)

This is a **two-step fingerprint**: first FFI lookup, then value discrimination. Compile.js needs to recognize this pattern and generate the appropriate compiled matcher.

Alternative: introduce a "virtual fingerprint" that evaluates `!get bytecode PC` to get the opcode, then dispatches to the rule with matching opcode. This is essentially the same O(1) lookup but structured as a pre-step before rule matching.

## Store changes

### New tag registration

```javascript
// store.js
['atom', 'freevar', ..., 'oplus', 'zero', 'arrlit'].forEach(registerTag);
```

### New side table

```javascript
// Offset-array structure for sub-array sharing
const ARRAY_TABLE = [];     // { data: Uint32Array, offset: u32, length: u32 }
let nextArrayId = 0;

const ARRAY_CHILD_TAGS = new Uint8Array(256);
ARRAY_CHILD_TAGS[TAG.arrlit] = 1;

function storeArray(data, offset = 0, length = data.length) {
  const id = nextArrayId++;
  ARRAY_TABLE.push({ data, offset, length });
  return id;
}

function getArray(id) {
  const entry = ARRAY_TABLE[id];
  return { data: entry.data, offset: entry.offset, length: entry.length };
}
```

### Content addressing

Two arrlit nodes with identical element hashes must produce the same Store hash. The hash function needs to incorporate all elements:

```javascript
function computeHash('arrlit', [arrayId]) {
  const { data, offset, length } = ARRAY_TABLE[arrayId];
  let h = hashInit('arrlit');
  for (let i = 0; i < length; i++) {
    h = hashCombine(h, data[offset + i]);
  }
  return h;
}
```

**Deduplication concern**: identical arrays (same elements) but different table entries must dedup to the same hash. The dedup map handles this — `put('arrlit', [...])` checks the hash.

### Snapshot/restore

```javascript
snapshot() → { ..., arrays: [{ data, offset, length }, ...] }
restore(data) → rebuild ARRAY_TABLE
```

### Binary serialization (store-binary.js)

New section after BigInt table:

```
Array table:
  arrayCount  u32
  for each array:
    offset    u32
    length    u32
    data      u32[length]   (Store hashes)
```

For a 1040-byte bytecode: 1 array × (8 + 4×1040) = 4168 bytes.
Current: 764 nodes × 18 bytes = 13,752 bytes. **3.3× smaller.**

## Theory compliance

### Linear logic

- `bytecode B` is linear: consumed and re-produced each step. This maintains the resource discipline. The bytecode array itself is immutable — mutations happen via new arrlit construction.
- `stack S` is linear: consumed and re-produced with new contents. `acons` creates a new arrlit (no in-place mutation).
- `!get`, `!set`, `!alen` are persistent: they compute facts from data, consistent with the FFI-is-optimization principle.

### Backward clause definitions (FFI safety net)

Every FFI-backed persistent predicate must have clause definitions:

```
get/acons/z: get (acons V T) 0 V.          % base case: index 0
get/acons/s: get (acons _ T) I V            % recursive: index > 0
  <- plus 1 I' I <- get T I' V.

set/acons/z: set (acons _ T) 0 V (acons V T).
set/acons/s: set (acons H T) I V (acons H T')
  <- plus 1 I' I <- set T I' V T'.

alen/ae: alen ae 0.
alen/acons: alen (acons _ T) N <- alen T N' <- inc N' N.
```

Note: out-of-bounds access on `ae` simply fails (no matching clause). No explicit zero/error rule needed.

With FFI disabled, the system falls back to these clause definitions (slower but correct). The ephemeral expansion in unify.js decomposes `arrlit` into `acons/ae` transparently.

### Focusing

`acons` is a positive connective (like `tensor`): it constructs data. Focusing should treat it as:
- Invertible on LEFT (decompose `acons(H,T)` eagerly in antecedent)
- Focusable on RIGHT (construct in succedent)

Since arrlit is used in forward rules (not the focused prover), this matters only if arrlit appears in backward-chaining contexts. The clause definitions above are already structured correctly.

## Symbolic values in arrlits

### The problem

Bytecode is fully ground — every element is a concrete byte (`binlit`). But the EVM stack contains symbolic values during symbolic execution:

```
% After CALLDATALOAD: V is a fresh freevar (symbolic input)
stack 0 V

% After ADD with symbolic operand: C' is existential (depends on V)
stack 0 C'

% Compound symbolic terms also appear:
stack 0 (sha3 Bytes)
```

An arrlit stack `arrlit([V, binlit(42), sha3_hash])` contains a mix of ground and symbolic Store hashes. This is representable (ARRAY_TABLE stores `Uint32Array` of opaque hashes), but raises several concerns.

### Why it works: hashes are opaque

The ARRAY_TABLE stores Store hashes (`uint32` indices). A hash can point to any node type: `binlit`, `freevar`, `app`, compound terms. The array doesn't distinguish — it's a flat sequence of hashes.

```
arrlit ARRAY_TABLE entry:
  [freevar_hash_17,  binlit_hash_42,  app_hash_sha3]
   ↑ symbolic         ↑ ground         ↑ compound
   all valid uint32 Store indices
```

Content-addressing works: two arrlits with identical hash sequences get the same Store hash, regardless of what the hashes point to. Symexec branching clones the arrlit hash (1 uint32), not the array contents.

### Normalization: acons-over-arrlit folding

When a rule produces `stack (acons C' REST)`, the substitution engine builds:

```
subApplyIdx(acons_pattern, theta, slots)
  → Store.put('acons', [resolved_C', rest_arrlit_hash])
```

This creates a **compound node** `acons(C', arrlit([...]))`, NOT a flat arrlit. Without normalization, repeated PUSHes produce nested chains:

```
acons(v1, acons(v2, acons(v3, arrlit([v4, v5]))))
```

This defeats the purpose — we'd have O(depth) chains instead of flat arrays.

**Solution: normalize at construction time.** When `Store.put('acons', [head, tail])` detects that `tail` is an arrlit, fold into a new arrlit:

```javascript
// In Store.put or a normalization wrapper
if (tagName === 'acons' && Store.tag(children[1]) === 'arrlit') {
  const tailArr = Store.getArray(children[1]);
  const newData = new Uint32Array(tailArr.length + 1);
  newData[0] = children[0];  // head (may be freevar, binlit, anything)
  newData.set(tailArr.elements(), 1);
  return Store.put('arrlit', [newData]);
}
// Symmetric: acons(head, ae) → arrlit([head])
if (tagName === 'acons' && Store.tag(children[1]) === 'atom'
    && Store.child(children[1], 0) === 'ae') {
  return Store.put('arrlit', [new Uint32Array([children[0]])]);
}
```

This mirrors binlit normalization: `builders.js` folds `(i binlit(5n))` → `binlit(11n)` at parse time. For arrlit, we fold at Store.put time so it applies everywhere (parser, substitution, FFI output).

**Alternative: lazy normalization.** Don't normalize; let `acons` chains accumulate. The unifier handles mixed representations via ephemeral expansion. Stack depth is bounded (~16), so chains are short. This is simpler but produces a less uniform representation and breaks the "1 fact = 1 arrlit" invariant.

Recommendation: **eager normalization** in Store.put. It's a small check (one tag comparison) and keeps the representation canonical.

### FFI behavior with symbolic elements

When `!get S I V` accesses an arrlit element that is symbolic:

```javascript
function get(args) {
  const [arrHash, idxHash, valHash] = args;
  const arr = Store.getArray(arrHash);
  const idx = binToInt(idxHash);
  if (arr === null || idx === null) return { success: null }; // non-ground index
  if (idx < 0n || idx >= BigInt(arr.length)) return { success: false };
  const element = arr.data[arr.offset + Number(idx)];
  // element might be a freevar — that's fine, bind V to it
  return { success: true, theta: [[valHash, element]] };
}
```

The FFI doesn't care whether `element` is ground or symbolic. It returns the hash as a binding for V. The caller handles unification normally. This is the same behavior as if the element were in a separate `stack H V` fact — the V would be a freevar hash either way.

When the **index I is non-ground** (symbolic), the FFI returns `{ success: null }`. The system falls back to backward clause resolution via `get/acons/z` and `get/acons/s`, which use ephemeral expansion to walk the arrlit. This is O(n) but correct.

### `!set` with symbolic values

`!set S I V S'` works identically: create a new arrlit with element I replaced by V (which may be a freevar hash). The new arrlit is content-addressed — if the same symbolic replacement happens in two branches, they get the same hash.

### Staging: ground-only first

**Stage A (ground-only):** `Store.put('arrlit', [...])` asserts all elements are ground (checked via `isGround()`). This is sufficient for:
- Bytecode (always ground binlits)
- Concrete test cases

At this stage, stack stays as individual `stack H V` facts. arrlit is only used for bytecode.

**Stage B (symbolic):** Remove the ground assertion. arrlit now accepts any Store hash as element. This enables:
- Stack-as-arrlit (with symbolic values from CALLDATALOAD, etc.)
- Memory regions as arrlit (future)

The delta between A and B is small: remove one assertion, add normalization in Store.put. All FFI and ephemeral expansion code is already symbolic-agnostic (it operates on opaque hashes).

### Edge cases

1. **Empty stack:** `arrlit([])` — the `ae` base case. Valid, represents an empty stack.

2. **Stack after branch merge:** Two branches may produce different symbolic values at the same position. Since symexec explores each branch independently (no merge), this isn't an issue — each branch has its own arrlit.

3. **Constraint solver interaction:** The `EqNeqSolver` tracks `!eq X Y` / `!neq X Y` constraints on symbolic values. These constraints reference freevar hashes. Whether those hashes live inside an arrlit or in individual facts doesn't matter — the solver operates on the hashes, not on the container.

4. **Structural memo with symbolic stacks:** `computeControlHash(state)` currently hashes PC and SH. With arrlit stacks, it would hash PC and the stack arrlit hash. Since the arrlit hash incorporates all element hashes (including symbolic freevars), two states with different symbolic stack contents get different control hashes. This is correct — they are genuinely different states.

## Performance analysis

### Loading

| Metric | Current | arrlit |
|---|---|---|
| Store.put calls (code) | 764 | 1 + 764 binlit |
| FactSet insertions | 764 | 1 |
| Parse time (estimated) | ~5ms | ~1ms |

The 764 binlit nodes for individual byte values are likely already in the Store (shared across programs). Only the arrlit container is new.

### Memory

| Metric | Current | arrlit |
|---|---|---|
| SoA nodes (code facts) | 764 × 18B = 13.7KB | 1 × 18B + 4.2KB array = 4.2KB |
| FactSet linear pool | 764 entries | 1 entry |
| Fingerprint index | 764-entry object | not needed |

### Symexec cloning

| Metric | Current | arrlit |
|---|---|---|
| Code facts to clone | 764 Int32 entries | 1 Int32 entry |
| Stack facts to clone | ~4-8 entries + sh | 1 entry |
| Total clone cost | O(764 + stack) | O(2) |

This is the biggest win: symexec explores ~300 nodes, each branching clones the state. Reducing from ~770 facts to ~2 facts eliminates the dominant cloning cost.

### Rule matching

| Metric | Current | arrlit |
|---|---|---|
| Fingerprint O(1) | via `_byKey[PC]` | via FFI `get(B, PC)` |
| Per-step overhead | 1 object lookup | 1 FFI call + 1 array access |

Roughly equivalent. FFI call has slightly more overhead than a plain object property lookup, but the difference is negligible at ~100ns scale.

## Implementation stages

### Stage 1: Store infrastructure (ground-only) — DONE

Commit `ea3fd10`. 50 tests.

- `arrlit` tag pre-registered, ARRAY_TABLE with offset-array structure
- `putArray(data)` / `getArrayElements(hash)` — O(1) create/lookup
- Content-addressing incorporates all elements
- `snapshot()`/`restore()` and `store-binary.js` serialization
- `show.js` displays `[0x1, 0x2, ...]` with truncation for large arrays

### Stage 2: Ephemeral expansion — DONE

Commit `bd7971e`. 45 tests.

- `unifyArrlit()` in `unify.js` — `acons(H,T)` / `ae` matching against arrlit
- `acons` registered as pre-registered tag, `ae` as atom
- Offset-array O(1) decomposition (no copy on tail)
- Integrated in `unify()`, `match()`, `matchIndexed()`

### Stage 3: FFI — DONE

Commit `df6ff81`. 25 tests.

- `lib/engine/ffi/array.js` — `arr_get`, `arr_set`, `alen`, `read_bytes`
- Backward clause definitions in `calculus/ill/prelude/arr.ill` (McCarthy axioms)
- Modes: `arr_get(+,+,-)`, `arr_set(+,+,+,-)`, `alen(+,-)`, `read_bytes(+,+,+,-)`

### Stage 4: Hex-to-arrlit parser + bracket syntax — DONE

Commits `3de7fb2`, `8d26bdc`. 13 tests.

- Long hex (> 64 hex chars) → arrlit of byte-sized binlits; short hex stays binlit
- `[...]` bracket syntax: `bytecode [0x60, 0x80, ...]`
- `expandHexNotation` removed from hot path

### Stage 5: EVM bytecode rules — DONE

Commit `8804d09`. E2E + memory tests pass.

- All 74 EVM rules rewritten: `code PC V` → `bytecode BC * !arr_get BC PC V`
- Virtual fingerprint in `compile.js`: detects `!arr_get B PC GROUND` pattern
- `codeToArrlit()` backward-compat conversion for old `.ill` files
- `bytesToSemantic()` groups PUSHn data bytes into single values
- Bytecode `.ill` files: 764 lines → 1 line each
- Stack remains as individual `stack H V` facts (deferred to Stage 7)

### Stage 6: Symbolic arrlit + acons normalization — DONE

Commit `8d9113b`. 7 tests.

- `acons(H, arrlit([...]))` → `arrlit([H, ...])` at `Store.put` time
- `acons(H, ae)` → `arrlit([H])`
- Cascading: `acons(v1, acons(v2, arrlit([v3])))` → `arrlit([v1, v2, v3])`
- Works with symbolic elements (freevars, compound terms)

### Stage 7: EVM stack as arrlit — DONE

- Removed `sh: nat -> type.` declaration, changed `stack: nat -> bin -> type.` to `stack: arr -> type.`
- Rewrote all ~50 EVM rules: PUSH uses `stack S → stack (acons V S)`, binary ops use `stack (acons A (acons B REST))`, DUP2+ uses `!arr_get S N V`, SWAP2+ uses `!arr_get/!arr_set`
- `computeControlHash` uses `PC + stack arrlit length` (not stack contents — same memo semantics as old `PC + sh`)
- Fixed substitution (`substitute.js`) to descend into arrlit elements via `_subArrlit` helper
- Fixed `isGround` (`ffi/convert.js`) — arrlit is always "ground" for FFI dispatch (concrete container)
- Made `arr_set` multiModal — value arg can be symbolic (needed for SWAP with symbolic stack elements)
- Updated all `.ill` initial states: `sh ee` → `stack ae`
- Updated memory.test.js, rule-analysis.test.js assertions
- Performance: multisig −51.5%, solc_symbolic −34% (benchmark comparison)

### Stage 8: Cleanup — DONE

- Updated benchmark files for new stack representation
- Updated test assertions for `bytecode`/`stack` predicates (no `code`/`sh`)
- Marked TODO complete

## Measured benchmarks (solc_symbolic, 477 nodes / 11 leaves)

Comparing pre-arrlit (before `feature/arrlit`) vs current:

| Phase | Before | After | Delta |
|---|---|---|---|
| Uncached setup (load + parse) | ~29ms | ~29ms | ~0ms |
| `decomposeQuery` | 1.53ms | 0.23ms | −85% |
| `codeToArrlit` | 1.07ms | 0.20ms | −81% |
| `bytesToSemantic` | — | 0.65ms | new |
| **explore** | **20.2ms** | **8.8ms** | **−57%** |

End-to-end (multisig): 18ms → 2.7ms (−85%). Tree structure unchanged (477/11 and 84/2 nodes/leaves) — speedup is from reduced cloning and matching overhead.

## Compact buffer storage analysis — REJECTED

**Question**: storing ~200 deduped binlit entries for bytecode bytes seems wasteful. Could a `bufflit(Uint8Array)` tag store raw bytes directly (like `binlit` stores BigInt) and expand lazily?

**Findings** (profiled on solc_symbolic, 1040-byte bytecode):

Content-addressing deduplicates byte-level binlits: only ~200 unique entries (bytes 0x00–0xFF that actually appear), not 1040. Total Store cost: ~8KB (0.01% of capacity). The hex parser creates binlits once; `bytesToSemantic()` then creates ~200 more semantic binlits (combined PUSH values).

During `explore()`, bytecode is accessed via virtual fingerprint (`elems[Number(idx)]`) and `arr_get` FFI — both O(1) into the semantic `Uint32Array`. They read pre-existing hashes, never create new Store entries. A compact buffer would produce the same Uint32Array after semantic conversion.

| Aspect | Savings | Cost |
|---|---|---|
| Load time | ~0.2ms (0.85ms → ~0.65ms) | New tag, side table, parser changes |
| Explore time | 0ms | Dual code path in `bytesToSemantic()` |
| Store entries | ~200 (0.005% of capacity) | Serialization in `store-binary.js` |

**Verdict**: not worth the complexity. The 0.2ms load-time savings is negligible. If load time matters, the precompiled binary cache (`mde.load(file, { cache: true })`) skips parsing and semantic conversion entirely (~2.6ms total vs ~14ms uncached).

## Resolved open questions

1. **acons/ae as atoms or tags?** — RESOLVED: `acons` is a pre-registered tag. `ae` is an atom (used via `atom('ae')`). Tag dispatch for `acons` in unify.js; atom comparison for `ae`.

2. **Sub-array deduplication** — RESOLVED: accepted. Content-address hash ensures logical equality. Physical sharing differs (different offsets into same backing data) but this is fine — dedup map handles it.

3. **arrlit of binlit vs. raw bytes (byteslit/bufflit)** — RESOLVED: rejected. See "Compact buffer storage analysis" above. The ~200 deduped binlits cost ~8KB. Not worth a new tag.

4. **PUSHn multi-byte data** — RESOLVED: implemented as `read_bytes` FFI in `ffi/array.js`. `bytesToSemantic()` pre-groups PUSH data at load time, so rules see single values at runtime. Both approaches coexist: raw byte access via `arr_get` and pre-grouped semantic access.

5. **Compiled matcher adaptation** — RESOLVED: implemented as "virtual fingerprint" in `compile.js` (Phase B2). Detects `!arr_get B PC GROUND`, generates FFI dispatch. O(1) rule selection preserved.

6. **Normalization placement** — RESOLVED: `Store.put` (one tag comparison per put call, negligible cost, canonical everywhere).

7. **Symbolic stack construction** — RESOLVED: Store.put normalization handles it transparently. Substitution engine needed arrlit-awareness (`_subArrlit` helper in `substitute.js`) to descend into arrlit element arrays.

8. **Mixed representation during transition** — RESOLVED: no longer mixed. Both bytecode and stack use arrlit. All stages complete.

## Stage 7 assessment: DONE — better than expected

Pre-assessment predicted ~0.2-0.3ms savings. Actual measured results (bench:diff:symexec, 20 iterations):

| Benchmark | Before | After | Delta |
|---|---|---|---|
| symexec.multisig | 3.9ms | 1.9ms | **−51.5%** |
| symexec.solc_symbolic | 10.0ms | 6.6ms | **−34%** |

The larger-than-predicted wins come from: (1) reduced FactSet operations (fewer facts per step), (2) simpler pattern matching (no nested `(s ...)` unwrapping), (3) reduced disc-tree index entries.

Key implementation discoveries:
- **Substitution into arrlits**: `acons-over-arrlit` normalization buries terms inside arrlit element arrays. All substitution functions (`sub`, `apply`, `applyIndexed`, `occurs`, `debruijnSubst`) needed arrlit-awareness via `_subArrlit` helper.
- **isGround for FFI dispatch**: Arrlit should always be considered "ground" for FFI purposes — it's a concrete container. Element groundness is irrelevant for container operations (`arr_get`, `arr_set`).
- **arr_set multiModal**: The value argument can be symbolic (e.g., SWAP4 with a symbolic stack element). Made `arr_set` multiModal so the FFI handles non-ground value args.
- **computeControlHash**: Uses `PC + stack length` (not stack contents), preserving structural memo semantics.
