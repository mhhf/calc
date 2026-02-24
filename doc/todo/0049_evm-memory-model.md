---
title: EVM Memory Model Design
created: 2026-02-24
modified: 2026-02-24
summary: Design MLOAD/MSTORE memory model for CALC's EVM symbolic executor
tags: [evm, memory, architecture, linear-logic, separation-logic]
type: design
status: researching
priority: 6
cluster: Symexec
depends_on: []
required_by: []
---

# EVM Memory Model Design

## Problem

Every solc-compiled contract uses MLOAD/MSTORE extensively (ABI encoding, scratch space, free memory pointer at `0x40`). Without memory support, CALC can only run hand-crafted bytecode that avoids memory operations. MLOAD (0x51) and MSTORE (0x52) are the blocking opcodes for all future benchmarks against hevm/halmos/KEVM.

## EVM Memory Semantics

From the Yellow Paper (precise spec):

- **Byte-addressable**: each address indexes one byte
- **MLOAD(offset)**: reads 32 bytes at `[offset, offset+32)`, returns 256-bit big-endian word
- **MSTORE(offset, value)**: writes 32-byte big-endian encoding of `value` at `[offset, offset+32)`
- **MSTORE8(offset, value)**: writes `value mod 256` (1 byte) at `[offset]`
- **Zero-initialized**: unwritten bytes are 0
- **Per call frame**: fresh memory for each CALL; caller memory restored on return
- **Dynamic expansion**: accessing offset `n` grows memory to `ceil((n+32)/32)` words
- **Gas**: `cost = words²/512 + 3*words` — quadratic for large memory
- **Non-aligned access**: MLOAD/MSTORE at ANY byte offset (not just multiples of 32)

Non-aligned access means MSTORE(0, X) then MSTORE(1, Y) produces an overlap at bytes [1..31]. MLOAD(0) must reconstruct from both writes. This is the central design challenge.

## Current State in CALC

`evm.ill:90` declares `memory: bin -> bin -> bin -> type.` — a **linear** ternary predicate `memory Pos Size V`. Used by two rules:

1. **concatMemory** (lines 388-403): iterates over `memory` facts, concatenating values. Consumes each `memory Pos Size V` and re-produces it (preserve-on-read pattern). Driven by `!neq Pos To` guard and `!plus Pos Size Pos'` increment.

2. **SHA3** (lines 405-423): triggers `concatMemory` with a loli continuation (`unblockConcatMemory Z -o {...}`). The continuation fires when `concatMemory/z` produces `unblockConcatMemory Z`, passing the concatenated bytes `Z` as `sha3 Z` onto the stack.

3. **CALLDATACOPY** (lines 577-612): produces `memory Ms Size D` facts from `calldata` facts. Also uses a blocking pattern (`unblock -o {pc PC'}`).

**Key observation**: Memory facts are **linear** — consumed on read, manually re-produced. This is the separation logic pattern `addr ↦ v * P ⊢ addr ↦ v * Q` encoded as `memory Pos Size V -o (memory Pos Size V * ...)`.

## How Other Tools Model Memory

See RES_0061 for full survey. Summary:

| Tool | Representation | Symbolic offsets | Read-after-write |
|------|---------------|-----------------|-----------------|
| **hevm** | Algebraic write-chain (`WriteWord o v buf`) | Abstract `ReadWord` term → SMT | Pattern match on concrete offsets; byte-by-byte for overlap |
| **KEVM** | K `Bytes` cell; rewrite rules | Transparent via matching logic | Implicit (single mutable cell) |
| **halmos** | `ByteVec` (concrete/symbolic chunks) | Require concrete; fork if symbolic | Chunk iteration |
| **Mythril** | Z3 `Array(BV256, BV8)` | Z3 `select` | SMT array theory |
| **Manticore** | SMT constraint arrays | Fork on concrete values | SMT constraint propagation |

**Key insight from hevm (RES_0060)**: Memory is an algebraic expression tree. Writes prepend nodes; reads traverse from newest to oldest. Concrete offsets resolve in O(1) per exact match or O(32) for byte-level reconstruction. Symbolic offsets produce abstract `ReadWord` terms deferred to SMT. Pre-SMT simplification (dead write elimination, constant folding) keeps terms small.

**Key insight from separation logic (RES_0061 §9)**: Linear logic's tensor `⊗` = separation logic's separating conjunction `*`. The lollipop `⊸` = magic wand `-*`. CALC's linear facts already model heap cells. The frame rule ("untouched resources are preserved") is structural in ILL.

## Design Options

### Option A: Write-Log Term (Recommended)

Single linear fact `mem M` where `M` is a content-addressed write-log:

```
mem: bin -> type.
write: bin -> bin -> bin -> bin.    % write(offset, value, prev_mem)
write8: bin -> bin -> bin -> bin.   % write8(offset, byte, prev_mem)
empty_mem: bin.
```

**MSTORE rule:**
```
evm/mstore:
  pc PC * code PC 0x52 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset *
  stack SH Value *
  mem M
  -o {
    exists M'. (
      code PC 0x52 *
      pc PC' *
      sh SH *
      mem M' *
      !mem_write Offset Value M M')
  }.
```

**MLOAD rule:**
```
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) *
  stack SH Offset *
  mem M
  -o {
    exists V. (
      code PC 0x51 *
      pc PC' *
      mem M *
      sh (s SH) *
      stack SH V *
      !mem_read Offset M V)
  }.
```

**FFI `mem_write`** (mode: `+ + + -`): creates `Store.put({tag:'write', children:[offset,value,oldMem]})`.

**FFI `mem_read`** (mode: `+ + -`): traverses write chain from newest to oldest, reconstructs 32-byte value handling overlaps.

#### Worked Example

```
% Initial: mem empty_mem

PUSH1 0x42  PUSH1 0x00  MSTORE
% → mem (write 0x00 0x42 empty_mem)

PUSH1 0xBB  PUSH1 0x20  MSTORE
% → mem (write 0x20 0xBB (write 0x00 0x42 empty_mem))

PUSH1 0x00  MLOAD
% → mem_read(0x00, write(0x20, 0xBB, write(0x00, 0x42, empty_mem)), V)
% → traverse: write(0x20,...) — offset 0x20 ≠ 0x00, skip
% → traverse: write(0x00, 0x42,...) — exact match, V = 0x42
```

#### Overlap Example

```
PUSH1 0xAA  PUSH1 0x00  MSTORE
% → write(0, 0xAA, empty)

PUSH1 0xBB  PUSH1 0x01  MSTORE
% → write(1, 0xBB, write(0, 0xAA, empty))

PUSH1 0x00  MLOAD   % read bytes [0..31]
% → byte 0: from write(0, 0xAA) — byte 0 of big-endian 0xAA
% → bytes 1..31: from write(1, 0xBB) — overwrites write(0) at those positions
% FFI reconstructs 32-byte value byte-by-byte, most recent write wins
```

#### Read Algorithm (FFI `mem_read`)

```
mem_read(offset, log):
  result = [0] * 32          // zero-initialized
  covered = [false] * 32     // which bytes resolved
  ptr = log
  while ptr ≠ empty_mem:
    match ptr:
      write(wo, wv, inner):
        for each byte position b in [0..31]:
          if covered[b]: continue
          target_addr = offset + b
          if wo ≤ target_addr < wo + 32:      // write covers this byte
            result[b] = byte_of(wv, target_addr - wo)
            covered[b] = true
        ptr = inner
      write8(wo, wb, inner):
        b = wo - offset
        if 0 ≤ b < 32 and not covered[b]:
          result[b] = wb
          covered[b] = true
        ptr = inner
  return big_endian_word(result)
```

**Complexity**: O(W * 32) where W = writes in chain. With early termination when all 32 bytes covered: typically O(1) for exact-match reads, O(W) worst case for heavily overlapping patterns.

**Optimization**: if offset is concrete and exactly matches a write offset with no intervening overlap, return immediately (O(1)).

#### Properties

| Property | Value |
|----------|-------|
| Linear facts | 1 (`mem M`) |
| Write cost | O(1) — prepend to chain |
| Read cost (aligned, exact match) | O(1) |
| Read cost (overlapping) | O(W * 32) |
| Undo in symexec | Restore single `mem` hash |
| Content-addressed sharing | Same write sequence = same hash across branches |
| Engine changes required | None (standard linear fact + FFI) |
| Symbolic offset support | Future (return abstract term) |

### Option B: Per-Cell Linear Facts

One linear fact per memory cell at some granularity.

**Word granularity**: `mem32 Offset Value` — one fact per 32-byte word.

```
evm/mstore:
  ... stack (s SH) Offset * stack SH Value *
  mem32 Offset Old
  -o {
    mem32 Offset Value * ...
  }.
```

**Problem 1 — First write**: No `mem32 Offset Old` exists for unwritten locations. Need either (a) pre-populate all offsets with zero (impractical — infinite), (b) two rules: `mstore_init` (no existing fact) + `mstore_update` (overwrite), or (c) negation-as-failure guard.

**Problem 2 — Non-aligned access**: MSTORE(1, V) writes bytes [1..32], spanning the word at offset 0 and offset 32. Must split into two partial updates: read word at 0, modify bytes [1..31], write back; read word at 32, modify byte [32], write back. This requires reading two facts, modifying, writing two facts. The rule becomes complex and the matching requires two separate memory facts.

**Problem 3 — Matching complexity**: Forward engine scans all `mem32` facts by predicate. With N active memory cells, each MLOAD/MSTORE rule match is O(N). Needs secondary indexing by offset.

**Byte granularity**: `mem1 Addr Byte` — one fact per byte.

```
evm/mstore:
  ... mem1 (Offset+0) _ * mem1 (Offset+1) _ * ... * mem1 (Offset+31) _
  -o {
    mem1 (Offset+0) byte0(Value) * ... * mem1 (Offset+31) byte31(Value) * ...
  }.
```

**Problem**: 32 linear pattern matches per MLOAD/MSTORE. 32 consumed + 32 produced per operation. Forward engine does 32× matching work. For 100 MSTOREs: 3200 facts in state.

#### Properties

| Property | Word granularity | Byte granularity |
|----------|-----------------|-----------------|
| Linear facts | N (one per written word) | N (one per written byte) |
| Write cost | O(N) matching | O(32*N) matching |
| Non-aligned access | Complex rule splitting | Natural |
| First-write problem | Needs two rules or guard | Needs two rules or guard |
| Engine changes | Secondary index on offset | Secondary index on addr |
| Symexec branching risk | 2× per first-write if two rules | Same |

### Option C: Generation Counters

```
!mem Offset Gen Value    % Persistent — all versions accumulate
memgen G                 % Linear — current generation (monotonic)
```

MSTORE increments gen and adds a new persistent fact. MLOAD queries for the latest gen at an offset.

**Problem 1**: Persistent facts cannot be retracted. All historical values accumulate. After 100 MSTOREs, 100 persistent memory facts exist. MLOAD must find the one with maximum gen for the target offset — requires FFI or backward chaining with ordering.

**Problem 2**: In symexec, different branches have different `memgen` values but share the persistent fact set. Branch A writes `!mem 0 gen5 0xAA`, branch B writes `!mem 0 gen5 0xBB` — collision. Persistent facts are branch-global in current symexec, not branch-local.

**Problem 3**: No way to "uncommit" persistent facts on symexec backtrack. The `undoMutate` log supports `TYPE=1` (persistent fact added) by removing it, but this contradicts the "persistent = never removed" semantics.

**Verdict**: Fundamentally incompatible with symexec's mutation/undo model.

### Option D: FFI Side-Effect Map

Memory lives entirely in a JavaScript `Map` on the state object. FFI predicates read/write it.

```javascript
state.memory = new Map();  // offset → Uint8Array (or BigInt)
```

**MSTORE**: FFI mutates `state.memory.set(offset, value)`.
**MLOAD**: FFI queries `state.memory.get(offset)` or returns 0.

**Problem 1 — Breaks proof terms**: No linear logic witness for memory operations. Memory changes are invisible to the proof tree. This undermines CALC's core value proposition (proofs as certificates).

**Problem 2 — Symexec undo**: `undoMutate` must save/restore the Map. Need a separate undo log for memory. Map deep-copy on each branch = O(N) per branch.

**Problem 3 — No symbolic reasoning**: If offset is a metavariable, FFI can't compute. No path forward to symbolic memory analysis.

**When it makes sense**: As an internal optimization behind Option A. The write-log term is the "official" representation; an FFI cache (`state._memCache`) accelerates concrete lookups.

### Option E: Persistent Map with Versioning (Functional Map)

Memory as a **persistent** (immutable, structural-sharing) data structure in the Store.

```
mem: bin -> type.
% Where the term is a hash-consed balanced tree / HAMT
```

Write produces a new root; old root still accessible. Like Clojure's persistent vectors or Ethereum's Merkle-Patricia trie.

**Problem**: The content-addressed Store doesn't support efficient tree structures natively. Would need to implement a persistent map inside the Store — significant complexity. Essentially reimplementing hevm's approach inside CALC's term language.

**When it makes sense**: If read performance on large memories becomes critical. The write-log's O(W) reads are fine for <1000 writes. For contracts with 10K+ memory operations, a persistent map would give O(log N) reads.

## Comparison Matrix

| | A: Write-Log | B: Per-Cell | C: Gen Counters | D: FFI Map | E: Persistent Map |
|---|---|---|---|---|---|
| **ILL semantics** | Clean | Clean | Broken (symexec) | None | Clean |
| **Engine changes** | None | Index needed | N/A | Undo log | Store extension |
| **Write cost** | O(1) | O(N) match | O(1) | O(1) | O(log N) |
| **Read cost** | O(W) | O(N) match | O(W) + ordering | O(1) | O(log N) |
| **Symexec undo** | 1 fact | N facts | Broken | Map copy | 1 fact |
| **Non-aligned** | FFI handles | Complex | FFI handles | FFI handles | FFI handles |
| **Zero-init** | FFI default | Two rules | FFI default | Map default | FFI default |
| **Symbolic offsets** | Future (abstract term) | Matching fails | N/A | Impossible | Future |
| **Content sharing** | Same writes = same hash | Per-fact | N/A | N/A | Same structure = same hash |
| **Complexity** | ~150 LOC FFI | ~50 LOC rules + engine | N/A | ~50 LOC FFI | ~500 LOC Store |
| **First-write** | No problem | Branching risk | No problem | No problem | No problem |

## Recommendation: Option A (Write-Log Term)

**Rationale**:

1. **Zero engine changes** — standard linear fact + persistent FFI predicates. No new indexing, no new matching strategies. The forward engine sees `mem M` as one more linear fact.

2. **Clean undo** — symexec restores a single hash. Current `undoMutate` already handles this.

3. **Content-addressed sharing** — identical write sequences across symexec branches share the same Store hash. Reduces memory and improves cycle detection.

4. **Separation of concerns** — ILL rules express control flow (which opcode fires, what stack effects occur). FFI handles byte-level reconstruction (overlap detection, big-endian encoding). Each layer does one thing.

5. **No first-write problem** — `empty_mem` is the initial state. FFI returns 0 for unwritten offsets.

6. **Path to symbolic** — when THY_0009 (symbolic arithmetic) is implemented, `mem_read` can return abstract `ReadWord(sym_offset, mem)` terms instead of failing on symbolic offsets.

7. **Suckless** — minimal code, no special cases, composes with existing machinery.

**Trade-off**: O(W) reads for W writes in the chain. Acceptable for typical contracts (W < 1000). Mitigations: (a) early termination when all 32 bytes covered, (b) exact-match fast path, (c) optional FFI cache for repeated reads at same offset.

## Implementation Plan

### TODO_0049.Stage_1 — Core FFI (mem_write, mem_read)

Register three new predicate tags: `write`, `write8`, `empty_mem`.

**`lib/engine/ffi/memory.js`** (~120 LOC):

```javascript
// mem_write(offset, value, oldMem, newMem) — mode: + + + -
//   newMem = Store.put({tag:'write', children:[offset, value, oldMem]})

// mem_write8(offset, byte, oldMem, newMem) — mode: + + + -
//   newMem = Store.put({tag:'write8', children:[offset, byte, oldMem]})

// mem_read(offset, memTerm, value) — mode: + + -
//   Traverse write chain, reconstruct 32-byte value, handle overlaps.
//   Return 0 for unwritten bytes.

// mem_size(memTerm, size) — mode: + -
//   Traverse chain, find max(offset + write_size). For MSIZE opcode.
```

Register in `lib/engine/ffi/index.js`:
```javascript
mem_write:  { ffi: 'memory.mem_write',  mode: '+ + + -' },
mem_write8: { ffi: 'memory.mem_write8', mode: '+ + + -' },
mem_read:   { ffi: 'memory.mem_read',   mode: '+ + -' },
mem_size:   { ffi: 'memory.mem_size',   mode: '+ -' },
```

### TODO_0049.Stage_2 — EVM Rules (MLOAD, MSTORE, MSTORE8, MSIZE)

Add to `evm.ill`:

```
% Memory types
mem: bin -> type.

% MLOAD (0x51): read 32 bytes at offset
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) * stack SH Offset *
  mem M
  -o {
    exists V. (
      code PC 0x51 * pc PC' *
      mem M * sh (s SH) * stack SH V *
      !mem_read Offset M V)
  }.

% MSTORE (0x52): write 32-byte word at offset
evm/mstore:
  pc PC * code PC 0x52 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M
  -o {
    exists M'. (
      code PC 0x52 * pc PC' *
      sh SH * mem M' *
      !mem_write Offset Value M M')
  }.

% MSTORE8 (0x53): write 1 byte at offset
evm/mstore8:
  pc PC * code PC 0x53 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M
  -o {
    exists M'. (
      code PC 0x53 * pc PC' *
      sh SH * mem M' *
      !mem_write8 Offset Value M M')
  }.

% MSIZE (0x59): current memory size in bytes (rounded up to 32)
evm/msize:
  pc PC * code PC 0x59 * !inc PC PC' *
  sh SH * mem M
  -o {
    exists S. (
      code PC 0x59 * pc PC' *
      mem M * sh (s SH) * stack SH S *
      !mem_size M S)
  }.
```

Initial state in query files: `mem empty_mem *`

### TODO_0049.Stage_3 — Migrate SHA3 and CALLDATACOPY

Replace the current `concatMemory`/`unblockConcatMemory` blocking pattern with direct FFI:

```
% SHA3: hash memory range [Offset, Offset+Size)
sha3_mem: bin -> bin -> bin -> bin -> type.  % FFI: sha3_mem Offset Size Mem Result

evm/sha3:
  pc PC * code PC 0x20 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) Offset * stack SH Size *
  mem M
  -o {
    exists V. (
      code PC 0x20 * pc PC' *
      mem M * sh (s SH) * stack SH V *
      !sha3_mem Offset Size M V)
  }.
```

FFI `sha3_mem` reads bytes `[Offset, Offset+Size)` from the write-log and either:
- Computes concrete keccak256 if all bytes are ground
- Returns symbolic `sha3(bytes)` term if any byte is symbolic

Similarly, CALLDATACOPY writes calldata bytes into the memory log:

```
calldatacopy_mem: bin -> bin -> bin -> bin -> bin -> bin -> type.
% FFI: calldatacopy_mem MemStart DataStart Length CalldataTerm OldMem NewMem

evm/calldatacopy:
  pc PC * code PC 0x37 * !inc PC PC' *
  sh (s (s (s SH))) *
  stack (s (s SH)) MemStart *
  stack (s SH) DataStart *
  stack SH Length *
  mem M * calldata_blob CD
  -o {
    exists M'. (
      code PC 0x37 * pc PC' *
      sh SH * mem M' * calldata_blob CD *
      !calldatacopy_mem MemStart DataStart Length CD M M')
  }.
```

This eliminates the iterative `concatMemory` loop and the loli-blocking pattern entirely. Each memory-touching opcode becomes a single rule + FFI call.

### TODO_0049.Stage_4 — Tests

```
tests/engine/memory.test.js:
  - MSTORE then MLOAD at same offset → correct value
  - MSTORE then MLOAD at different offset → 0
  - Two MSTOREs then MLOAD → latest value wins
  - Non-aligned overlap: MSTORE(0, X), MSTORE(1, Y), MLOAD(0) → correct merge
  - MSTORE8 then MLOAD → byte placed correctly
  - Zero initialization: MLOAD without prior MSTORE → 0
  - MSIZE after expansion
  - SHA3 via mem_read (replaces concatMemory tests)
  - Symexec with memory: branching preserves/restores mem correctly
```

### TODO_0049.Stage_5 — Benchmark (solc contract)

After memory works, compile a simple Solidity contract with `solc --bin`:

```solidity
contract Simple {
    function add(uint a, uint b) public pure returns (uint) {
        return a + b;
    }
}
```

This uses MLOAD/MSTORE for ABI decoding. Run through CALC symexec and compare with hevm.

## Edge Cases

### Non-Aligned Overlapping Writes

```
MSTORE(0, 0xAAAA...AA)   → 32 bytes of 0xAA at [0..31]
MSTORE(16, 0xBBBB...BB)  → 32 bytes of 0xBB at [16..47]
MLOAD(0) → bytes [0..15] from first write, bytes [16..31] from second write
```

The read algorithm handles this: traverse from newest write, fill bytes, most recent write wins for each byte position.

### MSTORE8 + MLOAD Interaction

```
MSTORE(0, 0)              → 32 zero bytes at [0..31]
MSTORE8(31, 0xFF)         → byte 0xFF at [31]
MLOAD(0) → 0x00...00FF    → 255
```

Write chain: `write8(31, 0xFF, write(0, 0, empty_mem))`. Read traverses: byte 31 covered by `write8`, bytes [0..30] covered by `write(0, 0, ...)`.

### Symbolic Offsets

When `Offset` is a metavariable (not ground):

- **Stage 1 (current plan)**: `mem_read` returns `{success: false, reason: 'symbolic_offset'}`. The forward rule fails to fire. Symexec records a stuck leaf. This is the halmos approach — practical for solc code where offsets are almost always concrete.

- **Stage 2 (future, connects to THY_0009)**: Return an abstract `ReadWord(sym_offset, mem_snapshot)` term as the value. The term is content-addressed and can participate in later equality/inequality reasoning. This is the hevm approach.

- **Stage 3 (future, connects to RES_0049)**: Fork on possible concrete values via constraint analysis. Only viable with a constraint propagation system.

### Memory Across CALL Frames

Each CALL creates fresh memory. With write-log:

```
% Before CALL:
%   mem M_caller

% CALL fires:
%   consume: mem M_caller
%   produce: mem empty_mem * saved_mem M_caller

% Callee executes with fresh memory...

% RETURN fires:
%   consume: mem M_callee * saved_mem M_caller
%   produce: mem M_caller * returndata (extract M_callee ret_offset ret_size)
```

The caller's memory is preserved as a linear `saved_mem` fact, restored on return. Clean and compositional.

## Performance Analysis

### Write Performance

O(1) — one `Store.put` to create a `write` node. The content-addressed Store deduplicates identical writes automatically.

### Read Performance

| Scenario | Cost | Typical for solc |
|----------|------|-----------------|
| Exact aligned match (most common) | O(1) per match + O(W) chain traversal worst case | Yes — free memory pointer at 0x40, ABI slots |
| Non-overlapping different offset | O(W) traversal to not-found, then zero | Rare |
| Overlapping writes | O(W * 32) byte reconstruction | Very rare |
| All 32 bytes covered early | O(K) where K = writes until coverage | Common |

**Typical solc pattern**: 5-20 memory operations per function. Write-log length W ≈ 5-20. Read cost ≈ O(5-20) traversal steps. At ~50ns per Store.get, this is ~250ns-1μs per MLOAD. Negligible compared to rule matching (~10μs).

### State Size

One `mem` fact in `state.linear` regardless of memory size. No memory-proportional state growth. Write-log nodes accumulate in Store but are content-addressed (shared across branches).

### Symexec Branching

**Zero spurious branches from memory operations.** Each MLOAD/MSTORE fires exactly one rule (the `evm/mload` or `evm/mstore` rule). No two-rule ambiguity, no negation-as-failure needed.

Compare with Option B (per-cell): `mstore_init` + `mstore_update` = 2 rules per MSTORE = potential 2^N branching in symexec for N MSTOREs.

### Scalability

- **1K writes** (medium contract): O(1K) reads worst case, ~50μs per MLOAD. Fine.
- **10K writes** (complex contract): O(10K) reads = ~500μs per MLOAD. Might need optimization.
- **Optimization path**: periodic "compaction" — flatten concrete portions of the write-log to a `ConcreteBuf` node. FFI reads a `ConcreteBuf` in O(1) via direct byte access. This is exactly hevm's `simplifyReads` strategy.

## Connections to Theory

### Separation Logic Correspondence (RES_0061 §9)

| CALC | Separation Logic | Meaning |
|------|-----------------|---------|
| `mem M₁ ⊗ mem M₂` | Not possible — single `mem` | Memory is one resource, not split |
| `mem M ⊸ mem M'` | `{P} MSTORE {Q}` | Memory update as linear transformation |
| `mem M ⊗ stack N V` | `M * (N ↦ V)` | Memory and stack are disjoint resources |
| Content-addressed hash | Heap fingerprint | O(1) state equality |

### Linear Logic Advantage (vs hevm/halmos)

All other tools struggle with memory aliasing: "does symbolic address A refer to the same cell as symbolic address B?" This requires SMT reasoning (Z3 array theory or bitvector theory).

CALC's linear fact `mem M` exists exactly once. There is no aliasing — the write-log is a totally-ordered sequence of writes. The only question is "which write covers this byte?", which is a local traversal, not a global constraint.

**This is the theoretical core of why CALC's approach is sound**: linear logic's no-contraction rule means each memory cell is unique by construction. Separation logic's separating conjunction `*` = tensor `⊗` gives disjointness for free. See RES_0061 §12.

### Proof Terms

Each memory operation produces a proof term via the forward engine's derivation tree:

```
evm/mstore @ step 5:
  consumed: [mem(write(0, 0xAA, empty)), stack(1, 0), stack(0, 0xAA), ...]
  produced: [mem(write(0, 0xAA, write(0, 0xAA, empty))), ...]
```

This is a verifiable certificate: L1 kernel can check that the memory transformation was valid by replaying the FFI computation. The write-log term IS the proof witness for the memory state.

## Open Questions

1. **Tag registration**: Should `write`, `write8`, `empty_mem` be pre-registered tags (below `PRED_BOUNDARY`) or dynamic predicates? Pre-registered = faster matching; dynamic = cleaner separation. Recommendation: dynamic (they're only used inside `mem` terms, never as standalone predicates).

2. **Compaction strategy**: When to flatten the write-log? Options: (a) never (simplest), (b) after N writes (periodic), (c) on read miss (lazy). Start with (a), measure, add (b) if needed.

3. **Gas for memory expansion**: Track `msize` as a separate linear fact `memsize S`? Or compute dynamically from the write-log? Separate fact is cleaner — `mem_write` FFI also updates `memsize` if offset+32 exceeds current size.

4. **MCOPY (EIP-5656)**: `copy(dst, src, len)` node in write-log. FFI `mem_read` resolves `copy` nodes by reading from the source region. Straightforward extension.

5. **RETURNDATASIZE / RETURNDATACOPY**: Return data from CALL is a separate buffer, not part of `mem`. Model as `returndata RD` linear fact with similar write-log structure.
