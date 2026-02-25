---
title: EVM Memory Model Design
created: 2026-02-24
modified: 2026-02-25
summary: Design MLOAD/MSTORE memory model for CALC's EVM symbolic executor
tags: [evm, memory, architecture, linear-logic, separation-logic]
type: design
status: researching
priority: 6
cluster: Symexec
depends_on: []
required_by: []
starred: true
---

# EVM Memory Model Design

## Problem

Every solc-compiled contract uses MLOAD/MSTORE extensively (ABI encoding, scratch space, free memory pointer at `0x40`). Without memory support, CALC can only run hand-crafted bytecode. MLOAD (0x51) and MSTORE (0x52) are the blocking opcodes for all future benchmarks against hevm/halmos/KEVM.

## EVM Memory Semantics

From the Yellow Paper:

- **Byte-addressable**: each address indexes one byte
- **MLOAD(offset)**: reads 32 bytes at `[offset, offset+32)`, returns 256-bit big-endian word
- **MSTORE(offset, value)**: writes 32-byte big-endian encoding of `value` at `[offset, offset+32)`
- **MSTORE8(offset, value)**: writes `value mod 256` (1 byte) at `[offset]`
- **Zero-initialized**: unwritten bytes are 0
- **Per call frame**: fresh memory for each CALL; caller memory restored on return
- **Dynamic expansion**: accessing offset `n` grows memory to `ceil((n+32)/32)` words
- **Gas**: `cost = words²/512 + 3*words` — quadratic for large memory
- **Non-aligned access**: MLOAD/MSTORE at ANY byte offset (not just multiples of 32)

Non-aligned access means MSTORE(0, X) then MSTORE(1, Y) produces an overlap at bytes [1..31]. MLOAD(0) must reconstruct from both writes.

## Current State in CALC

`evm.ill:90` declares `memory: bin -> bin -> bin -> type.` — a **linear** ternary predicate `memory Pos Size V`. Used by:

1. **concatMemory** (lines 388-403): iterates over `memory` facts via recursive forward rules, concatenating values. Consumes each `memory Pos Size V` and re-produces it (preserve-on-read). Driven by `!neq` guard and `!plus` increment.

2. **SHA3** (lines 405-423): triggers `concatMemory` with a loli continuation (`unblockConcatMemory Z -o {...}`). The continuation fires when traversal completes, passing concatenated bytes as `sha3 Z`.

3. **CALLDATACOPY** (lines 577-612): produces `memory Ms Size D` facts from `calldata` facts. Uses blocking pattern (`unblock -o {pc PC'}`).

**Key observation**: concatMemory already IS a rule-based write-chain traversal — recursive forward rules that walk a data structure, gated by a loli continuation. The memory model follows the same pattern.

## How Other Tools Model Memory

See RES_0061 for full survey, RES_0062 for data structures, RES_0063 for engine internals.

| Tool | Representation | Symbolic offsets | Read-after-write |
|------|---------------|-----------------|-----------------|
| **hevm** | Algebraic write-chain (`WriteWord o v buf`) | Abstract `ReadWord` term → SMT | Pattern match on offsets; byte-by-byte for overlap |
| **KEVM** | K `Bytes` cell; rewrite rules | Transparent via matching logic | Implicit (single mutable cell) |
| **halmos** | `ByteVec` (concrete/symbolic chunks) | Require concrete; fork if symbolic | Chunk iteration |
| **Mythril** | Z3 `Array(BV256, BV8)` | Z3 `select` | SMT array theory |
| **Manticore** | SMT constraint arrays | Fork on concrete values | SMT constraint propagation |

## Design: Write-Log with Rule-Based Traversal

Single linear fact `mem M` where `M` is a content-addressed write-log term. MSTORE wraps a `write` constructor (O(1)). MLOAD fires a recursive rule traversal via loli continuation — the same established pattern as SHA3/concatMemory.

CALC's forward rules ARE the semantics. Existing FFI-accelerated predicates (`!neq`, `!plus`, `!inc`, `!mul`) have clean ILL clause definitions — the FFI is an optimization layer, not the definition. The read traversal is forward rules encoding McCarthy's array axioms directly in ILL. **The rules define the semantics; FFI may accelerate later.**

### Type Declarations

```
mem: bin -> type.
mem_reading: bin -> bin -> bin -> type.   % mem_reading Offset CurrentTerm OrigMem
mem_read_done: bin -> type.               % mem_read_done Value (triggers loli)
write: bin -> bin -> bin -> bin.           % write(offset, value, prev)
write8: bin -> bin -> bin -> bin.          % write8(addr, byte, prev)
empty_mem: bin.
```

### MSTORE — O(1), one rule

```
evm/mstore:
  pc PC * code PC 0x52 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M
  -o {
    code PC 0x52 * pc PC' * sh SH *
    mem (write Offset Value M)
  }.
```

Just wraps a `write` constructor. Content-addressed: same write sequence = same hash across symexec branches.

### MLOAD — loli continuation + recursive traversal

```
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) * stack SH Offset *
  mem M
  -o {
    code PC 0x51 *
    mem_reading Offset M M *
    (mem_read_done V -o {
      pc PC' * sh (s SH) * stack SH V * mem M
    })
  }.
```

Key design: `pc PC'` is NOT produced yet — it's captured in the loli. No opcode rule can fire during traversal (they all need `pc`). Only `mem_read/*` rules match.

### Traversal Rules — McCarthy's Axioms as ILL

```
% Axiom 1: select(store(a, i, v), i) = v
mem_read/hit:
  mem_reading Offset (write Offset V Rest) OrigMem
  -o { mem_read_done V }.

% Axiom 2: i ≠ j ⟹ select(store(a, i, v), j) = select(a, j)
mem_read/miss:
  mem_reading Offset (write Other V Rest) OrigMem *
  !neq Offset Other
  -o { mem_reading Offset Rest OrigMem }.

% Zero-initialization: select(empty, i) = 0
mem_read/zero:
  mem_reading Offset empty_mem OrigMem
  -o { mem_read_done 0 }.
```

**These three rules ARE the array theory.** No FFI, no engine changes. Just the axioms expressed as ILL forward rules.

### How Unification Handles This

`mem_read/hit` has pattern `mem_reading Offset (write Offset V Rest) OrigMem`. Against a state fact like `mem_reading(0x40, write(0x40, 0x42, empty_mem), full_mem)`:

1. Top-level: tag `mem_reading`, arity 3 — match
2. Child 0: `Offset` binds to `0x40`
3. Child 1: unify with `write(Offset, V, Rest)` — tag `write`, arity 3, decompose:
   - `Offset` (already bound to `0x40`) vs `0x40` → equal ✓
   - `V` binds to `0x42`
   - `Rest` binds to `empty_mem`
4. Child 2: `OrigMem` binds to `full_mem`

Standard structural unification on content-addressed terms (`unify.js:322-335`). No extensions needed.

### Mutual Exclusion — No Spurious Branching

At each traversal step, exactly one of {hit, miss, zero} can fire:

- **hit**: unification succeeds iff outermost write offset = read offset (same metavar `Offset` appears in both positions — non-linear pattern, checked by unification)
- **miss**: unification succeeds for any `write` node, but `!neq Offset Other` fails when offsets are equal (because `Other` binds to the same value as `Offset`)
- **zero**: only matches `empty_mem` (different tag than `write` — structural mismatch excludes hit/miss)

In symexec, `findAllMatches` tries all three rules but only one succeeds per state. Zero spurious branches.

### Worked Example

```
% Initial: mem empty_mem * pc 0 * ... (some bytecode)

Step 1: PUSH1 0x42 → stack 0 0x42
Step 2: PUSH1 0x00 → stack 1 0x00
Step 3: MSTORE → mem (write 0x00 0x42 empty_mem)

Step 4: PUSH1 0xBB → stack 0 0xBB
Step 5: PUSH1 0x20 → stack 1 0x20
Step 6: MSTORE → mem (write 0x20 0xBB (write 0x00 0x42 empty_mem))

Step 7: PUSH1 0x00 → stack 0 0x00
Step 8: MLOAD fires:
  consumes: mem (write 0x20 0xBB (write 0x00 0x42 empty_mem)), stack 0 0x00
  produces: mem_reading 0x00 (write 0x20 0xBB ...) (write 0x20 0xBB ...)
            loli: (mem_read_done V -o { pc PC' * sh (s SH) * stack SH V * mem (write 0x20 ...) })

Step 9: mem_read/miss fires (0x00 ≠ 0x20):
  consumes: mem_reading 0x00 (write 0x20 0xBB (write 0x00 0x42 empty_mem)) OrigMem
  produces: mem_reading 0x00 (write 0x00 0x42 empty_mem) OrigMem

Step 10: mem_read/hit fires (0x00 = 0x00):
  consumes: mem_reading 0x00 (write 0x00 0x42 empty_mem) OrigMem
  produces: mem_read_done 0x42

Step 11: loli fires:
  consumes: mem_read_done 0x42
  produces: pc PC' * sh (s SH) * stack SH 0x42 * mem (write 0x20 0xBB (write 0x00 0x42 empty_mem))
```

3 traversal steps for W=2 writes. Original memory restored via loli. Opcode dispatch resumes.

### MSTORE8

```
evm/mstore8:
  pc PC * code PC 0x53 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M
  -o {
    exists Byte. (
      code PC 0x53 * pc PC' * sh SH *
      mem (write8 Offset Byte M) *
      !mod Value 0x100 Byte)
  }.
```

Additional traversal rule for `write8` nodes (skipped during word-level reads):

```
mem_read/skip8:
  mem_reading Offset (write8 Addr Byte Rest) OrigMem
  -o { mem_reading Offset Rest OrigMem }.
```

## Concrete/Symbolic Value Mixing

Offsets and values are independently concrete or symbolic in the write-log. Every combination works:

| Read offset | Write offset | Write value | Behavior |
|-------------|-------------|-------------|----------|
| Concrete | Concrete | Concrete | Normal traversal, concrete result |
| Concrete | Concrete | Symbolic | `hit` returns symbolic value as-is |
| Concrete | Symbolic | Any | Stuck leaf (can't determine alias) |
| Symbolic expr | Concrete | Any | Stuck leaf (can't determine alias) |
| Free metavar | Concrete | Any | Binds metavar — fork on possible values |

**Symbolic values flow through unchanged.** `write(0x40, calldataload(4), M)` then MLOAD(0x40): `hit` fires, returns `calldataload(4)` as an opaque term on the stack. The symbolic value is just a content-addressed term — unification doesn't care whether it's concrete or symbolic.

**Mixed chains work naturally.** Consider:

```
mem = write(0x40, sym_V, write(sym_off, 0xBEEF, empty_mem))

MLOAD(0x40):
  Step 1: hit at write(0x40, sym_V, ...) → mem_read_done sym_V ✓

MLOAD(0x20):
  Step 1: miss at write(0x40, ...) — 0x20 ≠ 0x40 ✓
  Step 2: at write(sym_off, 0xBEEF, ...) — neq(0x20, sym_off) non-ground → stuck ✓
```

The concrete write at 0x40 resolves normally. The symbolic write at `sym_off` blocks traversal — sound because we can't know if `sym_off == 0x20`.

## Performance

### Cost per MLOAD

Each MLOAD takes **W forward steps** where W = writes in the chain. Each step = one `findAllMatches` + one `applyMatch`.

| W (writes) | Steps per MLOAD | At ~10μs/step | Context |
|-----------|----------------|---------------|---------|
| 1 | 2 (miss/zero or hit) | ~20μs | Free memory pointer read (`0x40`) — most common solc MLOAD |
| 5-10 | 6-11 | 50-110μs | Simple function |
| 20-50 | 21-51 | 200-510μs | Medium contract |
| 100-500 | 101-501 | 1-5ms | Heavy contract |
| 1000+ | 1001+ | 10ms+ | Pathological (needs FFI fast-path) |

### State Size

One `mem` fact in `state.linear` regardless of memory size. Write-log nodes accumulate in Store but are content-addressed (shared across branches).

### Symexec Tree Impact

Each MLOAD adds W intermediate `mem_reading` nodes. These are linear chains (no branching). For a contract with R reads and average chain length W:

- Additional nodes: R × W
- Additional branching: 0

For a contract with 20 MLOADs and W=10: 200 extra nodes. On a tree of ~200 nodes (current multisig), this roughly doubles the tree size but adds zero branches.

## Byte-Addressable Overlap Handling

The aligned word-level McCarthy rules cover ~99% of solc-compiled code. But EVM memory is byte-addressable: MSTORE writes 32 bytes at `[offset, offset+32)`, and nothing prevents overlapping writes at arbitrary byte offsets.

### The Problem

```
Step 1: MSTORE(0, 0xAAAA...AA)    → writes 32 bytes at [0, 32)
Step 2: MSTORE(16, 0xBBBB...BB)   → writes 32 bytes at [16, 48)
Step 3: MLOAD(0)                   → reads 32 bytes at [0, 32)
```

MLOAD(0) should return `bytes [0..15] from AA ++ bytes [0..15] from BB`. But `mem_read/hit` at `write(0, AA, ...)` returns the full `AA` value — wrong, because the second write overwrote bytes [16..31].

McCarthy's axioms model word-addressable arrays (writes are atomic at a single index). EVM MSTORE writes a 32-byte window that can partially overlap with other windows.

Three alternative approaches were investigated and rejected (see RES_0062):

- **Per-Byte Decomposition**: 32× chain blowup — 1M rule steps at 1000 MSTOREs. Structurally incompatible with linked-list write-log.
- **Non-Overlapping Interval Tree**: Breaks content-addressed sharing (order-dependent tree shape). Requires heavy FFI. Symbolic offsets fail completely.
- **Region Splitting**: Requires bytecode static analysis CALC doesn't have. Solidity-specific.

### Overlap-Aware Read Rules

Extend the traversal with overlap detection. Replace `!neq` with `!no_overlap` (disjoint ranges) and add `!overlaps` (partial coverage). Collect overlapping writes as `mem_patch` facts during traversal, assemble via `splice` at the end.

```
% 1. Exact hit (same offset): return full value
mem_read/hit:
  mem_reading Offset (write Offset V Rest) OrigMem
  -o { mem_base_found Offset V }.

% 2. Clean miss (no overlap): skip
mem_read/miss:
  mem_reading R (write W V Rest) OrigMem *
  !neq R W *
  !no_overlap R 32 W 32       % [R,R+32) ∩ [W,W+32) = ∅
  -o { mem_reading R Rest OrigMem }.

% 3. Partial overlap: record patch, continue
mem_read/partial:
  mem_reading R (write W V Rest) OrigMem *
  !neq R W *
  !overlaps R 32 W 32          % [R,R+32) ∩ [W,W+32) ≠ ∅
  -o {
    mem_reading R Rest OrigMem *
    mem_patch R W V
  }.

% 4. Zero (end of chain)
mem_read/zero:
  mem_reading Offset empty_mem OrigMem
  -o { mem_base_found Offset 0 }.

% 5. Finalize: no patches → return base directly
mem_finalize/clean:
  mem_base_found Offset V
  -o { mem_read_done V }.

% 6. Finalize: apply patches newest-first
mem_finalize/patch:
  mem_base_found Offset Base *
  mem_patch Offset W PatchV
  -o {
    mem_base_found Offset (splice Base Offset W PatchV)
  }.
```

`splice(Base, ReadOff, WriteOff, WriteVal)` = "take Base as default 32-byte value, overlay bytes from WriteVal at WriteOff for the portion intersecting `[ReadOff, ReadOff+32)`."

For concrete values, `splice` is computed by FFI (byte extraction + concatenation). For symbolic values, it remains as an opaque term capturing the overlap relationship.

### Worked Example (Overlapping)

```
MLOAD(0) after MSTORE(0, 0xAA..AA) + MSTORE(16, 0xBB..BB):

Step 1: partial overlap at W=16 → mem_patch 0 16 0xBB..BB
Step 2: exact hit at W=0 → mem_base_found 0 0xAA..AA
Step 3: patch exists → splice(0xAA..AA, 0, 16, 0xBB..BB)
        = "take 0xAA..AA, overlay bytes [16..31] with bytes [0..15] of 0xBB..BB"
        For concrete: first 16 bytes AA, last 16 bytes BB ✓
```

### Symbolic Overlap Case

```
MSTORE(0, X) + MSTORE(10, Y), then MLOAD(5):

Read range [5, 37). Write at 10 covers [10, 42) — overlaps.
Write at 0 covers [0, 32) — overlaps.

Step 1: partial at W=10 → mem_patch 5 10 Y
Step 2: partial at W=0  → mem_patch 5 0 X
Step 3: zero → mem_base_found 5 0
Step 4: apply patch (W=0, older): splice(0, 5, 0, X)
Step 5: apply patch (W=10, newer): splice(splice(0, 5, 0, X), 5, 10, Y)

Result: nested splice term capturing:
  bytes [5..9] from X, bytes [10..36] from Y, byte 37 = 0
```

For concrete X and Y, the FFI evaluates this to actual bytes. For symbolic X and Y, the term preserves all information.

### FFI Predicates

| Predicate | Semantics | Cost |
|-----------|-----------|------|
| `!no_overlap R Rs W Ws` | `[R,R+Rs) ∩ [W,W+Ws) = ∅` i.e. `R+Rs ≤ W ∨ W+Ws ≤ R` | O(1) |
| `!overlaps R Rs W Ws` | Negation of `!no_overlap` | O(1) |
| `!splice Base R W V Result` | Overlay V@W onto Base@R, produce Result | O(32) bytes |

All pure arithmetic on concrete bigints. No state mutation. `!no_overlap` and `!overlaps` have ILL clause definitions (like `!neq`). `!splice` is irreducibly computational (like `!mul`).

### Performance (Overlap Case)

For aligned solc code: `!no_overlap` passes on every step (all writes are 32-byte aligned at distinct offsets). `mem_read/hit` fires at exact match. **Identical to the base rules.** No patches generated.

For overlapping writes: O(W) traversal + O(k) patch assembly where k = overlapping writes (typically 0-2). The `splice` FFI computes concrete results in O(k × 32) byte operations.

## Variable-Length Writes

EVM MSTORE always writes exactly 32 bytes. But related operations have variable lengths:

- **CALLDATACOPY(destOffset, offset, size)**: copies `size` bytes from calldata to memory
- **CODECOPY(destOffset, offset, size)**: copies `size` bytes from code to memory
- **RETURNDATACOPY(destOffset, offset, size)**: copies `size` bytes from return data
- **MCOPY(dest, src, size)** (EIP-5656): copies `size` bytes within memory

```
% Variable-length write term constructor
vwrite: bin -> bin -> bin -> bin -> bin.   % vwrite(Offset, Size, SourceData, Prev)

% Traversal rules for vwrite nodes
mem_read/vmiss:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !no_overlap R 32 W Ws
  -o { mem_reading R Rest OrigMem }.

mem_read/vpartial:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !overlaps R 32 W Ws
  -o { mem_reading R Rest OrigMem * mem_vpatch R W Ws V }.

mem_read/vhit:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !le W R * !le (plus R 32) (plus W Ws)
  -o { mem_read_done (extract V (minus R W) 32) }.
```

When `Ws` (size) is symbolic, `!no_overlap R 32 W Ws` fails → stuck leaf. Correct: can't determine coverage without knowing the size.

**MCOPY** redirects reads within the log — no data copying:

```
evm/mcopy:
  ... mem M -o { mem (mcopy Dest Src Size M) }.

mem_read/mcopy_redirect:
  mem_reading R (mcopy D S Sz Rest) OrigMem *
  !le D R * !le (plus R 32) (plus D Sz)
  -o { mem_reading (plus S (minus R D)) Rest OrigMem }.
```

A read at `R` in the dest range becomes a read at `S + (R - D)` in the source range, starting from `Rest` (pre-MCOPY state). Pure rules, no FFI.

## SHA3 Migration

Current SHA3 uses `concatMemory` to iterate over `memory Pos Size V` facts. With the write-log, SHA3 reads a byte range:

```
evm/sha3:
  pc PC * code PC 0x20 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) From * stack SH Size *
  mem M
  -o {
    exists To. (
      code PC 0x20 *
      sha3_reading From To M 0 *
      !plus From Size To *
      (sha3_read_done Z -o {
        pc PC' * sh (s SH) * stack SH (sha3 Z) * mem M
      })
    )
  }.
```

Each byte position triggers a sub-traversal of the write-log. O(Size × W) rule steps. For SHA3(64 bytes, W=10): ~640 steps. Expensive but pure.

The hash computation (keccak256) is irreducibly computational — uses opaque `sha3(Z)` term. Keccak256 FFI justified only if concrete hash values are needed (storage slot computation).

## Memory Across CALL Frames

```
% CALL: save caller memory, fresh memory for callee
evm/call:
  ... mem M_caller ...
  -o { mem empty_mem * saved_mem M_caller * ... }.

% RETURN: restore caller memory
evm/return:
  ... mem M_callee * saved_mem M_caller ...
  -o { mem M_caller * ... }.
```

`saved_mem` is a linear fact — consumed exactly once on RETURN. The caller's write-log is preserved as a content-addressed term in the Store.

## Connections to Theory

### McCarthy's Axioms = ILL Forward Rules

| McCarthy Axiom | ILL Rule | Meaning |
|---------------|----------|---------|
| `select(store(a, i, v), i) = v` | `mem_read/hit` | Read what you wrote |
| `i ≠ j ⟹ select(store(a, i, v), j) = select(a, j)` | `mem_read/miss` | Reads at other indices unaffected |
| `select(empty, i) = 0` | `mem_read/zero` | Zero initialization |

The three rules are a direct encoding. No interpretation gap.

### Separation Logic Correspondence

| Linear Logic | Separation Logic | In CALC |
|-------------|-----------------|---------|
| `⊗` (tensor) | `*` (separating conjunction) | `mem M * stack N V` = disjoint resources |
| `⊸` (lollipop) | `-*` (magic wand) | `mem M ⊸ mem (write O V M)` = memory update |
| `1` (unit) | `emp` (empty heap) | `empty_mem` |
| No contraction | Disjointness | Each `mem` fact exists once = no aliasing |

### Linear Logic Advantage Over SMT-Based Tools

hevm/halmos/Mythril/Manticore all struggle with memory aliasing: "does symbolic address A refer to the same cell as B?" This requires SMT reasoning.

CALC's `mem M` exists exactly once (linearity). The write-log is totally ordered. The question "which write covers this byte?" is a local traversal, not a global constraint. Aliasing is impossible by construction — separation logic's frame rule is structural in ILL.

## Implementation Plan

### TODO_0049.Stage_1 — Core Rules (Aligned Access)

Add to `evm.ill`:
- Type declarations: `mem`, `mem_reading`, `mem_read_done`, `write`, `write8`, `empty_mem`
- Rules: `evm/mstore`, `evm/mstore8`, `evm/mload`, `evm/msize`
- Traversal: `mem_read/hit`, `mem_read/miss` (with `!neq`), `mem_read/zero`, `mem_read/skip8`

No FFI. No engine changes. ~30 lines of `.ill` rules. Initial state: `mem empty_mem *`.

Sufficient for all solc-compiled code (aligned 32-byte access).

### TODO_0049.Stage_2 — Migrate SHA3 and CALLDATACOPY

Replace `concatMemory`/`unblockConcatMemory` with write-log-aware range reading. SHA3 iterates byte positions; each triggers a sub-traversal. CALLDATACOPY wraps calldata bytes as `write8` entries in the log (or a single `vwrite` term node).

### TODO_0049.Stage_3 — Tests

```
tests/engine/memory.test.js:
  - MSTORE then MLOAD at same offset → correct value
  - MSTORE then MLOAD at different offset → 0
  - Two MSTOREs then MLOAD → latest value wins
  - MSTORE8 skip during word-level MLOAD
  - Zero initialization: MLOAD without prior MSTORE → 0
  - Symexec branching: memory preserved/restored correctly on backtrack
  - Symbolic offset: MLOAD with symbolic offset → stuck leaf
  - Symbolic value: MLOAD returns symbolic value as-is
  - Mixed chain: concrete + symbolic values in same write-log
  - Loli gating: no opcode fires during mem_read traversal
```

### TODO_0049.Stage_4 — Benchmark (solc contract)

Compile simple Solidity contract with `solc --bin`. Run through CALC symexec. Compare tree size and timing with hevm.

### TODO_0049.Stage_5 — Overlap Detection (if needed)

Replace `!neq` with `!no_overlap` in `mem_read/miss`. Add `mem_read/partial` with `!overlaps`. Add `mem_base_found`/`mem_finalize` patch assembly rules. Add `!splice` FFI. Three new FFI predicates, all pure arithmetic.

Only needed when a real contract requires non-aligned memory access.

### TODO_0049.Stage_6 — FFI Fast-Path (if needed)

If profiling shows memory reads dominate execution time, add FFI `mem_read` that traverses the write-log in JavaScript (O(W) at ~50ns/step instead of ~10μs/step). The rules remain the definition. Analogous to how `!plus` FFI accelerates `plus/z + plus/s`.

### TODO_0049.Stage_7 — Compaction (if needed)

Add `compact(ByteMap, Prev)` term constructor that flattens concrete portions of the chain into a direct-lookup structure. Reads check compact nodes first (O(1)), then scan remaining writes. Compaction traverses newest→oldest, resolves overlaps via most-recent-write-wins per byte. Symbolic writes stay above the compact node. This is hevm's `simplifyReads` strategy expressed as a term constructor.

## Open Questions

1. **Tag registration**: `write`, `write8`, `empty_mem`, `vwrite`, `mcopy`, `splice` should be dynamic predicate tags (above `PRED_BOUNDARY`). Same status as `sha3`, `concat`, `s`, `e`.

2. **Gas for memory expansion**: Track as separate linear `memsize S` fact. MSTORE/MLOAD rules include `!mem_expand` persistent guard that computes new size and gas cost. Orthogonal to memory model.

3. **RETURNDATASIZE / RETURNDATACOPY**: Return data is a separate buffer. Model as `returndata RD` linear fact with similar write-log structure.

4. **Patch ordering**: When multiple patches exist, they must be applied newest-first (most-recent-write-wins). The traversal naturally visits writes newest→oldest, so patches accumulate in the correct order.

5. **`splice` commutativity**: `splice(splice(Base, R, W1, V1), R, W2, V2)` must equal `splice(Base, R, W2, V2)` when W2's range fully covers W1's range within the read window. The FFI must respect this.
