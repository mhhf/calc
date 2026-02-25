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

**Key observation**: concatMemory already IS a rule-based write-chain traversal — recursive forward rules that walk a data structure, gated by a loli continuation. The memory model should follow the same pattern.

## How Other Tools Model Memory

See RES_0061 for full survey. Summary:

| Tool | Representation | Symbolic offsets | Read-after-write |
|------|---------------|-----------------|-----------------|
| **hevm** | Algebraic write-chain (`WriteWord o v buf`) | Abstract `ReadWord` term → SMT | Pattern match on offsets; byte-by-byte for overlap |
| **KEVM** | K `Bytes` cell; rewrite rules | Transparent via matching logic | Implicit (single mutable cell) |
| **halmos** | `ByteVec` (concrete/symbolic chunks) | Require concrete; fork if symbolic | Chunk iteration |
| **Mythril** | Z3 `Array(BV256, BV8)` | Z3 `select` | SMT array theory |
| **Manticore** | SMT constraint arrays | Fork on concrete values | SMT constraint propagation |

## Design Philosophy

CALC's forward rules ARE the semantics. Existing "FFI-accelerated" predicates (`!neq`, `!plus`, `!inc`, `!mul`) have clean ILL clause definitions — the FFI is an optimization layer, not the definition. Memory read/write should follow the same principle: **the rules define the semantics; FFI may accelerate later**.

The write-log idea (single linear `mem M` fact with nested `write` terms) is correct. The key reconsidered insight: **the read traversal should be forward rules, not FFI**. CALC's unification already handles nested term destructuring (`sh (s (s SH))` matches nested `s` constructors). The same mechanism destructures `write(Offset, V, Rest)` — zero new engine machinery needed.

## Design Options

### Option A: Pure ILL Rules with Write-Log (Recommended)

Single linear fact `mem M` where `M` is a content-addressed write-log. MSTORE wraps a `write` constructor (O(1)). MLOAD fires a recursive rule traversal via loli continuation — the same established pattern as SHA3/concatMemory.

#### Type Declarations

```
mem: bin -> type.
mem_reading: bin -> bin -> bin -> type.   % mem_reading Offset CurrentTerm OrigMem
mem_read_done: bin -> type.               % mem_read_done Value (triggers loli)
write: bin -> bin -> bin -> bin.           % write(offset, value, prev)
write8: bin -> bin -> bin -> bin.          % write8(addr, byte, prev)
empty_mem: bin.
```

#### MSTORE — O(1), one rule

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

#### MLOAD — loli continuation + recursive traversal

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

#### Traversal Rules — McCarthy's Axioms as ILL

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

#### How Unification Handles This

`mem_read/hit` has pattern `mem_reading Offset (write Offset V Rest) OrigMem`. Against a state fact like `mem_reading(0x40, write(0x40, 0x42, empty_mem), full_mem)`:

1. Top-level: tag `mem_reading`, arity 3 — match
2. Child 0: `Offset` binds to `0x40`
3. Child 1: unify with `write(Offset, V, Rest)` — tag `write`, arity 3, decompose:
   - `Offset` (already bound to `0x40`) vs `0x40` → equal ✓
   - `V` binds to `0x42`
   - `Rest` binds to `empty_mem`
4. Child 2: `OrigMem` binds to `full_mem`

This is standard structural unification on content-addressed terms (`unify.js:322-335`). No extensions needed.

#### Mutual Exclusion — No Spurious Branching

At each traversal step, exactly one of {hit, miss, zero} can fire:

- **hit**: unification succeeds iff outermost write offset = read offset (same metavar `Offset` appears in both positions — non-linear pattern, checked by unification)
- **miss**: unification succeeds for any `write` node, but `!neq Offset Other` fails when offsets are equal (because `Other` binds to the same value as `Offset`)
- **zero**: only matches `empty_mem` (different tag than `write` — structural mismatch excludes hit/miss)

In symexec, `findAllMatches` tries all three rules but only one succeeds per state. Zero spurious branches.

#### Worked Example

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

#### MSTORE8

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

Additional traversal rule for `write8` nodes (skipped during word-level reads — see Non-Aligned Access below):

```
mem_read/skip8:
  mem_reading Offset (write8 Addr Byte Rest) OrigMem
  -o { mem_reading Offset Rest OrigMem }.
```

This skips `write8` entries during aligned 32-byte reads. Full byte-level reconstruction (where `write8` contributes a single byte to the result) is a Stage 2 extension.

### Option B: Per-Cell Linear Facts

One linear fact per memory cell.

**First-write problem**: No fact exists for unwritten locations. Needs either `mstore_init` + `mstore_update` (two rules → 2^N branching in symexec) or negation-as-failure (not in ILL).

**Matching complexity**: O(N) scan per MLOAD/MSTORE for N active cells. Needs engine-level secondary indexing.

**Non-aligned access**: MSTORE(1, V) spans two word-aligned regions. Requires consuming and splitting two `mem32` facts.

**Verdict**: Correct theory but engineering problems (branching, indexing, first-write) make it impractical without engine extensions.

### Option C: Generation Counters

Persistent `!mem Offset Gen Value` facts with monotonic counter.

**Verdict**: Fundamentally incompatible with symexec's mutation/undo. Persistent facts are branch-global; different branches produce conflicting versions at same gen. See detailed analysis in previous revision.

### Option D: FFI Side-Effect Map

Memory as JavaScript `Map` on state object. FFI mutates it.

**Verdict**: Breaks proof terms (memory invisible to derivation tree). Breaks symexec undo (need separate undo log). No path to symbolic reasoning. Fast but unprincipled — the memory semantics live outside the logic.

### Option E: Write-Log with FFI Traversal

Same write-log term as Option A, but read traversal done in FFI (`mem_read` JavaScript function) instead of forward rules.

**Verdict**: Correct representation but the traversal — which IS McCarthy's array axioms — is hidden in FFI. The axioms should be rules, not code. FFI is justified for irreducibly computational operations (keccak256, bigint arithmetic) but not for axiom application that ILL can express directly. See Design Philosophy above.

**As optimization**: Option E is a valid fast-path for Option A. Like `!plus` has clause definitions (`plus/z`, `plus/s`) but FFI evaluates in O(1). Same principle: define via rules, accelerate via FFI when profiling shows it matters.

## Comparison Matrix

| | A: Pure Rules | B: Per-Cell | C: Gen Counters | D: FFI Map | E: FFI Traversal |
|---|---|---|---|---|---|
| **Theory faithful** | Yes | Yes | No (symexec) | No | Partially |
| **Engine changes** | None | Index needed | N/A | Undo log | None |
| **Write** | O(1) | O(N) match | O(1) | O(1) | O(1) |
| **Read** | O(W) rule steps | O(N) match | Broken | O(1) | O(W) in FFI |
| **No spurious branching** | Yes | No (first-write) | N/A | N/A | Yes |
| **Proof witness** | Every step | Every step | N/A | None | Single step |
| **Symexec undo** | 1 fact | N facts | Broken | Map copy | 1 fact |
| **Symbolic offsets** | Sound stuck | Matching fails | N/A | Impossible | FFI fails |
| **Content sharing** | Yes | Per-fact | N/A | N/A | Yes |
| **New FFI predicates** | 0 | 0 | N/A | 3+ | 3+ |

## Recommendation: Option A (Pure ILL Rules)

The three `mem_read` rules encode McCarthy's select/store axioms directly in ILL. Memory write is a term constructor. Memory read is a recursive rule traversal gated by a loli continuation — the same established pattern as SHA3's `concatMemory`.

**Why this fits CALC's philosophy**:

1. **Rules ARE the semantics** — each traversal step is a valid ILL inference. The execution tree shows how the read resolved, not just the result.

2. **Zero new machinery** — no FFI, no engine changes, no new indexing. Uses only structural unification (already in `unify.js`), `!neq` (already FFI-accelerated), and loli continuations (already used by SHA3/CALLDATACOPY).

3. **Content-addressed sharing** — identical write sequences across branches share the same Store hash. The `mem (write 0x40 0x80 empty_mem)` term for the Solidity free-memory-pointer initialization is created once, shared across all branches.

4. **Sound symbolic behavior** — when offsets are symbolic, the traversal gets stuck (neither hit nor miss can fire). This is the correct approximation: the logic can't determine the read result without knowing the offset.

5. **Optimization path** — if profiling shows reads are slow, add FFI `mem_read` as a fast-path (like `!plus` FFI). The rules remain the definition; the FFI is the acceleration. No theory change needed.

## Symbolic Computation Analysis

### Concrete Offsets (typical solc code)

All offsets are ground `binlit` values. Unification resolves hit/miss deterministically. `!neq` evaluates in O(1) via FFI. Each MLOAD takes W forward steps.

### Symbolic MSTORE Offset

`write(sym_offset, V, M)` wraps fine — the symbolic offset is just a term in the write-log. O(1). No issue.

### Concrete Read, Symbolic Write in Chain

Reading at `0x40`, chain has `write(calldataload(4), V, ...)`:

- `mem_read/hit`: unify `0x40 ?= calldataload(4)`. Different tags → fails.
- `mem_read/miss`: `!neq 0x40 calldataload(4)`. `neq` FFI gets non-ground input → `{success: false}`. Fails.
- Neither fires → **stuck leaf**.

This is the sound approximation: can't determine alias without knowing the symbolic offset's value.

### Symbolic Read Offset

Reading with `calldataload(4)` as offset, chain has `write(0x40, V, ...)`:

- `mem_read/hit`: unify `calldataload(4) ?= 0x40`. Structural mismatch → fails.
- `mem_read/miss`: `!neq calldataload(4) 0x40`. Non-ground → fails.
- **Stuck leaf**.

Same sound approximation.

### Free Metavar as Offset (eigenvariable)

If the stack value is genuinely a free metavar `X` (from existential introduction):

- `mem_read/hit`: unify `X ?= 0x40`. X is a metavar → **binds X = 0x40**. Rule fires.

This is actually correct: it means "this execution path assumes the read offset is 0x40." Each write in the chain produces one such binding, and only the first-matched one fires (committed choice in `run()`) or all are explored (symexec). If symexec tries all writes, each produces a branch where the metavar is bound to that write's offset. This is **fork on possible values** — emerging naturally from the logic, not from an explicit fork mechanism.

### Symbolic Value in Write

`write(0x40, sym_value, M)`. Reading at 0x40:

- `mem_read/hit` succeeds (offsets match), produces `mem_read_done sym_value`.
- The symbolic value flows through as a proof term. Works perfectly.

### Summary Table

| Read offset | Write offset | Behavior | Correct? |
|-------------|-------------|----------|----------|
| Concrete | Concrete | Normal traversal | Yes |
| Concrete | Symbolic | Stuck leaf (can't determine alias) | Yes (sound) |
| Symbolic expr | Concrete | Stuck leaf (can't determine alias) | Yes (sound) |
| Free metavar | Concrete | Binds metavar — fork on values | Yes (complete) |
| Any | Any (value symbolic) | Value flows through as term | Yes |

## Performance Analysis

### Cost per MLOAD

Each MLOAD takes **W forward steps** where W = writes in the chain. Each step = one `findAllMatches` + one `applyMatch`.

| W (writes) | Steps per MLOAD | At ~10μs/step | Context |
|-----------|----------------|---------------|---------|
| 1 | 2 (miss/zero or hit) | ~20μs | Free memory pointer read (`0x40`) — most common solc MLOAD |
| 5-10 | 6-11 | 50-110μs | Simple function |
| 20-50 | 21-51 | 200-510μs | Medium contract |
| 100-500 | 101-501 | 1-5ms | Heavy contract |
| 1000+ | 1001+ | 10ms+ | Pathological (needs FFI fast-path) |

### Comparison with FFI Approach

| | Rule-based (Option A) | FFI-based (Option E) |
|---|---|---|
| Cost per MLOAD | W × ~10μs (rule match) | 1 × 10μs + W × ~50ns (Store.get) |
| Constant factor | ~100× higher | Baseline |
| For W=1 (free mem ptr) | ~20μs | ~10μs |
| For W=10 (simple fn) | ~110μs | ~11μs |
| For W=100 (heavy) | ~1ms | ~15μs |
| Proof witness | Every step visible | Single opaque step |

The rule-based approach is ~10× slower for typical W. But:

1. **CALC's overall symexec is I/O-bound on rule matching, not memory reads.** The multisig benchmark (no memory) takes ~8ms for 124 nodes. Memory reads add intermediate nodes to the tree, but these are linear chains (no branching), so the tree stays tractable.

2. **solc's free-memory-pointer pattern**: `PUSH1 0x40 MLOAD` reads offset 0x40, written once at init. W=1, cost = 2 steps. This is the most common MLOAD in all solc output.

3. **If profiling shows reads dominate**: add FFI `mem_read` as a fast-path. The rules remain the definition.

### State Size

One `mem` fact in `state.linear` regardless of memory size. Write-log nodes accumulate in Store but are content-addressed (shared across branches).

### Symexec Tree Impact

Each MLOAD adds W intermediate `mem_reading` nodes. These are linear chains (no branching). For a contract with R reads and average chain length W:

- Additional nodes: R × W
- Additional branching: 0

For a contract with 20 MLOADs and W=10: 200 extra nodes. On a tree of ~200 nodes (current multisig), this roughly doubles the tree size but adds zero branches.

## Non-Aligned Access

The aligned rules (`mem_read/hit` checks exact offset match) cover ~99% of solc output. Non-aligned overlap (MLOAD at offset 1 after MSTORE at offset 0) requires byte-level reconstruction.

### Stage 1: Aligned Only

The three rules above handle aligned access correctly. Non-aligned reads that don't exactly match any write offset traverse the entire chain and return 0 — incorrect for overlapping writes but sufficient for solc code.

Document the limitation. Detect it: if `mem_read/zero` fires but the write chain contained writes whose ranges overlap the read range, log a warning.

### Stage 2: Byte-Level Reconstruction (future)

Add overlap detection rule:

```
% Overlap: write at Other partially covers read at Offset
mem_read/overlap:
  mem_reading Offset (write Other V Rest) OrigMem *
  !neq Offset Other *
  !overlaps Offset 32 Other 32     % ranges [Offset,Offset+32) and [Other,Other+32) intersect
  -o {
    % byte-level merge — complex multi-rule expansion
    ...
  }.
```

The `!overlaps` predicate is decidable arithmetic (FFI). The byte-level merge requires extracting individual bytes from the write value and merging them into the partial result. This is expressible as ILL rules but verbose (~30 lines). Defer to when a real contract needs it.

### Alternative: Byte-Granularity Write-Log

Store writes at byte level: MSTORE produces 32 `write8` entries. MLOAD reads 32 bytes individually.

- MSTORE cost: 32 `Store.put` calls (still O(1) per entry)
- MLOAD cost: 32 × W traversals per byte position = O(32W) steps

This handles overlap naturally but is 32× more expensive. Not worth it for the aligned-access common case. Keep as a design option if non-aligned access becomes critical.

## SHA3 Migration

Current SHA3 uses `concatMemory` to iterate over `memory Pos Size V` facts. With write-log memory, SHA3 needs to read a byte range from the log.

### Pure-Rule Approach

SHA3 produces a range-reading traversal that collects bytes, then the loli fires with `sha3(collected)` as an opaque symbolic term:

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

% SHA3 range read — collect bytes via MLOAD-like traversal per byte position
% (simplified — actual implementation iterates byte positions)
sha3_reading/done:
  sha3_reading Pos Pos OrigMem Acc
  -o { sha3_read_done Acc }.

sha3_reading/step:
  sha3_reading Pos To OrigMem Acc *
  !neq Pos To
  -o {
    exists Pos'. (
      sha3_byte_reading Pos To OrigMem OrigMem Acc *
      !inc Pos Pos')
  }.
```

Each byte position triggers a sub-traversal of the write-log to find the byte value at that position. Then `sha3_byte_reading` rules traverse the chain (like `mem_read`) to find which write covers byte `Pos`.

This is O(Size × W) rule steps. For SHA3(64 bytes, W=10): ~640 steps. Expensive but pure.

### Pragmatic Note

The hash computation (`keccak256`) cannot be expressed in ILL — it's irreducibly computational. The current approach uses an opaque `sha3(Z)` term (symbolic hash). If concrete hash values are ever needed (e.g., for storage slot computation in solc), keccak256 FFI would be justified — it's a cryptographic primitive, not an axiom.

## Memory Across CALL Frames

Each CALL creates fresh memory:

```
% CALL: save caller memory, fresh memory for callee
evm/call:
  ... mem M_caller ...
  -o {
    mem empty_mem * saved_mem M_caller * ...
  }.

% RETURN: restore caller memory
evm/return:
  ... mem M_callee * saved_mem M_caller ...
  -o {
    mem M_caller * ...
  }.
```

`saved_mem` is a linear fact — consumed exactly once on RETURN. The caller's write-log is preserved as a content-addressed term in the Store. Clean and compositional.

## Connections to Theory

### McCarthy's Axioms = ILL Forward Rules

| McCarthy Axiom | ILL Rule | Meaning |
|---------------|----------|---------|
| `select(store(a, i, v), i) = v` | `mem_read/hit` | Read what you wrote |
| `i ≠ j ⟹ select(store(a, i, v), j) = select(a, j)` | `mem_read/miss` | Reads at other indices unaffected |
| `select(empty, i) = 0` | `mem_read/zero` | Zero initialization |

The three rules are a direct encoding. No interpretation gap.

### Separation Logic Correspondence (RES_0061 §9)

| Linear Logic | Separation Logic | In CALC |
|-------------|-----------------|---------|
| `⊗` (tensor) | `*` (separating conjunction) | `mem M * stack N V` = disjoint resources |
| `⊸` (lollipop) | `-*` (magic wand) | `mem M ⊸ mem (write O V M)` = memory update |
| `1` (unit) | `emp` (empty heap) | `empty_mem` |
| No contraction | Disjointness | Each `mem` fact exists once = no aliasing |

### Linear Logic Advantage Over SMT-Based Tools

hevm/halmos/Mythril/Manticore all struggle with memory aliasing: "does symbolic address A refer to the same cell as B?" This requires SMT reasoning.

CALC's `mem M` exists exactly once (linearity). The write-log is totally ordered. The question "which write covers this byte?" is a local traversal, not a global constraint. Aliasing is impossible by construction — separation logic's frame rule is structural in ILL.

### Proof Witness Quality

Option A produces a proof tree where every memory read step is visible:

```
evm/mload → mem_read/miss → mem_read/miss → mem_read/hit → loli fires
```

Each step is a valid ILL inference. The L1 kernel can verify the full derivation. Compare with FFI-based reads where the traversal is a single opaque step — the proof certificate says "FFI computed V" but not how.

## Implementation Plan

### TODO_0049.Stage_1 — Core Rules

Add to `evm.ill`:
- Type declarations: `mem`, `mem_reading`, `mem_read_done`, `write`, `write8`, `empty_mem`
- Rules: `evm/mstore`, `evm/mstore8`, `evm/mload`, `evm/msize`
- Traversal: `mem_read/hit`, `mem_read/miss`, `mem_read/zero`, `mem_read/skip8`

No FFI. No engine changes. ~30 lines of `.ill` rules.

Initial state in query files: `mem empty_mem *`

### TODO_0049.Stage_2 — Migrate SHA3 and CALLDATACOPY

Replace `concatMemory`/`unblockConcatMemory` with write-log-aware range reading. SHA3 iterates byte positions; each triggers a sub-traversal. CALLDATACOPY wraps calldata bytes as `write8` entries in the log (or a single `calldatacopy` term node if byte-level is too slow).

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
  - Loli gating: no opcode fires during mem_read traversal
```

### TODO_0049.Stage_4 — Benchmark (solc contract)

Compile simple Solidity contract with `solc --bin`. Run through CALC symexec. Compare tree size and timing with hevm.

### TODO_0049.Stage_5 — FFI Fast-Path (if needed)

If profiling shows memory reads dominate execution time, add FFI `mem_read` that traverses the write-log in JavaScript (O(W) at ~50ns/step instead of ~10μs/step). The rules remain the definition. The FFI is registered as an acceleration for `mem_read/hit + mem_read/miss + mem_read/zero`, analogous to how `!plus` FFI accelerates `plus/z + plus/s`.

### TODO_0049.Stage_6 — Non-Aligned Access (if needed)

Add `mem_read/overlap` rule with `!overlaps` arithmetic guard and byte-level merge rules. Only needed when a real contract requires non-aligned memory access.

## Byte-Addressable Memory: Deep Analysis

The aligned word-level McCarthy rules (Stage 1) cover ~99% of solc-compiled code. But EVM memory is byte-addressable: MSTORE writes 32 bytes at `[offset, offset+32)`, and nothing prevents overlapping writes at arbitrary byte offsets. This section analyzes approaches for the general case.

See RES_0062 for data structure survey, RES_0063 for engine internals of KLEE/angr/Crucible/Triton/MEMSIGHT.

### The Core Problem: Overlapping Multi-Byte Writes

Consider this concrete scenario:

```
Step 1: MSTORE(0, 0xAAAAAAAA...AA)    → writes 32 bytes at [0, 32)
Step 2: MSTORE(16, 0xBBBBBBBB...BB)   → writes 32 bytes at [16, 48)
Step 3: MLOAD(0)                       → reads 32 bytes at [0, 32)
```

The write-log after step 2: `write(16, 0xBB..BB, write(0, 0xAA..AA, empty_mem))`.

MLOAD(0) should return: `bytes [0..15] from 0xAA..AA ++ bytes [0..15] from 0xBB..BB`.

But `mem_read/hit` checks `Offset == 0` against `write(16, ...)` — fails (16 ≠ 0). `mem_read/miss` skips via `!neq 0 16`. Next: `write(0, 0xAA..AA, empty_mem)` — `mem_read/hit` fires, returns `0xAA..AA`. **Wrong**: the second write overwrote bytes [16..31].

The fundamental issue: McCarthy's axioms model **word-addressable** arrays where writes are atomic at a single index. EVM's MSTORE writes a 32-byte **window** that can partially overlap with other windows.

### The Symbolic Case: Arbitrary-Length Values

With symbolic values it gets harder. Consider:

```
Step 1: MSTORE(0, X)       → writes symbolic 32-byte value X at [0, 32)
Step 2: MSTORE(10, Y)      → writes symbolic 32-byte value Y at [10, 42)
Step 3: MLOAD(5)           → reads 32 bytes at [5, 37)
```

The result must be:
- Bytes [5..9]: bytes 5-9 of X (i.e., `extract(X, 5, 5)`)
- Bytes [10..36]: bytes 0-26 of Y (i.e., `extract(Y, 0, 27)`)
- (Byte positions are relative to X and Y's big-endian 32-byte encoding)

With symbolic offsets it becomes even more complex: if the write offset is `calldataload(4)`, we can't determine which bytes overlap at analysis time.

### Design Space

Three approaches were investigated and rejected before arriving at the recommended design. They are documented in RES_0062 for reference but are not viable for CALC:

- **Per-Byte Decomposition** (KLEE/angr/Triton style): Decompose MSTORE into 32 `write8` nodes. Correct semantics but 32× chain blowup — at 1000 MSTOREs, MLOAD costs 1,024,000 rule steps. KLEE/angr avoid this via O(1) byte arrays; CALC's linked-list write-log has no random access. Structurally incompatible.

- **Non-Overlapping Interval Tree**: Memory as a balanced tree of `[start, len) → value` intervals, split on write. O(log n) reads, but: insertion-order-dependent tree shape breaks content-addressed sharing (two identical memory states can have different Store hashes); interval splitting logic requires heavy FFI (not expressible as pure ILL rules); symbolic offsets completely fail (all comparisons need ground values).

- **Region Splitting** (Certora style): Static analysis partitions memory into disjoint regions with separate `mem` facts. 120× speedup reported but requires bytecode analysis infrastructure CALC doesn't have, depends on Solidity allocator conventions, and symbolic offsets may span region boundaries. A preprocessing optimization, not a memory model.

#### Write-Log with Overlap Detection (Recommended for CALC)

**Idea**: Extend the Stage 1 write-log with overlap-aware read rules and deferred overlap resolution. Instead of reconstructing bytes eagerly, produce symbolic `splice` terms that capture the overlap relationship. Concrete extraction happens lazily (only when needed for a comparison or branch condition).

```
% Core write-log (identical to Stage 1)
write: bin -> bin -> bin -> bin.    % write(Offset, Value, Prev)
empty_mem: bin.

% MSTORE: O(1) wrap
evm/mstore:
  ... mem M -o { mem (write Offset Value M) }.

% MLOAD read traversal — three outcomes:

% 1. Exact hit (same offset): return full value
mem_read/hit:
  mem_reading Offset (write Offset V Rest) OrigMem
  -o { mem_read_done V }.

% 2. Clean miss (no overlap): skip
mem_read/miss:
  mem_reading R (write W V Rest) OrigMem *
  !neq R W *
  !no_overlap R 32 W 32       % [R,R+32) ∩ [W,W+32) = ∅
  -o { mem_reading R Rest OrigMem }.

% 3. Partial overlap: produce symbolic slice term
mem_read/partial:
  mem_reading R (write W V Rest) OrigMem *
  !neq R W *
  !overlaps R 32 W 32          % [R,R+32) ∩ [W,W+32) ≠ ∅
  -o {
    % Continue traversal to find remaining bytes
    mem_reading R Rest OrigMem *
    mem_patch R W V             % record that V at W partially covers R
  }.

% 4. Zero (end of chain): assemble from patches
mem_read/assemble:
  mem_reading Offset empty_mem OrigMem
  -o { mem_assemble Offset }.

% Assembly: combine base (zero) with patches
mem_assemble_done:
  mem_assemble Offset            % no more patches
  -o { mem_read_done 0 }.        % base value is zero

mem_assemble_patch:
  mem_assemble Offset *
  mem_patch Offset W V
  -o {
    mem_assemble Offset *         % continue collecting patches
    % The actual byte extraction is deferred:
    % At the end, produce splice(R, [(W1,V1), (W2,V2), ...]) term
  }.
```

**The key insight**: instead of computing byte extractions eagerly, collect all overlapping writes as `mem_patch` facts during traversal. At the end, combine them into a single `splice` term: `splice(ReadOffset, [(W1,V1), (W2,V2), ..., (Wk,Vk)])`. This term is:

- **Opaque for symbolic values**: just a term that records the relationship
- **Evaluable for concrete values**: an FFI can compute the actual byte result
- **Sound**: the `splice` term contains all information needed to determine the result

**Worked example**:

```
MSTORE(0, 0xAA..AA) → write(0, 0xAA..AA, empty_mem)
MSTORE(16, 0xBB..BB) → write(16, 0xBB..BB, write(0, 0xAA..AA, empty_mem))
MLOAD(0):

Step 1: mem_reading 0 (write 16 0xBB..BB ...) OrigMem
        R=0, W=16. neq ✓. overlaps(0,32,16,32) → [0,32)∩[16,48) = [16,32) ✓
        → mem_read/partial fires
        Produces: mem_reading 0 (write 0 0xAA..AA empty_mem) OrigMem
                  mem_patch 0 16 0xBB..BB

Step 2: mem_reading 0 (write 0 0xAA..AA empty_mem) OrigMem
        R=0, W=0. → mem_read/hit fires
        Produces: mem_read_done 0xAA..AA

Wait — but we also have mem_patch 0 16 0xBB..BB. The hit returned 0xAA..AA
but bytes [16..31] should come from 0xBB..BB.
```

This reveals a subtlety: `mem_read/hit` should NOT fire when patches exist. Two options:

**Option 6a**: `mem_read/hit` returns the base value, then patches are applied on top:

```
% Modified: hit produces base value, patches modify it
mem_read/hit_with_patches:
  mem_reading Offset (write Offset V Rest) OrigMem
  -o { mem_base_found Offset V }.

% If no patches: done
mem_finalize/clean:
  mem_base_found Offset V
  -o { mem_read_done V }.         % no patches → return V directly

% If patches exist: apply newest-first
mem_finalize/patch:
  mem_base_found Offset Base *
  mem_patch Offset W PatchV
  -o {
    mem_base_found Offset (splice Base Offset W PatchV)
  }.
```

Where `splice(Base, ReadOff, WriteOff, WriteVal)` means: "take Base as default, overlay bytes from WriteVal at WriteOff for the portion that intersects [ReadOff, ReadOff+32)."

For concrete values, `splice` can be computed by FFI. For symbolic values, it remains as a symbolic term.

**Revised worked example**:

```
MLOAD(0) after MSTORE(0, 0xAA..AA) + MSTORE(16, 0xBB..BB):

Step 1: partial overlap at W=16 → mem_patch 0 16 0xBB..BB
Step 2: exact hit at W=0 → mem_base_found 0 0xAA..AA
Step 3: patch exists → splice(0xAA..AA, 0, 16, 0xBB..BB)
        = "take 0xAA..AA, overlay bytes [16..31] with bytes [0..15] of 0xBB..BB"
        For concrete: 0xAAAA...AA_BBBB...BB (first 16 bytes AA, last 16 bytes BB) ✓
```

**Performance at 1000+ operations** (typical solc code — aligned writes):

| Metric | Value | Explanation |
|--------|-------|-------------|
| MSTORE cost | O(1) | Single `write` wrap |
| MLOAD cost (aligned) | O(W) steps | Same as Stage 1 — `!no_overlap` passes, `hit` fires |
| MLOAD cost (overlapping) | O(W) steps + O(k) patches | k = overlapping writes (typically 0-2) |
| `!no_overlap` FFI cost | O(1) | Two comparisons: `R+32 ≤ W` or `W+32 ≤ R` |
| `!overlaps` FFI cost | O(1) | Negation of no_overlap |
| Patch assembly | O(k) | k = overlapping writes |

**For aligned solc code**: `!no_overlap` replaces `!neq` as the skip condition. Same O(W) traversal, slightly more expensive per step (two comparisons vs one). No patches generated. `mem_read/hit` fires at exact match. **Identical behavior to Stage 1 for aligned access**.

**For overlapping writes**: patches are collected linearly during traversal, assembled at the end. The `splice` term is O(1) to construct. For concrete values, the FFI computes the result in O(k×32) byte operations. For symbolic values, the term captures the relationship.

**For symbolic offsets**: `!no_overlap` and `!overlaps` both fail on non-ground inputs → stuck leaf. Same sound approximation as Stage 1.

### New FFI Predicates Needed

| Predicate | Semantics | Cost |
|-----------|-----------|------|
| `!no_overlap R Rs W Ws` | `[R,R+Rs) ∩ [W,W+Ws) = ∅` i.e. `R+Rs ≤ W ∨ W+Ws ≤ R` | O(1) |
| `!overlaps R Rs W Ws` | Negation of `!no_overlap` | O(1) |
| `!splice Base R W V Result` | Overlay V@W onto Base@R, produce Result | O(32) bytes |

All three are pure arithmetic on concrete bigints. No state mutation. Clean FFI.

`!no_overlap` and `!overlaps` have clean ILL clause definitions:
```
% no_overlap(R, Rs, W, Ws) ← R + Rs ≤ W
% no_overlap(R, Rs, W, Ws) ← W + Ws ≤ R
```

`!splice` is irreducibly computational (byte manipulation) — like `!mul` or `sha3`. FFI is justified.

### Why This Approach Fits CALC

1. **Faithful to the theory**: The write-log IS the memory. Traversal rules ARE McCarthy's axioms (extended with overlap). The `splice` term is an honest representation of the overlap relationship — not a hack.

2. **Backward compatible with Stage 1**: For aligned access (99% of solc code), the rules produce identical behavior. `!no_overlap` replaces `!neq` as the skip condition. Zero overhead for the common case.

3. **Minimal FFI**: Three new predicates, all pure arithmetic. No state mutation, no opaque data structures. `!no_overlap` and `!overlaps` have ILL clause definitions (just like `!neq`). `!splice` is irreducibly computational (like `!mul`).

4. **Correct for overlapping writes**: Patches accumulate during traversal, assembled at the end. For concrete values, FFI computes the byte result. For symbolic values, the `splice` term preserves all information.

5. **Content-addressed sharing**: Same write sequence = same Store hash, regardless of which branches created it.

6. **Sound symbolic approximation**: Symbolic offsets → stuck leaves. Same principle as Stage 1.

7. **Performance**: O(W) per MLOAD like Stage 1. Overlap detection adds O(1) per step. Patch assembly adds O(k) where k is typically 0. At 1000 MSTOREs, MLOAD is 1000 rule steps (~10ms at 10μs/step) — acceptable. If profiling shows this is slow, FFI fast-path (Option E from Stage 5) accelerates to ~50μs.

### Optimization: Compaction (hevm Style)

If write chains grow long enough to matter, a `compact(ByteMap, Prev)` term constructor flattens concrete portions into a direct-lookup structure. Reads check compact nodes first (O(1)), then scan remaining writes. Compaction traverses newest→oldest, applies most-recent-write-wins per byte, resolves overlaps. Symbolic writes stay above the compact node. This is an FFI optimization layer — the rules remain the definition. See Stage 5 in the implementation plan and RES_0062 §4 for details.

### Implementation Staging

- **Stage 1**: Ship with `mem_read/hit + mem_read/miss + mem_read/zero` (current plan). `!neq` is sufficient for aligned access.
- **Stage 2**: Replace `!neq` with `!no_overlap` in `mem_read/miss`. Add `mem_read/partial` with `!overlaps`. Add patch assembly rules. Add `!splice` FFI.
- **Stage 3**: If needed, add compaction as optimization layer on top.

### Symbolic Values of Arbitrary Length

EVM MSTORE always writes exactly 32 bytes. But related operations have variable lengths:

- **CALLDATACOPY(destOffset, offset, size)**: copies `size` bytes from calldata to memory
- **CODECOPY(destOffset, offset, size)**: copies `size` bytes from code to memory
- **RETURNDATACOPY(destOffset, offset, size)**: copies `size` bytes from return data
- **MCOPY(dest, src, size)** (EIP-5656): copies `size` bytes within memory

When `size` is symbolic, the write length is unknown at analysis time.

**How the write-log handles this**:

```
% Variable-length write term constructor
vwrite: bin -> bin -> bin -> bin -> bin.
  % vwrite(Offset, Size, SourceData, Prev)

% CALLDATACOPY produces a vwrite node
evm/calldatacopy:
  ... mem M * calldata CD
  -o {
    mem (vwrite DestOffset Size (extract_calldata CD SrcOffset Size) M) *
    calldata CD
  }.
```

**Reading through a vwrite node**:

```
% Clean miss: read range entirely outside vwrite range
mem_read/vmiss:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !no_overlap R 32 W Ws
  -o { mem_reading R Rest OrigMem }.

% Overlap: read range intersects vwrite range
mem_read/vpartial:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !overlaps R 32 W Ws
  -o {
    mem_reading R Rest OrigMem *
    mem_vpatch R W Ws V
  }.

% Full cover: vwrite entirely covers read range
mem_read/vhit:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !le W R *
  !le (plus R 32) (plus W Ws)
  -o { mem_read_done (extract V (minus R W) 32) }.
```

When `Ws` (size) is symbolic, `!no_overlap R 32 W Ws` fails on non-ground → stuck leaf. **Correct**: we can't determine coverage without knowing the size.

When `Ws` is concrete but `W` is symbolic: same stuck-leaf behavior.

**For MCOPY** (intra-memory copy), the source data is itself in the write-log:

```
evm/mcopy:
  ... mem M
  -o {
    mem (mcopy Dest Src Size M)
  }.

% Reading through mcopy: if read hits the dest range,
% redirect to reading from the src range in the same log
mem_read/mcopy_redirect:
  mem_reading R (mcopy D S Sz Rest) OrigMem *
  !le D R * !le (plus R 32) (plus D Sz)
  -o {
    % Read from src instead: adjust offset
    mem_reading (plus S (minus R D)) Rest OrigMem
  }.
```

This is a **pointer redirection within the log** — the read at `R` in the dest range becomes a read at `S + (R - D)` in the source range, starting from `Rest` (the state before MCOPY). Pure rules, no FFI.

## Open Questions

1. **Tag registration**: `write`, `write8`, `empty_mem`, `vwrite`, `mcopy`, `splice` should be dynamic predicate tags (above `PRED_BOUNDARY`). They're term constructors used inside `mem` arguments, not standalone predicates. Same status as `sha3`, `concat`, `s`, `e`.

2. **Gas for memory expansion**: Track as separate linear `memsize S` fact. MSTORE/MLOAD rules include `!mem_expand` persistent guard that computes new size and gas cost. Orthogonal to memory model.

3. **MCOPY (EIP-5656)**: Add `mcopy(dst, src, len, prev)` term constructor. Read traversal handles `mcopy` nodes by redirecting reads from dest range to src range within the same log. Expressible as pure rules (see above).

4. **RETURNDATASIZE / RETURNDATACOPY**: Return data is a separate buffer. Model as `returndata RD` linear fact with similar write-log structure.

5. **Compaction**: If write chains grow very long, add a `compact(ByteMap, prev)` term constructor that flattens concrete portions. Read traversal checks `compact` first (O(1) for covered bytes). This is hevm's `simplifyReads` strategy expressed as a term constructor. See "Optimization: Compaction" section above.

6. **`!no_overlap` vs `!neq`**: Stage 1 uses `!neq` (sufficient for aligned 32-byte access). Stage 2 replaces with `!no_overlap` (handles arbitrary overlap). The transition is backward-compatible: `!neq R W` implies `!no_overlap R 32 W 32` for aligned access. But `!no_overlap` is strictly more permissive (skips non-overlapping writes that `!neq` would also skip, plus catches the edge case where `R ≠ W` but ranges overlap). For Stage 1, `!neq` is correct because all EVM MSTORE/MLOAD are 32-byte aligned and non-overlapping in solc code.

7. **Patch ordering**: When multiple patches exist (multiple overlapping writes), they must be applied newest-first (most-recent-write-wins). The traversal naturally visits writes newest→oldest, so patches accumulate in the correct order. The assembly rules must apply them in collection order (FIFO for newest-first).

8. **`splice` commutativity**: For symbolic values, `splice(splice(Base, R, W1, V1), R, W2, V2)` must equal `splice(Base, R, W2, V2)` when W2's range fully covers W1's range within the read window. This is a semantic property of the `splice` operation that the FFI must respect.
