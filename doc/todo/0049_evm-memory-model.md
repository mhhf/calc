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

## Open Questions

1. **Tag registration**: `write`, `write8`, `empty_mem` should be dynamic predicate tags (above `PRED_BOUNDARY`). They're term constructors used inside `mem` arguments, not standalone predicates. Same status as `sha3`, `concat`, `s`, `e`.

2. **Gas for memory expansion**: Track as separate linear `memsize S` fact. MSTORE/MLOAD rules include `!mem_expand` persistent guard that computes new size and gas cost. Orthogonal to memory model.

3. **MCOPY (EIP-5656)**: Add `copy(dst, src, len, prev)` term constructor. Read traversal handles `copy` nodes by reading from the source region of the same log. Expressible as rules.

4. **RETURNDATASIZE / RETURNDATACOPY**: Return data is a separate buffer. Model as `returndata RD` linear fact with similar write-log structure.

5. **Compaction**: If write chains grow very long, add a `compact(ByteMap, prev)` term constructor that flattens concrete portions. Read traversal checks `compact` first (O(1) for covered bytes). This is hevm's `simplifyReads` strategy expressed as a term constructor.
