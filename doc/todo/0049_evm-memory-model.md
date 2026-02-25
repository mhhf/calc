---
title: EVM Memory Model Design
created: 2026-02-24
modified: 2026-02-25
summary: Design MLOAD/MSTORE memory model for CALC's EVM symbolic executor
tags: [evm, memory-model, architecture, linear-logic, separation-logic, symexec, forward-chaining, McCarthy]
type: design
status: ready for implementation
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

### MSIZE (0x59) Semantics

From the Yellow Paper function M (eq. 224–225):

```
M(s, f, l) = max(s, ceil((f + l) / 32))   when l ≠ 0
M(s, f, l) = s                              when l = 0
```

Where `s` = current size in words, `f` = byte offset, `l` = access length. MSIZE returns `s × 32` (bytes).

Properties:
- **Monotonically increasing** — memory never shrinks within a call frame
- **Per call frame** — fresh on CALL, callee's size discarded on RETURN
- **32-byte granularity** — MSIZE always returns a multiple of 32
- **Triggered by access, not by content** — MLOAD at offset 992 with no prior writes still expands to 1024 bytes
- **Zero-length access does NOT expand** — `l = 0` leaves size unchanged (go-ethereum `calcMemSize64`)

Opcodes that trigger expansion: MLOAD, MSTORE, MSTORE8, SHA3, CALLDATACOPY, CODECOPY, RETURNDATACOPY, MCOPY, CREATE, CALL (for in/out ranges).

## Current State in CALC

`evm.ill:90` declares `memory: bin -> bin -> bin -> type.` — a **linear** ternary predicate `memory Pos Size V`. Used by:

1. **concatMemory** (lines 388-403): iterates over `memory` facts via recursive forward rules, concatenating values. Consumes each `memory Pos Size V` and re-produces it (preserve-on-read). Driven by `!neq` guard and `!plus` increment.

2. **SHA3** (lines 405-423): triggers `concatMemory` with a loli continuation (`unblockConcatMemory Z -o {...}`). The continuation fires when traversal completes, passing concatenated bytes as `sha3 Z`.

3. **CALLDATACOPY** (lines 577-612): produces `memory Ms Size D` facts from `calldata` facts. Uses blocking pattern (`unblock -o {pc PC'}`).

**Migration approach**: The old `memory` type and all rules depending on it (`concatMemory`, `unblockConcatMemory`, old SHA3, old CALLDATACOPY) will be **removed and replaced** by the new write-log model. No backward compatibility — clean break for a cleaner design.

**Key observation**: concatMemory already IS a rule-based write-chain traversal — recursive forward rules that walk a data structure, gated by a loli continuation. The new memory model follows the same established pattern.

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
mem: bin -> type.                          % single linear fact: the memory
memsize: bin -> type.                      % single linear fact: high-water mark (bytes)
mem_reading: bin -> bin -> bin -> type.     % mem_reading Offset CurrentTerm OrigMem
mem_read_done: bin -> type.                % mem_read_done Value (triggers loli)
write: bin -> bin -> bin -> bin.            % write(offset, value, prev)
empty_mem: bin.                            % zero-initialized base
saved_mem: bin -> type.                    % CALL frame save (linear)
saved_memsize: bin -> type.                % CALL frame save (linear)
```

### MSTORE — O(1), one rule

```
evm/mstore:
  pc PC * code PC 0x52 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M * memsize S *
  !mem_expand S Offset 32 S'
  -o {
    code PC 0x52 * pc PC' * sh SH *
    mem (write Offset Value M) * memsize S'
  }.
```

Just wraps a `write` constructor. Content-addressed: same write sequence = same hash across symexec branches. `!mem_expand` updates the high-water mark.

### MLOAD — loli continuation + recursive traversal

```
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) * stack SH Offset *
  mem M * memsize S *
  !mem_expand S Offset 32 S'
  -o {
    code PC 0x51 *
    memsize S' *
    mem_reading Offset M M *
    (mem_read_done V -o {
      pc PC' * sh (s SH) * stack SH V * mem M
    })
  }.
```

Key design: `pc PC'` is NOT produced yet — it's captured in the loli. No opcode rule can fire during traversal (they all need `pc`). Only `mem_read/*` rules match. `memsize S'` is produced immediately (not gated by the loli) because memory expansion happens before the read, not after.

### MSIZE — O(1), read high-water mark

```
evm/msize:
  pc PC * code PC 0x59 * !inc PC PC' *
  sh SH *
  memsize S
  -o {
    code PC 0x59 * pc PC' *
    sh (s SH) * stack SH S *
    memsize S
  }.
```

`memsize S` is consumed and re-produced (preserve-on-read). Different symexec branches may have different memory sizes.

### `!mem_expand` FFI

```javascript
// mode: + + + -
function mem_expand(args) {
  const [oldSize, offset, accessLen, outSlot] = args;
  const s = binToInt(oldSize), o = binToInt(offset), l = binToInt(accessLen);
  if (s === null || o === null || l === null)
    return { success: false, reason: 'mode_mismatch' };
  if (l === 0n) return { success: true, theta: [[outSlot, oldSize]] };
  const needed = ((o + l + 31n) / 32n) * 32n;
  const newSize = needed > s ? needed : s;
  return { success: true, theta: [[outSlot, intToBin(newSize)]] };
}
```

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

`mem_read/hit` has pattern `mem_reading Offset (write Offset V Rest) OrigMem`. The same metavar `Offset` appears twice — a non-linear pattern. `matchIndexed` (`unify.js:502-581`) handles this: first occurrence binds, second occurrence checks equality (`existing !== t` at line 517). Standard structural unification on content-addressed terms. No extensions needed.

### Mutual Exclusion — No Spurious Branching

At each traversal step, exactly one of {hit, miss, zero} can fire:

- **hit**: unification succeeds iff outermost write offset = read offset (non-linear pattern)
- **miss**: unification succeeds for any `write` node, but `!neq Offset Other` fails when offsets are equal (because `Other` binds to the same value as `Offset`)
- **zero**: only matches `empty_mem` (different tag than `write` — structural mismatch)

In symexec, `findAllMatches` tries all three rules but only one succeeds per state. Zero spurious branches.

### Worked Example

```
% Initial: mem empty_mem * memsize 0 * pc 0 * ...

Step 1: PUSH1 0x42 → stack 0 0x42
Step 2: PUSH1 0x00 → stack 1 0x00
Step 3: MSTORE → mem (write 0x00 0x42 empty_mem) * memsize 32

Step 4: PUSH1 0xBB → stack 0 0xBB
Step 5: PUSH1 0x20 → stack 1 0x20
Step 6: MSTORE → mem (write 0x20 0xBB (write 0x00 0x42 empty_mem)) * memsize 64

Step 7: PUSH1 0x00 → stack 0 0x00
Step 8: MLOAD fires:
  consumes: mem (write 0x20 0xBB (write 0x00 0x42 empty_mem)), stack 0 0x00, memsize 64
  produces: memsize 64, mem_reading 0x00 (write 0x20 0xBB ...) (write 0x20 0xBB ...)
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

**`!neq` behavior on symbolic operands**: `neq` FFI (`arithmetic.js:361-365`) checks `isGround(a) && isGround(b)`. Non-ground → returns `{ success: false, reason: 'mode_mismatch' }`. `tryFFIDirect` (`match.js:245`) treats reason-bearing failures as non-definitive → returns null → backward prover finds no clause → `mem_read/miss` fails to fire → stuck leaf. Sound: can't determine if symbolic offset aliases the read offset.

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

One `mem` fact + one `memsize` fact in `state.linear` regardless of memory size. Write-log nodes accumulate in Store but are content-addressed (shared across branches).

### Symexec Tree Impact

Each MLOAD adds W intermediate `mem_reading` nodes. These are linear chains (no branching). For a contract with R reads and average chain length W:

- Additional nodes: R × W
- Additional branching: 0

For a contract with 20 MLOADs and W=10: 200 extra nodes. On a tree of ~200 nodes (current multisig), this roughly doubles the tree size but adds zero branches.

## SHA3 Migration

Current SHA3 uses `concatMemory` to iterate over `memory Pos Size V` facts. The old `memory` type, `concatMemory`, and `unblockConcatMemory` are removed entirely.

### New Design: `!mem_read_range` FFI

SHA3 becomes a single rule with an FFI-backed persistent predicate:

```
evm/sha3:
  pc PC * code PC 0x20 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Size *
  mem M * memsize S *
  !mem_expand S Offset Size S' *
  !mem_read_range M Offset Size Bytes
  -o {
    code PC 0x20 * pc PC' *
    sh (s SH) * stack SH (sha3 Bytes) *
    mem M * memsize S'
  }.
```

No loli continuation needed. `!mem_read_range` reads the byte range in one step. The result is wrapped in opaque `sha3(Bytes)`. Same bytes → same hash (by content-addressing).

### Why `!mem_read_range` FFI works

Unlike `!calldata_extract` (which would need state access), the write-log IS a content-addressed term in the Store. The FFI receives `M` (the write-log root hash) and traverses it via `Store.get`/`Store.child`/`Store.tag` — no state access needed.

```javascript
// mode: + + + -
function mem_read_range(args) {
  const [memHash, offsetHash, sizeHash, bytesSlot] = args;
  const offset = binToInt(offsetHash);
  const size = binToInt(sizeHash);
  if (offset === null || size === null)
    return { success: false, reason: 'mode_mismatch' };
  if (size === 0n)
    return { success: true, theta: [[bytesSlot, intToBin(0n)]] };

  const result = new Uint8Array(Number(size));  // zero-filled
  const covered = new Uint8Array(Number(size)); // 0 = uncovered, 1 = covered

  let current = memHash;
  while (true) {
    const tag = Store.tag(current);
    if (tag === 'empty_mem') break;
    if (tag === 'write') {
      const wOff = binToInt(Store.child(current, 0));
      if (wOff === null)
        return { success: false, reason: 'symbolic_offset' };
      const wVal = Store.child(current, 1);
      const wValInt = binToInt(wVal);
      if (wValInt === null)
        return { success: false, reason: 'symbolic_value' };
      // write covers [wOff, wOff+32). Read covers [offset, offset+size).
      const overlapStart = wOff > offset ? wOff : offset;
      const overlapEnd = (wOff + 32n) < (offset + size)
        ? (wOff + 32n) : (offset + size);
      if (overlapStart < overlapEnd) {
        // Extract overlapping bytes from 32-byte big-endian value
        for (let i = overlapStart; i < overlapEnd; i++) {
          const ri = Number(i - offset);
          if (!covered[ri]) {
            // Most-recent-write-wins: outermost write takes priority
            const byteIdx = Number(i - wOff);
            result[ri] = Number((wValInt >> BigInt(8 * (31 - byteIdx))) & 0xFFn);
            covered[ri] = 1;
          }
        }
      }
      current = Store.child(current, 2);  // rest
    } else {
      return { success: false, reason: 'unknown_node' };
    }
  }
  // Assemble result bytes into a BigInt (big-endian)
  let resultInt = 0n;
  for (let i = 0; i < result.length; i++)
    resultInt = (resultInt << 8n) | BigInt(result[i]);
  return { success: true, theta: [[bytesSlot, intToBin(resultInt)]] };
}
```

**Fallback**: when offsets or values are symbolic, the FFI returns `{ success: false, reason: ... }` → `tryFFIDirect` returns null → backward prover falls back to clause definitions (the traversal rules from Stage 1). Those rules produce a stuck leaf for symbolic offsets. Same soundness guarantee.

### SHA3 Common Case

In Solidity, the most common SHA3 is `keccak256(abi.encodePacked(key, slot))` — SHA3(0x00, 0x40) for storage mapping slots. Memory is `write(0x20, slot, write(0x00, key, empty_mem))`. The FFI traverses 2 write nodes, extracts 64 bytes from two non-overlapping 32-byte writes. ~100ns total.

### Keccak256 Computation

The hash itself is irreducibly computational. `sha3(Bytes)` is an opaque content-addressed term. Two SHA3s of the same bytes produce the same hash (by content-addressing). An optional `!keccak256 Bytes Hash` FFI can compute the actual keccak256 when concrete hash values are needed (e.g., storage slot computation for SLOAD).

## CALLDATACOPY Migration

Current CALLDATACOPY iterates over `calldata Cs Size D` facts, producing `memory Ms Size D` facts. The new version uses the same iterative forward-rule pattern but writes `write` nodes into the write-log instead.

### New Design: Forward-Rule Iteration into Write-Log

```
calldatacopy_iter: bin -> bin -> bin -> bin -> type.
  % calldatacopy_iter DestOffset CalldataPos CalldataEnd Mem

evm/calldatacopy:
  pc PC * code PC 0x37 * !inc PC PC' *
  sh (s (s (s SH))) *
  stack (s (s SH)) DestOffset *
  stack (s SH) DataOffset *
  stack SH Size *
  mem M * memsize S *
  !mem_expand S DestOffset Size S'
  -o {
    exists End. (
      code PC 0x37 *
      memsize S' *
      calldatacopy_iter DestOffset DataOffset End M *
      !plus DataOffset Size End *
      (calldatacopy_done M' -o {
        pc PC' * sh SH * mem M'
      })
    )
  }.

calldatacopy_done: bin -> type.

calldatacopy_iter/s:
  calldatacopy_iter Dest Cs Ce M *
  calldata Cs Size D *
  !neq Cs Ce
  -o {
    exists Cs'. exists Dest'. (
      calldata Cs Size D *
      calldatacopy_iter Dest' Cs' Ce (write Dest D M) *
      !plus Cs Size Cs' *
      !plus Dest Size Dest')
  }.

calldatacopy_iter/z:
  calldatacopy_iter Dest Ce Ce M
  -o { calldatacopy_done M }.
```

### Why Forward Rules, Not FFI

FFI functions (`tryFFIDirect` at `match.js:241`) receive only their argument hashes — no state access. Calldata lives as individual `calldata Pos Size V` persistent facts in the state. An FFI `!calldata_extract` can't see them. The forward-rule iteration naturally accesses calldata facts via pattern matching.

### What Changes from Current CALLDATACOPY

| Aspect | Old | New |
|--------|-----|-----|
| Output | `memory Ms Size D` facts (N separate linear facts) | `write(Dest, D, M)` nodes in write-log (one `mem` fact) |
| Signal | `unblock` | `calldatacopy_done M'` |
| Blocking | `(unblock -o {pc PC'})` | `(calldatacopy_done M' -o {pc PC' * sh SH * mem M'})` |
| MSIZE | Not tracked | `!mem_expand` in main rule |

The iteration is identical — same `!neq`/`!plus` guards, same calldata chunk matching. Only the output differs: `write(Dest, D, M)` wrapping instead of `memory` fact production.

### Calldata Chunk Size Assumption

Current programs use 32-byte calldata chunks (`calldata 0 32 Deadline`). Using `write(Dest, D, M)` implies 32-byte MSTORE semantics. For non-32-byte calldata chunks, `vwrite(Dest, Size, D, M)` would be needed — deferred to Stage 5 alongside overlap handling.

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

### MSTORE8

MSTORE8 belongs in this stage (not Stage 1) because a `write8` node within a 32-byte MLOAD range is a partial overlap requiring proper handling.

```
evm/mstore8:
  pc PC * code PC 0x53 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset * stack SH Value *
  mem M * memsize S *
  !mem_expand S Offset 1 S'
  -o {
    exists Byte. (
      code PC 0x53 * pc PC' * sh SH *
      mem (write8 Offset Byte M) * memsize S' *
      !mod Value 0x100 Byte)
  }.
```

Additional type and traversal rules:

```
write8: bin -> bin -> bin -> bin.          % write8(addr, byte, prev)

% write8 during word-level read: always a partial overlap
mem_read/write8_miss:
  mem_reading R (write8 Addr Byte Rest) OrigMem *
  !no_overlap R 32 Addr 1
  -o { mem_reading R Rest OrigMem }.

mem_read/write8_overlap:
  mem_reading R (write8 Addr Byte Rest) OrigMem *
  !overlaps R 32 Addr 1
  -o { mem_reading R Rest OrigMem * mem_patch_byte R Addr Byte }.
```

### Variable-Length Writes

`vwrite` for CALLDATACOPY with non-32-byte chunks, CODECOPY, RETURNDATACOPY, MCOPY.

```
vwrite: bin -> bin -> bin -> bin -> bin.   % vwrite(Offset, Size, SourceData, Prev)

mem_read/vmiss:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !no_overlap R 32 W Ws
  -o { mem_reading R Rest OrigMem }.

mem_read/vpartial:
  mem_reading R (vwrite W Ws V Rest) OrigMem *
  !overlaps R 32 W Ws
  -o { mem_reading R Rest OrigMem * mem_vpatch R W Ws V }.
```

When `Ws` (size) is symbolic, `!no_overlap R 32 W Ws` fails → stuck leaf. Correct: can't determine coverage without knowing the size.

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

## Memory Across CALL Frames

```
% CALL: save caller memory + memsize, fresh for callee
evm/call:
  ... mem M_caller * memsize S_caller ...
  -o { mem empty_mem * memsize 0 * saved_mem M_caller * saved_memsize S_caller * ... }.

% RETURN: restore caller memory + memsize, discard callee's
evm/return:
  ... mem M_callee * memsize S_callee * saved_mem M_caller * saved_memsize S_caller ...
  -o { mem M_caller * memsize S_caller * ... }.
```

`saved_mem` and `saved_memsize` are linear facts — consumed exactly once on RETURN. The caller's write-log is preserved as a content-addressed term in the Store. The callee starts with `mem empty_mem * memsize 0`.

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

## Constraint Propagation Interaction (TODO_0005)

When MLOAD returns a symbolic value (evar or opaque term) and that value flows into arithmetic, constraints accumulate in the persistent state. TODO_0005 (Levels 0+1) resolves these chains. This section documents the interaction.

### How Symbolic Values Flow from Memory

```
Step 1: MLOAD(0x04)
  mem_read/hit returns calldataload(4) — an opaque symbolic term
  → stack SH calldataload(4)

Step 2: ADD (calldataload(4) + 3)
  FFI plus(calldataload(4), 3, C): binToInt(calldataload(4)) = null → mode_mismatch
  resolveExistentials creates evar(0) as witness
  → stack SH evar(0), persistent: !plus(calldataload(4), 3, evar(0))

Step 3: ADD (evar(0) + 5)
  FFI plus(evar(0), 5, C): binToInt(evar(0)) = null → mode_mismatch
  resolveExistentials creates evar(1)
  → stack SH evar(1), persistent: !plus(evar(0), 5, evar(1))

Step 4: EQ (evar(1) == 100) → ⊕ branch
  Branch A: evar(1) ≠ 100 — path condition: !neq(evar(1), 100)
  Branch B: evar(1) = 100 — path condition: !eq(evar(1), 100)
```

Both branches survive because evar(1) is symbolic. Without TODO_0005, the constraint chain `!plus(calldataload(4), 3, evar(0)), !plus(evar(0), 5, evar(1))` accumulates indefinitely.

### Key Asymmetry: `isGround` vs `binToInt`

`isGround(evar(0))` returns **true** (evar has tag `'evar'` with a BigInt child — recursion finds no metavars). But `binToInt(evar(0))` returns **null** (tag is `'evar'`, not `'binlit'`). FFI mode checks use `binToInt`, which correctly rejects evars. This means evars are structurally complete (no metavars) but semantically unknown (can't be converted to numbers).

### TODO_0005 Level 0+1 Resolution

With Level 0 (equality resolution) + Level 1 (FFI re-check):

```
Branch B receives: !eq(evar(1), 100)

Level 0: substitute evar(1) → 100 everywhere
  !plus(evar(0), 5, evar(1))  →  !plus(evar(0), 5, 100)

Level 1: re-check now-ground constraints
  plus(evar(0), 5, 100): reverse mode (- + +) → evar(0) = 95

Level 0 again: substitute evar(0) → 95
  !plus(calldataload(4), 3, evar(0))  →  !plus(calldataload(4), 3, 95)

Level 1 again: plus(calldataload(4), 3, 95): calldataload(4) is opaque (not evar)
  → constraint stays (can't resolve opaque term)
```

Result: 3 evars → 1 remaining constraint. The chain resolved backward from the path condition.

### Impact on Memory Model

The memory model itself doesn't need TODO_0005. MLOAD/MSTORE work correctly with symbolic values — opaque terms pass through unification unchanged, and stuck leaves are produced for symbolic offsets.

TODO_0005 benefits the *downstream* computation after MLOAD returns a symbolic value. Without it, every arithmetic operation on a symbolic memory value produces a new evar and a new constraint. With Level 0+1, path conditions cascade backward through these chains, often resolving intermediate evars to concrete values.

For k-dss scale contracts (5000+ nodes), TODO_0005 Level 0+1 is estimated at 3-10x speedup from constraint reduction + branch pruning. For simple contracts, the overhead is <5%.

### Independence

TODO_0005 is orthogonal to the memory model. All memory stages can be implemented and tested without it. TODO_0005 can be implemented before or after the memory model. The interaction is purely at the constraint level — when path conditions happen to constrain values that originated from memory reads.

## Design Properties

### Not Skolemization — Uninterpreted Functions

The memory model uses **structured symbolic terms**, not Skolemization.

Skolemization eliminates ∃ by introducing fresh constants: `∃x. P(x)` → `P(sk)`. Our engine handles `exists` via fresh evars resolved by constraints — standard.

What we do with `sha3(Bytes)` and `write(Offset, Value, Mem)` is create **uninterpreted function terms**. Key property: **congruence** — two `sha3` terms with the same argument are content-addressed to the same hash → automatically equal. Different arguments → automatically distinct. No axioms needed.

The asymmetry with arithmetic is deliberate:

| Domain | Representation | Why |
|--------|---------------|-----|
| Memory | Structural terms: `write(O, V, M)` | Writes are data construction, not computation |
| SHA3 | Opaque term: `sha3(Bytes)` | Hash is uncomputable, but equality is structural |
| Arithmetic | Concrete or fail | FFI needs actual numbers; `plus(X, 3)` would poison downstream `binToInt` |

Design principle: **structural where possible** (memory, SHA3), **computational where necessary** (arithmetic), **stuck where unknown** (symbolic guards).

### No Simplification Needed

The write-log is append-only. We don't have rewrite rules, and we don't need them.

**Dead writes are harmless.** `write(0, B, write(0, A, empty_mem))` — inner `write(0, A, ...)` is dead. But `mem_read/hit` matches the outermost write first and returns `B`. The dead write costs one extra miss step for reads at other offsets, nothing more.

**Content-addressing gives free structural sharing.** The term `write(0, A, empty_mem)` is a single hash in the Store. Every symexec branch sharing this memory prefix shares the actual data. Write-log grows linearly per branch, but common prefixes are shared across the exploration tree.

**Why not compact?** A GC rule like `mem (write O V1 (write O V2 Rest)) -o { mem (write O V1 Rest) }` would compete nondeterministically with read rules in the committed-choice engine. The correct optimization layer is FFI (Idea 1+2 in Optimization Ideas) — not term rewriting.

### Overlap Behavior by Stage

With `!neq`-based rules (no overlap handling): unaligned overlapping writes produce **silently wrong** answers (miss skips a partially-overlapping write because offsets differ).

With `!no_overlap`-based rules (overlap-aware): unaligned overlapping writes produce either correct spliced results (concrete) or **loud stuck leaves** (symbolic). Silent wrong is worse than loud stuck.

**Decision: go directly to `!no_overlap` from the start.** The aligned solc fast path is identical — `!no_overlap R 32 W 32` passes on every step when all writes are 32-byte aligned at distinct offsets, same as `!neq R W`. For unaligned writes, partial overlap is correctly detected and patched.

## Audit Findings

### `mh` → `memsize` Migration

`mh: bin -> type.` (evm.ill:91) is unused legacy ("memory height"). Never referenced in any forward rule. Initial states in `multisig.ill` and `multisig_nocall.ill` have `mh 0` — must be replaced with `mem empty_mem * memsize 0`. The `mh` type declaration is removed entirely.

### Gas Omission in Memory Rules

Memory rules omit `gas G * !gasCost G Cost G'` — consistent with ADD/MUL/SUB pattern. EQ/ISZERO/SHA3/JUMP include gas. This is an intentional simplification for the arithmetic subset. Gas can be added uniformly later.

### `memory` Type Scope

`memory: bin -> bin -> bin -> type.` is only used by `concatMemory/s`, `concatMemory/z`, old `calldatacopy/s`, old `calldatacopy/z`. Clean removal — no other rules reference it.

### Loli Variable Capture — Verified Correct

MLOAD's loli `(mem_read_done V -o { pc PC' * ... * mem M })` captures `M`, `PC'`, `SH`. Variables in the loli body are substituted during consequent instantiation via `subApplyIdx` (compile.js). `M` correctly refers to the original memory at loli creation time, not at firing time. Verified through compile.js and match.js code paths.

### `memsize` Safety During Traversal

No `mem_read/*` rule matches `memsize` — it sits inert during the traversal. `memsize S'` is produced immediately by MLOAD (not gated by the loli) because expansion happens before the read. Verified: no interference.

### `binToInt` Handles Zero Correctly

`binToInt(atom('e'))` → 0n (convert.js:26). The `!mem_read_range` FFI will correctly extract byte value 0 from write-log entries. `mem_read/zero` produces literal `0` which is `atom('e')` in the Store.

## Implementation Plan

The stages are ordered for implementing everything in one pass — no intermediate states, no backward compatibility. Tests accompany each code change rather than being a separate stage.

### TODO_0049.Stage_1 — FFIs

New file `lib/engine/ffi/memory.js` with all memory FFI predicates:
- `!mem_expand` — memory size high-water mark update
- `!mem_read_range` — read byte range from write-log (~60 LOC)
- `!no_overlap` — disjoint range check: `[R,R+Rs) ∩ [W,W+Ws) = ∅`
- `!overlaps` — partial overlap check (negation of `!no_overlap`)
- `!splice` — byte-level overlay of overlapping writes (~30 LOC)
- `!mod` — modulo for MSTORE8 (unless already in arithmetic.js)

FFI registration in `lib/engine/ffi/index.js`.

~150 LOC total. Pure arithmetic on content-addressed terms. No state access.

### TODO_0049.Stage_2 — evm.ill Rewrite

Single atomic pass through `evm.ill`:

**Remove:**
- `memory: bin -> bin -> bin -> type.`
- `mh: bin -> type.`
- `unblock: type.`
- `concatMemory`, `unblockConcatMemory`, `concatMemory/z`, `concatMemory/s`
- Old `evm/sha3`, old `evm/calldatacopy`, `calldatacopy/z`, `calldatacopy/s`

**Add types:**
- `mem`, `memsize`, `mem_reading`, `mem_read_done`, `mem_base_found`
- `mem_patch`, `mem_patch_byte`, `mem_vpatch`
- `write`, `write8`, `vwrite`, `empty_mem`, `splice`
- `saved_mem`, `saved_memsize`
- `calldatacopy_iter`, `calldatacopy_done`

**Add rules:**
- `evm/mstore`, `evm/mload`, `evm/msize`, `evm/mstore8`
- Overlap-aware traversal: `mem_read/hit`, `mem_read/miss` (with `!no_overlap`), `mem_read/partial` (with `!overlaps`), `mem_read/zero`
- `write8` traversal: `mem_read/write8_miss`, `mem_read/write8_overlap`
- `vwrite` traversal: `mem_read/vmiss`, `mem_read/vpartial`
- Finalization: `mem_finalize/clean`, `mem_finalize/patch`
- New `evm/sha3` (single rule with `!mem_read_range`)
- New `evm/calldatacopy` + `calldatacopy_iter/s` + `calldatacopy_iter/z`

**Update initial states** in `multisig.ill`, `multisig_nocall.ill`:
- Remove `mh 0`
- Add `mem empty_mem * memsize 0`

~80 lines `.ill` changes. No engine changes.

### TODO_0049.Stage_3 — CALL Frame Memory

Add to `evm.ill`:
- `saved_mem`, `saved_memsize` types (already declared in Stage 2)
- Update `evm/call` to save caller memory: `mem M * memsize S → saved_mem M * saved_memsize S * mem empty_mem * memsize 0`
- Update `evm/return` to restore: `mem M_callee * saved_mem M_caller * saved_memsize S_caller → mem M_caller * memsize S_caller`

Needed for multi-contract benchmarks (external calls).

### TODO_0049.Stage_4 — Tests

```
tests/engine/memory.test.js:
  Core:
  - MSTORE then MLOAD at same offset → correct value
  - MSTORE then MLOAD at different offset → 0
  - Two MSTOREs then MLOAD → latest value wins (most recent write)
  - Zero initialization: MLOAD without prior MSTORE → 0

  MSIZE:
  - MSIZE returns 0 initially
  - MSTORE at offset 0 → MSIZE = 32
  - MSTORE at offset 32 → MSIZE = 64
  - MLOAD at offset 992 → MSIZE = 1024
  - MSIZE monotonically increasing (two MSTOREs, check after each)

  Overlap:
  - Aligned writes at distinct offsets: !no_overlap passes, identical to !neq path
  - Overlapping writes: MSTORE(0, A) then MSTORE(16, B) then MLOAD(0) → splice(A, 0, 16, B)
  - MSTORE8: write8 node correctly patched into word-level read
  - Symbolic overlap: partial overlap with symbolic offset → stuck leaf

  MSTORE8:
  - MSTORE8 then MLOAD at containing word → correct byte patched

  Symbolic:
  - Symbolic offset: MLOAD with symbolic offset → stuck leaf
  - Symbolic value: MLOAD returns symbolic value as-is
  - Mixed chain: concrete + symbolic values in same write-log

  SHA3:
  - SHA3 of two 32-byte writes → correct hash term
  - SHA3 with symbolic memory value → sha3(symbolic_bytes) opaque

  CALLDATACOPY:
  - CALLDATACOPY then MLOAD at copied offset → correct calldata value
  - CALLDATACOPY with multiple chunks → all accessible via MLOAD

  Symexec:
  - Memory preserved/restored correctly on backtrack (mutate/undo)
  - Loli gating: no opcode fires during mem_read traversal
  - Content-addressed sharing: same write sequence = same mem hash across branches
```

### TODO_0049.Stage_5 — Benchmark (solc contract)

Compile simple Solidity contract with `solc --bin`. Run through CALC symexec. Compare tree size and timing with hevm.

### Deferred: FFI Fast-Path + Memoization

Not a stage — implement only if profiling shows memory reads dominate execution time. Add FFI `!mem_read` for MLOAD (see Optimization Idea 1) with memoization cache (Idea 2). The rules remain the definition.

O(W) at ~50ns/step instead of ~10μs/step. 200× speedup. Zero logic changes. Cache keyed by `(mem_hash, offset)` — content-addressed = no invalidation needed.

## Optimization Ideas

The write-log traversal is O(W) per MLOAD. At 500 writes that's ~5ms per read at 10μs/step. This section collects optimization strategies that are **sound for symbolic offsets and overlapping writes**. All preserve the ILL rules as the logical definition. Ideas that break for symbolic offsets (Baker Array, Shadow Map, Embedded HAMT, Generalized Array) were evaluated and rejected — see RES_0062 for details.

### Idea 1: Backward-Chaining Oracle (`!mem_read` as Persistent Predicate)

Make memory read a **persistent predicate** resolved by backward chaining, exactly like `!plus`, `!neq`, `!inc`.

```
% Instead of forward traversal rules, MLOAD uses a persistent guard:
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) * stack SH Offset *
  mem M *
  !mem_read M Offset V           % ← backward-chaining, FFI-accelerated
  -o {
    code PC 0x51 * pc PC' * sh (s SH) * stack SH V * mem M
  }.
```

The FFI for `mem_read` traverses the write-log in JavaScript: `Store.get` calls at ~50ns/step instead of ~10μs/step per rule application. Result: O(W) at 50ns = 25μs for W=500, vs 5ms for rule-based traversal. **200× speedup**, zero logic changes.

The traversal rules (`hit`/`miss`/`zero`) remain as ILL clause definitions — the backward prover falls back to them if no FFI is registered. Same pattern as `plus/z`, `plus/s` clauses with `!plus` FFI.

### Idea 2: Memoized Reads via Content-Addressing

Since write-logs are content-addressed, `(mem_hash, offset)` **uniquely determines** the read result. A global cache exploits this:

```javascript
const readCache = new Map();
function mem_read(memHash, offset) {
  const key = `${memHash}:${offset}`;
  if (readCache.has(key)) return readCache.get(key);
  const value = traverseWriteLog(memHash, offset);
  readCache.set(key, value);
  return value;
}
```

Many branches share the same memory prefix. After MSTORE(0x40, 0x80) at init, every branch has the same write-log for the free memory pointer. MLOAD(0x40) in branch 47 hits the cache populated by branch 1. O(1). No cache invalidation needed (content-addressed = immutable).

### Idea 3: Content-Addressed Read-Through Cache on Store Terms

Attach a read cache **to each write-log term** in the Store. Cache `{offset → result}` per term. Shared across branches because write-log terms are content-addressed. O(1) per cache probe.

### Idea 4: Generalized Indexed Persistent Predicate

O(1) lookup for `code PC V` and `calldata` via engine-level indexing. Orthogonal to memory model. See full description in earlier version.

### Idea 5: Traversal Short-Circuit (Engine-Level Batching)

Engine recognizes `mem_reading` traversal pattern, executes in JavaScript batch, produces W proof steps for verification. Single engine step instead of W steps.

### Comparison

| Idea | Read Cost | Write Cost | Complexity | Symbolic Sound |
|------|-----------|------------|------------|---------------|
| 1. BC Oracle | O(W)@50ns | O(1) | Low | Yes (fallback to rules) |
| 2. Memo Cache | O(1) amortized | O(1) | Low | Yes (cache miss → rules) |
| 3. Term Cache | O(1) amortized | O(1) | Medium | Yes (cache miss → rules) |
| 4. Indexed Pred | O(1) | N/A (persistent) | Medium | Orthogonal (code/calldata) |
| 5. Short-Circuit | O(1) engine | O(1) | Medium | Yes (abort → rules) |

### Recommended Optimization Path

**Phase 1** (easy, high impact): Ideas 1 + 2. `!mem_read` FFI with memoization. ~50 LOC. 200× speedup.

**Phase 2** (medium): Idea 3. Per-term read cache in Store. Exploits content-addressed sharing.

**Phase 3** (medium, orthogonal): Idea 4. Indexed persistent predicates for `code`/`calldata`.

**Phase 4** (medium, if needed): Idea 5. Engine-level traversal short-circuit.

## Open Questions

1. ~~**Tag registration**~~: Resolved. `write`, `empty_mem`, `write8`, `vwrite`, `splice` are dynamic predicate tags (above `PRED_BOUNDARY`). Automatic — no action needed.

2. **Gas for memory expansion**: Currently modeled via `!mem_expand` FFI updating `memsize S`. Gas cost computation (`words²/512 + 3*words`) is orthogonal — add `!mem_gas OldSize NewSize GasCost` FFI when gas modeling matters. Memory rules omit gas, consistent with ADD/MUL/SUB.

3. **RETURNDATASIZE / RETURNDATACOPY**: Return data is a separate buffer. Model as `returndata RD` linear fact with `vwrite`-based write-log. Same pattern as `mem`.

4. ~~**Patch ordering**~~: Resolved. Traversal visits writes newest→oldest, patches accumulate in correct order (most-recent-write-wins).

5. **`splice` commutativity**: `splice(splice(Base, R, W1, V1), R, W2, V2)` must equal `splice(Base, R, W2, V2)` when W2's range fully covers W1's range within the read window. The FFI must respect this.

6. **`!keccak256` FFI**: Concrete keccak256 computation for storage slot resolution. Add when SLOAD needs concrete slot computation (e.g., `storage (sha3 (concat 0 slot)) V` requires matching against actual slot hash).

7. ~~**CALLDATACOPY loli stack height**~~: Resolved. Loli captures `sh SH` and restores it on `calldatacopy_done`. Same pattern as existing CALLDATACOPY blocking.

8. ~~**`mh` legacy type**~~: Resolved. `mh: bin -> type.` is unused. Remove and replace `mh 0` with `mem empty_mem * memsize 0` in initial states.

9. ~~**Loli variable capture**~~: Resolved. `M` in MLOAD's loli is substituted during consequent instantiation via `subApplyIdx`. Correctly refers to original memory at loli creation.

10. ~~**`memsize` during traversal**~~: Resolved. No `mem_read/*` rule matches `memsize`. Safe.

11. ~~**`binToInt` zero handling**~~: Resolved. `binToInt(atom('e'))` → 0n. `mem_read/zero` produces literal 0 correctly.
