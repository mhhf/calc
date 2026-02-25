---
title: "Symbolic Memory Data Structures -- Beyond McCarthy Arrays"
created: 2026-02-25
modified: 2026-02-25
summary: "Deep survey of persistent data structures for byte-addressable symbolic memory -- interval trees, write-log models, persistent structures, HAMTs, Patricia tries, hash-consed treaps, region-based models, plus content-addressed Store representations and ILL forward rule encodings for CALC integration"
tags: [symbolic-execution, memory-model, data-structures, interval-tree, persistent-data-structure, copy-on-write, write-absorption, KLEE, angr, hevm, Crucible, MemSight, linear-logic, separation-logic, HAMT, patricia-trie, hash-consing, content-addressing, treap]
category: "Performance"
---

# RES_0062: Symbolic Memory Data Structures -- Beyond McCarthy Arrays

Companion to RES_0061 (EVM-specific memory models). This document surveys **data structures and algorithmic approaches** for symbolic memory across all symbolic execution tools, with focus on novel techniques beyond McCarthy select/store arrays.

## 1. The Problem Space

Symbolic memory must handle:
- **Byte-addressable** space (EVM: 2^256, x86: 2^64)
- **Writes of arbitrary length** (1 byte to 32+ bytes)
- **Overlapping writes** (later write to [10,42) partially covers earlier write to [0,32))
- **Partial reads** (read 4 bytes from a region where two different 32-byte writes overlap)
- **Symbolic offsets** (address is a formula, not a concrete number)
- **Symbolic values** (stored data is a formula)
- **Efficient state forking** (branch = copy entire memory state)
- **Sparsity** (vast address space, few touched locations)

## 2. McCarthy Arrays (Baseline)

The standard approach. Memory is an SMT array `A : BitVec(n) -> BitVec(8)`.

**Axioms:**
```
select(store(A, i, v), i) = v                          -- read-after-write, same index
i != j => select(store(A, i, v), j) = select(A, j)    -- read-after-write, different index
(forall i. select(A, i) = select(B, i)) => A = B       -- extensionality
```

**Limitations:**
- Byte-granular: a 32-byte `MSTORE` becomes 32 chained `store` operations
- Nested `store` chains grow linearly with writes; read resolution is O(n)
- Initializing via `store` chains is **50x slower** than via assertions (EPFL finding)
- Extensionality causes solver to enumerate all indices when comparing arrays
- No native multi-byte operations (memset, memcpy require loop unrolling or theory extensions)

**Extension:** Hadarean et al. (VSTTE 2013) extended array theory with `memset(A, start, len, val)` and `memcpy(A, B, srcOff, dstOff, len)` as first-class operations with dedicated axioms, avoiding expansion into per-byte stores.

## 3. Interval-Based Memory Models

### 3.1 MemSight: Paged Interval Tree (ASE 2017)

Coppa, D'Elia, Demetrescu. The most sophisticated interval-based symbolic memory model in the literature.

**Core idea:** Memory is a set of tuples `(addr, value, timestamp, guard)` where `addr` can be symbolic. Tuples are stored in a **paged interval tree** (pitree).

**Data structure (two levels):**
1. **Primary interval tree** -- indexed by page boundaries. Each node points to a secondary tree.
2. **Secondary interval trees** -- within each page, store the actual memory tuples.

**Tuple format:**
- `addr`: symbolic or concrete address expression
- `value`: symbolic or concrete value expression
- `timestamp`: positive for explicit writes, negative for implicit stores
- `guard`: path condition under which this write is active

**Write operation:** Insert tuple into the pitree at the address interval. No splitting/merging of existing entries -- all tuples coexist.

**Read operation:**
1. Query pitree for all tuples whose address interval overlaps the read range
2. Sort by timestamp (most recent first)
3. Build an ITE (if-then-else) chain: `if guard_n && addr_n == read_addr then value_n else if guard_{n-1} && ... else default`

**Copy-on-write:** Both primary and secondary trees use CoW. On state fork, only the path from root to modified node is copied. Unmodified subtrees are shared.

**Concrete memory optimization:** Writes to concrete addresses go into a separate **paged hashmap** (not the interval tree), since they don't need symbolic reasoning. The hashmap also uses CoW page cloning.

**Write absorption (cleanup):** When a new tuple has an address provably equal to an existing tuple's address (for all valuations of symbols), the old tuple is removed.

**Performance:** Handles symbolic pointers without forking (unlike angr/KLEE default). Trades SMT query complexity (larger ITE chains) for path reduction. Effective when symbolic pointer ranges are bounded.

### 3.2 Interval Tree Variant: Non-Overlapping Intervals

An alternative approach (not implemented in any major tool, but conceptually clean):

**Invariant:** Memory is a set of non-overlapping `[start, start+len)` intervals, each mapping to a value expression.

**Write `[o, o+s)` with value `v`:**
1. Find all intervals overlapping `[o, o+s)`
2. Split each overlapping interval into at most 3 pieces: before, overlapping, after
3. Remove the overlapping pieces
4. Insert new interval `[o, o+s) -> v`
5. Reinsert the non-overlapping before/after pieces

**Read `[o, o+s)`:**
1. Find all intervals covering `[o, o+s)`
2. If fully covered by one interval: extract bytes
3. If spanning multiple intervals: concatenate byte extractions
4. If gaps exist: fill with default (zero)

**Cost:** O(k log n) per operation, where k = number of overlapping intervals, n = total intervals. In practice, EVM programs have few overlaps (sequential allocation), so k is small.

**Advantage over MemSight:** No ITE chains -- reads are deterministic when addresses are concrete. Memory state is always compact (no stale entries).

**Disadvantage:** Requires concrete addresses. Symbolic addresses require either concretization or falling back to a different model.

## 4. Write-Log Models

### 4.1 Crucible (Galois): Log of Writes

Crucible represents memory as a **sequential log of writes**, read by backward traversal.

**Structure:**
- Each allocation has a unique block ID
- Pointers = `(block_id, offset)`, both can be symbolic
- Write log is append-only
- Reads scan backwards until fully covered

**Two implementations:**
1. **Traditional (`doStore`):** Mostly concrete. Reads/writes resolved in Haskell. Simple SMT problems but struggles with symbolic reads; can exhaust memory.
2. **Symbolic (`doArrayStore`):** Delegates offset calculations to SMT array theory. Each allocation becomes an SMT array. All reads become `select` operations.

**Lazy initialization (Macaw):** For binary analysis, memory is split into 1024-byte chunks. Chunks are populated on first access. Read-only sections (`.rodata`) bypass SMT entirely -- return raw bytes.

**Performance:** Lazy chunking reduced startup from hours to seconds for 1.8 MB binaries.

### 4.2 hevm: Algebraic Write Chains

(Detailed in RES_0061, section 2.)

Memory as nested Haskell constructors: `WriteWord offset value (WriteWord ... (ConcreteBuf ""))`. Read = outermost-first traversal. Key feature: each `ReadWord` term **contains a snapshot** of the entire buffer state, making it stateless and self-contained.

### 4.3 Write Absorption in Write Logs

The general technique of removing stale writes:

**Eager absorption:** On each new write, scan for prior writes to the same address and remove them. Cost: O(n) per write, but keeps log compact.

**Lazy absorption:** Keep all writes; on read, skip superseded writes. Cost: O(1) per write, O(n) per read.

**Batch compaction:** Periodically traverse the log, remove all superseded writes. Similar to LSM-tree compaction. Amortized cost.

**MemSight's approach:** A tuple is removed if its address is "equivalent" to a newly written address -- i.e., they resolve to the same concrete address for all symbol valuations. This requires an SMT satisfiability check per candidate pair, making it expensive for symbolic addresses.

## 5. Memory as a Function

### 5.1 Lambda/Closure Representation

Memory as `lambda addr. if addr in [o1, o1+s1) then extract(v1, addr-o1) else if addr in [o2, o2+s2) then extract(v2, addr-o2) else ... else 0`.

**Write:** Wrap existing function with new case: `lambda addr. if addr in [o, o+s) then extract(v, addr-o) else old_mem(addr)`.

**Read:** Apply function to address. For concrete addresses, evaluation reduces to a concrete value. For symbolic addresses, the ITE chain becomes an SMT formula.

**Properties:**
- O(1) write (wrap closure)
- O(n) read worst case (traverse ITE chain), where n = number of writes
- Natural handling of overlaps -- most recent write is outermost `if`
- No data structure overhead -- just function composition
- Persistent by construction -- old function still exists

**Who uses it:** This is essentially what MemSight, Mayhem, and angr build when they construct ITE chains for symbolic reads. The "lambda" representation is the denotational semantics of all write-log approaches.

**SMT encoding:** `(ite (and (bvuge addr o1) (bvult addr (bvadd o1 s1))) (extract v1 (bvsub addr o1)) (ite ... 0))`. Performance degrades with chain length; the ITE tree depth equals the number of writes.

### 5.2 Mayhem's Partial Functional Model

Mayhem (CMU, 2012) uses a hybrid:
- **Writes always concretized** -- address forced to concrete value
- **Reads may be symbolic** -- modeled as ITE over a "memory object" (bounded region)
- If symbolic address range exceeds 1024, concretize to single value
- This avoids building long ITE chains while enabling some symbolic reasoning

## 6. Region-Based Memory Models

### 6.1 Segmented Memory Model (Kapus & Cadar, ESEC/FSE 2019)

**Problem:** Symbolic pointer dereference causes forking on every possible target object.

**Solution:** Use points-to analysis to partition memory into segments. Each symbolic pointer refers to objects within a single segment.

**Algorithm:**
1. Run pointer analysis to compute points-to sets
2. Merge overlapping points-to sets until no overlap
3. Each resulting set = one memory segment
4. Symbolic pointer dereference only considers objects in its segment
5. Threshold: if segment size exceeds bound, fall back to concretization

**Results:** Significant reduction in forking on real programs (m4, make, SQLite). Some benchmarks go from timeout to completing in seconds.

### 6.2 Certora Memory Splitting (OOPSLA 2024)

**Problem:** EVM memory is one monolithic byte array. Solidity's bump allocator creates logically separate data structures that all live in this flat space.

**Solution:** Static analysis on EVM bytecode TAC representation to identify logically separate memory regions. Split the single monolithic SMT array into multiple disjoint arrays.

**Key insight:** Solidity's free memory pointer (`0x40`) creates a bump allocator. Each `MSTORE` to `[freePtr, freePtr+32)` followed by advancing freePtr indicates a new allocation. The analysis identifies which MLOAD/MSTORE operations belong to which allocation.

**Performance:** Up to **120x speedup** in SMT solving. Mitigated 16 timeouts out of 229 real-world verification tasks.

### 6.3 KLEE's Object-Level Isolation

KLEE assigns each `malloc()` a unique `MemoryObject` with a unique `ObjectState`. Pointers carry `(object_id, offset)`. Objects are completely isolated -- no pointer arithmetic can cross object boundaries (by default).

**ObjectState byte model (three states per byte):**
1. **Concrete:** value in `concreteStore[i]`, `concreteMask[i] = 1`
2. **Known Symbolic:** expression in `knownSymbolics[i]`, `concreteMask[i] = 0`
3. **Flushed:** byte pushed to UpdateList for SMT. Triggered when write offset is symbolic (all concrete/knownSymbolic bytes get flushed).

**Write at concrete offset, concrete value:** Store in `concreteStore`, mark concrete. O(1).
**Write at concrete offset, symbolic value:** Store in `knownSymbolics`, mark symbolic. O(1).
**Write at symbolic offset:** Flush all bytes to UpdateList, create symbolic `WriteExpr`. O(n) for n = object size.

**Copy-on-write:** KLEE's AddressSpace is an immutable map of `(MemoryObject -> ObjectState)`. State fork shares the map; copy-on-write at object granularity (not page granularity).

### 6.4 Trtik & Strejcek: Segment-Offset-Plane Model (ATVA 2014)

Memory organized as `(segment, offset)` pairs. Each segment is an independent memory plane. Supports:
- Symbolic pointers (within a segment)
- Allocations of symbolic size
- Multi-byte writes

Satisfiability-based simplification: SMT solver checks whether partial constraints can simplify memory expressions, reducing formula size.

## 7. angr's Paged Memory Architecture

angr uses a **mixin-based** memory system with multiple page implementations.

### 7.1 UltraPage (Default)

Three parallel structures per page (default page size 0x1000):
- `concrete_data: bytearray` -- concrete byte values
- `symbolic_bitmap: bytearray` -- 0x00 = concrete, 0x01 = symbolic at this offset
- `symbolic_data: SortedDict` -- offset -> `SimMemoryObject` (sparse, only symbolic bytes)

**Write (concrete):** Update `concrete_data[offset]`, set `symbolic_bitmap[offset] = 0x00`. O(1).
**Write (symbolic):** Set `symbolic_bitmap[offset] = 0x01`, insert into `symbolic_data` SortedDict. Remove overlapping entries. O(log n).
**Read:** Check bitmap. If concrete, bit-shift bytes together. If symbolic, retrieve from SortedDict or create default. O(k) where k = bytes read.

**Merge (state join):** Compare pages byte-by-byte, create ITE expressions for differing bytes.

### 7.2 Concretization Strategies

When a memory index is symbolic:
1. Check strategies in order (read_strategies / write_strategies)
2. Default write: concretize always
3. Default read: if range > 128 solutions, concretize to single value
4. `MultiwriteAnnotation`: allows symbolic writes up to 128 possible addresses
5. Each possible address -> separate write guarded by condition

## 8. Persistent / Copy-on-Write Data Structures

### 8.1 Persistent Segment Trees

Standard segment tree made persistent via **path copying**. On modification:
1. Create new nodes only along root-to-leaf path (O(log n) nodes)
2. Unmodified children shared with previous version
3. Old root still valid -- access any historical state

**For memory:** Tree over the address space. Leaves store byte values. Write = path copy to modified leaf. Read = traverse current version's root.

**Cost:** O(log N) time and space per operation, where N = address space size. For 2^256 addresses, log N = 256, which is constant.

**Practical issue:** Tree must be lazy -- don't materialize the full 2^256 depth. Only paths that have been written get materialized. Untouched paths implicitly return default (zero).

### 8.2 Persistent Red-Black Trees / Treaps

For representing a **sparse set of written intervals**:
- Keys = write start addresses
- Values = (length, value_expression)
- Persistent via path copying: O(log n) per mutation, structural sharing

**Treap advantage:** Only O(1) amortized rotations per insert/delete (vs O(log n) for AVL). Fewer nodes copied per mutation.

**Functional red-black tree** (Okasaki 1999): purely functional, efficient persistent insert. Well-suited for Haskell-like environments.

### 8.3 Hash Array Mapped Tries (HAMTs)

Used by Clojure, Scala, Haskell (`unordered-containers`) for persistent maps.

**Structure:** 32-way branching trie on hash bits. Each node has a 32-bit bitmap indicating which children exist, plus a packed array of those children.

**For memory:** Hash the address, use HAMT to map address -> value.

**Cost:** O(log32 n) = O(n/5) for n = number of written addresses. In practice, ~7 levels for millions of entries.

**Persistence:** Path copying on modification. Shared structure between versions. O(log32 n) new nodes per mutation.

**Advantage over balanced trees:** Cache-friendly (packed arrays), good constant factors, amortized O(1) for small maps.

**Disadvantage:** No range queries. Finding all writes overlapping with `[o, o+s)` requires scanning. Not suitable for interval-based queries.

### 8.4 Lazy Persistent Tries (for 2^256 address spaces)

For EVM's 2^256 address space, a trie keyed on address bits is natural:
- 256 levels, binary branching
- Only materialized on written paths
- Default: zero at all unmaterialized leaves
- Path copying for persistence

**With 32-way branching:** 256/5 = ~51 levels. Each node is a 32-entry array with a bitmap.

**Optimization:** Collapse long chains of single-child nodes (path compression). A write to address `0x1234...` with no nearby writes has a single compressed edge from root to leaf.

## 9. Sparse Representations

### 9.1 The Sparsity Problem

EVM memory: 2^256 possible addresses, typically < 1000 are touched. Ratio: ~10^-74 occupancy.

**Approaches by density:**
- **< 100 entries:** Sorted array of `(addr, value)` pairs. O(n) scan, but small n.
- **100-10000 entries:** Balanced BST or HAMT. O(log n) operations.
- **> 10000 entries:** Paged structures (angr-style) or hash maps.

### 9.2 Dictionary / Map Approach

Most tools ultimately use this: a map from `address -> value` with a default value of zero.

- KLEE: immutable map of `(MemoryObject -> ObjectState)`
- angr: dict of `(page_number -> Page)`
- Halmos: Python dict / Z3 array with default 0
- Crucible: write log (effectively an ordered map by time)

### 9.3 Compressed Sparse Representations

**Run-length encoding:** For `memset(mem, 0, 256)`, store as `(start=0, len=256, val=0)` instead of 256 entries. Useful for zero-initialization.

**Block allocation tracking:** Track which 32-byte blocks have been written. Only create per-byte structure on first access. Similar to Galois's lazy 1024-byte chunk approach.

## 10. Write-Set / Read-Set Abstractions

### 10.1 Abstract Tracking Without Materializing Values

Track which regions were written/read without storing actual values:

**Write-set:** `{[o1, o1+s1), [o2, o2+s2), ...}` -- set of written intervals
**Read-set:** `{[r1, r1+rs1), ...}` -- set of read intervals

**Use cases:**
- **Conflict detection:** Two parallel executions conflict if write-sets overlap with each other's read-sets
- **Frame computation:** In separation logic, the frame is everything not in the write-set
- **Dead write elimination:** A write is dead if no subsequent read overlaps it
- **Independence analysis:** Two code blocks are independent if their write-sets and read-sets don't overlap

### 10.2 Application to Certora's Memory Splitting

Certora's analysis computes write-sets and read-sets for each allocation region. If two regions have non-overlapping write/read sets, they can be modeled as separate SMT arrays -- eliminating aliasing constraints between them.

## 11. Performance Analysis

### 11.1 Bottlenecks at 1000+ Memory Operations

**Constraint solving (75% of runtime):**
- Array theory with deeply nested `store` chains
- Each symbolic read generates a `select` over the full write history
- Z3's lazy axiom instantiation can trigger exponential blowup

**ITE chain construction (MemSight-style):**
- O(k) per read, where k = writes overlapping the read address
- For symbolic addresses, k = all writes (worst case)
- ITE depth directly impacts solver difficulty

**State forking overhead:**
- Copy-on-write helps, but each fork still creates O(log n) new nodes
- Deep exploration trees create millions of states, each with its own memory

### 11.2 What Works Best (Empirical)

| Workload | Best Model | Why |
|----------|-----------|-----|
| Mostly concrete addresses | KLEE ObjectState / angr UltraPage | Concrete fast path, symbolic only when needed |
| Many symbolic pointers | MemSight interval tree | Avoids forking, compact ITE representation |
| EVM smart contracts | hevm write chains + simplification | Algebraic simplification before SMT; eager exploration |
| Large binaries (>1MB) | Crucible lazy chunks | Don't pay for unaccessed memory |
| Verification (properties) | Certora memory splitting | 120x by decomposing monolithic array |
| Many state forks | Persistent structures (HAMT/treap) | O(log n) fork cost |

### 11.3 KLEE-Specific Findings

- Symbolic array accesses exceeding 4096 bytes trigger performance warnings
- Constraint independence optimization: decompose queries into independent sub-queries that share no variables. Reduces solver burden.
- Array constraint acceleration (Perry et al., ISSTA 2017): avoid redundant axiom instantiation for `select(store(...))` chains.

### 11.4 Encoding Matters More Than Structure

EPFL's systematic study:
- **Assertion-based init + arrays:** 1x (baseline)
- **Nested store init + arrays:** 50x slower
- **ITE encoding (no arrays):** 11x slower
- **Portfolio (incremental + non-incremental):** 2.25x faster than baseline
- **QF_ABV theory:** orders of magnitude faster than default strategy

Key takeaway: the SMT encoding of memory operations often matters more than the in-memory data structure choice.

## 12. Lazy Memory Initialization

### 12.1 JetKlee / Symbiotic Approach

Construct symbolic memory objects **lazily on first access**, not at allocation time. Benefits:
- Function-level symbolic execution without knowing arguments
- External variables can be pointers to unknown memory
- Memory created on demand = less upfront cost

### 12.2 Crucible/Macaw Lazy Chunks

Divide binary's address space into 1024-byte chunks. Populate SMT array chunk-by-chunk on first access. Immutable sections (`.rodata`) return raw bytes, bypassing SMT entirely.

## 13. Integration with Linear Logic Forward Chaining

### 13.1 Memory as Linear Resources

In CALC's linear logic engine, memory cells are naturally linear propositions:

```
mem(addr, val)         -- linear fact: this cell exists exactly once
mem(addr, old) -o mem(addr, new)   -- write: consume old, produce new
```

This gives **aliasing safety by construction** -- no two facts for the same address can coexist.

### 13.2 Data Structure Choice for CALC

CALC's forward engine needs:
1. **Fast pattern matching** on `mem(addr, val)` facts
2. **Efficient consumption/production** (remove old fact, insert new)
3. **State forking** for symexec exploration
4. **Symbolic address handling** when addr is a metavariable

**Recommended structure: Persistent sorted map (address -> value)**

- **Why sorted:** Range queries for overlapping checks, sequential memory access patterns
- **Why persistent:** Symexec creates many branches; structural sharing minimizes copy cost
- **Concrete path:** O(log n) lookup in sorted map
- **Symbolic path:** Fall back to pattern matching against all `mem` facts

### 13.3 Approaches Ranked by CALC Fit

| Approach | Fork Cost | Write | Read | Symbolic Addr | CALC Fit |
|----------|-----------|-------|------|---------------|----------|
| Persistent treap | O(log n) | O(log n) | O(log n) | Pattern match | Best |
| HAMT | O(log32 n) | O(log32 n) | O(log32 n) | Full scan | Good |
| Persistent interval tree | O(log n) | O(k log n) | O(k log n) | Native (ITE) | Good for symbolic |
| Write log | O(1) | O(1) | O(n) | Native | Simple but slow reads |
| Flat sorted array | O(n) | O(n) | O(log n) | Scan | Bad for forking |

### 13.4 The Linear Logic Advantage

Unlike conventional symbolic executors, CALC does not need:
- McCarthy array axioms (no SMT array theory)
- ITE chains for aliasing (linear uniqueness prevents aliasing)
- Concretization strategies (linear facts are already "concrete" in the logic)

The only challenge is **symbolic addresses** -- when a rule produces `mem(X, val)` where `X` is a metavariable. This requires either:
1. **Eager grounding:** Enumerate possible values of `X` from constraints
2. **Deferred matching:** Keep `mem(X, val)` as a symbolic fact; resolve when `X` is bound
3. **Constraint propagation:** Propagate address constraints to narrow `X`'s domain

## 14. Content-Addressed Store Representations

How each data structure maps to CALC's `{ tag, children }` Store nodes.

### 14.1 Persistent Interval Tree as Store Terms

An interval tree stores memory regions `[lo, hi) -> value`. Each node augmented with `max_hi` (maximum high endpoint in subtree) for pruning.

```
% In the Store (conceptual)
put('itree', ['nil'])                                          % empty
put('itree', ['node', left_h, lo_h, hi_h, val_h, maxhi_h, right_h])  % internal
```

Path-copying produces O(log n) new Store nodes per write. Shared subtrees have identical hashes -- automatic deduplication. The augmented `max_hi` field must be recomputed along the path, which creates slightly more new nodes than a plain BST.

**Symbolic offset handling:** the overlap test `lo <= query < hi` becomes a constraint. Options: defer (keep read as unresolved term), fork (exponential worst case), or accumulate constraints along the path.

### 14.2 HAMT as Store Terms

A HAMT with 32-way branching, keyed by memory address directly (no pre-hashing needed since addresses are already integers).

```
put('hamt', ['empty'])                                         % empty
put('hamt', ['leaf', addr_h, val_h])                           % single entry
put('hamt', ['node', bitmap_h, child0_h, child1_h, ...])      % internal (bitmap + packed children)
put('hamt', ['collision', pair_list_h])                        % hash collision
```

With 5-bit chunks per level: 256/5 = ~52 levels for a full 256-bit address. However, EVM memory is concentrated in low addresses (< 2^16), so most tries have ~4 levels. The bitmap encoding means empty children consume no space.

**Structural sharing is automatic and maximal:** two execution branches that differ by one write share all HAMT nodes except the ~4 nodes on the modified path.

**Symbolic offset problem:** HAMT dispatch extracts specific bits from the key. A symbolic address means undefined bit extraction -- must fall back to scanning all children at each level (exponential worst case, but bounded by 32 per level).

### 14.3 Merkle Patricia Trie as Store Terms

Following Ethereum's Modified Merkle Patricia Trie pattern:

```
put('mtrie', ['empty'])                                        % empty trie
put('mtrie', ['leaf', suffix_h, val_h])                        % leaf: remaining key suffix + value
put('mtrie', ['ext', prefix_h, child_h])                       % extension: shared prefix + child
put('mtrie', ['branch', c0_h, c1_h, ..., c15_h, val_h])       % 16-way branch + optional value
```

**Why 16-way (hex):** each nibble (4 bits) of the address selects a branch. For 256-bit addresses, maximum depth is 64 nibbles. Patricia compression collapses long chains of single-child nodes into extension nodes, so typical depth is proportional to the discriminating prefix length.

**Sparsity:** a branch node with only 2 occupied children still stores 16 child slots (14 are `mtrie_empty`). In the Store, `mtrie_empty` is a single hash -- so 14 of the 16 children are the same hash, but they still take space in the `children` array. Optimization: use a bitmap like HAMT to pack only existing children.

**Content-addressing:** identical subtrees produce identical Store hashes by construction. This is exactly how Ethereum's state trie achieves its Merkle property.

### 14.4 Hash-Consed Treap as Store Terms

A treap (tree + heap) where priority = hash(key), giving **unique tree shape** for any set of keys.

```
put('htreap', ['nil'])                                         % empty
put('htreap', ['node', addr_h, val_h, left_h, right_h])       % BST by addr, heap by hash(addr)
```

**Why unique representation matters:** two memory states with the same set of `(addr, value)` pairs produce the exact same treap structure, regardless of insertion order. This means:
- O(1) memory state equality: root hashes match iff memory contents are identical
- Automatic deduplication across execution branches that reach the same state
- No normalization needed -- the shape is a pure function of the data

**Confluent persistence (Liljenzin 2013):** merge two treaps that share most content in O(m log(n/m)) where m = number of differing entries among n total. Equal subtrees are detected by O(1) hash comparison and skipped. Directly applicable to merging execution paths after conditional branches.

**Priority computation:** `priority(addr) = FNV_hash(addr)`. Since CALC already uses FNV-1a for content-addressing, the same hash function serves double duty. The priority need not be stored explicitly -- it can be recomputed from the address.

## 15. ILL Forward Rule Encodings

Three approaches for expressing memory operations as ILL rules.

### 15.1 Approach A: Memory as Opaque FFI Term

The memory structure is a single linear fact `mem(T)` where `T` is a Store hash pointing to the tree root. Read/write are FFI-backed:

```
% MSTORE: consume old memory, produce new memory via FFI
evm/mstore:
  pc PC * code PC 0x52 * !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) Offset *
  stack SH Value *
  mem M
  -o {
    code PC 0x52 * sh SH * pc PC' *
    mem (ffi_mstore M Offset 32 Value)
  }.

% MLOAD: read value from memory via FFI (memory not consumed)
evm/mload:
  pc PC * code PC 0x51 * !inc PC PC' *
  sh (s SH) *
  stack SH Offset *
  mem M *
  !ffi_mload M Offset 32 V
  -o {
    code PC 0x51 * sh (s (s SH)) *
    stack (s SH) V *
    mem M *
    pc PC'
  }.
```

**Pros:** clean linear semantics; tree operations in FFI are fast; existing `prove.js` FFI infrastructure handles `ffi_mstore`/`ffi_mload`.

**Cons:** memory structure is opaque to the logic; cannot reason about memory contents within proofs; FFI is a trusted boundary.

### 15.2 Approach B: Tree Nodes as Linear Facts

Each tree node is a separate linear fact. Writes decompose into path-copy rules:

```
% BST node: mem_node(key, value, left_subtree_id, right_subtree_id)
mem_node : bin -> bin -> bin -> bin -> type.

% Write left: target < node key
mem_write/left:
  mem_node K V L R * write_target T Val * !less T K
  -o { exists L'. (
    mem_node K V L' R *
    write_into L T Val L')
  }.

% Write right: target >= node key
mem_write/right:
  mem_node K V L R * write_target T Val * !geq T K * !neq T K
  -o { exists R'. (
    mem_node K V L R' *
    write_into R T Val R')
  }.

% Write hit: target = node key (update in place)
mem_write/hit:
  mem_node K V L R * write_target K Val'
  -o {
    mem_node K Val' L R
  }.
```

**Pros:** fully expressible in ILL; memory structure is transparent to the logic; proofs witness the tree path.

**Cons:** many rules; hard to keep balanced (rebalancing rules are complex); O(log n) rule applications per write; each node is a separate linear fact that the forward engine must match.

### 15.3 Approach C: Hybrid (Recommended)

FFI-backed tree operations behind a linear interface. The memory is ONE linear fact `mem(root_hash)`. FFI functions implement the tree operations:

```javascript
// In lib/engine/ffi/memory.js
function ffi_mstore(state, args) {
  // args: [root_hash, offset, size, value]
  const root = args[0], offset = args[1], size = args[2], val = args[3];
  // Perform persistent trie insert, return new root hash
  return patriciaTrie.write(root, offset, size, val);
}

function ffi_mload(state, args) {
  // args: [root_hash, offset, size]
  const root = args[0], offset = args[1], size = args[2];
  // Read from persistent trie, return value hash
  return patriciaTrie.read(root, offset, size);
}
```

The persistent trie operations create new Store nodes (via `Store.put`) and return root hashes. Since the tree is in the Store, it participates in content-addressing: identical memory states have identical root hashes.

**MLOAD semantics:** `mem M` is consumed and re-produced unchanged. This maintains linear discipline while allowing the forward engine to track that the memory fact was "used." Alternatively, `!mem M` (persistent) avoids consumption/re-production but loses the ability to track memory frame changes.

## 16. Comparative Analysis for CALC Integration

### 16.1 Content-Addressing Quality

| Structure | Unique Representation | Hash-Cons Automatic | Structural Sharing |
|-----------|----------------------|--------------------|--------------------|
| Flat `memory` facts (current) | Yes (per fact) | Yes | Per-fact only |
| hevm write chain | No (order-dependent) | No | Full chain |
| Interval tree | No (rotation-dependent) | No | Path-copy |
| HAMT | Yes (if key = addr directly) | Yes (by construction) | Excellent |
| Patricia trie | Yes | Yes (Merkle property) | Excellent |
| Hash-consed treap | **Yes** (strongest) | **Yes** (by construction) | **Excellent + merge** |

### 16.2 Symbolic Offset Compatibility

| Structure | Concrete | Bounded Symbolic | Unbounded Symbolic |
|-----------|----------|------------------|--------------------|
| Flat facts | O(n) scan | Natural (unification) | Natural (unification) |
| Write chain | O(n) scan | Defer | Defer |
| HAMT | O(1) effective | O(32^levels) branching | Impractical |
| Patricia trie | O(key_len) | Constraint propagation | O(16^levels) branching |
| Hash-consed treap | O(log n) | Fork | Fork |
| Hybrid (log + tree) | O(log n) | Log: natural | Log: natural |

### 16.3 EVM-Specific Fitness

For EVM symbolic execution in CALC:
- **90%+ of addresses are concrete** (computed by ADD/MUL on concrete values)
- **Memory is sparse** (typically < 1000 cells, in addresses 0x00-0xFFFF)
- **32-byte word alignment** is common (MSTORE/MLOAD are 32-byte operations)
- **State forking** happens at every conditional jump

**Recommended:** Merkle Patricia Trie (primary) with compacted write log (for symbolic addresses).

The Patricia trie handles the 90% concrete case at O(key_prefix_length) ~ O(4-8) levels. The write log handles the 10% symbolic case. Compaction moves entries from log to trie when addresses become concrete (resolved by backward chaining of `!plus`, `!inc` etc).

## 17. Recommended Architecture for CALC

### Tier 1: Merkle Patricia Trie (primary)

Implement as FFI-backed persistent trie in the Store:
- 16-way branching (hex nibbles of address)
- Patricia compression for sparse addresses
- Branch/Extension/Leaf node types (Ethereum-style)
- New Store tag: `mtrie` with subtags `empty`, `leaf`, `ext`, `branch`

### Tier 2: Compacted Write Log (symbolic layer)

For symbolic addresses that cannot enter the trie:
- Append-only log of `(symbolic_addr, size, value)` triples
- Reads check log first (O(k)), then trie (O(key_len))
- On address resolution (when metavar binds to concrete), compact into trie

### Tier 3: Hash-Consed Treap (for merge-heavy workloads)

If CALC develops path merging (join after conditional branches):
- O(m log(n/m)) merge via equal-subtree skipping
- Unique representation enables automatic detection of convergent states

## 18. Key Papers (extended)

- Coppa, D'Elia, Demetrescu. "Rethinking Pointer Reasoning in Symbolic Execution" (ASE 2017) -- MemSight
- Borzacchiello, Coppa, D'Elia, Demetrescu. "Memory Models in Symbolic Execution: Key Ideas and New Thoughts" (STVR 2019) -- comprehensive survey
- Kapus, Cadar. "A Segmented Memory Model for Symbolic Execution" (ESEC/FSE 2019) -- segmented model
- Trtik, Strejcek. "Symbolic Memory with Pointers" (ATVA 2014) -- segment-offset-plane model
- Cha et al. "Unleashing MAYHEM on Binary Code" (S&P 2012) -- hybrid symbolic/concrete memory
- Nandi et al. "Practical Verification of Smart Contracts using Memory Splitting" (OOPSLA 2024) -- Certora
- Hadarean et al. "Extending the Theory of Arrays: memset, memcpy, and Beyond" (VSTTE 2013) -- array theory extension
- Perry et al. "Accelerating Array Constraints in Symbolic Execution" (ISSTA 2017) -- KLEE array optimization
- Bucur et al. "Encoding Symbolic Expressions as Efficient Solver Queries" (EPFL 2015) -- encoding benchmark
- Slaby, Strejcek, Trtik. "Compact Symbolic Execution" (ATVA 2013) -- compact symex
- **Driscoll, Sarnak, Sleator, Tarjan (1989).** "Making Data Structures Persistent." *J. Computer and System Sciences* 38(1) -- foundational: path copying, fat nodes
- **Bagwell (2001).** "Ideal Hash Trees." -- original HAMT paper, 32-way branching, bitmap compression
- **Liljenzin (2013).** "Confluently Persistent Sets and Maps." arXiv:1301.3388 -- hash-consed treaps with unique representation and O(m log(n/m)) merge
- **Okasaki (1998).** *Purely Functional Data Structures.* -- canonical reference for persistent balanced trees
- **Filliâtre & Conchon (2006).** "Type-Safe Modular Hash-Consing." -- hash-consing in ML
- **Steindorfer & Vinju (2015).** "Optimizing Hash-Array Mapped Tries for Fast and Lean Immutable JVM Collections." *OOPSLA* -- CHAMP: improved HAMT
- **Ethereum Yellow Paper** (Appendix D). Modified Merkle Patricia Trie -- production-proven content-addressed trie over 2^256
- **Zhu (2025).** "Efficient Symbolic Computation via Hash Consing." arXiv:2509.20534 -- 3.2x speedup from hash-consing in symbolic computation

## 19. Open Questions

1. **Nibble vs. byte branching:** should the Patricia trie branch on 4-bit nibbles (Ethereum-style, 16-way) or 8-bit bytes (256-way, shallower)? Byte branching gives 32 levels for 256-bit keys but wider nodes.

2. **Compaction trigger:** for the hybrid log+trie approach, what is the optimal compaction threshold? Fixed count? Read-count-since-last-compaction? Triggered by metavar binding?

3. **MLOAD linearity:** should `mem(T)` be linear (consumed/re-produced by reads) or persistent (`!mem(T)`)? Linear is more precise but persistent avoids unnecessary consumption.

4. **Symbolic address narrowing:** can we exploit Patricia trie structure to narrow symbolic address ranges? If the trie has entries only at 0x00-0xFF, a symbolic address X with X > 0xFF reads zero.

5. **Incremental hash computation:** when path-copying a trie, can we avoid recomputing the full FNV hash? The root hash depends only on the changed child -- partial update possible.

- Coppa, D'Elia, Demetrescu. "Rethinking Pointer Reasoning in Symbolic Execution" (ASE 2017) -- MemSight
- Borzacchiello, Coppa, D'Elia, Demetrescu. "Memory Models in Symbolic Execution: Key Ideas and New Thoughts" (STVR 2019) -- comprehensive survey
- Kapus, Cadar. "A Segmented Memory Model for Symbolic Execution" (ESEC/FSE 2019) -- segmented model
- Trtik, Strejcek. "Symbolic Memory with Pointers" (ATVA 2014) -- segment-offset-plane model
- Cha et al. "Unleashing MAYHEM on Binary Code" (S&P 2012) -- hybrid symbolic/concrete memory
- Nandi et al. "Practical Verification of Smart Contracts using Memory Splitting" (OOPSLA 2024) -- Certora
- Hadarean et al. "Extending the Theory of Arrays: memset, memcpy, and Beyond" (VSTTE 2013) -- array theory extension
- Perry et al. "Accelerating Array Constraints in Symbolic Execution" (ISSTA 2017) -- KLEE array optimization
- Bucur et al. "Encoding Symbolic Expressions as Efficient Solver Queries" (EPFL 2015) -- encoding benchmark
- Slaby, Strejcek, Trtik. "Compact Symbolic Execution" (ATVA 2013) -- compact symex
