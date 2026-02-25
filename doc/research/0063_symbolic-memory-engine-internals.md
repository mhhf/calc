---
title: "Symbolic Memory Engine Internals -- KLEE, angr, Triton, Crucible, SAW"
created: 2026-02-25
modified: 2026-02-25
summary: "Deep analysis of how five major symbolic execution engines implement byte-addressable memory: data structures, concrete fastpaths, symbolic addresses, overlapping writes, and complexity bounds"
tags: [symbolic-execution, memory-model, KLEE, angr, Triton, Crucible, SAW, data-structures]
category: "Symbolic Execution"
---

# Symbolic Memory Engine Internals

## 1. KLEE

### 1.1 Core Data Structures

**MemoryObject** -- represents an allocation site (malloc, stack, global). Key fields:
- `unsigned id` -- unique identifier
- `uintptr_t address` -- base address
- `size_t size` -- allocation size in bytes
- `size_t alignment`
- `bool isLocal, isGlobal, isFixed`
- `const llvm::Value *allocSite`

**ObjectState** -- stores actual byte contents of one MemoryObject in one ExecutionState. Dual-representation:
- `uint8_t *concreteStore` -- flat byte array for concrete values
- `BitArray *concreteMask` -- 1-bit-per-byte: which bytes are concrete
- `ref<Expr> *knownSymbolics` -- expression array for symbolic bytes
- `BitArray *unflushedMask` -- which bytes haven't been flushed to UpdateList
- `UpdateList updates` -- immutable linked list of (index, value) write records

**AddressSpace** -- maps MemoryObjects to ObjectStates:
```
typedef ImmutableMap<const MemoryObject*, ref<ObjectState>, MemoryObjectLT> MemoryMap;
```
The ImmutableMap is a persistent balanced tree (red-black or similar). Copy = O(1), lookup = O(log n), insert = O(log n) with structural sharing.

**MemoryObjectLT** -- comparator ordering MemoryObjects by address, enabling efficient range queries.

### 1.2 Concrete Fastpath

ObjectState maintains three zones per byte:
1. **Concrete** (`concreteMask[i] = 1`): value lives in `concreteStore[i]`, no Expr allocation
2. **Known symbolic** (`knownSymbolics[i] != null`): cached symbolic Expr
3. **Unflushed** (`unflushedMask[i] = 1`): byte not yet materialized in UpdateList

Read at constant offset with constant-width:
```cpp
ref<Expr> ObjectState::read8(unsigned offset) {
  if (isByteConcrete(offset))
    return ConstantExpr::create(concreteStore[offset], Expr::Int8);
  if (isByteKnownSymbolic(offset))
    return knownSymbolics[offset];
  // else: flush + construct ReadExpr from UpdateList
}
```

The top-level `read(offset, width)` checks if offset is a ConstantExpr; if so, dispatches to `read8(concrete_offset)` directly -- the "concrete fastpath". For symbolic offsets, it constructs a `ReadExpr` referencing the UpdateList.

**Multi-byte reads** decompose to individual byte reads and concat with endianness:
```cpp
for (i = 0; i < NumBytes; i++) {
  idx = isLittleEndian ? i : (NumBytes - i - 1);
  Byte = read8(offset + idx);
  Res = i ? ConcatExpr::create(Byte, Res) : Byte;
}
```

### 1.3 UpdateList and ReadExpr

**UpdateList** -- singly-linked immutable list of `UpdateNode`s. Each node: `(index: Expr, value: Expr, next: UpdateNode*)`. Newest write at the head.

**ReadExpr** -- `ReadExpr::create(updates, index)` scans the UpdateList head-to-tail:
- If `index` is concrete and matches a node with concrete index: return that value
- If a node has symbolic index: stop scanning (could alias), return a ReadExpr node

This is the SMT "array theory" encoding: `select(store(store(A, i1, v1), i2, v2), idx)`.

**Complexity**: read = O(k) where k = number of symbolic-index writes. With all-concrete indices, read = O(1) via knownSymbolics cache.

### 1.4 Write Handling

```cpp
void ObjectState::write8(unsigned offset, ref<Expr> value) {
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(value)) {
    concreteStore[offset] = CE->getZExtValue(8);
    setKnownSymbolic(offset, nullptr);
    markByteConcrete(offset);
    markByteUnflushed(offset);
  } else {
    setKnownSymbolic(offset, value);
    markByteSymbolic(offset);
    markByteUnflushed(offset);
  }
}
```

**Partial overlapping writes**: not explicitly handled. Each byte is independent. Writing 4 bytes at offset 3 writes bytes 3,4,5,6 individually. If a prior 8-byte symbolic write existed at offset 0, bytes 0-2 and 7 retain the old value; bytes 3-6 get overwritten. No coalescing.

### 1.5 Flush Mechanism

`flushRangeForRead(offset, numBytes)`: for each unflushed byte, appends to UpdateList:
```
updates.extend(ConstantExpr(offset), ConstantExpr(concreteStore[offset]))
```
Does NOT mark as symbolic. Purpose: make the byte visible to ReadExpr resolution.

`flushRangeForWrite(offset, numBytes)`: same, but ALSO marks the byte as symbolic afterward. Purpose: invalidate the concrete cache so future reads go through UpdateList.

### 1.6 Symbolic Address Resolution

`AddressSpace::resolve(addr_expr)` -- queries SMT solver for all MemoryObjects the pointer could reference. Returns `ResolutionList = vector<ObjectPair>`. The executor forks one state per resolution.

`AddressSpace::resolveOne(ConstantExpr addr)` -- binary search in ImmutableMap for the MemoryObject containing address. O(log n).

### 1.7 Symbolic-Length memcpy/memset

KLEE concretizes the length parameter. For symbolic lengths, it would need to fork on every possible length value, causing path explosion. Research (e.g., MInt model) proposes native array operations to handle this, but stock KLEE does not.

### 1.8 Copy-on-Write

ImmutableMap enables O(1) state fork: just copy the root pointer. When an ObjectState is modified, `AddressSpace::getWriteable()` copies only that single ObjectState. COW granularity = per-object (not per-page).

**Complexity summary**:
| Operation | Concrete addr | Symbolic addr |
|---|---|---|
| Read byte | O(1) | O(k) k=symbolic writes |
| Write byte | O(1) | O(1) + UpdateList append |
| State fork | O(1) | O(1) |
| Address resolve | O(log n) | O(solver) + O(n) fork |
| Lookup object | O(log n) | O(solver) |

---

## 2. angr / claripy

### 2.1 Architecture: Mixin Stack

angr's memory is built from composable mixins. The stack (bottom to top):
```
PagedMemoryMixin          -- page-indexed dict storage
  UltraPage / ListPage    -- per-page data structure
AddressConcretizationMixin -- symbolic addr → concrete dispatch
SizeResolutionMixin        -- symbolic size handling
DataNormalizationMixin     -- type coercion
NameResolutionMixin        -- register name → offset
UnwrapperMixin             -- SimActionData unwrapping
```

### 2.2 PagedMemoryMixin

Core data structure:
```python
self._pages: Dict[int, Optional[PageType]]  # page_number → Page
```
Default `page_size = 0x1000` (4KB). Pages created lazily on first access.

**Load**: `_divide_addr(addr)` → `(page_num, page_offset)`. Single-page reads go directly to page. Multi-page reads iterate and concatenate via `_compose_objects()`.

**Store**: `_decompose_objects()` splits data across page boundaries. Each page write calls `_get_page(writing=True)` which triggers copy-on-write via `page.acquire_unique()`.

**Copy-on-write**: shallow copy of the page dict. Individual pages are shared until written.

### 2.3 UltraPage (Default Page Type)

Three parallel arrays per 4KB page:
```python
concrete_data: bytearray          # 4096 bytes, actual values
symbolic_bitmap: bytearray        # 4096 bytes, 0=concrete / nonzero=symbolic
symbolic_data: SortedDict         # offset → SimMemoryObject (sparse)
```

**Concrete read**: check `symbolic_bitmap[offset]` == 0 → return `concrete_data[offset]`. O(1).

**Symbolic read**: look up in `SortedDict` via `irange(offset, offset+size)`. O(log s) where s = number of symbolic entries in page.

**Write concrete**: `concrete_data[offset] = val`, `symbolic_bitmap[offset] = 0`. O(1).

**Write symbolic**: set bitmap flags, remove overlapping SortedDict entries, insert new SimMemoryObject. O(log s).

**Copy**: `bytearray(self.concrete_data)` + `bytearray(self.symbolic_bitmap)` + `SortedDict(self.symbolic_data)`. O(4096 + s).

### 2.4 Symbolic Address Handling

`AddressConcretizationMixin` — when address is symbolic:

1. Query concretization strategies in order (read_strategies / write_strategies)
2. Strategy returns list of concrete addresses satisfying constraints
3. For each concrete address, perform concrete read/write
4. Merge results with ITE chain: `solver.If(addr == a1, val1, solver.If(addr == a2, val2, ...))`

Default write strategy: concretize to max solution (unless `MultiwriteAnnotation` present, then enumerate up to 128 solutions).

**ITE chain construction** for reads:
```python
result = DUMMY
for concrete_addr in concrete_addrs:
    sub_val = super().load(concrete_addr, ...)
    result = solver.If(addr == concrete_addr, sub_val, result)
```

### 2.5 MultiValues (Abstract Interpretation)

Used in angr's static analysis (not DSE). Each byte position can hold a SET of values:
```python
class MultiValues:
    _single_value: Optional[claripy.ast.Bits]     # fast path: one value at offset 0
    _values: Dict[int, Set[claripy.ast.Bits]]      # general: offset → {possible values}
```

**Merge**: union of value sets at each offset. O(m + k).

**Concat**: append with offset adjustment. O(p) where p = entries.

### 2.6 State Merging

When merging two ExecutionStates:
1. Clone one state as the merge target
2. Scan entire address space byte-by-byte
3. For each differing byte: construct `If(merge_flag, val_state1, val_state2)`
4. `claripy.ite_cases()` builds multi-way conditionals for addresses with differences

This is O(address_space_size) in the worst case, mitigated by page-level identity checks (skip pages that are reference-equal).

**Complexity summary**:
| Operation | Concrete addr | Symbolic addr |
|---|---|---|
| Read byte | O(1) | O(solver) + O(k * log s) |
| Write byte | O(1) or O(log s) | O(solver) + O(k * log s) |
| State fork | O(pages) shallow | O(pages) shallow |
| State merge | O(pages) fast-path | O(address_space) worst |
| Page copy | O(4096 + s) | -- |

---

## 3. Triton

### 3.1 Dual Memory Model

**Bitvector mode (default, QF_BV)**:
```cpp
std::unordered_map<uint64_t, SharedSymbolicExpression> memoryBitvector;
```
Flat hash map: concrete address → symbolic expression (SSA form). Every memory access is at a concretized address. No array theory involved.

**Array mode (MEMORY_ARRAY, QF_ABV)**:
```cpp
SharedSymbolicExpression memoryArray;  // single SMT array: (Array (BitVec 64) (BitVec 8))
```
All loads become `select()`, all stores become `store()` operations on this single array. Enables symbolic pointer reasoning but consumes significant RAM due to SSA chain growth.

### 3.2 Memory Operations (Bitvector Mode)

**Read multi-byte**: for each byte in range, look up `memoryBitvector[addr+i]`. If present, use the symbolic expression. If absent, read from concrete memory and wrap as `bv(val, 8)`. Concatenate bytes via `concat()`.

**Write multi-byte**: decompose into bytes via `extract()`. Store each byte's expression in `memoryBitvector[addr+i]`. Also write to concrete memory.

**Symbolic addresses**: NOT supported in bitvector mode. All addresses are concretized before lookup.

### 3.3 Memory Operations (Array Mode)

**Read**: `concat(select(M, addr), select(M, addr+1), ...)` where M is the current array state.

**Write**: `M' = store(store(M, addr, byte0), addr+1, byte1)` -- sequential stores creating new array state.

**Symbolic addresses**: fully supported. `select(M, symbolic_addr)` is valid SMT.

### 3.4 Concrete Memory

Separate `ConcreteMemory` class: raw byte storage (`std::unordered_map<uint64_t, uint8_t>` or direct mmap). Used for concrete execution alongside symbolic tracking.

### 3.5 Snapshot/Restore

Simple list-based: `[(addr, old_byte), ...]`. On snapshot, record bytes before mutation. On restore, replay in reverse. O(n) where n = mutations since snapshot.

**Complexity summary (bitvector mode)**:
| Operation | Complexity |
|---|---|
| Read byte | O(1) hash lookup |
| Write byte | O(1) hash insert |
| Multi-byte read | O(w) for w bytes |
| State copy | O(m) where m = symbolic entries |
| Snapshot/restore | O(n) mutations |

---

## 4. Crucible (Galois)

### 4.1 Write Log Architecture

Crucible's LLVM memory model is fundamentally different: memory is an append-only log of writes. No random-access array.

**LLVMPointer**: `(blockId: SymNat, offset: SymBV)` -- both components can be symbolic.

**Mem**: the global write log. Contains:
- List of allocations (each with unique block ID, size, mutability, alignment)
- Chronological write log entries
- Branch merge markers

### 4.2 Allocation Model

Each allocation is completely isolated. No pointer arithmetic can cross allocation boundaries. Block IDs are unique natural numbers. This models C's "provenance" semantics.

### 4.3 Two Write Modes

**doStore (Haskell-side resolution)**:
- Offset calculations resolved in Haskell
- Appends a write record: `(blockId, offset, storedType, value)`
- Reads scan backward through the log until the read range is fully covered
- Each write record checked: does it overlap the read range? If so, extract relevant bytes.

**doArrayStore (SMT array delegation)**:
- Initializes an allocation with an SMT array
- All offset calculations pushed to SMT `select`/`store`
- Better for symbolic offset patterns

### 4.4 Read Resolution

Reads traverse the write log backward:
1. For each write record: check if block IDs could match (SMT query if symbolic)
2. Check if offset ranges overlap
3. If write fully covers read: return value (possibly with extract)
4. If write partially covers read: split into covered and uncovered sub-reads
5. Continue backward for uncovered portions
6. If end of log reached for an allocation: return default (zero or symbolic)

**Symbolic pointer reads**: multiplexed across ALL allocations. For each allocation, perform the read, then build ITE: `If(blockId == alloc1, read_from_alloc1, If(blockId == alloc2, ...))`. Expensive.

### 4.5 memcpy/memset with Symbolic Length

Crucible has special handling: these generate single write-log entries that represent the range `[offset, offset+len)` where len can be symbolic. Read resolution handles the symbolic overlap checks via SMT queries.

### 4.6 Branch Merging

At control-flow merge points, the write log records a merge marker. Reads through a merge must check both branches' writes.

**Complexity**:
| Operation | Complexity |
|---|---|
| Write | O(1) append |
| Read (best) | O(1) last write matches |
| Read (worst) | O(W) scan all writes |
| Symbolic pointer read | O(W * A) W=writes, A=allocations |
| State fork | O(1) append merge marker |
| memcpy symbolic len | O(1) write, O(solver) read |

---

## 5. SAW (Software Analysis Workbench)

### 5.1 Relationship to Crucible

SAW uses Crucible's memory model for LLVM analysis. The memory model is identical to section 4 above. SAW adds a verification specification layer on top.

### 5.2 Term Representation

SAW translates programs to **SAWCore** terms -- a purely functional dependently-typed intermediate language. Memory operations become functional transformations:
- `store(mem, ptr, val)` → new `mem'` term
- `load(mem, ptr, type)` → value term + side conditions

### 5.3 Verification Backend

SAWCore terms can be compiled to:
- **AIG (And-Inverter Graphs)**: for SAT-based equivalence checking via ABC
- **SMT formulas**: for SMT solvers (Yices, Z3)
- **Cryptol terms**: for specification comparison

### 5.4 Memory Constraints

SAW requires fixed-size data: no unbounded loops, no dynamic allocation of unknown size. Programs are fully unrolled. This means the memory model never faces truly unbounded symbolic ranges.

### 5.5 Specification-Level Memory

SAW's `llvm_alloc` / `llvm_alloc_sym_init`:
- Create isolated memory blocks for verification
- `llvm_alloc_sym_init` fills with symbolic bytes (every byte is a fresh symbolic variable)
- Preconditions specify what's in memory before execution
- Postconditions specify what must be in memory after

---

## 6. MEMSIGHT (Novel Approach)

### 6.1 Paged Interval Tree

MEMSIGHT avoids concretization entirely. Data structure:

**MemoryItem**: `(addr, value, timestamp, guard)` where addr can be symbolic.

**Two-level storage**:
1. **Concrete memory** (`PagedMemory`): dict of pages → dict of offsets → MemoryItem. For concrete addresses.
2. **Symbolic memory** (`PITree`): paged interval tree. Primary tree indexes page ranges; secondary trees within each page hold MemoryItems.

### 6.2 Fully Symbolic Read

```python
min_addr, max_addr = solver.minmax(symbolic_addr)
P = concrete_memory.find(min_addr, max_addr)
P += symbolic_memory.search(min_addr, max_addr)
# filter by timestamp, build ITE chain
result = build_merged_ite(P, addr)
```

### 6.3 Timestamp Ordering

Every write increments a global timestamp. Reads filter items by recency. Multiple items at the same address with different guards coexist; the read builds ITE over all valid items ordered by timestamp.

### 6.4 Complexity

| Operation | Concrete addr | Symbolic addr |
|---|---|---|
| Write | O(1) page + O(log n) PITree | O(log n) PITree |
| Read | O(1) | O(log n) search + O(k) ITE build |
| State merge | O(pages) + O(items) | same |

---

## 7. Comparative Analysis

### 7.1 Memory Representation Strategies

| Tool | Representation | Granularity | Symbolic Addrs |
|---|---|---|---|
| KLEE | ImmutableMap + byte arrays + UpdateList | per-byte | fork on all resolutions |
| angr | Page dict + UltraPage (bytearray + SortedDict) | per-byte | concretize + ITE |
| Triton (BV) | unordered_map addr→expr | per-byte | concretize only |
| Triton (ABV) | single SMT array | per-byte | native SMT select/store |
| Crucible | append-only write log | per-write | mux across allocations |
| SAW | Crucible + SAWCore terms | per-write | fixed layouts only |
| MEMSIGHT | paged interval tree + page dict | per-byte | native interval search |

### 7.2 What Makes Them Fast

**KLEE**: concrete fastpath dominates. Programs are mostly concrete; the concreteMask/concreteStore avoids ANY Expr allocation for concrete bytes. ImmutableMap enables O(1) fork.

**angr**: UltraPage's `bytearray` for concrete data is cache-friendly. SortedDict for symbolic entries is sparse. Page-level COW avoids copying untouched pages.

**Triton**: `unordered_map` gives O(1) lookup. No page overhead. Simple and fast for dynamic analysis where addresses are always concrete.

**Crucible**: write log append is O(1). Short logs (common in bounded verification) make reads fast. SMT array delegation avoids Haskell-side pointer arithmetic.

### 7.3 What Makes Them Slow

**KLEE**: symbolic addresses force solver queries + state forking. UpdateList scan is O(k) per read after symbolic writes. State explosion from forking.

**angr**: state merging scans entire address space. Symbolic addresses need solver + O(k) ITE construction. UltraPage copy is O(4096) per touched page.

**Triton (ABV)**: SSA chain of store/select grows without bound. Solver queries become enormous. RAM consumption proportional to total memory operations.

**Crucible**: read resolution is O(W) in write log length. Symbolic pointers multiply by O(A) allocations. Long-running programs accumulate huge write logs.

**MEMSIGHT**: ITE chains grow with total writes to overlapping ranges. Interval tree operations have log overhead even for concrete addresses.

### 7.4 Key Design Insights

1. **Separate concrete/symbolic storage**: KLEE's concreteMask, angr's UltraPage bitmap, Triton's dual map. The concrete path must be allocation-free and branch-free.

2. **Immutable/persistent structures for state forking**: KLEE's ImmutableMap, angr's shallow page dict copy. Fork = O(1) or O(pages), not O(memory_size).

3. **Byte-level independence**: all tools decompose multi-byte operations to per-byte. Avoids complex overlap logic at the cost of ConcatExpr/ExtractExpr proliferation.

4. **Deferred SMT encoding**: KLEE's unflushedMask delays UpdateList materialization. Crucible's write log defers read resolution. Galois's lazy memory model defers array initialization. Avoid solver work until absolutely necessary.

5. **Concretization as pragmatic default**: angr, Triton, and even KLEE prefer concrete addresses. Fully symbolic memory (MEMSIGHT) is more precise but slower. The practical tradeoff favors concretization with symbolic fallback.
