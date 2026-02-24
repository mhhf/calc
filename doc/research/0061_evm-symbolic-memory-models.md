---
title: "EVM Symbolic Memory Models -- Survey of Approaches"
created: 2026-02-24
modified: 2026-02-24
summary: "Technical survey of how EVM symbolic executors model memory: hevm write-chain buffers, KEVM rewrite rules, Mythril/Manticore/Halmos SMT encodings, and connections to linear logic and separation logic"
tags: [evm, symbolic-execution, memory-model, smt, z3, array-theory, hevm, kevm, mythril, manticore, halmos, separation-logic, linear-logic]
category: "Symbolic Execution"
---

# RES_0061: EVM Symbolic Memory Models -- Survey of Approaches

## 1. EVM Memory Semantics (Yellow Paper)

EVM memory is a volatile, byte-addressable, zero-initialized array that expands on demand.

**Properties:**
- **Byte-addressable**: each address indexes a single byte
- **Word-aligned operations**: MLOAD/MSTORE read/write 32 bytes (256-bit words) at a byte offset
- **MSTORE8**: writes a single byte
- **Zero-initialized**: all locations are implicitly 0
- **Dynamic expansion**: no fixed size limit; accessing offset `n` grows memory to `ceil((n+32)/32)` words
- **Gas cost**: `memory_cost = (words^2)/512 + 3*words` -- linear for small memory, quadratic for large

**Key operations:**
| Opcode | Stack | Effect |
|--------|-------|--------|
| MLOAD | `[offset]` -> `[value]` | Read 32 bytes at offset |
| MSTORE | `[offset, value]` -> `[]` | Write 32 bytes at offset |
| MSTORE8 | `[offset, value]` -> `[]` | Write 1 byte at offset |
| MCOPY | `[dst, src, len]` -> `[]` | Copy `len` bytes from `src` to `dst` |
| MSIZE | `[]` -> `[size]` | Current memory size in bytes |

Memory is fresh per call frame (not persistent across transactions like storage).

## 2. hevm: Algebraic Write-Chain Buffers

hevm (Haskell, CAV 2024) uses a **purely algebraic** representation of memory as a term in a typed expression language.

### The Expr GADT (Buf type)

```haskell
data Expr (a :: EType) where
  -- Base buffers
  ConcreteBuf :: ByteString -> Expr Buf       -- concrete bytes; reads beyond length return 0
  AbstractBuf :: Text -> Expr Buf              -- fully symbolic, named for hashing

  -- Write operations (build chains)
  WriteByte  :: Expr EWord -> Expr Byte -> Expr Buf -> Expr Buf
  WriteWord  :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
  CopySlice  :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr Buf
  --            srcOff        dstOff        size          src          dst

  -- Read operations (traverse chains)
  ReadByte :: Expr EWord -> Expr Buf -> Expr Byte
  ReadWord :: Expr EWord -> Expr Buf -> Expr EWord

  -- Metadata
  BufLength :: Expr Buf -> Expr EWord
```

### Write-Chain Architecture

A `Buf` expression accumulates all historical writes as nested constructors. MSTORE at offset `o` with value `v` into memory `m` produces `WriteWord o v m`. Multiple writes to the same location are valid -- only the outermost (most recent) write is relevant.

**Example:** After `MSTORE 0x00 0xAA` then `MSTORE 0x20 0xBB` on empty memory:
```
WriteWord 0x20 0xBB (WriteWord 0x00 0xAA (ConcreteBuf ""))
```

**Read resolution:** `ReadWord offset buf` traverses the write chain from outermost to innermost, checking whether each write overlaps with the read region. If the offset is concrete and matches a write, the value is extracted directly. If symbolic, the read remains as an unresolved `ReadWord` term for the SMT solver.

### Local Context Principle

Each `ReadWord`/`ReadByte` term **contains a snapshot** of the buffer state at the time of the read. This makes the representation stateless -- all context needed to resolve a read is within the term itself. No external state lookup is needed during simplification or SMT encoding.

### Simplification (Before SMT)

hevm applies algebraic simplifications to buffer expressions before encoding to SMT:

- **simplifyReads**: removes irrelevant writes when reading from a buffer. If a `CopySlice` writes after the position being read, the `CopySlice` is stripped.
- **Constant folding**: concrete reads from `ConcreteBuf` are evaluated directly
- **Dead write elimination**: writes that are overwritten by later writes at the same offset
- **Out-of-range pruning**: reads/writes with provably non-overlapping ranges

### SMT Encoding

`assertProps` translates `Expr` and `Prop` into SMT-LIB2. Buffers become uninterpreted functions or arrays. The encoding is accurate but **uninterpreted functions are an empirical bottleneck** in SMT query execution.

**Key optimization**: storage access analysis reconstructs Solidity storage layout, collapsing hash-based slot computations into direct array accesses.

### Performance

hevm's eager exploration (build full execution tree, then query SMT only for postcondition checking) yields 0.08-0.1s on single-transaction benchmarks vs 1.6-3.4s for Manticore/Mythril.

## 3. KEVM: K Framework Rewrite Rules

KEVM formalizes EVM in the K framework using rewriting logic. Memory is a `Bytes` value in the `<localMem>` configuration cell.

### Rewrite Rules

```k
// MLOAD: read 32 bytes, push as word
rule <k> MLOAD INDEX => #asWord(#range(LM, INDEX, 32)) ~> #push ... </k>
     <localMem> LM </localMem>

// MSTORE: write 32-byte word
rule <k> MSTORE INDEX VALUE => . ... </k>
     <localMem> LM => LM [ INDEX := #padToWidth(32, #asByteStack(VALUE)) ] </localMem>

// MSTORE8: write single byte
rule <k> MSTORE8 INDEX VALUE => . ... </k>
     <localMem> LM => LM [ INDEX := (VALUE modInt 256) ] </localMem>
```

### Helper Functions

- `#range(LM, START, WIDTH)` -- extract `WIDTH` bytes starting at `START`
- `#asWord(bytes)` -- interpret byte sequence as 256-bit big-endian word
- `#padToWidth(N, bytes)` -- zero-pad byte sequence to `N` bytes
- `#asByteStack(value)` -- convert word to byte sequence
- `LM [ INDEX := BYTES ]` -- K's map/array update notation

### Symbolic Execution

K provides two backends: LLVM (concrete) and Haskell (symbolic). The rewrite rules work uniformly for both -- K's matching logic handles symbolic values transparently. Memory expansion tracked via `<memoryUsed>` cell with `#memoryUsageUpdate`.

### Strengths

- Rules serve as both executable specification and formal semantics
- Symbolic analysis via K's built-in reachability logic prover
- Same rules used for concrete testing, symbolic execution, and formal verification

## 4. Mythril: Python Lists to Z3 Arrays

Mythril (Python, Z3) evolved from concrete to symbolic memory.

### Old Model (Concrete Lists)

Memory was a Python `list` of bytes. MLOAD/MSTORE attempted to extract concrete byte values, failing on symbolic addresses.

### New Model (Z3 K-Arrays)

Refactored to use Z3's `K`-type arrays (arrays with default values):

- **Type**: Z3 Array from 256-bit bitvectors to 8-bit bitvectors
- **Auto-initialization**: default value 0 (matches EVM semantics)
- **Symbolic reads**: supported via `select` operations
- **Symbolic writes**: remained out of scope in the initial refactoring

**Architecture:** A `Memory` class wraps a Z3 K-array internally, exposing `__getitem__` for reads (individual indices and slices).

### Limitations

- Only Z3 supported (not Yices2, Boolector, etc.)
- Symbolic write support was deferred
- Array theory overhead for large memory regions

## 5. Manticore: Constraint-Based Symbolic Arrays

Manticore (Trail of Bits, Python) uses an SMT-LIB abstraction layer.

### Memory Representation

```python
self.memory = constraints.new_array(
    index_bits=256,    # 256-bit addresses
    value_bits=8,      # byte values
    name="EMPTY_MEMORY_...",
    default=0,         # zero-initialized
)
```

Memory is an 8-bit-value array with 256-bit indexing, matching EVM semantics exactly.

### Operations

- **MLOAD**: `memory.read_BE(offset, 32)` -- read 32 bytes big-endian
- **MSTORE**: `memory.write_BE(offset, value, 32)` -- write 32 bytes big-endian
- **MSTORE8**: `Operators.EXTRACT(value, 0, 8)` then single-byte write

### State Forking

When a memory address is symbolic:
- Concretize to possible values
- Fork execution state for each concrete value
- Each fork gets its own memory copy

Gas concretization: if gas fee becomes symbolic, Manticore forks on possible gas values.

### Taint Tracking

Memory operations propagate taint information. If the program counter is tainted (influenced by user input), writes are flagged.

## 6. Halmos: Bitvector Concat/Extract

Halmos (a16z, Python, Z3) wraps all EVM values as **Z3 bitvectors**.

### Core Strategy

Rather than Z3 arrays, Halmos uses bitvector operations:
- `Concat(bv1, bv2, ...)` -- concatenate bitvectors
- `Extract(high, low, bv)` -- extract bit range
- Zero-padding via `Concat(val, con(0, padding_bits))`

### Memory Operations

- `extract_bytes(data, offset, size_bytes)` -- extract bytes from bitvector, zero-pad if out of bounds
- `extract_word(data, offset)` -- extract 256-bit word at offset

The `Bytes` type is `Union[bytes, BitVecRef, ByteVec]` -- supporting concrete bytes, symbolic bitvectors, and a custom byte vector type.

### Optimizations

- Explicit quantifier instantiation to generate quantifier-free queries
- Alternative encoding of Z3 const arrays with SMT-LIB standard
- Storage layout reconstruction (idea originated in Halmos, adopted by hevm)
- Radically optimized EVM interpreter loop (up to 32x speedup)

## 7. SMT Array Theory for Memory

### McCarthy's Select/Store Axioms

The foundational theory for modeling memory in SMT solvers:

```
select(store(a, i, v), i) = v                           -- read-after-write (same index)
i ≠ j => select(store(a, i, v), j) = select(a, j)      -- read-after-write (different index)
(∀i. select(a, i) = select(b, i)) => a = b              -- extensionality
```

### Z3 Array Features

- **Constant arrays**: `(as const (Array T1 T2))` -- all indices map to same value (models zero-init)
- **Array map**: parameterized `map` for pointwise operations on array values
- **as-array**: convert function to array -- `(_ as-array f)` where `select(a, i) = f(i)`
- **Extensionality**: enforced by default -- equal-on-all-reads implies equal arrays

### Encoding Strategies (Performance-Critical)

From EPFL's systematic study of encoding symbolic expressions as solver queries:

| Encoding | Relative Performance |
|----------|---------------------|
| Arrays + assertion-based init | **1x (baseline)** |
| Arrays + nested write init | **50x slower** |
| If-then-else (ITE) encoding | **11x slower** |
| Incremental (assumptions) | **2.3x slower** |
| Portfolio (incr + non-incr) | **0.44x (2.25x faster)** |

**Critical finding**: initializing arrays via `store` chains is 50x slower than via assertions. Always use `(assert (= (select a i) v))` rather than `a = store(store(store(...), i1, v1), i2, v2)`.

**Theory configuration matters**: Z3 with `QF_ABV` (quantifier-free arrays + bitvectors) is dramatically faster than the default general-purpose strategy. Performance differences span two orders of magnitude.

### Lazy vs Eager Initialization

From Galois's work on machine code memory models:

- **Eager**: pre-populate entire memory as SMT array. A 1.8 MB binary took hours before simulation began.
- **Lazy**: populate 1024-byte chunks on demand. Simulation begins instantly.
- **Concrete bypass**: reads from immutable sections (`.rodata`) return raw bytes instead of going through SMT, avoiding unnecessary array operations.

## 8. SMT-Friendly Solidity Memory Formalization

Hajdu & Jovanovic (ESOP 2020) formalized Solidity's memory model for verification:

- **Mappings** → SMT arrays directly
- **Fixed/dynamic arrays** → same SMT type, different handling in statements/expressions
- **Memory arrays** → pointer-based: integers as pointers, separate heap associating pointers to array contents (`MemArrT` datatype)
- Implemented in solc-verify with extensive test validation

## 9. Separation Logic and Linear Logic Connections

Separation logic (Reynolds, O'Hearn) extends Hoare logic for reasoning about heap-manipulating programs. Its connectives map directly to linear logic:

| Separation Logic | Linear Logic | Semantics |
|-----------------|-------------|-----------|
| Separating conjunction `*` | Tensor `⊗` | Disjoint heap composition |
| Separating implication `-*` (magic wand) | Linear implication `⊸` (lollipop) | Heap extension/update |
| Classical conjunction `∧` | Additive conjunction `&` (with) | Shared/overlapping access |
| `emp` | Unit `1` | Empty heap |

### Frame Rule

The **frame rule** enables local reasoning: if `{P} C {Q}` and `C` does not touch resources in `R`, then `{P * R} C {Q * R}`. This is the computational analogue of the tensor's "no implicit sharing" property in linear logic.

### Memory Update as Linear Transformation

Separation logic supports **in-place updating of facts** that mirrors in-place update of memory during execution. A write `[addr] := v` transforms `addr ↦ old` to `addr ↦ v`, consuming the old fact and producing the new one -- exactly linear resource consumption.

### Symbolic Execution with Separation Logic

Berdine, Calcagno & O'Hearn developed symbolic execution adapted to separation logic:
- Symbolic heaps track the program's memory footprint
- Pointer dereference splits the assertion to isolate the accessed location
- Frame rule enables compositional, local analysis

## 10. Linear Logic for Mutable Memory

### Resource Interpretation of Memory

In linear logic's resource interpretation:
- A memory cell `addr ↦ v` is a **linear proposition** -- it exists exactly once
- Writing to a cell **consumes** the old proposition and **produces** a new one
- Reading a cell in a linear context requires the cell to be under `!` (bang/of course) for non-destructive access, or consumes it for destructive read

### Substructural Mutable References (Ahmed et al.)

Ahmed's step-indexed model of substructural state supports four kinds of mutable references:
- **Unrestricted**: standard references (can be freely copied)
- **Relevant**: must be used at least once
- **Affine**: can be used at most once (supports deallocation)
- **Linear**: must be used exactly once

The model supports:
- **Deallocation** of references (affine/linear refs can be freed)
- **Strong (type-varying) updates** (linear refs can change type on write)
- **Unique objects in shared references** (linear values stored in unrestricted refs)

### Destination-Passing Style

Pfenning & others developed **substructural operational semantics** where mutable store is modeled via linear destination-passing. State changes are explicit consumption and production of linear propositions representing memory cells.

## 11. Performance Considerations

### Path Explosion from Memory Aliasing

A symbolic address may reference **any** memory cell. If address `a` is symbolic:
- MLOAD at `a` must consider all possible concrete values of `a`
- Each value potentially yields a different execution path
- Approaches: concretize (lose paths), fork (exponential blowup), or keep symbolic (solver burden)

**MemSight approach**: maps symbolic address expressions to data (not address instances), maintaining alternative states in compact implicit form.

### Constraint Solving Overhead

- **Array theory**: Z3's array decision procedure uses lazy axiom instantiation. Deeply nested `store` chains create large terms.
- **Quantifier instantiation**: newer Z3 versions (4.8.17+) can get stuck on array+bitvector queries that worked in 4.8.4
- **Incremental mode penalty**: ~20% overhead from different solving strategy
- **Solution**: portfolio approach (parallel incremental + non-incremental) gives 2.25x speedup

### Write Chain Length

In hevm's algebraic model, long write chains degrade:
- Read resolution: O(n) traversal per read, where n is chain length
- Simplification: must check each write for overlap
- SMT encoding: deeply nested terms
- **Mitigation**: periodic simplification passes, concrete evaluation where possible

### Memory Leak with WriteWord

hevm issue #292 documented memory leaks from accumulating `WriteWord` constructors without garbage collection of superseded writes.

## 12. Design Implications for CALC

### How Linear Logic Naturally Models Memory

CALC's linear context already has the right structure:
- **Linear facts as memory cells**: `mem(addr, val)` is a linear proposition consumed on read/write
- **MSTORE as rule**: `mem(addr, old) ⊸ mem(addr, new)` -- consumes old, produces new
- **MLOAD as rule**: needs careful design -- either consuming (destructive read) or via `!` for non-destructive
- **Zero-initialization**: no explicit `mem` fact means zero (closed-world assumption)
- **Disjointness for free**: linear logic's no-implicit-contraction means each cell is naturally unique

### Comparison of Approaches

| Approach | Representation | Aliasing | Solver Load | CALC Fit |
|----------|---------------|----------|-------------|----------|
| hevm write-chain | Algebraic terms | Deferred to SMT | Medium (after simplification) | Good -- similar to proof terms |
| KEVM rewrite rules | K Bytes cells | Transparent via matching logic | Low (concrete) / High (symbolic) | Good -- similar to inference rules |
| Mythril Z3 arrays | SMT Array(BV256, BV8) | Direct SMT | High | Poor -- external solver dependency |
| Manticore constraint arrays | SMT arrays + forking | Fork on symbolic addr | Very high | Poor -- state explosion |
| Halmos bitvectors | Concat/Extract on BV | Bitvector reasoning | Medium | Medium -- different paradigm |
| **Linear facts** | `mem(addr, val)` propositions | Unique by linearity | None (internal) | **Native** |

### Key Insight

The hevm write-chain model is closest to what CALC should do, but CALC has a structural advantage: linear logic's resource semantics means memory aliasing is **impossible by construction** -- each `mem(addr, val)` fact exists exactly once in the linear context. There is no need for SMT aliasing reasoning. The challenge shifts to handling **symbolic addresses** (when `addr` is a metavariable) during pattern matching in the forward engine.
