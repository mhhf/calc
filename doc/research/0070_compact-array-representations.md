---
title: "Compact Array/Sequence Representations Across Paradigms"
created: 2026-03-02
modified: 2026-03-02
summary: "Survey of array and sequence representations in SMT solvers, proof assistants, CHR, EVM symbolic executors, logic programming, and functional languages — design patterns for compact array literals in linear logic."
tags: [research, data-structures, array-theory, memory-model, smt, evm, linear-logic, performance, implementation, symbolic-execution, persistent-data-structure]
category: "Performance"
---

# Compact Array/Sequence Representations Across Paradigms

## 1. SMT Solvers: Theory of Arrays (Z3, CVC5)

### McCarthy Axioms (select/store)

The standard SMT array theory rests on two axioms:

```
select(store(A, i, v), i) = v                    (read-over-write-hit)
i != j => select(store(A, i, v), j) = select(A, j) (read-over-write-miss)
```

Z3 represents arrays as function spaces. Core operations:

- **`select(A, i)`** -- read index i
- **`store(A, i, v)`** -- new array identical to A except position i holds v
- **`const(v)`** -- array mapping all indices to v; `select(const(v), i) = v`
- **`map(f, A1, ..., An)`** -- pointwise function application
- **`as-array(f)`** -- lift function declaration to array sort
- **`Lambda(j, body)`** -- anonymous array constructor; `store(A,i,v) = Lambda(j, If(i==j, v, A[j]))`

**Extensionality** (default in Z3): two arrays equal iff they agree on all reads.

The decision procedure reduces array terms to EUF (equality with uninterpreted functions) by saturating with beta-reduction axioms. Satisfiability remains NP-complete for the decidable fragment.

### CVC5: Theory of Sequences

CVC5 extends beyond arrays with a theory of sequences, modeling `List` / `std::vector`:

- Sequences have **dynamic length** (arrays have fixed domain sort)
- Operations: concatenation, subsequence, read (`nth`), update, reverse, length, contains
- Hybrid solver: array-style axioms for read/update + string-solving algorithms for concatenation/subsequence

Key insight: **sequences unify array random access with list concatenation**. The solver combines two paradigms rather than choosing one.

### Relation to Linear Logic

CALC's write-log memory model (`mem (write Offset Value Prev)`) is structurally identical to the `store` chain in McCarthy's axioms. The `!mem_read` persistent predicate implements `select`. The correspondence:

| SMT Array | CALC ILL |
|-----------|----------|
| `store(A, i, v)` | `mem (write i v A)` |
| `select(A, i)` | `!mem_read A i V` |
| `const(0)` | `mem empty_mem` |
| extensionality | not applicable (linear consumption) |

The difference: SMT arrays are values in a satisfiability problem; CALC arrays are linear resources consumed and produced by forward rules. Linear logic naturally prevents aliasing -- no extensionality axiom needed.

**Design pattern: write-log chains.** Both SMT and CALC use the same functional update representation. The open question is whether a compact literal could short-circuit the chain for known-at-compile-time sequences (e.g., bytecode).

## 2. Proof Assistants: Primitive Arrays (Coq, Lean, Agda)

### Coq: PArray (Persistent Arrays)

Coq axiomatizes primitive persistent arrays:

```coq
Primitive array := #array_type.
Primitive get := #array_get.     (* t.[i]       *)
Primitive set := #array_set.     (* t.[i <- a]  *)
Primitive make := #array_make.
Primitive length := #array_length.
```

Axioms (must be trusted):
- `get_set_same`: `(set a i v).[i] = v`
- `get_set_other`: `i != j => (set a i v).[j] = a.[j]`

**Runtime optimization:** One version of the array holds native OCaml storage; other versions store modification lists (deltas). The system dynamically switches which version is "current," replaying deltas on access. This gives O(1) for the actively-used version while maintaining semantic persistence.

This is Baker's "shallow binding" technique (1991): the most recently accessed version occupies the flat representation, and older versions become chains of undo patches.

### Lean 4: Reference-Counted Destructive Update

Lean takes a different approach: `Array` and `ByteArray` are logically immutable but the runtime mutates in-place when the reference count is 1.

- `Array.set` checks the object header's refcount
- Refcount 1 => destructive update (no allocation)
- Refcount > 1 => copy-on-write
- `ByteArray` is a packed byte buffer (not `Array UInt8`)
- Compiler replaces `ByteArray.append` with `ByteArray.fastAppend`

**Key paper:** "Counting Immutable Beans" (Ullrich & de Moura, 2019) -- reference counting gives "functional but in-place" (FBIP) semantics. Linear usage patterns (which linear logic guarantees) always get O(1) updates.

### Agda: Builtin List + Extraction

Agda's `BUILTIN LIST` binding lets the GHC backend compile `List` to Haskell lists. `Vec A n` (length-indexed) shares constructor tags with `List` so conversion is a no-op when tags align. No primitive array type; relies on extraction pragmas to target efficient host representations.

### Design Pattern: Semantic/Operational Split

All three systems maintain a clean semantic model (persistent / functional) while using runtime tricks for efficiency:

| System | Semantic Model | Runtime Trick |
|--------|---------------|---------------|
| Coq PArray | persistent functional array | shallow binding / delta chains |
| Lean Array | immutable value | refcount-1 destructive update |
| Agda Vec | inductive type | extraction to host arrays |

**Relevance to CALC:** CALC's content-addressed store already hash-conses terms. A compact array literal could be a single hash pointing to a flat buffer, with `mem_read` FFI doing O(1) indexed lookup on the buffer -- semantic model unchanged (write-log chain), operational model short-circuited.

## 3. CHR and Array Constraints

CHR (Constraint Handling Rules) represents arrays as constraints in a multiset store, matching CALC's architecture:

- **De Angelis et al. (2017)**: "Program Verification using CHR and Array Constraint Generalizations" -- encodes McCarthy array axioms as CHR rules for program verification
- Array read/write become CHR constraints; simpagation rules implement the axioms
- Generalization operators (widening, convex hull) abstract over array contents for invariant inference

CHR's constraint store is a multiset of atomic constraints -- structurally identical to CALC's linear fact set. CHR simpagation (`kept \ removed <=> guard | body`) maps directly to ILL forward rules with persistent/linear antecedents.

**Design pattern:** Arrays as constraints, not values. Rather than a single array "object," the array's contents are scattered as individual `element(Array, Index, Value)` constraints. This is precisely what CALC does with `mem (write Offset Value Prev)` -- but the cons-chain representation makes sequential access O(n) where n is the write count.

## 4. EVM Symbolic Execution Tools

### hevm: Expr GADT with Write History

hevm represents memory/storage as expression trees preserving full write history:

```haskell
data Expr (a :: EType) where
  ConcreteBuf :: ByteString -> Expr Buf    -- concrete bytes, zeros past end
  AbstractBuf :: Text -> Expr Buf          -- fully symbolic
  WriteByte   :: Expr EWord -> Expr Byte -> Expr Buf -> Expr Buf
  CopySlice   :: Expr EWord -> Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf -> Expr Buf
  WriteWord   :: Expr EWord -> Expr EWord -> Expr Buf -> Expr Buf
  ReadByte    :: Expr EWord -> Expr Buf -> Expr Byte
  ...
```

Key optimizations:
- **Concrete fast path:** When all state is concrete, uses `ST` monad for in-place mutable `ByteString`
- **Expression simplification:** Concrete subexpressions reduced eagerly
- **Storage decomposition (from halmos):** Analyzes access patterns to reconstruct Solidity storage layout, assigns separate SMT arrays per logical region, eliminates Keccak from SMT queries

### halmos: Storage Layout Recovery

halmos pioneered analyzing `SHA3(slot || key)` patterns to infer the high-level Solidity storage layout. This converts a single flat `2^256`-slot array into multiple named arrays (one per mapping/dynamic array), dramatically reducing SMT complexity.

### KEVM: K Framework Rewriting

KEVM uses K's configuration cells with rewriting rules. Memory is a map in the configuration; K's matching/rewriting handles read/write. The advantage is that the formal semantics are directly executable -- no separate "model" vs "implementation."

### Design Pattern: Dual Representation

hevm's `ConcreteBuf` vs `WriteByte` chain shows the core pattern:

- **Known data** (e.g., deployed bytecode): flat `ByteString`, O(1) indexed access
- **Symbolic/modified data**: write-log chain, resolved by SMT

CALC currently uses write-log chains for everything, including the 1040-byte bytecode that is fully known at load time. A compact representation would let CALC do what hevm does: flat buffer for concrete data, write-log for symbolic modifications.

## 5. Logic Programming: Lazy Lists and Compact Sequences

### Prolog: Difference Lists

Difference lists represent a list as the difference between two lists, with an unbound tail:

```prolog
% [1,2,3] as difference list: [1,2,3|Xs] - Xs
append_dl(Xs-Ys, Ys-Zs, Xs-Zs).  % O(1) append via unification
```

O(1) append vs O(n) for regular lists. Widely used for efficient list construction in Prolog.

### Prolog: Lazy Streams

Tarau (2019), "Lazy Stream Programming in Prolog": lazy lists look like regular Prolog lists but elements are computed on demand. Two isomorphic representations:
- Abstract stream API (state + step function)
- Lazy lists compatible with existing list predicates

### SWI-Prolog: Global Arrays

SWI-Prolog provides `nb_setarg/3` for destructive assignment (non-backtrackable) and global arrays via `nb_setval/nb_getval`. These break logical purity but give O(1) access for performance-critical code.

### Mercury: Tabling

Mercury uses tabling (memoization) for expensive computations. Arrays can be simulated via tabled predicates: `array_elem(Array, Index, Value)` with tabling caches results. The pure-logic interface hides the imperative implementation.

### Design Pattern: Indexed Predicate as Array

In logic programming, an array `A[0..n]` can be represented as:

```prolog
elem(a, 0, v0).
elem(a, 1, v1).
...
elem(a, n, vn).
```

This is O(n) lookup without indexing, but first-argument indexing on `Index` gives O(log n) or O(1). CALC's `code` facts (`code PC Op`) are exactly this pattern. The question is whether 1040 individual `code` facts can be replaced by a single compact term with FFI-accelerated lookup.

## 6. Functional Languages: Bridging Lists and Arrays

### Haskell: Stream Fusion (vector package)

The `vector` package bridges cons-lists and flat arrays via stream fusion:

```haskell
data Step s a = Yield a s | Skip s | Done

data Stream a = forall s. Stream (s -> Step s a) s
```

Operations (`map`, `filter`, `fold`) are defined on `Stream`, not on arrays. GHC's optimizer fuses chains of operations, eliminating intermediate structures. The final result materializes as a flat array.

**Bundle abstraction:** A "bundle of streams" where each stream targets a different representation. The compiler statically selects the optimal one. Zero runtime cost -- all intermediate `Bundle` structures are eliminated.

### Clojure: Persistent Vectors (HAMT / RRB-Trees)

Clojure vectors use Hash Array Mapped Tries (HAMT) with branching factor 32:
- O(log32 n) lookup, update, append
- Structural sharing between versions
- RRB-Trees (Relaxed Radix Balanced) add O(log n) concatenation and slicing

### Futhark: Uniqueness Types for In-Place Arrays

Futhark uses uniqueness types (dual to linear types): a unique array reference guarantees no aliasing, enabling in-place update. The `with` expression `a with [i] = v` is O(|v|) not O(|a|) when `a` is unique.

### Baker's Shallow Binding (1991)

Key insight: the "trailer" technique for persistent functional arrays is shallow binding in disguise. Keep the current version in a flat array; older versions store undo patches. Single-threaded (linear) usage is O(1) per operation.

**Comparison with Coq PArray:** Coq implements exactly Baker's technique. The operational semantics match: the most-recently-accessed version occupies the flat buffer, others chain through deltas.

### Design Pattern: Representation Switching

| Access Pattern | Best Representation |
|---------------|-------------------|
| Sequential construction, then frozen | Flat array (build once, read many) |
| Random update + read | Baker/PArray (shallow binding) |
| Symbolic/partial | Write-log chain (SMT-friendly) |
| Fusion pipeline | Stream (no materialization) |

## 7. Design Patterns for CALC

### Pattern A: Compact Bytecode Literal

**Problem:** EVM bytecode is 1040 bytes, loaded as ~1040 individual `code PC Op` linear facts. Each fact is consumed and re-produced by every opcode rule.

**Solution:** A single `bytecode(Buffer)` linear fact where `Buffer` is a content-addressed reference to a flat byte array in the Store. An FFI-accelerated `!code_at` persistent predicate does O(1) indexed lookup.

**Analogy:** hevm's `ConcreteBuf ByteString`. The bytecode never changes during execution -- it's read-only data encoded as a linear resource for consumption tracking, but the data itself is static.

### Pattern B: Hybrid Write-Log + Flat Base

**Problem:** EVM memory starts empty and accumulates writes. Currently `mem (write Offset Value Prev)` chains can grow long, making `mem_read` traversal O(writes).

**Solution:** Two-level representation:
1. **Base:** flat array (for concrete initial state or checkpointed state)
2. **Overlay:** write-log chain (for recent modifications)

`mem_read` checks the overlay first (most recent writes), falls through to O(1) base lookup. Periodically "compact" the overlay into the base.

**Analogy:** LSM-trees (memtable + SSTable), Baker's shallow binding, Coq PArray.

### Pattern C: Sequence Theory Integration

**Problem:** CALC uses cons-lists for sequences (e.g., stack `s (push Value Rest)`). Operations like "reverse" or "take N" are O(n) traversals.

**Solution:** Introduce a sequence sort (inspired by CVC5's theory of sequences) with concat, subsequence, length as native operations. FFI implements them on flat arrays; the logic-level representation remains a sequence term.

### Pattern D: Indexed Predicate Compression

**Problem:** N individual `pred(i, v_i)` facts occupy N Store entries + N FactSet slots.

**Solution:** A single `pred_table(PackedData)` fact. The `PackedData` is a Store entry referencing a typed array. FFI-backed persistent predicates do O(1) lookup. At the logic level, `!pred(I, V)` backward clauses resolve to FFI calls against the packed data.

**Analogy:** Database column stores, Prolog first-argument indexing over asserted facts.

## References

- Baker, H.G. (1991). "Shallow Binding Makes Functional Arrays Fast." SIGPLAN Notices 26(8).
- Bagwell, P. & Rompf, T. (2011). "RRB-Trees: Efficient Immutable Vectors." ICFP.
- Bjorner, N. & de Moura, L. "Programming Z3." https://theory.stanford.edu/~nikolaj/programmingz3.html
- Coutts, D. et al. (2007). "Stream Fusion: From Lists to Streams to Nothing at All."
- De Angelis, E. et al. (2017). "Program Verification using CHR and Array Constraint Generalizations." Fundamenta Informaticae 150(1).
- Hojjat, H. et al. (2022). "Reasoning About Vectors using an SMT Theory of Sequences." IJCAR.
- Moskal, M. et al. (2024). "Hevm, a Fast Symbolic Execution Framework for EVM Bytecode." CAV.
- Tarau, P. (2019). "Lazy Stream Programming in Prolog." arXiv:1907.11354.
- Ullrich, S. & de Moura, L. (2019). "Counting Immutable Beans." arXiv:1908.05647.
- Z3 Guide: Arrays. https://microsoft.github.io/z3guide/docs/theories/Arrays/
- CVC5 Blog: Theory of Sequences. https://cvc5.github.io/2024/02/15/sequences-theory.html
- Coq Reference: Primitive Objects. https://rocq-prover.org/doc/V8.18.0/refman/language/core/primitive.html
- Lean 4 Reference: Arrays. https://lean-lang.org/doc/reference/latest/Basic-Types/Arrays/
