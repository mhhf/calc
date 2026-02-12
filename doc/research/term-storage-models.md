# Term Storage Models: A Comparative Analysis

This document compares CALC's content-addressed term storage with the storage models used by major functional and logical programming languages.

---

## CALC's Model: Content-Addressed Store

**Architecture**: Global `Map<hash, {tag, children}>` with FNV-1a 32-bit hashing.

```javascript
// Core operations
function intern(tag, children) {
  const h = computeHash(tag, children);
  if (!STORE.has(h)) STORE.set(h, { tag, children });
  return h;
}

function get(h) { return STORE.get(h); }
const eq = (a, b) => a === b;  // O(1) equality
```

**Properties**:
| Property | Value |
|----------|-------|
| Write | O(1) amortized (hash + lookup + insert) |
| Lookup | O(1) hash table lookup |
| Equality | O(1) integer comparison |
| Sharing | Automatic maximal sharing |
| Persistence | In-memory only |
| Collision risk | ~77k items (birthday paradox @ 32-bit) |

**Children encoding**:
- `number`: hash reference to another term
- `string`: primitive (variable/atom names)
- `bigint`: compact numeric literals

---

## I. Haskell (GHC/STG Machine)

### Storage Model

GHC uses the **Spineless Tagless G-machine (STG)** with heap-allocated closures. No hash consing by default.

**Closure layout**:
```
┌─────────────┬──────────────────────┐
│ Info Pointer│ Payload (free vars)  │
└─────────────┴──────────────────────┘
```

**Key characteristics**:
- All values represented uniformly as closures
- Thunks (unevaluated computations) share same representation as values
- Lazy evaluation via self-updating thunks
- Pointer tagging: bottom 2-3 bits encode constructor/arity

**Closure types**:
| Type | Description |
|------|-------------|
| FUN | Function closure |
| CON | Constructor application (evaluated) |
| THUNK | Unevaluated suspension |
| PAP | Partial application |
| IND | Indirection (after thunk update) |

### Operations

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Allocation | O(1) | Bump pointer allocation |
| Read | O(1) | Direct pointer dereference |
| Equality | O(n) | Structural traversal (no default sharing) |
| GC | Generational | Stop-the-world, copying collector |

### Sharing

GHC does **not** hash-cons by default. Sharing occurs only via:
1. Let-binding (explicit sharing)
2. Common subexpression elimination (CSE) optimization
3. Thunk update (lazy evaluation creates sharing)

**Appel-Shao hash-consing GC** (1992): Optional technique combining copying GC with hash consing, achieving ~50% GC time reduction in SML/NJ compiler.

### Comparison with CALC

| Aspect | GHC | CALC |
|--------|-----|------|
| Default sharing | Explicit only | Automatic maximal |
| Equality | O(n) structural | O(1) hash compare |
| Memory overhead | Lower (no hash table) | Higher (global store) |
| Thunk support | Yes (lazy) | No (strict) |
| Mutable data | Supported | Not supported |

**Relevance**: GHC's model prioritizes lazy evaluation and general-purpose computation. CALC's model is optimized for proof search where term equality is critical.

---

## II. OCaml

### Storage Model

OCaml uses a **uniform tagged representation** with a copying garbage collector.

**Value encoding**:
```
┌─────────────────────────────────────┐
│ ... value data ...        │ tag bit │
└─────────────────────────────────────┘
                              └── 0 = pointer, 1 = integer
```

**Heap block layout**:
```
┌────────────────────────┬─────────────────────────┐
│ Header (1 word)        │ Payload (n words)       │
│ [size|color|tag]       │ [field₁|field₂|...|fieldₙ]│
└────────────────────────┴─────────────────────────┘
```

**Key characteristics**:
- Integers unboxed (63-bit on 64-bit systems)
- Booleans, unit, empty list stored as integers
- Tuples, records, arrays: tag 0 with fields as payload
- Variants: tag encodes constructor

### Hash Consing in OCaml

OCaml has a well-developed hash-consing ecosystem via libraries:

**`backtracking/ocaml-hashcons`**:
```ocaml
type +'a hash_consed = private {
  hkey: int;   (* cached hash *)
  tag : int;   (* unique id *)
  node: 'a;    (* actual data *)
}
```

Features:
- Weak hash table storage (allows GC of unreferenced terms)
- User-provided hash function for efficient recursive hashing
- O(1) equality via tag comparison
- Structural hash computed once at construction

**`fpottier/fix`**: Alternative with `Fix.HashCons` module.

### Operations

| Operation | Standard | With hashcons |
|-----------|----------|---------------|
| Allocation | O(1) | O(1) amortized |
| Equality | O(n) | O(1) |
| Memory | No sharing | Maximal sharing |

### Comparison with CALC

| Aspect | OCaml | CALC |
|--------|-------|------|
| Hash consing | Optional library | Built-in |
| Weak references | Yes (GC-friendly) | No |
| Tag bit scheme | Yes (unboxed ints) | No |
| Unique IDs | Separate from hash | Hash IS the ID |

**Insight**: OCaml's hashcons library architecture (weak tables, cached hashes) could inform CALC's evolution toward GC-friendly persistence.

---

## III. Standard ML

### Storage Model Variants

SML implementations diverge significantly:

**SML/NJ**: Generational GC, similar to OCaml
- Uniform representation with tag bits
- CPS-based intermediate representation
- Historical hash-consing GC research (Appel-Shao)

**MLKit**: Region-based memory management
```
┌────────────┐     ┌────────────┐
│ Region Desc│──→  │ Page 1     │──→ Page 2 ──→ ...
│ (on stack) │     │ [objects]  │
└────────────┘     └────────────┘
```

Features:
- Compile-time region inference predicts allocation lifetimes
- Stack-like region allocation/deallocation
- No runtime GC overhead for deterministic regions
- Pages (1KB-32KB) form linked lists per region

**MLton**: Traditional GC
- Whole-program optimization
- No regions (complexity vs. unclear benefits)

### Operations (MLKit)

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Allocate | O(1) | Bump pointer within region page |
| Deallocate | O(regions) | Pop region stack |
| Read | O(1) | Direct pointer |
| Equality | O(n) | Structural |

### Comparison with CALC

| Aspect | SML | CALC |
|--------|-----|------|
| Memory management | GC or regions | Manual/GC |
| Default sharing | None | Automatic |
| Region inference | MLKit only | Not applicable |
| Equality | O(n) | O(1) |

**Insight**: MLKit's region inference is orthogonal to hash consing but demonstrates static analysis can predict allocation patterns—potentially applicable to proof search contexts.

---

## IV. Prolog (Warren Abstract Machine)

### Storage Model

The WAM uses a **multi-area memory architecture** optimized for unification and backtracking.

**Memory areas**:
```
┌─────────────┐
│ Code Area   │ Compiled WAM instructions
├─────────────┤
│ Heap        │ Terms (structures, lists)
├─────────────┤
│ Stack       │ Environments, choice points
├─────────────┤
│ Trail       │ Variable bindings (for undo)
├─────────────┤
│ PDL         │ Push-down list (unification)
└─────────────┘
```

**Cell types** (tagged words):
| Tag | Name | Description |
|-----|------|-------------|
| REF | Reference | Unbound variable (points to self or binding) |
| STR | Structure | Compound term (functor/arity + args) |
| CON | Constant | Atoms, numbers |
| LIS | List | Cons cell (head + tail) |

**Term representation**:
```
Structure f(a, X):
  Heap[H]   = <STR, H+1>
  Heap[H+1] = f/2
  Heap[H+2] = <CON, a>
  Heap[H+3] = <REF, H+3>    ← unbound X
```

### Key Operations

**Dereferencing**: Follow REF chains to reach value
```
deref(addr):
  cell = heap[addr]
  while cell.tag == REF and cell.value != addr:
    addr = cell.value
    cell = heap[addr]
  return addr
```

**Unification**: Read/write mode dual execution
- Read mode: match existing structure
- Write mode: construct new terms

### Operations

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Allocate | O(1) | Increment heap pointer |
| Deref | O(binding chain) | Follow REF chain |
| Unify | O(term size) | Recursive descent |
| Backtrack | O(trail size) | Undo bindings |

### Comparison with CALC

| Aspect | WAM | CALC |
|--------|-----|------|
| Variables | Mutable REF cells | Immutable + substitution |
| Sharing | Via binding | Structural via hash |
| Backtracking | Trail-based undo | No built-in |
| Equality | Unification | O(1) hash |
| Structure | Flattened heap | Nested hash refs |

**Insight**: WAM's design optimizes for Prolog's operational semantics (unification, backtracking). CALC's content-addressing is inappropriate for mutable bindings but ideal for immutable proof terms.

---

## V. Coq

### Storage Model

Coq uses the **Calculus of Inductive Constructions (CIC)** with hash consing enabled since 1998.

**`Constr.t` type** (kernel terms):
```ocaml
type t =
  | Rel of int           (* de Bruijn index *)
  | Var of Id.t          (* named variable *)
  | Meta of metavariable
  | Evar of econstr
  | Sort of Sorts.t
  | Cast of t * cast_kind * t
  | Prod of Name.t * t * t
  | Lambda of Name.t * t * t
  | LetIn of Name.t * t * t * t
  | App of t * t array
  | Const of Constant.t * Instance.t
  | Ind of inductive * Instance.t
  | Construct of constructor * Instance.t
  | Case of case_info * Instance.t * t array * ...
  | Fix of fixpoint
  | CoFix of cofixpoint
  | Proj of Projection.t * t
  | Int of Uint63.t
  | Float of Float64.t
  | String of Pstring.t
  | Array of ...
```

### Hash Consing Implementation

From `kernel/constr.ml` comments:
- "Hash-consing by Bruno Barras in Feb 1998"
- Recent work (2025): "avoid recomputing hashes" optimization

**Strategy**:
- Hash subterms recursively
- Cache hash in term representation
- Use for fast equality in type checking
- Recent PR #13563: compact pattern-matching representation

### Operations

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Construction | O(subterms) | Hash computation |
| Equality | O(1) | Via hash |
| Type checking | O(term) | Uses fast equality |
| Reduction | O(term) | Hash-consed results |

### Comparison with CALC

| Aspect | Coq | CALC |
|--------|-----|------|
| Hash consing | Since 1998 | Built-in |
| Term representation | OCaml ADT | Hash → {tag, children} |
| Universe handling | Cumulative | None (yet) |
| De Bruijn | Yes | Yes (freevar/boundvar) |
| Proof terms | Yes | Building toward |

**Insight**: Coq's long experience with hash consing validates CALC's approach. Coq's recent optimizations (avoiding hash recomputation) suggest CALC should memoize hashes at construction time—which it already does.

---

## VI. Agda

### Storage Model

Agda uses a Haskell-based implementation with three syntax levels:

**Syntax progression**:
```
Concrete → Abstract → Internal
(user)     (pre-TC)   (checked)
```

**`Agda.Syntax.Internal.Term`**:
```haskell
data Term = Var   !Int Elims
          | Lam   ArgInfo (Abs Term)
          | Lit   Literal
          | Def   QName Elims
          | Con   ConHead ConInfo Elims
          | Pi    (Dom Type) (Abs Type)
          | Sort  Sort
          | Level Level
          | MetaV MetaId Elims
          | DontCare Term
          | Dummy String Elims
```

### Storage Characteristics

- De Bruijn indices for bound variables
- Beta-normal form maintained
- Metavariables for incremental elaboration
- No explicit hash consing (inherits GHC's representation)

### Operations

| Operation | Complexity | Notes |
|-----------|------------|-------|
| Construction | O(1) | GHC allocation |
| Equality | O(n) | Structural |
| Substitution | O(term) | De Bruijn adjustment |
| Type checking | O(term) | Bidirectional |

### Comparison with CALC

| Aspect | Agda | CALC |
|--------|------|------|
| Host language | Haskell | JavaScript |
| Hash consing | No | Yes |
| De Bruijn | Yes | Yes |
| Metavariables | Yes | Limited |
| Dependent types | Full | None |

**Insight**: Agda prioritizes dependent type checking over term sharing. CALC's domain (linear logic proof search) may benefit more from sharing.

---

## VII. Idris 2

### Storage Model

Idris 2 is **self-hosted** (written in Idris 2) with **Quantitative Type Theory (QTT)**.

**`Core.TT` term type**:
- Annotated with multiplicities (0, 1, ω)
- 0-multiplicity terms erased at runtime
- Compiles to Scheme, then native

**Multiplicities**:
| Multiplicity | Meaning | Runtime |
|--------------|---------|---------|
| 0 | Erased | Not present |
| 1 | Linear | Used exactly once |
| ω | Unrestricted | Used freely |

### Storage Characteristics

- QTT-aware elaboration and erasure
- Compiled representation discards erased terms
- Bootstrapped from Scheme

### Comparison with CALC

| Aspect | Idris 2 | CALC |
|--------|---------|------|
| Linearity | QTT multiplicities | Linear logic |
| Erasure | 0-multiplicity | Not yet |
| Self-hosting | Yes | No |
| Hash consing | No | Yes |

**Insight**: Idris 2's erasure of 0-multiplicity terms is relevant for CALC's potential optimization: erased terms need not be stored.

---

## VIII. Lean 4

### Storage Model

Lean 4 reimplemented the kernel in Lean itself with optimized expression representation.

**`Lean.Expr`**:
```lean
inductive Expr where
  | bvar   : Nat → Expr
  | fvar   : FVarId → Expr
  | mvar   : MVarId → Expr
  | sort   : Level → Expr
  | const  : Name → List Level → Expr
  | app    : Expr → Expr → Expr
  | lam    : Name → Expr → Expr → BinderInfo → Expr
  | forallE: Name → Expr → Expr → BinderInfo → Expr
  | letE   : Name → Expr → Expr → Expr → Bool → Expr
  | lit    : Literal → Expr
  | mdata  : MData → Expr → Expr
  | proj   : Name → Nat → Expr → Expr
```

### Hashing Strategy

**`Expr.Data`**: Cached metadata including hash
```lean
-- Hash computed at construction
-- mixHash with small primes per constructor
-- e.g., .const n lvls → mixHash 5 (mixHash (hash n) (hash lvls))
```

**Optimizations**:
- Literals for compact number/string storage
- Projections for efficient record access
- Compacted regions for serialization

### Comparison with CALC

| Aspect | Lean 4 | CALC |
|--------|--------|------|
| Hash caching | Yes | Implicit (hash IS ID) |
| Interning | Not traditional | Yes |
| Equality | Hash-assisted O(?) | O(1) |
| Serialization | Compacted regions | Not yet |

**Insight**: Lean 4's "compacted regions" for serialization suggest a path for CALC persistence.

---

## IX. Isabelle

### Storage Model

Isabelle/Pure uses ML (Poly/ML or SML/NJ) with sophisticated term representation.

**`Pure/term.ML`** (inferred from documentation):
- Terms, types, and theorems as ML datatypes
- Named theorem storage via functors
- Environment management via contexts

**Data structures** (`Pure/` directory):
- `alist.ML`: Association lists
- `graph.ML`: Directed graphs
- `table.ML`: Balanced trees (red-black)

### Storage Characteristics

- No documented default hash consing
- Sharing via explicit reference
- Sophisticated proof term compression

### Comparison with CALC

| Aspect | Isabelle | CALC |
|--------|----------|------|
| Hash consing | Unclear | Yes |
| Proof terms | Compressed | Not yet |
| Host language | ML | JavaScript |
| Theorem storage | Functors | None |

---

## X. Erlang/Elixir (BEAM VM)

### Storage Model

The BEAM VM uses a **process-isolated heap architecture** with message-passing concurrency. Each process has its own garbage-collected heap.

**Memory architecture**:
```
┌─────────────────────────────────────────────────┐
│                 Global Areas                     │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────┐  │
│  │ Atom Table  │  │ ETS Tables  │  │ Code    │  │
│  │ (never GC'd)│  │ (off-heap)  │  │ Area    │  │
│  └─────────────┘  └─────────────┘  └─────────┘  │
├─────────────────────────────────────────────────┤
│              Per-Process Areas                   │
│  ┌─────────────────────────────────────────┐    │
│  │ Process 1: Heap ←───────→ Stack         │    │
│  └─────────────────────────────────────────┘    │
│  ┌─────────────────────────────────────────┐    │
│  │ Process 2: Heap ←───────→ Stack         │    │
│  └─────────────────────────────────────────┘    │
└─────────────────────────────────────────────────┘
```

**Tagging system** (2-bit primary tags):
| Tag | Name | Description |
|-----|------|-------------|
| 00 | Header | Boxed value header |
| 01 | List | Cons cell pointer |
| 10 | Boxed | Pointer to heap object |
| 11 | Immediate | Small values in-word |

**Immediate subtypes**:
- Small integers (up to 60 bits on 64-bit)
- Atoms (index into global atom table)
- PIDs, ports
- NIL

**Boxed values** (larger structures):
```
┌────────────────────┬────────────────────────────┐
│ Header (1 word)    │ Payload (arity words)      │
│ [arity|tag]        │ [elem₁|elem₂|...|elemₙ]    │
└────────────────────┴────────────────────────────┘
```

### Atoms: Implicit Interning

Atoms in Erlang/Elixir are essentially **interned strings**:

```erlang
% Atoms are stored once in global atom table
:foo  % index 42
:foo  % same index 42 → O(1) equality via index comparison
```

**Properties**:
- Global atom table stores string content
- Each atom gets unique index (0, 1, 2, ...)
- Comparison is O(1) index comparison
- **Never garbage collected** (atoms are immortal)
- Limit: ~1M atoms per VM (configurable)

This is a form of **string interning**, analogous to hash consing but:
- Only for atoms, not general terms
- Index-based, not hash-based
- No deduplication of compound terms

### Storage Tiers

**1. Process Heap** (default):
- Private to each process
- Standard generational GC
- Data copied on message send

**2. ETS (Erlang Term Storage)**:
- Off-heap tables
- Shared between processes
- O(1) key lookup
- Data copied on read/write
- Owner process can control concurrent access

**3. Persistent Term**:
- Global immutable storage
- O(1) lookup without copying
- **No copy on read** (unlike ETS)
- Global GC scan on update/delete

```erlang
% Store once, read many (no copy)
persistent_term:put(config, #{debug => true}).
Config = persistent_term:get(config).  % Returns reference, not copy
```

### Operations

| Operation | Heap | ETS | persistent_term |
|-----------|------|-----|-----------------|
| Write | O(1) | O(1) | O(processes) global GC |
| Read | O(1) | O(1) + copy | O(1) no copy |
| Equality | O(n) structural | O(n) | O(n) |
| Sharing | Within process | None (copy) | Global reference |

### Data Copying Semantics

**Message passing**: All data copied except:
- Large binaries (reference counted, shared)
- Literals in compiled code
- persistent_term references

**ETS**: Full copy on insert and lookup (sharing lost)

```erlang
% Sharing lost when inserted into ETS
Shared = {1, 2, 3},
Tuple = {Shared, Shared},  % Shared in memory
ets:insert(Table, {key, Tuple}),
{key, Retrieved} = ets:lookup(Table, key),
% Retrieved has NO sharing - both copies of Shared
```

### Comparison with CALC

| Aspect | BEAM | CALC |
|--------|------|------|
| Interning | Atoms only | All terms |
| Sharing scope | Per-process | Global |
| Compound terms | Not deduplicated | Hash-consed |
| Equality | O(n) general, O(1) atoms | O(1) all |
| Concurrency | Process isolation | Single-threaded |
| GC | Per-process | Manual/none |
| Persistence | persistent_term | Not yet |

### Insights for CALC

**1. Atom table pattern**:
- BEAM's atom interning is limited to atoms
- CALC extends this to all terms via hash consing
- BEAM's approach avoids overhead for non-atom data

**2. persistent_term model**:
- Read-heavy workloads benefit from no-copy reads
- Global GC on update is acceptable if updates rare
- **Directly applicable** to proof term storage

**3. Process isolation trade-off**:
- BEAM prioritizes fault tolerance over sharing
- CALC can afford global sharing (no concurrency concerns yet)
- If CALC becomes concurrent, consider per-"process" stores

**4. Tiered storage**:
- BEAM's three-tier system (heap/ETS/persistent_term) suggests
- CALC could have: working set (fast) vs persistent (verified)

---

## Comparative Summary

### Storage Paradigms

| Language | Paradigm | Hash Consing | Equality |
|----------|----------|--------------|----------|
| **CALC** | Content-addressed | Built-in | O(1) |
| Haskell/GHC | Closures | None | O(n) |
| OCaml | Tagged values | Library | O(1) with lib |
| SML | Tagged/Regions | Optional | O(n) |
| Prolog/WAM | Tagged cells | None | Unification |
| Coq | ADT + hash cons | Since 1998 | O(1) |
| Agda | Haskell ADT | None | O(n) |
| Idris 2 | Self-hosted | None | O(n) |
| Lean 4 | Lean ADT | Hash-cached | O(1)ish |
| Isabelle | ML ADT | Unclear | O(n)? |
| Erlang/BEAM | Process heaps | Atoms only | O(1) atoms, O(n) else |

### Memory Efficiency

| Approach | Sharing | Overhead | Best For |
|----------|---------|----------|----------|
| No sharing | None | Minimal | Mutable data |
| Explicit sharing | Manual | Low | General purpose |
| Hash consing | Maximal | Hash table | Immutable symbolic |
| Regions | Scope-based | Region descriptors | Predictable lifetimes |

### CALC's Position

**Strengths**:
1. O(1) equality—critical for proof search
2. Automatic maximal sharing—memory efficient for terms with common substructures
3. Simple model—single global store

**Weaknesses**:
1. 32-bit collision risk at scale (~77k terms)
2. No GC integration (weak references)
3. No persistence/serialization
4. Global mutable state (the STORE)

---

## Recommendations for CALC

### Immediate Improvements

1. **Hybrid hashing** (already noted in hash.js):
   - 32-bit for runtime operations
   - 128-bit for persistence/verification
   - Memoize hash at construction (already done)

2. **Collision handling**:
   - Implement fallback structural equality on collision
   - Monitor collision rate in benchmarks

### Medium-term

3. **Weak reference integration**:
   - Allow GC of unreferenced terms
   - Requires WeakMap or finalization registry

4. **Serialization**:
   - Consider Lean 4's "compacted regions" approach
   - Store subgraph as contiguous memory

### Research Directions

5. **Region inference for proof search**:
   - Proofs have predictable structure
   - Could combine MLKit-style regions with hash consing

6. **Erasure optimization** (from Idris 2):
   - Don't store terms marked as compile-time-only
   - Relevant for CALC's potential QTT extension

7. **Tiered storage** (from Erlang/BEAM):
   - Working set: fast hash-consed store (current model)
   - Persistent: verified, serialized (like persistent_term)
   - Consider no-copy reads for frequently accessed terms

---

## Bibliography

- [GHC Heap Objects](https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/Storage/HeapObjects)
- [STG Machine](https://medium.com/superstringtheory/haskell-compilation-pipeline-and-stg-language-7fe5bb4ed2de)
- [OCaml Memory Representation](https://ocaml.org/docs/memory-representation)
- [OCaml hashcons library](https://fairyland-ocaml.github.io/libraries/hashcons.html)
- [Warren Abstract Machine Tutorial](https://cliplab.org/~logalg/slides/8_wam_AitKaci_book.pdf)
- [WAM on Grokipedia](https://grokipedia.com/page/Warren_Abstract_Machine)
- [Coq kernel/constr.ml](https://github.com/coq/coq/blob/master/kernel/constr.ml)
- [Agda Internal.hs](https://github.com/agda/agda/blob/master/src/full/Agda/Syntax/Internal.hs)
- [Idris 2: QTT in Practice](https://arxiv.org/abs/2104.00480)
- [Lean 4 Expr](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
- [MLKit Regions](https://elsman.com/pdf/mlkit-4.7.2.pdf)
- [Hash Consing Wikipedia](https://en.wikipedia.org/wiki/Hash_consing)
- [Hash Consing GC (Appel-Shao)](https://www.cs.princeton.edu/~appel/papers/hashgc.pdf)
- [Efficient Symbolic Computation via Hash Consing](https://arxiv.org/html/2509.20534)
- [The BEAM Book](https://blog.stenmans.org/theBeamBook/)
- [Erlang BEAM Primer](https://www.erlang.org/blog/a-brief-beam-primer/)
- [Erlang Memory Usage](https://www.erlang.org/doc/system/memory.html)
- [Erlang persistent_term](https://www.erlang.org/doc/apps/erts/persistent_term.html)
- [Elixir Memory Structure](https://www.honeybadger.io/blog/elixir-memory-structure/)
- [Elixir Internal Data Representation](https://arunramgt.medium.com/elixir-internal-data-representation-7ad49389e9ea)

---

*Last updated: 2026-02-11*
