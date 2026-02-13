# Flat vs Curried Term Representations

The current system stores `code(PC, OP)` as `app(app(atom("code"), PC), OP)` -- nested binary applications requiring O(arity) Store.get() calls to extract head or arguments. This document surveys how real systems handle this and evaluates alternatives.

---

## The Problem

```
Current:  app(app(app(atom("f"), a), b), c)   -- 3 Store nodes, 3 lookups to get head
Flat:     f(a, b, c)                           -- 1 Store node, 1 lookup
```

Extracting head functor (`getHead` in `lib/engine/prove.js`) walks the entire app chain. First-argument indexing (`getFirstArgCtor`) walks it again. Every unification decomposes through O(arity) intermediate `app` nodes.

---

## 1. WAM (Prolog): Flat Functor/Arity/Args

The WAM stores `f(a, b, c)` as a contiguous heap block:

```
Heap[H]   = <STR, H+1>     -- pointer to functor cell
Heap[H+1] = f/3             -- functor + arity
Heap[H+2] = <REF, a>        -- arg 1
Heap[H+3] = <REF, b>        -- arg 2
Heap[H+4] = <REF, c>        -- arg 3
```

- Head extraction: O(1) -- read functor cell directly
- First-arg indexing: O(1) -- read Heap[H+2]
- Arity: O(1) -- encoded in functor cell
- Pattern matching: direct positional comparison

This is the gold standard for first-order logic programming. Every production Prolog (SWI, YAP, XSB, GNU Prolog) uses this layout.

**Deep indexing** (SWI-Prolog JIT): builds hash tables on functor+arity of any argument position, not just first. Enabled by flat layout since argument access is O(1).

Sources: [WAM Tutorial (Ait-Kaci)](https://cliplab.org/~logalg/slides/8_wam_AitKaci_book.pdf), [SWI-Prolog JIT indexing](https://www.swi-prolog.org/pldoc/man?section=jitindex)

---

## 2. Coq: Flat App with Array

Coq's kernel uses **n-ary application** with a flat array:

```ocaml
type constr =
  | App of constr * constr array    (* f, [|a; b; c|] *)
  | Rel of int                      (* de Bruijn index *)
  | Lambda of Name.t * constr * constr
  | ...
```

Invariants enforced by `mkApp`:
- Function `f` is never itself an `App` (flattening: `App(App(f, [a;b]), [c;d])` becomes `App(f, [a;b;c;d])`)
- Argument array is non-empty

This means head extraction is O(1) and argument access is O(1) by index. Coq hash-conses these terms, so equality remains O(1).

The formal specification (PCUIC) uses binary application, but the **implementation** uses flat. This is a deliberate performance decision.

Sources: [Coq Constr API](https://rocq-prover.org/doc/v8.15/api/coq-core/Constr/index.html), [coq/kernel/constr.ml](https://github.com/coq/coq/blob/master/kernel/constr.ml)

---

## 3. Lean 4: Binary App (Curried)

Lean 4 uses **binary curried application** like our current system:

```lean
inductive Expr where
  | app    : Expr -> Expr -> Expr     -- binary!
  | lam    : Name -> Expr -> Expr -> BinderInfo -> Expr
  | const  : Name -> List Level -> Expr
  | ...
```

`f x y z` is `app (app (app (const f) x) y) z`.

Convenience functions like `mkAppN` accept an array but build the nested chain. `getAppFn` walks the chain to get the head, `getAppArgs` collects args into an array -- both O(arity).

Lean accepts this cost because:
- Higher-order lambda calculus needs partial application naturally
- The kernel is small and correctness matters more than speed
- Tactics/elaboration work at a higher level

Sources: [Lean4 Expressions](https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html), [Lean4 Expr.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)

---

## 4. Isabelle: Binary App (Curried)

Isabelle's Pure kernel also uses binary application:

```sml
datatype term =
    Const of string * typ
  | Free of string * typ
  | Var of indexname * typ
  | Bound of int
  | Abs of string * typ * term
  | $ of term * term              -- binary application
```

Like Lean, this prioritizes higher-order logic where partial application is fundamental.

Sources: [Isabelle term.ML](https://isabelle.in.tum.de/repos/isabelle/file/717bc892e4d7/src/Pure/thm.ML), [Isabelle Cookbook](https://web.cs.wpi.edu/~dd/resources_isabelle/isabelle_programming.urban.pdf)

---

## 5. Ehoh (E Prover Extension): Flattened Spine

Ehoh extends the first-order superposition prover E to handle higher-order terms using a **flattened spine notation**:

```
Term cell = { f_code, num_args, args[] }

f         --> { f_code=F, num_args=0, args=[] }
f a       --> { f_code=F, num_args=1, args=[a] }
f a b     --> { f_code=F, num_args=2, args=[a, b] }
```

For free variable application `X a b`, uses internal symbol `@`:

```
X a b     --> { f_code=@, num_args=3, args=[X, a, b] }
```

This is essentially **spine form** -- head + argument list, stored flat. It preserves first-order performance while supporting higher-order terms.

Sources: [Extending a High-Performance Prover to Higher-Order Logic](https://matryoshka-project.github.io/pubs/lambdae.pdf)

---

## 6. egg / egglog: Flat Operator + Children

egg represents e-nodes with operator + flat children array:

```rust
// From define_language! macro
"+" = Add([Id; 2]),     // operator with 2 children
"*" = Mul([Id; 2]),
"f" = F([Id; 3]),       // 3-arg function

// Internal ENode (egg 0.1.x)
struct ENode<O, Child = Id> {
    op: O,
    children: SmallVec<[Child; 2]>,   // flat array, stack-allocated up to 2
}
```

SmallVec optimization: up to 2 children stored inline (no heap allocation), spills to heap for more. This is tuned for the common case of binary operators.

egglog extends this to relational tables where each function `f(a, b, c) = v` becomes a row `(a, b, c, v)` in a table indexed by `f`. This is fundamentally flat -- no nesting.

Sources: [egg docs](https://docs.rs/egg/0.1.2/egg/struct.ENode.html), [E-Graphs in Rust](https://www.stephendiehl.com/posts/egraphs/), [define_language!](https://egraphs-good.github.io/egg/egg/macro.define_language.html)

---

## 7. Spine Form (Lambda Calculus)

The spine representation factors `((f a) b) c` into `(f, [a, b, c])`:

```
type term = Lam of term | App of head * term list
type head = Var of int | Const of string
```

Used in Twelf, Beluga, and lambda-Prolog implementations. Key benefits:
- Head extraction: O(1)
- Argument access: O(1) by index
- Substitution: substitute into args, rebuild spine
- Pattern matching: compare heads first (fast fail), then args

The "locally nameless" variant combines de Bruijn indices for bound variables with named free variables, orthogonal to spine vs curried.

Sources: [Spinal Atomic Lambda-Calculus](https://hal.science/hal-03098744/document), [Lambda Term Representation](https://arxiv.org/pdf/1111.0085)

---

## Performance Comparison

### Memory Overhead

| Representation | Nodes for `f(a,b,c)` | Store lookups for head | Store lookups for arg[i] |
|---|---|---|---|
| Curried app chain | 3 app + 1 atom = 4 | 3 (walk chain) | 3-i (walk chain) |
| Flat functor/args | 1 node | 1 | 1 |
| Spine (head, args[]) | 1 node | 1 | 1 |

For arity-N predicates:
- **Curried**: N app nodes + head = N+1 nodes, O(N) head extraction
- **Flat**: 1 node with N children, O(1) everything
- Memory: curried uses ~3x more store entries (each app node = tag + 2 children)

### Hash Computation

- **Curried**: hash computed bottom-up naturally (each app hashes its two children)
- **Flat**: hash computed over tag + arity + all children in one pass. Same total work but fewer Store.put() calls

### Structural Sharing (Trade-off)

**Curried wins here.** With curried representation:
```
f(a, b)  =  app(app(f, a), b)
f(a, c)  =  app(app(f, a), c)
                  ^^^^^^^^ shared!
```
The `app(f, a)` subterm is shared between any application of `f` to `a` regardless of second argument. With flat representation, `{tag:'f', children:[a,b]}` and `{tag:'f', children:[a,c]}` are distinct nodes.

**However**: this sharing matters most when:
- Many terms share long prefixes (common in curried functional code)
- Memory is the primary bottleneck

In CALC's use case (logic programming with predicates), sharing of partial applications is rare. Predicates like `code(PC, OP)` don't typically share `code(PC, ?)` prefixes meaningfully.

### Unification

**Flat is strictly better for first-order unification:**
1. Tag+arity check first (fast fail) -- O(1)
2. Pairwise argument comparison -- O(min-arity) to first mismatch
3. No intermediate app nodes to decompose

With curried, unification of `f(a,b)` vs `g(x,y)` requires:
1. Decompose outer app -> push (app(f,a), app(g,x)) and (b, y)
2. Decompose inner app -> push (f, g) and (a, x)
3. Fail at f != g
Total: 5 Store.get() calls instead of 1

---

## 8. Hybrid Approaches

### Coq's Strategy
Coq uses flat internally but binary in the formal specification. `mkApp` auto-flattens. This is the cleanest hybrid: the API looks curried, the storage is flat.

### Ehoh's Strategy
Spine form with a special `@` symbol for variable-head applications. First-order terms get flat treatment, higher-order terms get explicit application.

### Proposed for CALC

**Option A: Flat predicate node (new tag)**

```javascript
// Instead of: app(app(atom("code"), PC), OP)
// Store:      { tag: 'pred', children: ['code', PC, OP] }
//                                       ^name  ^args

Store.put('pred', ['code', pcHash, opHash])
```

- Head extraction: O(1) -- `children[0]`
- Argument access: O(1) -- `children[i+1]`
- Arity: O(1) -- `children.length - 1`
- Hash: computed once over all children
- Backward compatible: can coexist with app nodes for genuine higher-order terms

**Option B: Auto-flattening at Store.put**

```javascript
// Store.put('app', [left, right]) detects chains and flattens:
// put('app', [put('app', [atom_f, a]), b])
//   --> internally stores as { tag: 'app', children: [atom_f, a, b] }
```

Transparent to callers but requires careful handling of the variable-head case.

**Option C: Cached spine decomposition**

Keep curried representation but cache `{ head, args }` decomposition:

```javascript
// Lazy spine cache on first access
function getSpine(h) {
  if (spineCache.has(h)) return spineCache.get(h);
  const args = [];
  let cur = h;
  while (Store.tag(cur) === 'app') {
    const node = Store.get(cur);
    args.push(node.children[1]);
    cur = node.children[0];
  }
  args.reverse();
  const result = { head: cur, args };
  spineCache.set(h, result);
  return result;
}
```

Minimal change, caches O(arity) work. Invalidation not needed since content-addressed terms are immutable.

---

## Summary Table

| System | Representation | Why |
|--------|---------------|-----|
| WAM (Prolog) | Flat functor/arity/args | First-order, performance critical |
| Coq | Flat App(f, args[]) | Performance; spec uses binary |
| Lean 4 | Binary app (curried) | Higher-order, correctness first |
| Isabelle | Binary $ (curried) | Higher-order |
| Ehoh/E | Flat spine cells | First-order perf + HO extension |
| egg/egglog | Flat operator+children | E-graph efficiency |
| Twelf/Beluga | Spine form | LF implementation efficiency |

**Pattern**: Systems doing first-order logic programming or rewriting use flat. Systems doing higher-order type theory use curried. Coq is the notable exception -- higher-order theory but flat implementation.

---

## Recommendation for CALC

CALC is primarily a **first-order logic programming engine** (predicates with ground/variable arguments, backward chaining, first-argument indexing). Higher-order features (if needed) are limited to macro-level rule application, not runtime term manipulation.

**Option A (flat pred node)** is the strongest choice:
- O(1) head extraction eliminates the `getHead` walk (hot path in prove.js)
- O(1) first-arg access eliminates the `getFirstArgCtor` walk (hot path in indexing)
- Unification skips N-1 intermediate app decompositions
- Hash computation is simpler (one node instead of N+1)
- The `app` tag can remain for genuine higher-order applications if needed
- Content addressing still works -- just hash tag + all children

The structural sharing loss is acceptable because CALC's predicates don't exhibit the partial-application sharing patterns that make curried representation worthwhile.

---

## Bibliography

- [WAM Tutorial Reconstruction (Ait-Kaci)](https://cliplab.org/~logalg/slides/8_wam_AitKaci_book.pdf)
- [SWI-Prolog JIT Indexing](https://www.swi-prolog.org/pldoc/man?section=jitindex)
- [SWI-Prolog Deep Indexing](https://www.swi-prolog.org/pldoc/man?section=deep-indexing)
- [Coq Constr API](https://rocq-prover.org/doc/v8.15/api/coq-core/Constr/index.html)
- [coq/kernel/constr.ml](https://github.com/coq/coq/blob/master/kernel/constr.ml)
- [Lean4 Expr.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Expr.lean)
- [Lean4 Metaprogramming: Expressions](https://leanprover-community.github.io/lean4-metaprogramming-book/main/03_expressions.html)
- [Isabelle term.ML](https://isabelle.in.tum.de/repos/isabelle/file/717bc892e4d7/src/Pure/thm.ML)
- [Extending E to Higher-Order Logic (Ehoh)](https://matryoshka-project.github.io/pubs/lambdae.pdf)
- [egg ENode docs](https://docs.rs/egg/0.1.2/egg/struct.ENode.html)
- [egg define_language!](https://egraphs-good.github.io/egg/egg/macro.define_language.html)
- [E-Graphs in Rust (Diehl)](https://www.stephendiehl.com/posts/egraphs/)
- [egglog paper (PLDI 2023)](https://ztatlock.net/pubs/2023-pldi-egglog/2023-pldi-egglog.pdf)
- [Spinal Atomic Lambda-Calculus](https://hal.science/hal-03098744/document)
- [Lambda Term Representation (Linear Ordered Logic)](https://arxiv.org/pdf/1111.0085)
- [Hash Consing (Wikipedia)](https://en.wikipedia.org/wiki/Hash_consing)
- [Efficient Symbolic Computation via Hash Consing](https://arxiv.org/html/2509.20534)
- [Comparing Curried and Uncurried Rewriting](https://www.sciencedirect.com/science/article/pii/S0747717196900024)
- [Prolog Efficiency (Metalevel)](https://www.metalevel.at/prolog/efficiency)

*Last updated: 2026-02-13*
