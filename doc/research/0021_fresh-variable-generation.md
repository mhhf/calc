---
title: "Fresh Variable Generation in Proof Systems"
created: 2026-02-21
modified: 2026-02-21
summary: "How proof systems generate fresh variables: techniques from Celf, Twelf, Coq, Lean, Isabelle, Agda, and Prolog/WAM including locally nameless and de Bruijn approaches."
tags: [fresh-variables, eigenvariable, metavariables, proof-assistants, locally-nameless]
category: "Symbolic Execution"
---

# Fresh Variable Generation in Proof Systems

How proof assistants and logic programming systems generate fresh variables for quantifier rules.

## The Problem

Two quantifier rules need fresh variables during proof search:
- **Eigenvariable rules** (∃L, ∀R): open a binder with a fresh *parameter* (must not occur elsewhere)
- **Witness rules** (∃R, ∀L): open a binder with a fresh *logic variable* (to be determined by unification)

The eigenvariable condition: the fresh name must not appear in the conclusion or any other open branch.

## 1. Celf (SML, CLF linear logic)

**Mechanism:** Global mutable counter + mutable reference cells.

```sml
(* Syntax.sml *)
val lVarCnt = ref 0w0
fun nextLVarCnt () = (lVarCnt := (!lVarCnt) + 0w1 ; !lVarCnt)
```

Two separate counters: `lVarCnt` (object-level logic variables) and `tyLVarCnt` (type-level). Each `newLVarCtx` allocates a fresh `ref NONE` cell — the ref identity *is* the variable identity. The counter only provides a `tag : word` for debugging/printing.

**Backtracking interaction:** Logic variables are mutable ref cells. Instantiation writes `SOME value` into the ref. Celf's `BackTrack.backtrack` module handles undo — on failure, refs are reset to `NONE`. The counter itself is **never decremented** (monotonic). Fresh variables created in failed branches keep their tags — no reuse, no conflict.

**Eigenvariables:** In operational semantics (`OpSem.sml`), Celf uses `newLVarCtx` during monad generation for `∃`-like constructs. Universal quantifier goals (`{x:A} B`) generate a fresh *parameter* — a new constant scoped to the branch.

**Key insight:** Freshness = memory allocation (new ref cell). Counter is cosmetic. No threading needed — global mutation in SML.

Sources: [Celf GitHub](https://github.com/clf/celf), [Schack-Nielsen & Schurmann 2008](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28)

## 2. Twelf / Lambda-Prolog

**Mechanism:** Higher-order abstract syntax (HOAS) — the metalanguage's binding *is* the object binding.

Universal quantifier goals `{x:A} B` create a fresh parameter by introducing a new LF constant, scoped by metalanguage binding. The "fresh name" is the HOAS parameter itself — no explicit counter needed.

Existential goals create logic variables (like Celf). Constraint simplification replaces full higher-order unification.

**Key insight:** HOAS eliminates the fresh name problem for eigenvariables — the metalanguage handles it. Logic variables still need explicit generation (global ref-based, same as Celf).

Sources: [Twelf User's Guide](https://www.cs.cmu.edu/~twelf/guide-1-4/twelf_5.html), [Pfenning & Schurmann 1999](https://www.cs.cmu.edu/~fp/papers/cade99.pdf)

## 3. Coq (OCaml)

**Mechanism:** Monotonic counter inside `evar_map` (global proof state), threaded monadically.

Evars are isomorphic to `int`. The `evar_map` (module `Evd`) maps evar ids to `{ type, context, definition }` records. Creating a fresh evar:

```
Evarutil.new_evar : env -> evar_map -> types -> evar_map * constr
```

Returns updated map + a term containing the fresh evar. The map is threaded through the tactic monad (`Proofview`), which provides:
- **Global state:** `evar_map` (evars + their instantiations)
- **Goal list:** ordered list of holes (which are just evars)

Fresh name generation for hypotheses uses `Namegen.next_name_away` — takes a name hint + set of used names, appends numeric suffix until fresh.

**Backtracking:** Coq's tactic monad supports backtracking by *restoring the old evar_map*. Evar ids from failed branches become dangling — they're never reused (monotonic counter), so no conflict.

**Key insight:** Counter lives *inside* the monad state. Pure functional threading — the `evar_map` is passed and returned, never mutated in place. Freshness = next int from counter in map.

Sources: [Coq proof-engine.md](https://github.com/coq/coq/blob/master/dev/doc/proof-engine.md), [Evd API](https://ocaml.org/p/coq/8.14.0/doc/Evd/index.html)

## 4. Lean 4

**Mechanism:** `NameGenerator` with hierarchical counter, threaded through monad stack.

```lean
structure NameGenerator where
  namePrefix : Name
  idx : Nat        -- monotonic counter
```

The `MetavarContext` contains `ngen : NameGenerator`. Each `mkFreshExprMVar` call:
1. Takes next id from `ngen`
2. Creates `MVarId` (unique `Name`)
3. Stores in `MetavarContext` with type + local context
4. Returns updated state

**Branching:** `mkChild` splits the generator — parent gets even indices, child gets odd (or similar prefix partitioning). Allows parallel elaboration without coordination.

**Depth-based scoping:** Metavariables have a `depth` field. Lean only assigns a metavar if its depth equals the current `MetavarContext` depth. This prevents backtracking from leaking assignments.

**Key insight:** Hierarchical name generator allows splitting for parallelism. Counter is part of monad state (not global mutable). `MetaM` monad carries both the counter and all metavar assignments.

Sources: [Lean 4 MetaM](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html), [Lean CoreM](https://github.com/leanprover/lean4/blob/master/src/Lean/CoreM.lean)

## 5. Isabelle (SML)

**Mechanism:** `maxidx` — schematic variables carry integer indices; freshness = incrementing beyond max.

Every theorem tracks `maxidx`: the maximum index of any schematic variable (`?x.i`) appearing in it. When two theorems are combined (resolution, composition):

1. Compute `maxidx` of both theorems
2. `incr_indexes` on one theorem to shift all its schematic variables above the other's `maxidx`
3. Now all variables are disjoint — safe to unify

```
Thm A (maxidx=3):  ?P.0, ?Q.2, ?R.3
Thm B (maxidx=1):  ?x.0, ?y.1
After incr_indexes(B, 4):  ?x.4, ?y.5
Combined maxidx = 5
```

**Eigenvariables:** Proof goals use `fix` (or `!!`) to introduce eigenvariables — Isar proof language scopes them. Internally, `Variable.variant` generates names avoiding a given set.

**Key insight:** No global counter needed. Each theorem carries its own `maxidx`. Freshness is *relative* — ensured at combination time by shifting, not at creation time. Extremely elegant for a kernel that must verify proofs.

Sources: [Isabelle thm.ML](https://isabelle.in.tum.de/repos/isabelle/file/717bc892e4d7/src/Pure/thm.ML), [Paulson 1989](https://arxiv.org/pdf/cs/9301105)

## 6. Agda (Haskell)

**Mechanism:** `nextLocalMeta` counter in the type-checking monad state.

```haskell
-- Agda.TypeChecking.Monad.MetaVars
newMeta' :: ... -> TCM MetaId
```

The `TC` monad carries a `MetaId` counter. Each `newMeta'` call takes the next id, creates a record in the meta store (a mutable `IORef` map), and returns the fresh id.

**Key insight:** Standard monadic counter pattern. Counter is part of `TCState`, threaded through `TCM` (which is `StateT TCState IO`). The `IO` layer provides true mutability for the store.

Sources: [Agda MetaVars](https://hackage.haskell.org/package/Agda-2.7.0/docs/Agda-TypeChecking-Monad-MetaVars.html)

## 7. Prolog / WAM

**Mechanism:** Heap allocation — each variable is a heap cell, freshness = next heap address.

When a clause is activated, the WAM:
1. Allocates fresh heap cells for each variable in the clause (`put_variable Yn, Ai`)
2. Each cell is self-referencing (unbound variable = pointer to itself)
3. Unification binds by overwriting the cell with a pointer to the binding

**Backtracking:** The **trail** records which cells were bound since the last choice point. On failure, trail is unwound: bound cells reset to self-referencing. Heap pointer reset to choice point level (bulk deallocation).

**No counter needed:** Heap address *is* the variable identity. Monotonically growing heap pointer. `copy_term/2` creates fresh copies by allocating new cells for all variables in a term.

**CLP:** Same variable mechanism. Constraints are stored in a constraint store alongside the trail. Backtracking unwinds both variable bindings and constraints.

**Key insight:** Variables = heap cells. Fresh = allocate. Backtracking = reset heap pointer + unwind trail. Beautifully simple.

Sources: [Ait-Kaci WAM Tutorial](https://cliplab.org/~logalg/slides/8_wam_AitKaci_book.pdf), [SWI-Prolog copy_term](https://www.swi-prolog.org/pldoc/man?predicate=copy_term/2)

## 8. Locally Nameless (Charguéraud)

**Mechanism:** Bound variables are de Bruijn indices; free variables are names. "Opening" a binder substitutes `bound(0)` with a chosen fresh name.

Fresh name source: pick any atom not in the finite set of currently active names. Implementation: counter or `gensym`.

**Key property:** No shifting needed during substitution. Free variables are names (not indices), so they're invariant under changes to binding depth. This is why Coq and Lean use locally nameless internally.

**For quantifier rules:**
- ∃L / ∀R: open with `fresh_atom(used_names)` → eigenvariable
- ∃R / ∀L: open with `fresh_metavar(counter)` → logic variable

Sources: [Charguéraud 2011](https://chargueraud.org/research/2009/ln/main.pdf)

## Comparison Table

| System | Mechanism | Threading | Backtracking | Eigenvariable |
|--------|-----------|-----------|--------------|---------------|
| Celf | Global ref counter + ref cells | None (global mutation) | Trail-based undo of refs | newLVarCtx |
| Twelf | HOAS (metalanguage binding) | N/A | N/A for eigenvars | HOAS parameter |
| Coq | Int counter in evar_map | Monadic (pass & return) | Restore old evar_map | Namegen.next_name_away |
| Lean 4 | NameGenerator in MetavarContext | Monadic (pass & return) | Depth-gated assignment | mkFreshFVarId |
| Isabelle | maxidx + incr_indexes | Per-theorem (no global) | N/A (kernel verifies) | Variable.variant |
| Agda | Counter in TCState | Monadic (StateT + IO) | N/A (no backtracking) | newMeta' |
| Prolog/WAM | Heap address | Implicit (heap pointer) | Trail + heap reset | N/A |
| Locally nameless | Any gensym / counter | Depends on host | Depends on host | open with fresh atom |

## Design Analysis for CALC

CALC's situation: JavaScript, content-addressed Store, no persistent monad, forward+backward engine.

### Ruled out: Isabelle's maxidx (relative freshness)

Incompatible with content-addressing. Shifting `evar(3)` → `evar(7)` creates a new Store hash, requiring cascading rebuilds through every term containing the shifted variable. Same fundamental problem as full de Bruijn indices for bound variables — locally nameless was chosen precisely to avoid this.

### Ruled out: Random/hash-based names

Non-deterministic: same program, different run → different evar names → different Store hashes → tests can't assert specific values, benchmarks aren't comparable, bugs aren't reproducible. All major proof systems (Coq, Lean, Isabelle, Celf, Agda, Prolog) use sequential identifiers.

### Confirmed: Monotonic counter

Content-addressed Store makes it trivial: `Store.put('evar', [N])` → unique hash. Monotonic = backtracking-safe (counter only goes up, failed branches waste ids, no undo needed).

### Decided: Module-level splittable counter in `lib/kernel/fresh.js`

Module-level singleton with `fork(n)` for parallelism (Lean's `mkChild` pattern). One counter for the whole process — globally unique ids. `fork(n)` splits into n non-overlapping interleaved streams by multiplying stride. Works recursively to arbitrary depth (fork a fork of a fork). Serializable (two integers: start + stride), works across machines. `reset()` for test determinism.

Imported by: forward engine (`expandItem` ∃ case), rule interpreter (`makePremises` eigenvariable closures), backward engine (`prove.js`, replacing existing `freshCounter`).

**Key design:** `next` is the next id to hand out (not the last used). `freshEvar()` returns `next`, then advances `next += stride`. `fork(n)` gives child i starting position `next + i*stride` with stride `stride*n`. Zero gaps — every positive integer is assigned to exactly one source.

```javascript
// lib/kernel/fresh.js
const Store = require('./store')

function createFreshSource(next = 1, stride = 1) {
  let _next = next
  let _stride = stride
  return {
    freshEvar() {
      const id = _next
      _next += _stride
      return Store.put('evar', [id])
    },
    fork(n) {
      const base = _next
      const childStride = _stride * n
      const children = Array.from({ length: n }, (_, i) =>
        createFreshSource(base + i * _stride, childStride)
      )
      return children
    },
    reset() { _next = next; _stride = stride }
  }
}

// Module-level singleton
const source = createFreshSource()
module.exports = {
  freshEvar: () => source.freshEvar(),
  fork: (n) => source.fork(n),
  reset: () => source.reset(),
  createFreshSource
}
```

**Recursive fork example (zero gaps):**
```
root (next=1, stride=1): hands out 1, 2          (now next=3)
  fork(2):
    A (next=3, stride=2): hands out 3, 5, 7      (now next=9)
    B (next=4, stride=2): hands out 4, 6, 8      (now next=10)
      B.fork(2):
        B1 (next=10, stride=4): hands out 10, 14, 18, ...
        B2 (next=12, stride=4): hands out 12, 16, 20, ...
      A.fork(3):
        A1 (next=9, stride=6):  hands out 9, 15, 21, ...
        A2 (next=11, stride=6): hands out 11, 17, 23, ...
        A3 (next=13, stride=6): hands out 13, 19, 25, ...
```
All ids globally unique. Zero gaps. Each child can fork again independently to arbitrary depth.
