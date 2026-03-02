---
title: "Guarded Branch Semantics: Tensor Encoding + Constraint Graph Satisfiability"
created: 2026-02-28
modified: 2026-02-27
summary: "Tensor-in-oplus encoding for guarded branches, with additive zero for dead branch elimination and modular constraint solver (oracle interface, starting with eq/neq union-find) for path condition satisfiability at oplus expansion time"
tags: [linear-logic, clf, oplus, symexec, forward-chaining, theory, symbolic-execution, path-conditions, proof-theory, soundness, CLP, design-decision]
type: design
status: done
priority: 10
cluster: Theory
depends_on: []
required_by: [TODO_0005, TODO_0042]
starred: true
---

# Guarded Branch Semantics

## The Problem

When a forward rule branches (JUMPI, EQ, ISZERO), we use oplus (`⊕`) to create alternatives. Each alternative has a **guard** — a condition that determines if the branch is valid. The old loli encoding (`!guard -o {body}`) violates CLF, causes commuting matches, and kills both branches for symbolic values. We need:

1. **CLF-compliant encoding** — tensor+bang in the monad, not loli
2. **Works for ground AND symbolic** — one mechanism, no modes
3. **Complete contradiction detection** — catches `!leq X 5 * !leq 6 X`, not just `!eq X Y * !neq X Y`
4. **Theory-internal** — no external oracle (Z3), everything justified by ILL proof theory

## Encoding: Tensor-in-oplus (decided)

```
evm/jumpi: pc PC * code PC 0x57 * !inc PC PC' * stack SH C * stack (s SH) NPC * ...
  -o { code PC 0x57 * ... *
       ((!neq C 0 ⊗ pc NPC) ⊕ (!eq C 0 ⊗ pc PC')) }
```

Guards are **persistent facts produced** (asserted as path conditions), not checked.

**Why tensor:**
- **CLF compliance**: `!A ⊗ B` is allowed in the CLF monad (`S ::= P | S₁ ⊗ S₂ | 1 | !A | ∃x.S`). Loli is not.
- **Symbolic execution**: tensor produces path conditions naturally. Both branches explored.
- **No commuting matches**: no deferred computation, no loli fusion hack needed.
- **Simpler engine**: no `matchLoli` for guard resolution — it's just fact production.

**The only issue tensor introduces**: it asserts facts that might be false (e.g., `!eq 5 0`). This is handled by the satisfiability check + additive zero (below).

## Additive Zero (0)

### The connective

`0` (additive false) is standard ILL with one rule:

```
─────────── 0_L       (no 0_R rule exists — 0 is unprovable)
Γ, 0 ⊢ C
```

`0_L` has no premises. If `0` appears in the linear context, the branch is immediately closed — *ex falso quodlibet* for linear logic.

### The key isomorphism: A ⊕ 0 ≅ A

If one oplus branch produces `0`, that branch is trivially eliminable. The oplus collapses to the surviving branch. This is the mechanism for dead branch elimination.

### In the forward engine

When `0` is produced in the linear state, the engine returns `{ type: 'dead' }` — an infeasible branch, pruned by the satisfiability check.

## The One Operation: UNSAT(Γ ∪ {g})

At every oplus expansion, for each alternative branch B_i:

```
Let Γ = accumulated path conditions (persistent facts from prior oplus expansions)
Let g_i = new guard produced by B_i
If UNSAT(Γ ∪ {g_i}):
  Replace B_i with 0          (dead branch — 0_L eliminates it)
Else:
  Produce g_i as persistent fact, continue exploration
```

This is the **only** pruning operation. There is one mechanism, not levels or stages.

### Ground is a special case

Ground evaluation is what happens when the constraint solver receives a fully instantiated query. `UNSAT(∅ ∪ {!eq(5, 0)})` = "is eq(5,0) satisfiable?" = "is eq(5,0) true?" = FFI returns false → UNSAT. No mode switching, no special case. The solver just happens to return immediately for ground inputs.

### Path conditions accumulate AT oplus expansion

Path conditions accumulate at oplus expansion points — the only places where new persistent guard facts are produced. Each expansion adds constraints; the satisfiability check verifies consistency with all prior constraints.

```
Step 1: JUMPI fires on symbolic C
  ├─ Branch A: guard !neq(C, 0)
  │    UNSAT(∅ ∪ {!neq(C,0)})? SAT → assert. Γ_A = {!neq(C,0)}
  │    Step 2: EQ compares C with 0
  │    ├─ Branch A.1: guard !neq(C, 0)
  │    │    UNSAT({!neq(C,0)} ∪ {!neq(C,0)})? SAT → continue ✓
  │    └─ Branch A.2: guard !eq(C, 0)
  │         UNSAT({!neq(C,0)} ∪ {!eq(C,0)})? UNSAT! → 0 ✓
  └─ Branch B: guard !eq(C, 0)
       UNSAT(∅ ∪ {!eq(C,0)})? SAT → assert. Γ_B = {!eq(C,0)}
       Step 2: EQ compares C with 0
       ├─ Branch B.1: guard !neq(C, 0)
       │    UNSAT({!eq(C,0)} ∪ {!neq(C,0)})? UNSAT! → 0 ✓
       └─ Branch B.2: guard !eq(C, 0)
            UNSAT({!eq(C,0)} ∪ {!eq(C,0)})? SAT → continue ✓
```

4 potential branches → 2 pruned immediately. Exponential savings.

## Modular Constraint Solver Architecture

The constraint domain will grow over time. Today the guards are `eq`/`neq`. Tomorrow they might include `leq`/`gt`. Eventually they could involve `plus`, memory predicates, or user-defined constraints. The architecture must be **modular** — a stable interface with pluggable theory solvers behind it.

### The interface

```
ConstraintSolver:
  addConstraint(fact)  → void       // add a persistent fact as constraint
  checkSAT()           → bool       // is the accumulated constraint set satisfiable?
  checkpoint()         → token      // snapshot for DFS backtracking
  restore(token)       → void       // undo to a previous snapshot
```

This interface is called at oplus expansion time. The implementation behind it can be anything — from a simple complement lookup to a full SMT solver. The rest of the engine doesn't care.

### Trust model: oracle (NOT like FFI)

The solver is an **oracle** — it says "SAT" or "UNSAT" and the engine trusts the answer. This is **not** the same trust model as FFI.

**The difference:** FFI is optimization, theory is semantics. Every FFI predicate (`plus`, `neq`, `inc`) has backward clause definitions. Turn off FFI → clause resolution takes over, slower but produces the same results with full proof objects. The constraint solver has **no such fallback**. Turn it off → UNSAT branches are never pruned → the tree is correct but exponentially larger. There is no backward clause that derives `0` from contradictory path conditions.

This makes the constraint solver a **new trust boundary** in the system:
- **FFI**: trusted optimization (can be removed, proofs still produced)
- **Constraint solver**: trusted authority (cannot be removed without losing pruning entirely)

**Why this is acceptable (for now):**
- The forward engine already operates outside the kernel's trust boundary. No forward execution produces kernel-verifiable proof objects today.
- The solver's correctness is mathematically verifiable for each theory (union-find for eq/neq, Bellman-Ford for QF_IDL). These are textbook algorithms with known completeness proofs.
- Soundness failure (solver says UNSAT when SAT) would prune a reachable branch — a **missed execution path**, detectable by comparison with solver-off runs.

**The open question:** Can we close this gap? Two paths:
1. **Contradiction axioms as witness**: `!eq X Y * !neq X Y -o { 0 }` is a proof-producing forward rule. If the solver could emit the specific contradicting facts, the engine could fire the appropriate axiom to derive `0` with a proof object. This works for eq/neq but requires axiom schemas for each theory extension.
2. **Proof-producing solver**: Z3 can produce UNSAT proofs. Translate them into ILL derivations of `0`. Principled but significant work.

For Phase 1–3, we proceed with the oracle. The modular interface supports upgrading to proof-producing without engine changes.

### Predicate registration

The solver needs to know which persistent facts are constraints (vs. ordinary persistent facts like `!code`). This uses the same mechanism as FFI: **explicit predicate registration**.

```
solver.registerPredicate('eq', { arity: 2, type: 'equality' });
solver.registerPredicate('neq', { arity: 2, type: 'disequality' });
// later:
solver.registerPredicate('lt', { arity: 2, type: 'less-than' });
```

At oplus expansion, persistent facts from the alternative are checked against registered predicates. Registered → fed to solver. Not registered → produced as ordinary persistent facts. This mirrors how FFI registration works in `calc.ffi`.

### Theory solver progression

Start minimal, extend as programs demand:

| Theory | Predicates | Algorithm | Completeness | When |
|---|---|---|---|---|
| **Equality + disequality** | eq, neq | Union-find + forbid list | Complete for eq/neq | Phase 1 (start here) |
| **Integer Difference Logic** | + lt, le, gt, ge | Constraint graph + Bellman-Ford | Complete for QF_IDL | When comparison guards appear |
| **Linear Integer Arithmetic** | + plus(X,Y,Z) symbolic | Simplex + branch-and-bound | Complete for QF_LIA | When symbolic plus guards appear |
| **Z3 backend** | anything | SMT | Complete for supported theories | When theories get complex |

Each row SUBSUMES the previous. The interface never changes — only the implementation behind `checkSAT()`.

### Why start with eq/neq, not jump to Bellman-Ford?

1. **Current programs only produce eq/neq guards** (EVM's JUMPI, EQ, ISZERO)
2. Union-find + forbid is ~50 lines, well-understood, O(α(n))
3. Adding Bellman-Ford later is extending the solver, not replacing it (union-find handles eq faster than the constraint graph would)
4. We don't design for hypothetical complexity — we extend when real programs need it

### What union-find + forbid catches

- `!eq X Y * !neq X Y` → X in same class as Y, forbidden → **UNSAT** ✓
- `!eq X Y * !eq Y Z * !neq X Z` → transitivity via union-find → **UNSAT** ✓
- `!neq X 0 * !neq Y 0 * !eq X Y` → X=Y forced, but X≠0 not violated → **SAT** ✓

### What it does NOT catch (needs Bellman-Ford extension)

- `!leq X 5 * !leq 6 X` → X ≤ 5 ∧ 6 ≤ X → **contradiction** (missed — no eq/neq reasoning applies)
- `!lt X Y * !lt Y Z * !lt Z X` → cyclic ordering → **contradiction** (missed)
- `!eq X Y * !lt X Y` → X = Y ∧ X < Y → **contradiction** (partially — eq detected, but lt interaction missed)

These are real contradictions but they require **arithmetic bound reasoning**. When programs produce comparison guards, we add the constraint graph layer.

### The Bellman-Ford layer (when needed)

All comparison predicates normalize to `X - Y ≤ c` (difference constraints):

| Guard | Normalized | Notes |
|---|---|---|
| `eq(X, Y)` | `X - Y ≤ 0` ∧ `Y - X ≤ 0` | Two edges |
| `neq(X, Y)` | Forbid(X, Y) | Separate list |
| `lt(X, Y)` | `X - Y ≤ -1` | Integers: strict → non-strict |
| `le(X, Y)` | `X - Y ≤ 0` | Direct |
| `gt(X, Y)` | `Y - X ≤ -1` | Flip + strict |

Build a directed weighted graph. **Negative-weight cycle = UNSAT.** This is complete for QF_IDL.

Example: `!leq X 5 * !leq 6 X`:
- Edges: `zero →(5) X` and `X →(-6) zero`
- Cycle weight: 5 + (-6) = -1 < 0 → **UNSAT** ✓

### Ground: degenerate case

When all arguments are ground, there are no symbolic variables to reason about. `UNSAT(∅ ∪ {!eq(5, 0)})` = "is eq(5,0) true?" = FFI evaluates: false → UNSAT. The solver just happens to return immediately. As a practical optimization, ground guards short-circuit through FFI before consulting the constraint solver.

## The CLP(T) Correspondence

This architecture is exactly **CLP(T)** — Constraint Logic Programming over a theory T:

| CLP(T) concept | CALC equivalent |
|---|---|
| Constraint store S | Constraint solver state (accumulated path conditions) |
| New constraint c | Guard g in oplus branch |
| Background theory T | Pluggable (eq/neq → QF_IDL → QF_LIA → ...) |
| Satisfiability check | `solver.checkSAT()` at oplus expansion |
| Failure (⊥) | Additive zero (0) in ILL |
| Choice point | Oplus expansion |

Properties:
- **Soundness**: if the solver says UNSAT, the branch is genuinely infeasible
- **Completeness**: depends on the solver — complete for its supported theory, conservative (never false UNSAT) for unsupported predicates
- **Monotonicity**: adding constraints can only make UNSAT more likely, never less. Path conditions accumulate monotonically.
- **Modularity**: upgrading the solver improves pruning precision without changing the architecture

## Contradiction Axioms: Safety Net, Not Primary Mechanism

Contradiction axioms like `!eq X Y * !neq X Y -o { 0 }` are valid ILL derivations and useful as a defense-in-depth mechanism for general programs where persistent facts might be produced outside oplus expansions. But for the primary path — oplus expansion with satisfiability check — they are redundant. The constraint graph catches everything they would catch and more.

Keep them in the calculus as forward rules for generality. Don't rely on them for correctness.

## What Needs to Be Added

### To the calculus

1. **Additive zero connective** in `ill.calc`:
   ```
   zero: formula @ascii "0" @latex "\\mathbf{0}" @category additive @polarity positive.
   ```

2. **Zero-left rule** in `ill.rules`:
   ```
   zero_L: Γ, 0 ⊢ C.
   ```

3. **Contradiction axioms** (optional, in prelude):
   ```
   contra/eq_neq: !eq X Y * !neq X Y -o { 0 }.
   ```

4. **Rewrite 3 EVM rules** from loli-in-oplus to tensor-in-oplus

### To the engine

| Component | Change |
|---|---|
| `lib/engine/constraint.js` | **NEW**: ConstraintSolver interface + eq/neq solver (union-find + forbid) |
| `symexec.js` | Init solver in `explore()`, call at oplus expansion, checkpoint/restore in DFS |
| `symexec.js` | Detect `0` in state → return `{ type: 'dead' }` |
| `tree-utils.js` | `dead` node type (color: orange) |
| `compile.js` | No change (oplus expansion already produces alternatives with persistent patterns) |
| `match.js` | `drainPersistentLolis` becomes unnecessary for guard lolis |

### What becomes unnecessary

- Loli fusion (TODO_0054 Option C) — no persistent-trigger lolis from guards
- `matchLoli` for guard-only lolis — guards are asserted, not checked
- (Keep memoization (Option E) and `matchLoli` for non-guard lolis)

## Connection to TODO_0005 (Constraint Propagation)

TODO_0005 describes constraint propagation levels (equality resolution, FFI re-check, chain simplification, domain propagation). The modular constraint solver subsumes this:

- **Equality resolution** (`!eq(evar(N), v)` → substitute): the eq/neq solver's union-find propagates equalities
- **FFI re-check**: ground guards short-circuit through FFI (optimization)
- **Chain simplification / domain propagation**: future solver layers (Bellman-Ford, Simplex) handle these

TODO_0005 should be reframed as "extending the constraint solver with new theory layers" rather than a standalone feature.

## Research Directions

### R1: Z3 as a solver backend

If constraints grow complex enough (nonlinear arithmetic, bit-vectors, memory models), a Z3 backend behind the `ConstraintSolver` interface would be the pragmatic choice. The theory concern is that Z3 is an external oracle — it says UNSAT but doesn't produce a `0` derivation in ILL. Two approaches:

1. **Trust the oracle**: Z3 says UNSAT → produce 0. Sound if Z3 is sound (it is for supported theories). No proof object.
2. **Proof-producing Z3**: Z3 can produce proofs. Translate the UNSAT proof into an ILL derivation that produces 0. Principled but significant work.

For now, approach 1 is acceptable — the `0` production is justified by the soundness of the decision procedure (see trust model discussion above). The modular interface means we can add Z3 without touching the rest of the engine. Approach 2 would close the trust gap identified in the trust model section.

### R2: Focused proof search

`0` is positive (synchronous). Its left rule `0_L` is invertible → applied eagerly in the asynchronous phase. When `0` appears during focusing, the branch is immediately closed. This integrates naturally with CALC's backward prover.

The forward engine's oplus expansion can be seen as a focusing phase: `⊕R₁`/`⊕R₂` are non-invertible (synchronous). The satisfiability check determines which branches to explore.

### R3: Connection to CHC (Constrained Horn Clauses)

Our tensor encoding `(!neq C 0 ⊗ pc NPC)` parallels CHC's constraint-in-clause-body encoding:

```
% CHC:
post(NPC) :- pre(PC, C), C ≠ 0.
post(PC')  :- pre(PC, C), C = 0.
```

The guard `C ≠ 0` is a constraint in the background theory. CALC's constraint graph is the decision procedure for this theory.

### R4: Incremental solver with DFS undo

The DFS exploration in `symexec.js` uses mutation/undo. The constraint solver needs the same pattern — this is why the interface has `checkpoint()`/`restore()`:

- **Union-find undo**: log union operations, reverse on restore. Standard "union-find with rollback."
- **Constraint graph undo**: log added edges, remove on restore.
- **Z3**: push/pop scope (Z3 natively supports incremental assertions with backtracking).

Each solver backend implements checkpoint/restore in the way natural to its data structure.

## Implementation Phases

All design decisions are resolved. No open questions remain for Phases 1–4.

### Phase 1: Add zero to the calculus
- Add `zero` connective to `ill.calc`
- Add `zero_L` rule to `ill.rules`
- Rebuild `out/ill.json`
- Update backward prover to handle `zero_L`

### Phase 2: Modular constraint solver + eq/neq theory
- Define `ConstraintSolver` interface: `addConstraint`, `checkSAT`, `checkpoint`, `restore`
- Implement eq/neq solver: union-find + forbid list with predicate registration
- Ground optimization: short-circuit through FFI for fully ground guards
- Hook into `go()` at oplus expansion: check `UNSAT(Γ ∪ {g})` before recursing
- Produce 0 on UNSAT, detect `0` → `{ type: 'dead' }` tree node

### Phase 3: Tensor encoding + EVM rule rewrite
- Rewrite 3 EVM rules from loli-in-oplus to tensor-in-oplus
- Add contradiction axiom `contra/eq_neq` as forward rule (safety net)
- Verify all tests pass

### Phase 4: Cleanup
- Remove loli fusion (TODO_0054 Option C) for guard lolis (guards no longer produce lolis)
- Update tree-utils for `dead` node type
- Keep memoization (Option E) as general safety net
- Keep `matchLoli` for non-guard lolis (linear-trigger lolis still exist)

### Future: extend solver as programs demand
- Comparison guards (lt/le/gt/ge) → add Bellman-Ford layer
- Symbolic arithmetic guards (plus) → add Simplex layer or Z3 backend
- Each extension is behind the same `ConstraintSolver` interface
- Upgrade from oracle to witness-producing solver if kernel verification extends to forward execution

## References

### Linear logic and zero
- Girard (1987) "Linear Logic" — additive zero `0`, `0_L` rule, `A ⊕ 0 ≅ A`
- Braüner (1996) "Introduction to Linear Logic" — BRICS-LS-96-6, clear presentation of additive units
- Pfenning (CMU 15-317) Lecture notes on linear logic — sequent calculus rules for `0` and `⊤`

### CLF and the monad
- Watkins, Cervesato, Pfenning, Walker (2004) "A Concurrent Logical Framework" — CLF type grammar, monad restrictions
- Watkins et al. (2004) "CLF: The Propositional Fragment" — synchronous types in monad: `S ::= P | S₁ ⊗ S₂ | 1 | !A | ∃x.S`

### Integer Difference Logic and constraint graphs
- Bellman (1958) "On a routing problem" — shortest path algorithm
- Dill (1989) "Timing Assumptions and Verification of Finite-State Concurrent Systems" — DBM for verification
- Cotton & Maler (2006) "Fast and Flexible Difference Constraint Propagation for DPLL(T)" — incremental IDL
- Nieuwenhuis, Oliveras, Tinelli (2006) "Solving SAT and SAT Modulo Theories" — DPLL(T) architecture

### Constraint logic programming
- Jaffar & Lassez (1987) "Constraint Logic Programming" — CLP(X) framework
- Jaffar, Maher et al. (1994) "Constraint Logic Programming: A Survey" — constraint theory integration
- Marriott & Stuckey (1998) "Programming with Constraints" — CLP implementation, satisfiability at choice points
- Hodas & Miller (1994) "Logic Programming in a Fragment of Intuitionistic Linear Logic" — linear logic + constraints

### CHR and contradiction handling
- Fruhwirth (1998) "Theory and practice of Constraint Handling Rules" — `fail` built-in
- Fruhwirth (2009) "Constraint Handling Rules" — comprehensive treatment

### Symbolic execution
- King (1976) "Symbolic Execution and Program Testing" — path conditions
- Baldoni et al. (2018) "A Survey of Symbolic Execution Techniques"

### Focusing and proof search
- Andreoli (1992) "Logic Programming with Focusing Proofs in Linear Logic" — polarity of `0` (positive)

### Decidability and constructive logic
- Martin-Löf (1984) "Intuitionistic Type Theory" — `Dec(A) = A + (A → 0)`
- Presburger (1929) "Über die Vollständigkeit eines gewissen Systems der Arithmetik" — decidability of integer arithmetic without multiplication

### Existing CALC theory
- [THY_0001](../theory/0001_exhaustive-forward-chaining.md) — loli-in-monad extension (to be superseded)
- [THY_0004](../theory/0004_symbolic-branching.md) — oplus for symbolic branching
- [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) — three problems of symbolic values
- [TODO_0054](0054_commuting-match-reduction.md) — commuting match reduction
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation (to be reframed as constraint graph implementation)
- [RES_0049](../research/0049_constraint-propagation-systems.md) — CLP/CHR survey
- [RES_0039](../research/0039_symbolic-arithmetic-design-space.md) — symbolic arithmetic design space
