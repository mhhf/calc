---
title: "Guarded Branch Semantics: Encoding Conditional Oplus in ILL Forward Chaining"
created: 2026-02-28
modified: 2026-02-28
summary: "Core design decision: how to encode guarded branches (JUMPI, EQ, ISZERO) in oplus consequents — loli vs tensor vs hybrid — and how to prune infeasible branches within the theory using additive zero"
tags: [linear-logic, clf, oplus, loli, symexec, forward-chaining, theory, symbolic-execution, path-conditions, proof-theory, evm, soundness, design-decision]
type: design
status: researching
priority: 10
cluster: Theory
depends_on: [TODO_0054]
required_by: [TODO_0005, TODO_0042]
starred: true
---

# Guarded Branch Semantics

## The Problem in One Paragraph

When a forward rule branches (EVM's JUMPI, EQ, ISZERO), we use oplus (`⊕`) to create alternatives. Each alternative has a **guard** — a condition that determines if the branch is valid. Currently we encode guards as **loli** (`!guard -o {body}`), which defers the check. This violates CLF, causes commuting matches (fixed by fusion in TODO_0054), and **kills both branches when guards are symbolic** (can't prove `!neq X Y` for symbolic X, Y). Switching to **tensor** (`!guard ⊗ body`) would fix the CLF violation but **asserts unchecked facts** — including false ones for ground values. Neither encoding works for both ground and symbolic execution. We need a unified semantics that is theory-clean, correct for ground values, and extends to symbolic path conditions.

## Concrete Example: JUMPI

The EVM `JUMPI` instruction pops a condition `C` and destination `NPC` from the stack. If `C ≠ 0`, jump to `NPC`. If `C = 0`, continue to `PC'`.

### Current encoding (loli-in-oplus)

```
evm/jumpi: pc PC * code PC 0x57 * !inc PC PC' * stack SH C * stack (s SH) NPC * ...
  -o { code PC 0x57 * ... *
       ((!neq C 0 -o { pc NPC }) ⊕ (!eq C 0 -o { pc PC' })) }
```

The oplus produces two alternatives. Each is a **loli** — a deferred computation that fires when its guard is provable.

**Ground C = 5:**
- Branch 0: loli `!neq 5 0 -o {pc NPC}` → FFI proves `neq 5 0` → fires → `pc NPC`
- Branch 1: loli `!eq 5 0 -o {pc PC'}` → FFI disproves `eq 5 0` → stuck → dead leaf

**Symbolic C = X:**
- Branch 0: loli `!neq X 0 -o {pc NPC}` → can't prove `neq X 0` → stuck → dead leaf
- Branch 1: loli `!eq X 0 -o {pc PC'}` → can't prove `eq X 0` → stuck → dead leaf
- **Both branches die.** Execution halts at the first conditional.

### Proposed encoding (tensor-in-oplus)

```
evm/jumpi: ... -o { ... *
  ((!neq C 0 ⊗ pc NPC) ⊕ (!eq C 0 ⊗ pc PC')) }
```

The `!neq C 0` is a persistent fact **produced** (asserted), not checked.

**Ground C = 5:**
- Branch 0: asserts `!neq 5 0`, produces `pc NPC` → continues (correct)
- Branch 1: asserts `!eq 5 0`, produces `pc PC'` → continues (**wrong — asserts a false fact**)

**Symbolic C = X:**
- Branch 0: asserts `!neq X 0` (path condition: X ≠ 0), produces `pc NPC` → continues
- Branch 1: asserts `!eq X 0` (path condition: X = 0), produces `pc PC'` → continues
- **Both branches explored.** This is exactly symbolic execution with path conditions.

### The tension

| | Loli (check) | Tensor (assert) |
|---|---|---|
| Ground, true branch | Fires correctly | Asserts true fact (correct) |
| Ground, false branch | Stuck (correct pruning) | **Asserts false fact (unsound)** |
| Symbolic, both branches | **Both die (too conservative)** | Both explored (correct) |
| CLF compliance | **Violates** (loli in monad) | Compliant (tensor+bang in monad) |
| Commuting matches | Yes (fixed by fusion) | No (no loli produced) |

Neither works alone. We need both: **check when decidable, assert when symbolic**.

## Three Semantic Roles of Guards

The core confusion is that `!neq C 0` plays three different roles depending on context:

### 1. Guard as CHECK (loli encoding)

"Prove `neq C 0` before proceeding."

- Semantics: persistent antecedent in a loli continuation
- Mechanism: backward chaining / FFI
- Ground: correct (decidable → prune false branch)
- Symbolic: broken (unprovable → both branches die)

### 2. Guard as ASSERTION (tensor encoding)

"Assert `neq C 0` as a persistent fact."

- Semantics: persistent consequent in a tensor product
- Mechanism: fact production
- Ground: unsound (may assert false facts)
- Symbolic: correct (path condition accumulation)

### 3. Guard as PATH CONDITION (symbolic execution)

"On this branch, assume `neq C 0` holds. Check consistency later."

- Semantics: constraint in a path condition set
- Mechanism: accumulate constraints, check satisfiability
- Ground: correct if we check decidable constraints eagerly
- Symbolic: correct (standard symbolic execution)

**Key insight:** roles 2 and 3 are the same when we add **contradiction detection**. A false assertion (`!eq 5 0`) becomes detectable when paired with a true fact (`!neq 5 0`). The question is how to detect and handle the contradiction.

## The Four Encodings

### Encoding A: Loli-in-oplus (current)

```
((!neq C 0 -o { pc NPC }) ⊕ (!eq C 0 -o { pc PC' }))
```

| Property | Value |
|---|---|
| CLF compliance | No (loli in monad) |
| Ground correctness | Yes (guard checked via FFI) |
| Symbolic support | No (both branches die) |
| Commuting matches | Yes (needs fusion hack) |
| Complexity | Low (already implemented) |

### Encoding B: Tensor-in-oplus (naive)

```
((!neq C 0 ⊗ pc NPC) ⊕ (!eq C 0 ⊗ pc PC'))
```

| Property | Value |
|---|---|
| CLF compliance | Yes (tensor+bang in monad is allowed) |
| Ground correctness | **No** (asserts false facts) |
| Symbolic support | Yes (path conditions) |
| Commuting matches | No |
| Complexity | Low (syntax change only) |

### Encoding C: Guard-as-antecedent (Ceptre pattern)

Two separate forward rules:

```
jumpi_neq: pc PC * code PC 0x57 * !neq C 0 * stack SH C * ... -o { pc NPC * ... }
jumpi_eq:  pc PC * code PC 0x57 * !eq C 0  * stack SH C * ... -o { pc PC' * ... }
```

| Property | Value |
|---|---|
| CLF compliance | Yes (guard is rule antecedent, not in monad) |
| Ground correctness | Yes (guard checked during matching) |
| Symbolic support | No (neither rule fires) |
| Commuting matches | No |
| Complexity | Medium (duplicate rules, no oplus) |

### Encoding D: Tensor-in-oplus + decidability + zero (proposed)

```
((!neq C 0 ⊗ pc NPC) ⊕ (!eq C 0 ⊗ pc PC'))
```

Plus: additive zero (`0`) as a connective, contradiction axioms, and decidability-aware expansion.

| Property | Value |
|---|---|
| CLF compliance | Yes (tensor+bang in monad; 0 is standard ILL) |
| Ground correctness | Yes (decidable guards checked at expansion; false → 0 → branch eliminated) |
| Symbolic support | Yes (non-ground guards become path conditions) |
| Commuting matches | No |
| Complexity | Medium-high (needs 0, contradiction axioms, decidability check) |

## Theory-Internal Branch Pruning via Additive Zero

This is the crucial piece that makes Encoding D work without external oracles.

### Additive zero (0) in ILL

The additive false `0` is a standard ILL connective with one rule:

```

─────────── 0_L       (no 0_R rule exists — 0 is unprovable)
Γ, 0 ⊢ C
```

`0_L` has **no premises**. If `0` appears in the linear context, the branch is **immediately closed** — it's the linear logic version of *ex falso quodlibet*.

### The key isomorphism: A ⊕ 0 ≅ A

```
                                ───── Id        ─────── 0_L
───── Id                         A ⊢ A           0 ⊢ A
A ⊢ A ⊕ 0  (via ⊕R₁)          ─────────────────────── ⊕L
                                      A ⊕ 0 ⊢ A
```

If one branch of an oplus produces `0`, that branch is trivially eliminable. The oplus collapses to the surviving branch.

### Contradiction axioms as forward rules

Add these as forward rules in the calculus:

```
contra/eq_neq: !eq X Y * !neq X Y -o { 0 }.
```

When the same state contains both `!eq X Y` and `!neq X Y`, this rule fires and produces `0`. The `0` in the linear context triggers `0_L`, eliminating the branch.

**For ground C = 5 with tensor encoding:**

1. Oplus expands into two branches
2. Branch 0: state has `!neq 5 0` (asserted) — no contradiction, continues
3. Branch 1: state has `!eq 5 0` (asserted) — but is `!neq 5 0` also present?

**Problem:** `!neq 5 0` is NOT in the persistent state on Branch 1. It's on Branch 0. The two assertions are on separate oplus branches. The contradiction axiom doesn't fire because both facts are never in the same state.

### Why contradiction axioms alone aren't enough (for single-step guards)

The contradiction axiom `!eq X Y * !neq X Y -o { 0 }` requires both facts in the same state. But in the basic case, `!neq C 0` and `!eq C 0` are produced on **different** branches.

**When contradiction axioms ARE useful:** accumulated path conditions. After multiple branches:

```
Step 1: JUMPI branches on C → path asserts !neq C 0
Step 2: EQ compares C with 0 → path asserts !eq C 0
Contradiction: !neq C 0 * !eq C 0 → 0 → branch dead
```

This catches **accumulated contradictions** across multiple branch points — exactly the infeasible path detection that symbolic execution needs.

### Decidability-aware expansion (for single-step guards)

For ground, decidable guards at the point of oplus expansion:

**Principle:** For a decidable predicate P with ground arguments, `P ∨ ¬P` holds constructively (Martin-Löf's `Dec(A)`). We can compute which branch is valid.

**Mechanism:** When `expandConsequentChoices` processes an oplus branch containing `!P(t₁,...,tₙ)`:

1. If all arguments are ground and P is decidable:
   - If `P(t₁,...,tₙ)` is true: produce the fact normally
   - If `P(t₁,...,tₙ)` is false: replace the entire branch with `0`
2. If any argument is non-ground: produce the fact as-is (path condition)

**This is theory-clean because:**
- The decidability check is justified by `Dec(P)` — not an oracle, but a theorem about the predicate
- The `0` production is standard ILL
- The `A ⊕ 0 ≅ A` isomorphism eliminates the dead branch
- For non-ground terms, the fact becomes a path condition (standard symbolic execution)

### The full picture: three layers of pruning

```
Layer 1: Decidability check at expansion (single-step, ground guards)
  → Ground eq/neq decided by FFI/clauses → dead branch becomes 0

Layer 2: Contradiction axioms as forward rules (multi-step, accumulated path conditions)
  → !eq X Y * !neq X Y in same state → 0 → branch eliminated

Layer 3: Constraint propagation (future, for richer reasoning)
  → !eq X Y * !neq Y Z * !eq X Z → transitivity → contradiction
  → Requires propagation rules (CHR-style solver in ILL)
```

Each layer is independently correct and theory-internal.

## Ground vs Symbolic: Unified Semantics

### Ground execution (all variables instantiated)

1. Oplus expands into N branches
2. Each branch's guard is decidable (ground args + decidable predicate)
3. Decidability check replaces false branches with `0`
4. Only true branch survives
5. Result: deterministic execution, single path (like loli encoding today)

### Symbolic execution (some variables uninstantiated)

1. Oplus expands into N branches
2. Each branch's guard has non-ground args — NOT decidable
3. Guard is produced as persistent fact (path condition)
4. Both branches explored
5. Contradiction axioms detect accumulated inconsistencies
6. Result: forking execution with path conditions (standard symbolic execution)

### Mixed execution (some guards ground, some symbolic)

Both mechanisms work simultaneously. Ground guards get decided. Symbolic guards become path conditions. No special cases needed.

## What Needs to Be Added to the Calculus

### 1. Additive zero connective

Add `0` to `calculus/ill/ill.calc`:
```
zero: formula
  @ascii "0"
  @latex "\\mathbf{0}"
  @category additive
  @polarity positive.
```

### 2. Zero-left rule

Add to `calculus/ill/ill.rules`:
```
zero_L: Γ, 0 ⊢ C.
```
(No premises — the sequent is immediately provable.)

### 3. Contradiction axioms

Add as forward rules (in EVM programs or a shared prelude):
```
contra/eq_neq: !eq X Y * !neq X Y -o { 0 }.
```

Optionally, for richer theories:
```
contra/gt_eq: !gt X Y * !eq X Y -o { 0 }.
```

### 4. Decidability-aware oplus expansion

Modify `expandConsequentChoices` in `compile.js` to check ground decidable guards and replace false branches with `0`.

### 5. Zero handling in forward engine

When `0` appears in the linear state, the state is immediately quiescent (no rules can fire on `0`). The engine returns a `{ type: 'leaf', state }` with `0` in it, classified as an infeasible branch.

Alternatively: detect `0` production and return a `{ type: 'dead' }` node (new tree node type for pruned branches — cleaner than letting them become stuck leaves).

## Decision: Tensor vs Loli vs Hybrid

### Recommendation: Tensor (Encoding D) with decidability + zero

**Why tensor, not loli:**
1. **CLF compliance**: tensor+bang is allowed in the monad. Loli is not.
2. **Symbolic execution**: tensor produces path conditions naturally. Loli blocks both branches.
3. **No commuting matches**: tensor produces no deferred computation. No fusion hack needed.
4. **Simpler engine**: no `matchLoli` needed for guard resolution — it's just fact production.

**Why decidability check, not blind assertion:**
1. **Ground correctness**: blind tensor asserts false facts. Decidability check prevents this.
2. **Theory-clean**: justified by `Dec(P)` (constructive excluded middle for decidable predicates).
3. **Compatible with symbolic**: non-ground guards pass through as path conditions.

**Why zero, not external pruning:**
1. **Theory-internal**: `0` is a standard ILL connective with well-understood proof theory.
2. **`A ⊕ 0 ≅ A`**: dead branch elimination is a theorem, not a hack.
3. **Composable**: contradiction axioms can catch accumulated path condition inconsistencies.
4. **No oracle dependency**: no Z3/SMT needed for basic pruning.

## Impact on Existing Code

### Rules affected (EVM)

Only 3 rules use loli-in-oplus:
- `evm/eq` (lines 259-279)
- `evm/iszero` (lines 281-296)
- `evm/jumpi` (lines 830-845)

The 3 plain-oplus rules (`evm/call`, `evm/delegatecall`, `evm/staticcall`) are unchanged — they have no guards.

### Engine changes

| Component | Change |
|---|---|
| `ill.calc` | Add `zero` connective |
| `ill.rules` | Add `zero_L` rule |
| `compile.js` | Decidability-aware `expandConsequentChoices` |
| `symexec.js` | Detect `0` in state → dead branch |
| `tree-utils.js` | Optional: `dead` node type |
| `match.js` | `drainPersistentLolis` becomes unnecessary for guard lolis |
| `evm.ill` | Rewrite 3 rules: loli → tensor |

### What becomes unnecessary

- Loli fusion (TODO_0054 Option C) — no persistent-trigger lolis from guards
- `matchLoli` for guard-only lolis — guards are resolved at expansion, not runtime
- State memoization for guard commuting — no commuting to memoize

Note: `matchLoli` is still needed for other lolis (linear-trigger lolis, non-guard deferred computations). And memoization is still useful for other sources of state duplication.

## Research Directions

### R1: Constraint propagation rules as forward rules (CHR-in-ILL)

Write the constraint solver as forward rules in the calculus:

```
% Transitivity
prop/eq_trans: !eq X Y * !eq Y Z -o { !eq X Z }.

% Substitution into neq
prop/neq_eq: !neq X Y * !eq X Z -o { !neq Z Y }.

% Contradiction
contra/eq_neq: !eq X Y * !neq X Y -o { 0 }.
```

**Research questions:**
- Termination: can propagation rules loop? (e.g., `!eq X Y → !eq Y X → !eq X Y → ...`)
- Completeness: do the propagation rules catch all contradictions?
- Interaction with forward execution: when do propagation rules fire relative to EVM rules?
- Connection to CHR: these ARE CHR propagation rules. Can we use CHR confluence/termination analysis?

### R2: Decidability as a type-level property

Annotate predicates with decidability:

```
eq: bin -> bin -> type @decidable.
neq: bin -> bin -> type @decidable.
plus: bin -> bin -> bin -> type @decidable.
```

The `@decidable` annotation tells the engine that for ground arguments, the predicate can be fully evaluated. This replaces the current ad-hoc FFI registration with a theory-level concept.

**Connection to Martin-Löf type theory:** `Dec(A) = A + (A → 0)`. For decidable predicates, we have a procedure that returns either a proof or a refutation. This is exactly what the FFI provides.

### R3: Relationship to focused proof search

In Andreoli's focusing discipline:
- `0` is positive (synchronous). Its left rule `0_L` is invertible → applied eagerly in the asynchronous phase.
- When `0` appears in the context during the asynchronous phase, the branch is immediately closed.
- This integrates naturally with the focusing-based proof search that CALC's backward prover uses.

**Question:** Can the forward engine's oplus expansion be seen as a focusing phase? The oplus right rules (`⊕R₁`, `⊕R₂`) are non-invertible — choosing a branch is a synchronous (focused) operation. The decidability check determines which branch to focus on.

### R4: Connection to CHC (Constrained Horn Clauses)

Our tensor encoding `(!neq C 0 ⊗ pc NPC)` parallels CHC's constraint-in-clause-body encoding:

```
% CHC:
post(NPC) :- pre(PC, C), C ≠ 0.
post(PC')  :- pre(PC, C), C = 0.
```

The guard `C ≠ 0` is a constraint in the background theory. CHC solvers (Spacer, Eldarica) use SMT to check satisfiability.

**Question:** Can CALC's persistent predicates serve as a constraint theory? The backward clauses define the theory (like CHC's background theory). The FFI provides decision procedures. The contradiction axioms internalize theory consequences. Is this a complete CHC encoding?

### R5: Path condition satisfiability without SMT

For simple constraints (eq, neq on binary numbers with mostly-ground terms), can we avoid SMT entirely?

**Approach:** Union-find for equality + complement checking for inequality.
- `!eq X Y` → union X and Y
- `!neq X Y` → check if X and Y are in the same equivalence class. If yes → contradiction.
- O(α(n)) per operation — effectively O(1).

This is a specialized constraint solver for the equality/inequality fragment, implementable as forward rules or FFI. Theory-clean (union-find is a decision procedure for the theory of equality).

### R6: The SSOS connection

Pfenning and Simmons' SSOS (Substructural Operational Semantics) encodes conditionals as two forward rules with pattern matching on concrete values:

```
retn(true,  D') * cont(D', if_cont(E2,E3), D) -o eval(E2, D).
retn(false, D') * cont(D', if_cont(E2,E3), D) -o eval(E3, D).
```

The branching is implicit in rule matching — no oplus, no guards. For symbolic values, neither rule matches, and execution is stuck (same as our Encoding C).

**Question:** Can we combine SSOS-style matching with oplus-style branching? The concrete case uses matching. The symbolic case uses oplus with path conditions. This would be a two-mode system: concrete → deterministic matching, symbolic → nondeterministic branching with constraints.

## Implementation Phases

### Phase 0: Theory validation
- Formalize the decidability-aware oplus expansion
- Prove: for decidable P with ground args, `(!P ⊗ A) ⊕ (!¬P ⊗ B)` with P false reduces to `0 ⊕ B ≅ B`
- Verify the contradiction axiom is a valid ILL derivation

### Phase 1: Add zero to the calculus
- Add `zero` connective to `ill.calc`
- Add `zero_L` rule to `ill.rules`
- Rebuild `out/ill.json`
- Update backward prover to handle `zero_L`

### Phase 2: Decidability-aware expansion
- Modify `expandConsequentChoices` in `compile.js`
- Detect bang-terms in oplus branches
- Check groundness + call FFI for decidable predicates
- Replace false branches with `0`

### Phase 3: Zero handling in forward engine
- Detect `0` in linear state after rule application
- Return appropriate tree node (dead/pruned)
- Update tree-utils for new node type

### Phase 4: Rewrite EVM rules
- Change 3 rules from loli-in-oplus to tensor-in-oplus
- Add contradiction axiom (`contra/eq_neq`)
- Verify all tests pass with new encoding

### Phase 5: Remove fusion hack
- Once tensor encoding is verified, the loli fusion from TODO_0054 Option C becomes unnecessary for guard lolis
- Keep memoization (Option E) as general safety net
- Keep `matchLoli` for non-guard lolis

## References

### Linear logic and zero
- Girard (1987) "Linear Logic" — additive zero `0`, `0_L` rule, `A ⊕ 0 ≅ A`
- Braüner (1996) "Introduction to Linear Logic" — BRICS-LS-96-6, clear presentation of additive units
- Pfenning (CMU 15-317) Lecture notes on linear logic — sequent calculus rules for `0` and `⊤`

### CLF and the monad
- Watkins, Cervesato, Pfenning, Walker (2004) "A Concurrent Logical Framework" — CLF type grammar, monad restrictions
- Watkins et al. (2004) "CLF: The Propositional Fragment" — synchronous types in monad: `S ::= P | S₁ ⊗ S₂ | 1 | !A | ∃x.S`

### Symbolic execution and path conditions
- King (1976) "Symbolic Execution and Program Testing" — original formulation
- Baldoni et al. (2018) "A Survey of Symbolic Execution Techniques" — comprehensive survey
- Cadar, Dunbar, Engler (2008) "KLEE: Unassisted and Automatic Generation of High-Coverage Tests" — practical SE

### Constraint logic programming
- Jaffar & Lassez (1987) "Constraint Logic Programming" — CLP(X) framework
- Jaffar, Maher et al. (1994) "Constraint Logic Programming: A Survey" — constraint theory integration

### CHR and contradiction handling
- Fruhwirth (1998) "Theory and practice of Constraint Handling Rules" — `fail` built-in, contradiction rules
- Fruhwirth (2009) "Constraint Handling Rules" — comprehensive treatment

### Negation in linear logic
- Cerrito (1992) "A linear axiomatization of negation as failure"
- Stuckey (1991) "Constructive negation for CLP" — constructive complement computation
- Fages (1997) "Constructive negation by pruning"

### Focusing and proof search
- Andreoli (1992) "Logic Programming with Focusing Proofs in Linear Logic" — polarity of `0` (positive)
- Liang & Miller (2009) "Focusing and Polarization in Linear, Intuitionistic, and Classical Logics"

### SSOS
- Pfenning & Simmons (2009) "Substructural Operational Semantics as Ordered Logic Programming"
- Simmons (2012) "Substructural Logical Specifications" — PhD thesis

### Decidability and constructive logic
- Martin-Löf (1984) "Intuitionistic Type Theory" — `Dec(A) = A + (A → 0)`

### Existing CALC theory
- [THY_0001](../theory/0001_exhaustive-forward-chaining.md) — loli-in-monad extension
- [THY_0004](../theory/0004_symbolic-branching.md) — oplus for symbolic branching
- [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) — three problems of symbolic values
- [TODO_0054](0054_commuting-match-reduction.md) — commuting match reduction (fusion hack)
- [TODO_0005](0005_symexec-simplification.md) — constraint propagation levels
- [RES_0049](../research/0049_constraint-propagation-systems.md) — CLP/CHR survey
- [RES_0039](../research/0039_symbolic-arithmetic-design-space.md) — symbolic arithmetic design space
