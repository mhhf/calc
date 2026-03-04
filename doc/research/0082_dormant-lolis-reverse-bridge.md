---
title: "Dormant Lolis and the Reverse Bridge: Residual Linear Implications Across Mode Boundaries"
created: 2026-03-04
modified: 2026-03-04
summary: "Analysis of what happens to dormant loli continuations when the forward engine returns to the backward prover, surveying analogous phenomena in CHR, CLP, partial evaluation, and tabled resolution."
tags: [loli, lax-monad, forward-chaining, backward-chaining, quiescence, clf, chr, residuation, soundness, completeness, resource-semantics, partial-evaluation, CLP, theory]
category: "Forward Chaining"
---

# Dormant Lolis and the Reverse Bridge

## Problem Statement

When CALC's forward engine reaches quiescence inside the lax monad `{S}`, the resulting state may contain **dormant lolis** -- linear implications `!G -o B` whose guard `G` is unprovable in forward mode. The reverse bridge must convert this state back to the backward prover's context. The question: what should happen to these dormant resources?

This situation is unique to CALC. CLF, LolliMon, SLS, and Ceptre all forbid lolis inside the monadic state (see RES_0080), so the problem never arises in the standard theory.

## 1. Existing Systems with Analogous Problems

### 1.1 No Direct Precedent Exists

No existing linear logic system has this exact problem:

- **CLF** (Watkins et al. 2004): Forbids loli inside `{S}`. States are flat (atoms, tensor, bang, exists). Quiescence yields only atomic residuals.
- **LolliMon** (Lopez et al. 2005): Inherits CLF's restriction. Monadic state is a multiset of atoms.
- **Ceptre** (Martens 2015): All-forward design with no backward mode to return to. Quiescent state is the final answer.
- **SLS** (Simmons 2012): States are atomic propositions. Rules are the program, not in the state.
- **Lygon** (Harland, Pym, Winikoff 2000): Mixed-mode computation in linear logic for BDI agents. Forward and backward chaining interact, but the state remains atomic -- no compound formulas cross mode boundaries.

### 1.2 CHR Embedded in Prolog: The Closest Analogy

**CHR** (Constraint Handling Rules) embedded in Prolog provides the closest analogy. CHR maintains a global constraint store. When CHR reaches quiescence (no more rules fire), residual constraints remain in the store. The Prolog host can then reason about these residual constraints.

Key mechanisms:
- `find_chr_constraint/1` extracts residual constraints from the CHR store into Prolog's reasoning
- `call_residue_vars/2` finds attributed variables left by constraint goals
- `copy_term/3` makes constraint associations available as Prolog terms

**Analogy to CALC:**

| CHR + Prolog | CALC |
|---|---|
| CHR constraint store | Forward engine state |
| Prolog host language | Backward prover (L2/L3) |
| CHR quiescence | Forward quiescence |
| Residual CHR constraints | Dormant lolis + unconsumed atoms |
| `find_chr_constraint/1` | Reverse bridge (state -> sequent context) |
| Prolog reasoning about residuals | Backward prover decomposing compound formulas |

**Critical difference:** CHR constraints are atomic (first-order terms). They do not contain implications. Prolog can reason *about* them but cannot *decompose* them structurally. CALC's dormant lolis are compound formulas (linear implications) that the backward prover CAN decompose via loli-left/loli-right.

### 1.3 CLP Delayed Goals: Waking Across Modes

Constraint Logic Programming (CLP) has "delayed goals" -- goals suspended until variables become sufficiently instantiated. When instantiation occurs, delayed goals "wake up" and execute. This is implemented via Prolog's coroutining primitives (`freeze/2`, `when/2`).

**Analogy:** A dormant loli `!G -o B` is like a delayed goal waiting for `G` to become provable. In CLP, when the host computation provides more information (binds a variable), the delayed goal wakes. In CALC, when the backward prover provides more reasoning power (clause resolution unavailable to forward), the dormant loli could "wake."

**Key insight from CLP:** Delayed goals that remain at the end of computation are called **floundered** goals. A floundered computation is considered incomplete -- the answer is conditional on the residual constraints being satisfiable. SWI-Prolog displays floundered constraints as part of the answer.

### 1.4 Tabled Resolution: Partial Answers

XSB Prolog's tabled resolution computes partial answers that are incrementally completed. When a tabled goal encounters a cycle, it suspends and returns a partial answer. Later, when more complete answers become available, suspended computations resume.

**Analogy:** Forward quiescence produces a "partial answer" (the state including dormant lolis). The backward prover could complete the answer by resolving the dormant guards. The dormant lolis are analogous to suspended tabled computations waiting for more answers.

## 2. Partial Evaluation / Residualization

In partial evaluation, a program is specialized with respect to known (static) inputs. Computations that depend on unknown (dynamic) inputs cannot be evaluated and are **residualized** -- left as code in the output program. When dynamic inputs become available at runtime, the residual code executes.

**Precise analogy:**

| Partial Evaluation | CALC |
|---|---|
| Static inputs | Facts provable by forward engine (state + FFI) |
| Dynamic inputs | Facts only provable by backward prover |
| Evaluation | Forward rule firing |
| Residualization | Dormant loli remaining in state |
| Residual program | Collection of dormant lolis |
| Runtime execution of residual | Backward prover decomposing dormant lolis |

A dormant loli `!G -o {B}` is a **residual computation**: "if G becomes provable, produce B." The forward engine residualizes it because G is dynamic (not available in forward mode). The backward prover is the "runtime" where the dynamic input may become available.

**The analogy is strong and suggests design (a) -- return dormant lolis as-is.** Just as a residual program is valid code awaiting execution, dormant lolis are valid resources awaiting their guard.

## 3. Linear Logic Resource Semantics

### 3.1 A Dormant Loli Is a Capability

A linear formula `!G -o B` in the context represents a **capability**: "given evidence of G (which can be reused), produce B (consuming this capability)." It is NOT an obligation. Having an unfired capability at quiescence is semantically valid -- it means the triggering condition never arose.

From the proof theory: the loli `!G -o B` can be eliminated via loli-left:

```
  Gamma, !G -o B |- C
  ─────────────────────── loli-L
  Gamma, !G, !G -o B |- C
```

But loli-left requires `!G` to be provable. If the forward engine cannot prove `G`, loli-left simply does not apply. The formula remains in the context as an unconsumed resource.

### 3.2 The Power Asymmetry

The forward engine proves persistent goals via a specific pipeline:

```
provePersistentGoals: FFI → state lookup → backward clause resolution
```

Each level has limitations:
- **FFI:** Only handles registered predicates (arithmetic: inc, plus, neq, mul, memory operations). Returns definitive failure for registered predicates.
- **State lookup:** Only matches against facts already in `state.persistent`.
- **Clause resolution:** Uses `prove.js` with a depth limit (maxDepth: 50). Only available when `calc.clauses` is provided.

The backward prover (L2/L3) has strictly more power:
- Full focused proof search with backtracking
- Access to all inference rules (not just compiled forward rules)
- Full linear context manipulation (context splitting, multiplicative/additive distribution)
- No committed choice -- can explore alternatives

Therefore, there exist guards `G` that are:
- **Unprovable by forward:** FFI not registered, not in persistent state, clause resolution fails or exceeds depth
- **Provable by backward:** Full focused search finds a proof

### 3.3 When Does the Power Asymmetry Matter?

In CALC's current EVM symbolic execution use case, loli guards are typically:
- `!eq X Y` -- equality of symbolic values
- `!neq X Y` -- inequality of symbolic values
- `!inc N N1` -- successor relation

These are all resolved by FFI (ground arithmetic). If FFI fails, backward clause resolution also fails (the guards involve ground arithmetic that either holds or doesn't). **For ground arithmetic guards, the power asymmetry is irrelevant.**

But CALC is not limited to EVM. Consider a hypothetical program:

```ill
% Forward rule producing a guarded loli
step: state(X) -o { state(f(X)) * (!reachable(X, Y) -o { output(Y) }) }.

% Backward clauses for reachable (transitive closure)
reachable/base: !edge(X, Y) -o reachable(X, Y).
reachable/step: !edge(X, Z) * !reachable(Z, Y) -o reachable(X, Y).
```

Here `!reachable(X, Y)` is provable by backward clause resolution (transitive closure over edges) but NOT by FFI or state lookup alone. The forward engine would leave `!reachable(X, Y) -o { output(Y) }` dormant. The backward prover could prove `reachable(X, Y)` via clause resolution and fire the loli.

**Conclusion:** The power asymmetry is real in general, even though it does not manifest for CALC's current EVM use case.

## 4. Soundness Analysis

### 4.1 The Core Question

If dormant lolis return to the backward prover as compound formulas in the linear context, the backward prover could decompose them:

```
  !G -o {B}  in context
  ──────────────────────── loli-L (backward prover decomposes)
  prove !G, then prove {B}
```

The backward prover succeeds where forward declared quiescence. Is this sound?

### 4.2 Soundness Argument (Design a: Return As-Is)

**Yes, this is sound.** The argument:

1. The forward engine runs inside the monad `{S}`. At quiescence, it produces a multiset of linear resources (the state), which may include dormant lolis.

2. The monad's elimination rule (`{}E` / `let`) binds the result:
```
  Delta |-_fwd S    (forward engine proved S)
  ──────────────────
  Delta |- {S}      (monad introduction)
```

3. The "S" here is the entire state at quiescence, including dormant lolis. So S contains terms of the form `!G -o B`.

4. When the backward prover receives S, it has these formulas in its linear context. The backward prover is free to apply any applicable rule, including loli-left on `!G -o B`.

5. If the backward prover can prove `!G`, then firing the loli is a valid proof step. There is no invariant being violated -- the forward engine merely *failed to* fire the loli, it did not *prohibit* firing it. Quiescence means "no more forward steps possible," not "no more proof steps possible."

6. The compound formula `loli(bang(G), monad(B))` in the context is a legitimate linear formula. The backward prover's rules for loli-left are sound. Applying them is a sound proof step.

**No invariant is broken.** Forward quiescence is a property of the forward engine's search strategy, not a logical guarantee. The backward prover having more reasoning power is expected -- that is the entire point of the monad boundary (forward is restricted, backward is general).

### 4.3 Analogy: Incomplete Search vs Unsatisfiability

Forward quiescence is like a SAT solver timing out. The solver says "I couldn't find a solution in the time allotted." This does not mean the problem is unsatisfiable. A more powerful solver (backward prover) may find a solution. Passing the residual formula to a more powerful solver is sound -- the formula has not changed, only the solver's capability.

## 5. Design Analysis

### 5.1 Design (a): Return Dormant Lolis As-Is

The backward prover receives the full state including `!G -o {B}` as linear formulas in its context.

**Soundness:** Sound. Every proof step the backward prover takes is justified by the proof rules. Loli-left on `!G -o B` is valid when `!G` is provable.

**Completeness:** Maximally complete. The backward prover can use all available resources, including dormant capabilities. If a proof exists that uses a dormant loli, design (a) finds it.

**Composability:** Excellent. The reverse bridge is a simple identity on the state. No information is lost. The backward prover sees exactly what the forward engine produced.

**Implementation:** The reverse bridge converts each hash in the forward state to a formula in the backward context. Compound formulas (lolis) are converted like any other formula. No special-casing needed.

**Caveat:** The backward prover must handle `monad(B)` formulas. If the body of a dormant loli is `{B}` (a monadic computation), the backward prover encountering it would need monad_r to switch back to forward mode. This creates a potential re-entrant loop: backward -> forward (quiescence, dormant loli) -> backward (fires loli) -> forward (inner monad). Each re-entry is at a strictly smaller state (the loli is consumed), so termination is guaranteed for acyclic programs.

### 5.2 Design (b): Strip Dormant Lolis

Remove all unfired lolis from the state before returning to the backward prover.

**Soundness:** Sound but trivially so -- we are discarding resources, which is a form of weakening. But linear logic does NOT admit weakening for linear resources. Discarding a linear loli violates linearity.

**In practice:** Only sound if we treat the stripped lolis as having been consumed with no effect, which requires either:
- An explicit `zero` / additive-false rule (the loli's capability is annihilated)
- A garbage-collection convention (the system agrees that unclaimed capabilities are void)

Neither has a clean proof-theoretic justification in ILL.

**Completeness:** Incomplete. If a proof exists that uses a dormant loli, design (b) cannot find it.

**Composability:** Poor. Information is lost. Downstream consumers cannot observe or use dormant capabilities.

**Verdict:** Unsound in pure ILL (violates linearity). Only acceptable in a system with explicit weakening for all types (affine logic), which CALC is not.

### 5.3 Design (c): Separate Residual Category

Return dormant lolis as a separate "residual" set, distinct from the main context.

**Soundness:** Sound, provided the residuals can be used in future proof steps. This is essentially design (a) with extra bookkeeping.

**Completeness:** Depends on whether the backward prover has access to the residual set. If yes, equivalent to (a). If no, equivalent to (b).

**Composability:** Moderate. Consumers must be aware of two categories (main context + residuals). This complicates the interface.

**Use case:** Design (c) is useful for *analysis* -- the caller can inspect which capabilities went unused and decide what to do with them (warn, retry with different strategy, pass to backward prover). But as a default semantics, design (a) is simpler and strictly more general.

**CLP parallel:** CLP's `call_residue_vars/2` is essentially design (c) -- residual constraints are kept separate from the main answer and can be inspected.

## 6. Does This Arise in Practice?

### 6.1 Current EVM Use Case: No

In CALC's EVM symbolic execution:
- Loli guards are `!eq X Y`, `!neq X Y`, `!inc N N1`, `!plus X Y Z`
- All resolved by FFI (ground arithmetic on symbolic values)
- FFI either succeeds (loli fires) or definitively fails (loli remains dormant)
- Backward clause resolution for these predicates also fails (arithmetic is ground)
- **Forward and backward have the same power for these guards**

Dormant lolis in EVM execution have genuinely unprovable guards (e.g., `!eq X Y` where X and Y are distinct symbolic constants). No amount of backward reasoning helps.

### 6.2 General Case: Yes, It Can Arise

For non-ground or non-arithmetic guards, the power asymmetry is real:

1. **Transitive closure:** `!reachable(X, Y)` provable by backward clause resolution, not by forward FFI
2. **Type-level predicates:** `!hasType(E, T)` provable by backward type-checking rules
3. **Unification-dependent guards:** `!unifies(P, Q)` where backward uses full unification
4. **Recursive predicates:** Any recursively-defined persistent predicate with clauses in `calc.clauses`

### 6.3 When Forward and Backward Power Are Equal

The asymmetry disappears when:
- All persistent predicates have FFI handlers AND FFI returns are authoritative
- OR all persistent predicates are ground and in the state (state lookup suffices)
- OR `provePersistentGoals` in `match.js` uses the same clause resolution as the backward prover (currently it does, via `prove.js`, but with a depth limit)

## 7. Recommendation

**Design (a) is correct.** Return dormant lolis as-is in the context.

This is the only design that is both sound and complete in ILL, preserves linearity, and requires no special-casing. The partial evaluation analogy is precise: dormant lolis are residual computations that a more capable execution environment (the backward prover) may be able to complete.

For the current EVM use case, the design choice is irrelevant (dormant guards are genuinely unprovable). For future extensions with richer guard predicates, design (a) is the only correct choice.

**Implementation note for Option B (TODO_0006):** When implementing the reverse bridge (forward state -> backward context), convert each state entry to a formula in the linear context. Dormant lolis `!G -o {B}` become `loli(bang(G), monad(B))` in the context. The backward prover treats them as any other linear formula. No special handling required beyond supporting `monad` as a connective that triggers re-entry into forward mode.

## References

### Systems and Mode Boundaries
- Watkins, Cervesato, Pfenning, Walker. [CLF](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). (2004).
- Lopez, Pfenning, Polakow, Watkins. [LolliMon](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf). PPDP 2005.
- Simmons. [Substructural Logical Specifications](https://www.cs.cmu.edu/~rwh/students/simmons.pdf). PhD thesis, CMU (2012).
- Martens. [Ceptre](https://www.cs.cmu.edu/~cmartens/ceptre.pdf). AIIDE 2015.
- Harland, Pym, Winikoff. [Agents via Mixed-Mode Computation in Linear Logic](https://link.springer.com/article/10.1023/B:AMAI.0000034526.31830.45). AMAI 2004.

### CHR and Residual Constraints
- Duck, Stuckey, de la Banda, Holzbaur. [Refined Operational Semantics of CHR](https://www.comp.nus.edu.sg/~gregory/papers/iclp2004a.pdf). ICLP 2004.
- Betz, Fruhwirth. CHR with Disjunction. ACM TOCL 14(1) (2013).
- [SWI-Prolog CHR documentation](https://www.swi-prolog.org/pldoc/man?section=chr).
- [How are Prolog and CHR supposed to interact?](https://swi-prolog.discourse.group/t/how-are-prolog-and-chr-supposed-to-interact/7027). SWI-Prolog forum.

### CLP and Delayed Goals
- Jaffar, Maher. [Constraint Logic Programming: A Survey](https://courses.grainger.illinois.edu/cs522/sp2016/ConstraintLogicProgrammingASurvey.pdf). JLP 1994.
- [SWI-Prolog Coroutining](https://www.swi-prolog.org/pldoc/man?section=coroutining).
- [Transforming Floundering into Success](https://www.cambridge.org/core/journals/theory-and-practice-of-logic-programming/article/abs/transforming-floundering-into-success/C118E6B8ACBE5073A12F487E6E03F6E0). TPLP.

### Partial Evaluation
- Jones, Gomard, Sestoft. [Partial Evaluation and Automatic Program Generation](https://www.cs.utexas.edu/~novak/jonesgomardsestoft.pdf). Prentice Hall 1993.
- Albert, Vidal. [A Residualizing Semantics for Functional Logic Programs](https://www.researchgate.net/publication/222534260). I&C 2002.

### Tabled Resolution
- [XSB: Extending Prolog with Tabled Logic Programming](https://ar5iv.labs.arxiv.org/html/1012.5123). TPLP 2012.
- Swift, Warren. Tabling with Answer Subsumption. ICLP 2010.

### CALC Internal
- RES_0080 — Quiescence in Forward-Chaining Linear Logic Systems
- THY_0001 — Exhaustive Forward Chaining in MALL with the Lax Monad
- TODO_0006 — Lax Monad Integration (Option B mode switch design)
- RES_0081 — CLF Type Stratification and Definitional Equality
