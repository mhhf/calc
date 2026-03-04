---
title: "Forward-Backward Return Value in CLF, LolliMon, Celf, and Ceptre"
created: 2026-03-03
modified: 2026-03-03
summary: "How CLF-family systems handle the return value when forward chaining completes and control returns to backward chaining"
tags: [clf, lollimon, Celf, Ceptre, forward-chaining, backward-chaining, lax-monad, focusing, quiescence, proof-theory, operational-semantics, linear-logic]
category: "Related Paradigms"
---

## 1. CLF Proof Term Structure

CLF (Watkins, Cervesato, Pfenning, Walker 2002-2004) segregates proof terms into five syntactic categories:

```
R ::= c · S | x · S          (Atomic objects — destructor sequences)
N ::= λx.N | {E}             (Normal objects — intro forms)
E ::= let {p} = R in E | M   (Expressions — monadic sequencing)
M ::= 1 | M₁ ⊗ M₂ | !N     (Monadic objects — sync intros)
p ::= 1 | p₁ ⊗ p₂ | !x     (Patterns — sync destructors)
```

The monad introduction `{E}` wraps an expression `E`. The expression `E` is a sequence of `let`-bindings that decompose monadic results, ending in a monadic object `M`. This is the CLF analog of do-notation.

**Key insight**: `{E}` carries a full expression — not just a final state. The expression records the sequence of forward steps as `let`-bindings. Each `let {p} = R in E'` says "apply rule R, bind its synchronous outputs to pattern p, continue with E'."

### The {}I Rule (Monad Introduction)

The right rule for `{A}` is:

```
  Γ; Δ; · ⊢ E ← S
  ─────────────────── {}R
  Γ; Δ ⊢ {E} ← {S}
```

Where `S` is a synchronous type and `E` is an expression. The context `Ψ` (pattern context) must be empty at the boundary — all synchronous bindings are internal to the expression.

The lax modality `{A}` is **negative** (its right rule is invertible). This means: when backward chaining encounters a goal `{S}`, it immediately enters the monadic expression without choice.

### Definitional Equality

CLF identifies monadic expressions that differ only in the order of independent `let`-bindings. Two expressions `let {p₁} = R₁ in let {p₂} = R₂ in M` and `let {p₂} = R₂ in let {p₁} = R₁ in M` are definitionally equal when their variable dependencies allow reordering. This captures the concurrency inherent in forward chaining — independent rule firings are unordered.


## 2. LolliMon (Lopez, Pfenning, Polakow, Watkins, PPDP 2005)

LolliMon is "CLF without terms" — it implements the logic but not the proof term language.

### What the Forward Engine Returns

**(c) Nothing — just success/failure.** LolliMon's forward engine uses committed choice (no backtracking inside the monad). When backward chaining encounters a goal `{S}`:

1. The `{}R` rule fires (invertible — no choice)
2. The context is decomposed into synchronous connectives
3. Forward chaining runs to **quiescence** (saturation)
4. After quiescence, the system checks if the resulting state satisfies `S`
5. Returns **success** (with variable bindings) or **failure**

LolliMon does not construct proof terms. It returns variable substitutions on success (e.g., `Success with [L := b :: a :: nil]`).

### Committed Choice

Inside the monad, LolliMon uses committed choice: once a forward step fires, it is irrevocable. No backtracking occurs within the monadic phase. This contrasts with the backward phase (outside the monad), which uses Lolli-style backtracking search.

### Quiescence

Forward chaining runs until no more rules can fire. This is the only termination mode in LolliMon — there is no step bound or timeout. Quiescence means the multiset state has stabilized.


## 3. Celf (Schack-Nielsen, Schurmann, IJCAR 2008)

Celf implements full CLF type theory including proof terms. It provides the clearest picture of the forward-backward boundary.

### Backward-Forward Transition

From the Celf system description: "When searching for an object of an asynchronous type the algorithm proceeds by a backwards, goal-directed search (resembling pure Prolog), but when searching for an object of a synchronous type the algorithm shifts to an undirected, non-deterministic, forward-chaining, and concurrent execution, using committed choice instead of backtracking."

The critical operational description: A backward-chaining rule of the form `r : (S -o {S'}) -> A` is executed as:
1. Populate the context with `S` (the linear antecedents)
2. Run all forward-chaining rules to quiescence
3. After quiescence, search backward for a proof of `S'`

### What Celf Returns

Celf has three query modes with different return types:

| Directive | Returns | Details |
|-----------|---------|---------|
| `#query` | **Proof term** | Backward chaining finds an inhabitant of a type; forward chaining inside the monad produces `let`-bindings in the proof term |
| `#exec` | **Final state** | Forward chaining runs to quiescence, reports the end state (remaining linear context) |
| `#trace` | **Final state + intermediate steps** | Like `#exec` but also reports each forward step |

For `#query`, the forward phase **does construct proof terms**. The `forwardChain` function in `OpSem.sml` returns `(N, sty, ctxm)` triples — a matched proof term `N`, its synchronous type `sty`, and the updated context `ctxm`. These are wrapped in `Let'(p, N, E)` constructors, building the monadic expression incrementally.

For `#exec`/`#trace`, the forward phase returns the **final multiset state** without proof terms. The step bound (first argument) controls termination: a specific number forces exactly that many steps; `*` runs to quiescence.

### Quiescence in Celf

When `forwardChain` finds no more applicable rules, it falls through to `rightFocus` with `genMon`, initiating backward search on the remaining goal. This is the quiescence boundary — forward chaining exhausts itself, then the system attempts to satisfy the monadic goal `S'` by backward search against the resulting state.


## 4. Ceptre (Martens, CMU thesis 2015)

Ceptre is purely forward-chaining — it does not have the CLF backward-forward-backward sandwich. Instead it uses **stages** to structure control flow.

### Stages and Quiescence

A stage is a named set of forward-chaining rules. Execution within a stage runs to quiescence (no more applicable rules). Transitions between stages are governed by rules that match the `qui` predicate:

```
qui * stage play * team_turn T * opp T T' -o stage generate_turns * team_turn T'.
qui * stage generate_turns -o stage play.
```

The `qui` token appears in the state when a stage reaches quiescence. Stage transition rules consume `qui` and the current stage marker, producing the next stage marker.

### What a Stage Returns

A stage returns **the final multiset state**. There is no proof term. The state is the collection of linear and persistent predicates that remain after all rules have been exhausted.

Ceptre records a **trace** of let-bindings showing which rules fired:
```
let [x4] = rule [x1, []];
let [x5] = rule [x2, []];
let [x6] = rule [x3, []];
```

This trace is the CLF monadic expression in operational form — each `let` corresponds to a forward step.

### Backward Chaining in Ceptre

Ceptre supports `bwd` predicates for backward-chaining rules that can compute persistent facts. These are not part of the main forward engine but serve as derived predicates (similar to CALC's `prove()` for persistent antecedents).


## 5. Focusing and the Synchronous/Asynchronous Boundary

### Chaudhuri-Pfenning-Price (IJCAR 2006, JAR 2008)

This paper characterizes forward and backward chaining as consequences of **focusing bias on atoms**:

- **Positive bias on atoms** → forward chaining (hyperresolution). Rules are applied when antecedents are available. Focus produces new facts.
- **Negative bias on atoms** → backward chaining (SLD resolution). Rules are applied when a goal matches a conclusion. Focus decomposes goals.

The synchronous focus phase "returns" to the asynchronous phase through **release** (sometimes called blur):

```
  Γ; Δ ⊢ A ↑        (asynchronous — invertible rules, no choice)
  Γ; Δ; A ↓ ⊢ C     (synchronous — focused, committed)
```

When the synchronous phase exhausts its focused formula (reaching an atom or a negative connective), it releases focus and returns to the asynchronous phase. The transition carries the **accumulated context changes** — new facts produced by forward steps, or decomposed goals from backward steps.

### Connection to CLF

In CLF terms:
- **Asynchronous phase** = backward chaining (outside the monad). Goal-directed, invertible decomposition.
- **Synchronous phase** = forward chaining (inside the monad). Committed-choice multiset rewriting.
- **`{}`R rule** = the transition from async to sync. Invertible (negative polarity of `{A}`), enters immediately.
- **Quiescence** = the sync phase has no more focused steps. Returns to async to check remaining goals.

The return value at the phase boundary is:
- In proof theory: the **accumulated synchronous proof fragment** (let-bindings)
- In Celf: `(proofTerm, syncType, updatedContext)`
- In LolliMon: just the updated context + success/failure
- In Ceptre: the final state multiset


## 6. Forward Termination Modes

| System | Quiescence | Step Bound | Timeout | Cycle Detection |
|--------|-----------|------------|---------|-----------------|
| CLF (theory) | Yes (defined) | No | No | No |
| LolliMon | Yes (only mode) | No | No | No |
| Celf | Yes (default `*`) | Yes (exact count) | No | No |
| Ceptre | Yes (per stage) | No | No | No |

**Quiescence**: All systems terminate when no more rules can fire. This is the primary termination mode.

**Step bound**: Only Celf supports a step bound (first argument to `#query`/`#exec`). It forces exactly N forward steps — no more, no fewer. If fewer steps are possible, the query fails.

**Timeout/Cycle**: None of these systems have built-in timeout or cycle detection for forward chaining. Non-termination is possible if forward rules can fire indefinitely.

Note: CALC's `symexec.explore` adds structural memoization for cycle detection and a step/node bound — features absent from the original CLF family.


## 7. Summary Table

| Question | CLF (theory) | LolliMon | Celf | Ceptre |
|----------|-------------|----------|------|--------|
| Forward returns what? | Monadic expression `E` (let-bindings) | Success/failure + substitution | Proof term or final state (mode-dependent) | Final state + trace |
| Proof terms? | Yes (`{E}` with let-bindings) | No (term-free) | Yes (for `#query`) | No (traces only) |
| Carries state? | Implicit in expression | Yes (context) | Yes (context) | Yes (multiset) |
| Forward termination | Quiescence | Quiescence | Quiescence or step bound | Quiescence (per stage) |
| Backward resumes? | After sync phase completes | After quiescence | After quiescence, checks S' | Via stage transitions |


## References

- Watkins, Cervesato, Pfenning, Walker. "A Concurrent Logical Framework I: Judgments and Properties." CMU-CS-02-101, 2002.
- Watkins, Cervesato, Pfenning, Walker. "A Concurrent Logical Framework: The Propositional Fragment." TYPES 2003.
- Watkins, Cervesato, Pfenning, Walker. "CLF: A Dependent Logical Framework for Concurrent Computations." 2004.
- Lopez, Pfenning, Polakow, Watkins. "Monadic Concurrent Linear Logic Programming." PPDP 2005.
- Chaudhuri, Pfenning, Price. "A Logical Characterization of Forward and Backward Chaining in the Inverse Method." IJCAR 2006 / JAR 2008.
- Schack-Nielsen, Schurmann. "Celf — A Logical Framework for Deductive and Concurrent Systems." IJCAR 2008.
- Simmons, Pfenning. "Linear Logical Algorithms." ICALP 2008.
- Martens. "Programming Interactive Worlds with Linear Logic." CMU PhD thesis, 2015.
