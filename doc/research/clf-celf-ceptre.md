# CLF, Celf, and Ceptre: Research for CALC v2 Integration

**Date:** 2026-02-02
**Status:** Research Complete
**Goal:** Understand what machinery is needed to reimplement CLF/Celf/Ceptre in CALC v2

---

## Executive Summary

> **See also:** [[typed-dsl-logical-framework]] for logical frameworks (LF, CLF, Twelf), [[ffi-logics]] for FFI patterns.

To achieve full CLF/Celf/Ceptre compatibility, CALC v2 needs:

| Feature | Current Status | Priority |
|---------|---------------|----------|
| Lax Monad `{A}` | ll.json experimental, not in v2 | **CRITICAL** |
| Forward Chaining | Not implemented | **CRITICAL** |
| Quiescence Detection | Not implemented | **CRITICAL** |
| Tensor `⊗` | ✓ Implemented | Done |
| Linear Implication `⊸` | ✓ Implemented | Done |
| With `&` | ✓ Implemented | Done |
| Bang `!` | ✓ Implemented | Done |
| Top `⊤` | Not implemented | HIGH |
| Existential `∃` | Not implemented | HIGH |
| Dependent Types `Π` | Not implemented | MEDIUM |
| Stages | Not implemented | HIGH (Ceptre) |

---

## 1. CLF (Concurrent Logical Framework)

### 1.1 Overview

CLF is a **dependent type theory** for representing concurrent computations. It extends the Linear Logical Framework (LLF) with:

- **Synchronous connectives** (`⊗`, `1`, `!`, `∃`) inside a monad
- **Lax modality** `{A}` for concurrent/effectful computation
- **Quiescence** as termination criterion

**Type theory notation:** `λΠ⊸&⊤{∃⊗1!}`

### 1.2 The Monad and Lax Logic

The lax monad `{A}` (written `○A` in lax logic) is the **key innovation**:

```
Outside monad:  Backward chaining, backtracking (Prolog-style)
Inside monad:   Forward chaining, committed choice (Datalog-style)
```

**Semantics:**
- `{A}` represents "eventually A" or "A is achievable through concurrent computation"
- Entering the monad switches proof search mode
- Exiting happens at **quiescence** (no more rules apply)

### 1.3 Synchronous vs Asynchronous Connectives

| Type | Connectives | Search Mode | Elimination |
|------|-------------|-------------|-------------|
| Asynchronous | `⊸`, `&`, `⊤` | Backward | Direct |
| Synchronous | `⊗`, `1`, `!`, `∃` | Forward | Let-binding |

**Why the split?** Synchronous connectives have "let-style" eliminators that require commuting conversions. The monad confines this complexity.

### 1.4 Quiescence

**Definition:** Forward chaining terminates when no more rules can fire.

```
#exec * {initial_state}   -- Run until quiescence
#exec 10 {initial_state}  -- Run for max 10 steps
```

**Quiescence vs Saturation:**
- **Quiescence:** Stop when no rules apply
- **Saturation:** Stop when no NEW facts can be derived (avoids infinite loops with persistent facts)

### 1.5 References

- [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf) (Watkins et al., 2004)
- [A Concurrent Logical Framework I: Judgments and Properties](http://www.cs.cmu.edu/~fp/papers/CMU-CS-02-101.pdf)
- [A Concurrent Logical Framework II: Examples and Applications](https://www.cs.cmu.edu/~iliano/papers/cmu-cs-02-102.pdf)

---

## 2. Celf (Implementation of CLF)

### 2.1 Overview

Celf is the **reference implementation** of CLF, written in Standard ML.

**Repository:** https://github.com/clf/celf

### 2.2 Proof Search Algorithm

Celf's proof search operates in **two modes**:

```
┌─────────────────────────────────────────────────────────────────┐
│ ASYNCHRONOUS (outside monad)                                    │
│ - Backward chaining (goal-directed)                             │
│ - Backtracking on failure                                       │
│ - Like Prolog/Lolli                                             │
└─────────────────────────────────────────────────────────────────┘
                              │
                              ▼ enter {A}
┌─────────────────────────────────────────────────────────────────┐
│ SYNCHRONOUS (inside monad)                                      │
│ - Forward chaining (data-driven)                                │
│ - Committed choice (no backtracking)                            │
│ - Multiset rewriting                                            │
│ - Runs until quiescence                                         │
└─────────────────────────────────────────────────────────────────┘
```

### 2.3 Focusing in Celf

Celf uses **Andreoli's focusing** (same as CALC v2!) but with two phases:

1. **Inversion phase:** Apply invertible rules eagerly
2. **Focus phase:** Choose formula, decompose until blur

The key difference: Celf's focusing spans BOTH backward and forward modes.

### 2.4 Query Directives

```celf
% Backward chaining query (find proof)
#query * 1 1 10 A.        -- 10 attempts to prove A

% Forward chaining execution
#exec * {initial_state}.   -- Run to quiescence
#exec 100 {initial_state}. -- Max 100 steps

% Trace execution (show intermediate states)
#trace * {initial_state}.
```

### 2.5 Celf Syntax Summary

```celf
% Type declarations
nat : type.
z : nat.
s : nat -> nat.

% Linear predicate (consumed on use)
token : type.

% Persistent predicate (reusable)
!fact : type.

% Linear implication (backward chaining)
rule1 : token -o result.

% Monadic forward chaining
rule2 : token -o {result1 * result2}.

% With monad inside
rule3 : a -o {b * !c}.  -- b linear, c persistent
```

### 2.6 References

- [Celf - A Logical Framework for Deductive and Concurrent Systems](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28)
- [Celf GitHub Wiki](https://github.com/clf/celf/wiki)

---

## 3. Ceptre (Linear Logic for Games/Interactivity)

### 3.1 Overview

Ceptre is a **simplified CLF** designed for:
- Game mechanics prototyping
- Interactive narrative generation
- Multi-agent simulation

**Author:** Chris Martens (CMU → NCSU)
**Repository:** https://github.com/chrisamaphone/interactive-lp

### 3.2 Key Simplifications from CLF

| CLF | Ceptre | Notes |
|-----|--------|-------|
| Dependent types | Simple types | No `Π` |
| Full monad | Implicit | All rules are forward chaining |
| Complex syntax | Simplified | Game-designer friendly |
| Quiescence | Stages | Explicit control structure |

### 3.3 Stages: Programming with Quiescence

**Stages** are Ceptre's key innovation beyond CLF:

```ceptre
stage combat = {
  attack : enemy * weapon -o damaged_enemy.
  defeat : damaged_enemy -o victory.
}

stage exploration = {
  move : at Player Room * connected Room Room2 -o at Player Room2.
  pickup : at Player Room * item_at Item Room -o has Player Item.
}

% Stage transitions
combat * victory -o exploration.
```

**Semantics:**
- Each stage runs until **quiescence** (no rules apply)
- Then stage transitions fire
- Enables structured, multi-phase computation

### 3.4 Interactivity

```ceptre
#interactive combat.  -- Human chooses among applicable rules
#trace _ combat {initial_state}.  -- Random selection
```

### 3.5 Ceptre Syntax

```ceptre
% Types
block : type.
location : type.

% Predicates
on : block -> block -> pred.
clear : block -> pred.
arm_holding : block -> pred.
arm_free : pred.

% Rules (all forward chaining)
pickup : arm_free * clear B * on B Table
      -o arm_holding B * clear Table.

putdown : arm_holding B * clear Table
       -o on B Table * clear B * arm_free.

% Initial context
context init = {on a b, on b table, clear a, arm_free}.

% Execute
#trace _ main init.
```

### 3.6 References

- [Ceptre: A Language for Modeling Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf)
- [Chris Martens' PhD Thesis: Programming Interactive Worlds with Linear Logic](https://www.cs.cmu.edu/~cmartens/thesis/)
- [Ceptre Tutorial](https://github.com/chrisamaphone/interactive-lp/blob/master/tutorial.md)

---

## 4. LolliMon (Bridge Between Lolli and CLF)

### 4.1 Overview

LolliMon = Lolli + Monad. It's the "missing link" showing how to add forward chaining to backward chaining.

**Key insight:** The monad cleanly separates the two search modes.

```
Lolli:    Backward chaining only (asynchronous fragment)
LolliMon: Backward + Forward (monad for synchronous)
CLF:      Full dependent types + LolliMon's operational semantics
Celf:     Implementation of CLF
Ceptre:   Simplified CLF for games
```

### 4.2 References

- [Monadic Concurrent Linear Logic Programming](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf) (López et al., PPDP 2005)
- [LolliMon GitHub](https://github.com/clf/lollimon)

---

## 5. What CALC v2 Needs

### 5.1 Critical: Lax Monad `{A}`

**Current state:** ll.json has `Formula_Monad` and `Formula_Lax` but marked experimental.

**Required implementation:**

```
% In ill.calc
monad : formula -> formula
  @ascii "{ _ }"
  @latex "\\{#1\\}"
  @polarity positive
  @category monadic.

% In ill.rules
monad_r : deriv (seq G D (hyp any (monad A)))
       <- deriv_lax (seq G D (hyp any A))
  @pretty "{}R"
  @mode_switch forward.
```

**Key requirement:** `deriv_lax` is a NEW judgment for forward-chaining mode.

### 5.2 Critical: Forward Chaining Engine

CALC v2 currently only has **backward chaining** (focused proof search).

**Required:**
1. Multiset rewriting engine
2. Committed choice (no backtracking)
3. Quiescence detection
4. Mode switching (backward ↔ forward)

**Architecture:**

```javascript
// lib/v2/prover/forward/engine.js
class ForwardEngine {
  constructor(rules) { ... }

  // Run until quiescence or step limit
  run(state, maxSteps = Infinity) {
    while (this.hasApplicableRules(state) && steps < maxSteps) {
      const rule = this.chooseRule(state);  // Non-deterministic
      state = this.applyRule(state, rule);  // Committed choice
      steps++;
    }
    return { state, quiescent: !this.hasApplicableRules(state) };
  }
}
```

### 5.3 Critical: Quiescence Detection

```javascript
// Check if any rule can fire
hasApplicableRules(state) {
  for (const rule of this.rules) {
    if (this.canFire(rule, state)) return true;
  }
  return false;
}
```

### 5.4 High Priority: Top `⊤`

Top (additive truth) is needed for CLF completeness.

```
top : formula
  @ascii "T"
  @latex "\\top"
  @polarity negative.

% Right rule (always succeeds, consumes no resources)
top_r : deriv (seq G D (hyp any top))
  @pretty "⊤R"
  @invertible true.
```

### 5.5 High Priority: Existential `∃`

Existential quantification over terms:

```
exists : (term -> formula) -> formula
  @ascii "exists _"
  @latex "\\exists #1"
  @polarity positive.

% Left rule (unpack)
exists_l : deriv (seq G (comma D (hyp t (exists F))) C)
        <- deriv (seq G (comma D (hyp t (F t))) C)
  @pretty "∃L".

% Right rule (provide witness)
exists_r : deriv (seq G D (hyp any (exists F)))
        <- deriv (seq G D (hyp any (F T)))
  @pretty "∃R".
```

### 5.6 High Priority: Stages (for Ceptre)

```javascript
// lib/v2/prover/stages.js
class StageEngine {
  constructor(stages, transitions) { ... }

  run(initialStage, initialState) {
    let stage = initialStage;
    let state = initialState;

    while (true) {
      // Run current stage to quiescence
      const result = this.runStage(stage, state);
      state = result.state;

      // Check stage transitions
      const nextStage = this.findTransition(stage, state);
      if (!nextStage) break;  // Terminal
      stage = nextStage;
    }

    return { stage, state };
  }
}
```

### 5.7 Medium Priority: Dependent Types `Π`

For full LF/LLF/CLF compatibility:

```
% Dependent function type
pi : (A : type) -> (A -> type) -> type.

% Example: length-indexed vectors
vec : nat -> type -> type.
vnil : pi A. vec z A.
vcons : pi A. pi N. A -> vec N A -> vec (s N) A.
```

This requires significant type system changes.

---

## 6. Implementation Roadmap

### Phase 4A: Complete ILL (Current)
- [x] Tensor, Loli, With, Bang, One
- [ ] Add Top `⊤`
- [ ] Test absorption/copy rules
- [ ] Verify cartesian context handling

### Phase 4B: Lax Monad Foundation
- [ ] Add `monad` connective to ill.calc
- [ ] Add `deriv_lax` judgment to lnl.family
- [ ] Implement monad_r rule (mode switch)
- [ ] Basic forward chaining engine

### Phase 4C: Forward Chaining
- [ ] Multiset rewriting engine
- [ ] Committed choice semantics
- [ ] Quiescence detection
- [ ] Integration with backward prover

### Phase 4D: Ceptre Features
- [ ] Stage system
- [ ] Stage transitions
- [ ] Interactive mode
- [ ] Trace/execution directives

### Phase 5: Full CLF
- [ ] Existential `∃`
- [ ] Dependent types `Π`
- [ ] Full LLF compatibility
- [ ] Celf-compatible syntax

---

## 7. Key Insights

### 7.1 The Monad is Central

Everything flows from the lax monad `{A}`:
- It separates backward from forward chaining
- It enables concurrent/effectful computation
- It's the bridge between Lolli and full linear logic

### 7.2 Focusing Unifies Everything

CALC v2 already has Andreoli's focusing. The same framework extends to:
- Backward chaining (current)
- Forward chaining (to implement)
- Mixed mode (CLF-style)

### 7.3 Quiescence Replaces Explicit Loops

In imperative programming: `while (condition) { ... }`
In linear logic: Run rules until quiescence

Stages (Ceptre) add structure: Run stage A to quiescence, then stage B, etc.

---

## 8. Questions for User

1. **Priority:** Should we implement the lax monad first, or complete ILL (add Top, test bang rules)?

2. **Stages:** Do you need Ceptre-style stages, or is basic quiescence sufficient?

3. **Dependent types:** How important is full CLF compatibility vs. a simpler Ceptre-like system?

4. **Syntax:** Should we support Celf syntax exactly, or design our own `.calc/.rules` extensions?

---

## Sources

- [CLF: A Dependent Logical Framework](https://www.cs.cmu.edu/~fp/papers/clf04.pdf)
- [Celf - A Logical Framework for Deductive and Concurrent Systems](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28)
- [Ceptre: A Language for Modeling Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf)
- [Monadic Concurrent Linear Logic Programming](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf)
- [Celf GitHub](https://github.com/clf/celf)
- [Ceptre GitHub](https://github.com/chrisamaphone/interactive-lp)
- [Ceptre Tutorial](https://github.com/chrisamaphone/interactive-lp/blob/master/tutorial.md)
