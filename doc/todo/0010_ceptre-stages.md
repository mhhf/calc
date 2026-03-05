---
title: "Ceptre Stages"
created: 2026-02-18
modified: 2026-03-04
summary: "Named rule subsets running to quiescence with inter-stage transitions"
tags: [Ceptre, stages, forward-engine, focusing, CLF, quiescence]
type: research
cluster: CLF
status: done
subsumed_by: TODO_0006
priority: 2
depends_on: [TODO_0006]
required_by: []
---

# Ceptre Stages

**Status: Subsumed by TODO_0006 (lax monad).**

The lax monad provides principled staging: backward chaining orchestrates forward phases, quiescence is implicit (`forward.run()` returns when no rules fire). Ceptre-style declared stages are unnecessary.

Research extracted to [RES_0085](../research/0085_stages-proof-theoretic-status.md).

---

## 1. What Ceptre Stages Are (Martens 2015)

### 1.1 Definition

A **stage** is a named set of forward-chaining linear logic rules. Execution within a stage proceeds by committed-choice multiset rewriting until **quiescence** (no rules can fire). Stage transitions are themselves rules that consume a `qui` token (produced at quiescence) and the current `stage S` fact, producing a new `stage S'` fact.

### 1.2 Syntax

```ceptre
stage combat = {
  attack : enemy * weapon -o damaged_enemy.
  defeat : damaged_enemy -o victory.
}

stage exploration = {
  move : at P R * connected R R2 -o at P R2.
  pickup : at P R * item_at I R -o has P I.
}

% Stage transition (fires at quiescence)
combat_to_explore : qui * stage combat * victory -o stage exploration.
```

Key elements:
- `stage S = { rules... }` --- named rule group
- `qui` --- special token produced when a stage reaches quiescence
- `stage S` --- linear fact tracking the current stage
- `#interactive S.` --- marks a stage for human choice (vs random/automatic)
- `#trace _ S {initial_context}.` --- execution directive

### 1.3 Concrete Example: Settlers-style Game

From Martens' `siedler1.cep`, five stages cycle: `setup -> roll -> produce -> trade -> build -> roll -> ...`

```ceptre
setup_to_rolling : qui * stage setup -o stage roll * die.
roll_to_prod     : qui * stage roll -o stage produce.
prod_to_trade    : qui * stage produce -o stage trade.
trade_to_build   : qui * stage trade * done P -o stage build * turn P.
build_to_roll    : qui * stage build * done P * next P P'
                   -o stage roll * turn P' * die.
```

Each transition can carry additional linear facts (e.g. `done P`, `turn P'`) between stages.

### 1.4 "Programming with Quiescence"

Martens' key claim: stages give the ability to **program with quiescence**, enabling computations that pure forward-chaining linear logic programming cannot express. The canonical example is any computation requiring a "barrier" --- all rules in phase A must complete before phase B begins. Pure committed-choice forward chaining has no way to detect "nothing left to do" from within the logic.

### 1.5 Internal Encoding

Internally, Ceptre compiles stages into the linear context:
- `stage S` is a linear predicate (consumed/produced by transitions)
- `qui` is a special token emitted by the runtime when quiescence is detected
- Rules within a stage are guarded by the presence of `stage S` (either as a persistent `$stage S` check or by the runtime's rule selection)
- The runtime checks quiescence externally and injects `qui` into the context

This encoding is **not derivable from linear logic itself** --- `qui` is produced by the runtime's fixed-point detection, not by any logical rule.

---

## 2. Proof-Theoretic Status of Stages

### 2.1 Stages Are Not a Logical Connective

Stages do **not** correspond to any connective or judgment form in linear logic. They are an **extra-logical control mechanism** layered on top of the logic. The evidence:

1. **No introduction/elimination rules.** A stage has no right-rule/left-rule in the sequent calculus. The `qui` token is injected by the runtime, not derived by proof search.

2. **No CLF encoding.** Martens' thesis describes Ceptre as a "simplified CLF" but stages are *not* part of CLF. CLF's monad `{A}` provides forward-chaining-until-quiescence for a single monadic block, but has no mechanism for sequencing multiple such blocks.

3. **Quiescence is a meta-level property.** "No rules can fire" is a statement *about* the proof search state, not a statement *within* the logic. It requires checking all rules against the entire context --- a global, non-local operation that cannot be expressed by any finite set of linear logic rules.

4. **Martens acknowledges this implicitly.** Ceptre is described as adding "stages and interactivity" *on top of* forward-chaining linear logic programming. The stages are a language feature, not a logical feature.

### 2.2 Relationship to CLF's Lax Monad

CLF's lax monad `{A}` provides a principled boundary:
- Outside `{A}`: backward chaining, backtracking
- Inside `{A}`: forward chaining, committed choice, runs to quiescence

The monad gives you **one** quiescence boundary per monadic invocation. Stages require **multiple sequential** quiescence boundaries. CLF has no built-in mechanism for sequencing multiple monadic computations to quiescence. You could nest them via backward chaining outside the monad:

```
phase1 : goal -o {phase1_rules...}.
phase2 : phase1_result -o {phase2_rules...}.
```

But this requires backward chaining to sequence the phases, which is a different operational model from Ceptre's purely-forward staged execution.

### 2.3 Relationship to Focusing

Andreoli's focusing creates **implicit phases** in proof search:
- **Asynchronous (negative) phase:** invertible rules applied eagerly, no choice
- **Synchronous (positive) phase:** choose a focus formula, decompose non-invertibly

This alternation resembles staging superficially, but differs fundamentally:
- Focusing phases are **within a single proof** and alternate at every step
- Stages are **across an entire computation** and transition only at quiescence
- Focusing preserves completeness; stages impose arbitrary partitioning
- Focusing is determined by polarity; stages are declared by the programmer

The connection: Chaudhuri and Pfenning (IJCAR 2006) showed that **atom polarity bias** determines forward vs. backward chaining in the focused inverse method. Positive atoms yield forward chaining (hyperresolution); negative atoms yield backward chaining (SLD resolution). This is a proof-theoretic characterization of *direction*, but not of *staging*.

---

## 3. Alternatives to Stages

### 3.1 CLF Lax Monad `{A}` (Watkins et al. 2004)

**Mechanism:** Entering `{A}` switches to forward chaining; exiting at quiescence returns to backward chaining. Multiple phases can be sequenced via backward-chaining goals.

**Strengths:** Proof-theoretically justified. The monad is a proper logical connective with introduction/elimination rules. Cut elimination holds.

**Limitations:** Requires a backward-chaining outer layer to sequence phases. Not purely forward-chaining. Does not directly give "run phase A to quiescence, then phase B to quiescence" in a purely forward model.

**CALC relevance:** TODO_0006 already tracks lax monad integration. If implemented, it provides a principled single-quiescence boundary but needs additional machinery for multi-phase sequencing.

### 3.2 Focusing Discipline as Implicit Phases

**Mechanism:** Rules partitioned by polarity into synchronous/asynchronous phases. Invertible rules run eagerly (like a "phase" that must complete); non-invertible rules require choice.

**Strengths:** Already implemented in CALC (L3 focused.js). The synchronous/asynchronous alternation is a proven proof-theoretic structure.

**Limitations:** Focusing phases are microscopic (per-formula), not macroscopic (per-computation-epoch). They cannot express "run all combustion rules to completion before starting exploration rules."

**Key insight from Chaudhuri-Pfenning:** The bias on atoms provides a *structural* (not operational) explanation for forward/backward chaining. But this controls *direction*, not *sequencing*.

### 3.3 Loli Continuations (already in CALC)

**Mechanism:** A loli `A -o B` in the linear context acts as a dormant continuation. When `A` appears, the loli fires. This creates implicit sequencing: helper computations run, produce a trigger fact, which unblocks the next phase.

**Strengths:** Already works in CALC's forward engine. Purely within the logic. No extra-logical machinery needed. The SHA3 `concatMemory` pattern demonstrates this.

**Limitations:** Requires manual encoding of the "barrier" via specific trigger predicates. Does not automatically detect quiescence --- rather, the programmer must ensure the helper produces exactly the right trigger. Cannot express "run *all* rules of type X to completion" without careful predicate design.

### 3.4 CHR Rule Priorities (Fruhwirth 1991, CHRrp)

**Mechanism:** Rules annotated with numeric priorities. Higher-priority rules fire first. CHRrp extends CHR with user-definable (static or dynamic) priorities.

**Strengths:** Fine-grained control without explicit stage boundaries. Can simulate stages by assigning priority ranges. Retains committed-choice semantics.

**Limitations:** Priority is operational, not proof-theoretic. No logical justification. Can lead to subtle ordering bugs. Static priorities cannot express quiescence-dependent transitions.

### 3.5 Datalog Stratification

**Mechanism:** Rules partitioned into strata based on predicate dependency. Stratum N runs to fixpoint before stratum N+1 begins. Originally motivated by stratified negation.

**Strengths:** Stratification can be **inferred** from rule structure (no user annotation needed). Well-studied theory with well-founded semantics.

**Limitations:** Classical Datalog stratification assumes monotonic rules within strata (no linear consumption). Extending to linear logic is non-trivial. Baillot and Terui's "abstract stratification" work operates at the complexity-theoretic level, not the programming model level.

**Key parallel:** If CALC rules have a predicate dependency graph (rules in group A produce predicates consumed by rules in group B, but not vice versa), an automatic stratification could be inferred. This is the most promising path toward *principled* staging.

### 3.6 Simmons' SLS and Subordination

**Mechanism:** Simmons' Substructural Logical Specifications (SLS) framework uses ordered linear lax logic with subordination constraints. The "generative invariants" methodology allows expressing and verifying structural properties of specifications.

**Strengths:** Full proof-theoretic foundation via structural focalization. Handles state, concurrency, and control flow within a single logical framework.

**Limitations:** More complex than Ceptre's simple staging. Requires ordered logic (beyond CALC's current intuitionistic linear logic).

### 3.7 Productive Proofs (Chaudhuri, Gantait, Miller 2025)

**Mechanism:** A "productive" forward-chaining step creates a fact not already provable. Forward chaining runs while inferences remain productive. "Safe for saturation" identifies formula classes guaranteed to saturate finitely.

**Strengths:** Proof-theoretic characterization of when forward chaining terminates. Implemented as a tactic in Abella. Based on focusing and bipolar formulas.

**Limitations:** Addresses termination, not multi-phase sequencing. Does not provide stage transitions.

---

## 4. Can Stages Be Derived from the Logic?

### 4.1 Encoding Quiescence Within Linear Logic

**Cannot be done directly.** Quiescence ("no rule applies") is a *negation-as-failure* property. It requires checking all rules against all possible instantiations --- a meta-level fixed-point that cannot be expressed as a finite linear logic formula.

**Partial encodings:**
- **Explicit completion tokens:** Each rule, when it cannot fire, produces a "done" token. When all "done" tokens are collected, the stage transitions. Problem: requires the programmer to manually encode failure conditions for every rule.
- **Counter-based:** Track the number of fireable rules. At zero, transition. Problem: counting fireable rules is itself meta-level.

### 4.2 Encoding Stages via Linear Predicates

Stages *can* be simulated within linear logic using guard predicates:

```
% Instead of stage combat = { attack : ... }
% Use a guard predicate:
attack : phase_combat * enemy * weapon -o phase_combat * damaged_enemy.
defeat : phase_combat * damaged_enemy -o phase_combat * victory.

% Transition requires consuming phase_combat (manual quiescence)
transition : phase_combat * victory -o phase_explore.
```

This works but has a critical limitation: there is no automatic quiescence detection. The programmer must manually encode when a phase is "done" via explicit trigger predicates. This is essentially what CALC's loli continuation pattern already does.

### 4.3 Automatic Stratification via Predicate Dependency

The most promising principled approach: analyze the rule dependency graph to infer strata.

**Algorithm:**
1. Build a directed graph: predicate P depends on predicate Q if some rule consuming P produces Q
2. Find strongly connected components (SCCs)
3. Topologically sort the SCCs
4. Each SCC becomes an implicit "stage"

**Example:** If rules consuming `raw_input` produce `parsed`, and rules consuming `parsed` produce `typed`, and there are no back-edges, then three implicit stages emerge: parsing, typing, and the rest.

**Challenges:**
- Cyclic dependencies (SCCs) must be handled --- these form single stages
- Linear logic's resource consumption means the dependency graph is more nuanced than Datalog's
- Does not handle *all* staging patterns (e.g., game turn cycling is inherently cyclic)

### 4.4 Verdict

| Approach | Proof-theoretic? | Automatic? | Expressiveness |
|----------|-----------------|------------|----------------|
| Ceptre stages | No | No (declared) | Full |
| CLF lax monad | Yes | No (programmed) | Sequential phases |
| Focusing phases | Yes | Yes | Per-formula only |
| Loli continuations | Yes | No (encoded) | Ad-hoc barriers |
| Predicate stratification | Partially | Yes (inferred) | Acyclic only |
| CHR priorities | No | No (annotated) | Full |
| Guard predicates | Yes | No (encoded) | Full (manual) |

---

## 5. Practical Staging Patterns

### 5.1 Game Phases

**Pattern:** combat -> exploration -> dialogue -> combat -> ...

**With stages:** Direct encoding, one stage per phase.

**Without stages (loli continuations):**
```
combat_done(X) -o exploration_start(X).
exploration_done(X) -o dialogue_start(X).
dialogue_done(X) -o combat_start(X).
```
Requires explicit "done" predicates per phase.

### 5.2 Compilation Phases

**Pattern:** lex -> parse -> typecheck -> codegen

**With stages:** Natural fit (acyclic, each phase runs to completion).

**Without stages (predicate stratification):** The dependency graph is acyclic (lex produces tokens, parse consumes tokens and produces AST, etc.). Automatic stratification would infer the correct phase ordering.

### 5.3 Protocol Phases

**Pattern:** handshake -> exchange -> close

**With stages:** Direct, with transition predicates carrying session state.

**Without stages (loli continuations):**
```
handshake_complete(S) -o ready_for_exchange(S).
exchange_complete(S) -o ready_for_close(S).
```
This is exactly what session-typed linear logic already does.

---

## 6. Implications for CALC

### 6.1 What CALC Already Has

- Forward-chaining engine with committed choice (lib/engine/forward.js)
- Quiescence detection (the main loop in `run()` terminates when no rules fire)
- Loli continuations for implicit sequencing
- Exhaustive DFS exploration (lib/engine/symexec.js) with quiescence at leaves

### 6.2 Recommendation

**Do not implement Ceptre-style declared stages.** Instead, pursue a layered approach:

1. **Short-term (no work needed):** Continue using loli continuations for ad-hoc sequencing. Already works.

2. **Medium-term:** Implement automatic predicate stratification. Analyze the rule dependency graph at load time. Rules in different strata automatically run in order. This gives staging behavior without extra-logical declarations.

3. **Long-term (TODO_0006):** Implement CLF lax monad `{A}` for principled forward/backward integration. This subsumes simple staging for the case where phases can be sequenced by a backward-chaining outer layer.

### 6.3 Open Questions

- Can predicate stratification handle cyclic game-like phases? (Probably not --- these require explicit transition logic.)
- Is there a useful notion of "nested quiescence" for hierarchical stages?
- Could the focusing discipline be extended to operate at the rule-set level (not just formula level)?

---

## 7. Key References

- Martens, C. (2015). *Programming Interactive Worlds with Linear Logic.* PhD thesis, CMU. [Thesis](https://www.cs.cmu.edu/~cmartens/thesis.pdf), [Ch. 4](https://www.cs.cmu.edu/~cmartens/thesis/4-ceptre_lang.pdf)
- Martens, C. (2015). Ceptre: A Language for Modeling Generative Interactive Systems. AIIDE. [Paper](https://www.cs.cmu.edu/~cmartens/ceptre.pdf)
- Watkins, K. et al. (2004). A Concurrent Logical Framework: The Propositional Fragment. [Paper](https://www.cs.cmu.edu/~iliano/papers/types03.pdf)
- Lopez, P. et al. (2005). Monadic Concurrent Linear Logic Programming. PPDP. [Paper](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf)
- Chaudhuri, K. and Pfenning, F. (2006). A Logical Characterization of Forward and Backward Chaining in the Inverse Method. IJCAR. [Paper](https://www.cs.cmu.edu/~fp/papers/ijcar06.pdf)
- Simmons, R. and Pfenning, F. (2008). Linear Logical Algorithms. ICALP. [Paper](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf)
- Simmons, R. (2012). Substructural Logical Specifications. PhD thesis, CMU. [Thesis](https://www.cs.cmu.edu/~rwh/students/simmons.pdf)
- Chaudhuri, K., Gantait, A., and Miller, D. (2025). Designing a Safe Forward Chaining Tactic Using Productive Proofs. TABLEAUX. [Draft](https://abella-prover.org/fc/draft25fc.pdf)
- Baillot, P. and Terui, K. (2014). An Abstract Approach to Stratification in Linear Logic. [Paper](https://arxiv.org/abs/1206.6504)
- Fruhwirth, T. (2009). Constraint Handling Rules. [Survey](https://arxiv.org/pdf/0906.4474)

## 7. Auto-Registration of Forward Rules as Backward Clauses

Now that TODO_0006/0066 implemented the lax monad `{A}` with mode switch bridge, the principled staging mechanism from CLF is available: backward prover plans over forward phases via auto-registered clauses.

**Mechanism:** At `mde.load()` time, each forward rule `A₁ * ... * Aₙ -o { S }` is registered as a backward clause with monadic head `{ S }` and body `[A₁, ..., Aₙ]`. The backward prover searches these clauses normally — "to prove `{ result(R) }`, I need `deployed(Addr, Runtime)` and `calldata(D)`. I can get `deployed` by proving `{ deployed(Addr, Runtime) }`, which requires `bytecode(B)`..." etc.

This is how CLF/Celf works and subsumes Ceptre-style stages without extra-logical machinery. See TODO_0066 §2.7 for the full design.

## Tasks

- [x] Study Ceptre stage semantics
- [x] Research whether stages have proof-theoretic justification
- [ ] Prototype automatic predicate stratification on existing rule sets
- [ ] Evaluate whether loli continuations cover all practical staging needs
- [ ] Design stage syntax for .calc/.rules (only if justified beyond stratification)
- [ ] Implement auto-registration of forward rules as backward clauses (from TODO_0066 §2.7)

See: `doc/research/0008_clf-celf-ceptre.md`
