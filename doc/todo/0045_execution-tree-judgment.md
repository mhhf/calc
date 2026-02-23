---
title: "Formalize Execution Tree Judgment"
created: 2026-02-19
modified: 2026-02-23
summary: "Formalize the execution tree as a proof-theoretic judgment — the central theoretical contribution of CALC's exhaustive forward chaining"
tags: [theory, execution-tree, judgment, proof-theory, formalization, focusing, chr, omega-l, qchr]
type: research
cluster: Theory
status: planning
priority: 7
depends_on: []
required_by: [TODO_0042]
---

# Formalize Execution Tree Judgment

## 1. The Goal

Give a rigorous proof-theoretic judgment for CALC's execution trees. The execution tree is the central data structure produced by `symexec.js:explore()` — it captures **all** possible forward-chaining traces from an initial state. Formalizing it as a judgment connects CALC's implementation to established proof theory and enables soundness/completeness proofs.

This is the formalization of `doc/theory/0001_exhaustive-forward-chaining.md` §Formal Judgment.

---

## 2. Proposed Judgment

### 2.1 Judgment Form

```
Σ; Δ ⊢_fwd T : A
```

- `Σ` = persistent rules (compiled forward rules, immutable program)
- `Δ` = linear state (multiset of linear facts, including loli continuations)
- `T` = execution tree (the proof term / witness)
- `A` = goal type (unconstrained for exhaustive exploration)

The judgment reads: "Under program Σ and initial state Δ, the execution tree T witnesses all reachable quiescent states."

### 2.2 Tree Constructors

```
T ::= leaf(Δ_q)                      — quiescent state (no rules fire)
    | step(r, θ, T')                  — deterministic step: rule r, substitution θ
    | fork(T₁, T₂)                   — ⊕ case split (from oplus in consequent)
    | branch(r₁:T₁, ..., rₙ:Tₙ)     — nondeterministic branch (multiple applicable rules)
    | cycle(Δ)                        — back-edge to previously seen state
    | bound(Δ)                        — depth limit reached
```

### 2.3 Constructor Semantics

| Constructor | Implementation | Proof-theoretic role |
|---|---|---|
| `leaf(Δ_q)` | `explore()` returns `{type:'leaf', state}` when `findAllMatches` returns `[]` | Terminal: no rules applicable = quiescence |
| `step(r,θ,T')` | Single match in `findAllMatches`, single alt in `consequentAlts` | Cut with rule axiom: apply r, continue |
| `fork(T₁,T₂)` | `alts.length > 1` in `explore()` loop (from `expandConsequentChoices`) | ⊕L inversion: case-split on disjunctive consequent |
| `branch(rᵢ:Tᵢ)` | `matches.length > 1` in `explore()` loop | ∀-branching: explore every applicable rule |
| `cycle(Δ)` | `pathVisited.has(ctx.stateHash)` in `explore()` | Back-edge: state already on current path |
| `bound(Δ)` | `depth >= maxDepth` in `explore()` | Truncation: finite approximation |

### 2.4 Worked Example: Minimal Step

```
Initial state Δ₀ = {pc(0), code(0, 0x01), stack(0, 3), stack(1, 5)}
Program Σ = {evm/add: pc(PC) * code(PC,0x01) * stack(0,A) * stack(1,B) * !plus(A,B,C)
                       -o {pc(PC') * stack(0,C)}}

Step 1: evm/add matches with θ = {PC↦0, A↦3, B↦5, C↦8, PC'↦1}
        consumed = {pc(0), stack(0,3), stack(1,5)}
        produced = {pc(1), stack(0,8)}

Step 2: No rules match (no code(1,...)) → quiescence

Tree: step(evm/add, θ, leaf({pc(1), code(0,0x01), stack(0,8)}))
```

### 2.5 Worked Example: Fork (⊕ Branching)

```
State: {pc(5), code(5,0x14), stack(0,X), stack(1,Y), ...}
Rule: evm/eq: ... -o {... * ((stack(0,0) * !neq(X,Y)) ⊕ (stack(0,1) * !eq(X,Y)))}

Tree: step(evm/eq, θ,
        fork(
          T₁,   -- branch where !neq(X,Y) holds, stack=0
          T₂    -- branch where !eq(X,Y) holds, stack=1
        ))
```

The `fork` reflects ⊕L inversion: both alternatives are explored because
the system cannot decide which disjunct holds for symbolic X, Y.

### 2.6 Worked Example: Branch (Rule Nondeterminism)

```
State: {pc(10), code(10,0x57), stack(0,addr), stack(1,C), ...}
Rules: Both evm/jumpi and some helper rule match simultaneously.

Tree: branch(
        evm/jumpi: step(evm/jumpi, θ₁, T₁),
        helper:    step(helper, θ₂, T₂)
      )
```

The `branch` reflects ∀-branching: all applicable rules are explored
exhaustively (don't-know nondeterminism over don't-care choices).

---

## 3. Proposed Inference Rules

### 3.1 Quiescence (Leaf)

```
  findAllMatches(Σ, Δ) = ∅
  ─────────────────────────────── LEAF
  Σ; Δ ⊢_fwd leaf(Δ) : A
```

No rules fire. The state Δ is quiescent.

### 3.2 Deterministic Step

```
  r ∈ Σ    θ = match(r, Δ)    Δ' = apply(r, θ, Δ)
  Σ; Δ' ⊢_fwd T : A
  findAllMatches(Σ, Δ) = {(r,θ)}
  ───────────────────────────────────────────────── STEP
  Σ; Δ ⊢_fwd step(r, θ, T) : A
```

Exactly one rule fires. Apply it and continue. This is a **cut** with the
rule axiom r, consuming linear resources and producing the consequent.

### 3.3 Additive Fork (⊕L Inversion)

```
  r ∈ Σ    θ = match(r, Δ)    apply(r,θ,Δ) produces C₁ ⊕ C₂
  Δ₁ = apply(r, θ, Δ, alt=1)    Δ₂ = apply(r, θ, Δ, alt=2)
  Σ; Δ₁ ⊢_fwd T₁ : A           Σ; Δ₂ ⊢_fwd T₂ : A
  ──────────────────────────────────────────────────────────── FORK
  Σ; Δ ⊢_fwd step(r, θ, fork(T₁, T₂)) : A
```

The rule consequent contains ⊕ (internal choice). Both branches are explored.
This corresponds to ⊕L (invertible, case-split eagerly). Each branch gets the
full shared context — branches are alternatives, not parallel.

**Key insight:** ⊕L is invertible, so the fork is **forced** (no choice involved).
This matches the implementation: `expandConsequentChoices` produces all alternatives,
and `explore()` iterates over all of them.

### 3.4 Nondeterministic Branch (∀ Over Rules)

```
  findAllMatches(Σ, Δ) = {(r₁,θ₁), ..., (rₙ,θₙ)}    n > 1
  ∀i. Δᵢ = apply(rᵢ, θᵢ, Δ)
  ∀i. Σ; Δᵢ ⊢_fwd Tᵢ : A
  ──────────────────────────────────────────────────────── BRANCH
  Σ; Δ ⊢_fwd branch(r₁:T₁, ..., rₙ:Tₙ) : A
```

Multiple rules can fire. All are explored. This is the **∀-branching** that
distinguishes CALC's exhaustive exploration from CLF's committed choice.

In Stéphan's ω_l terms: CLF makes a single &L choice (committed choice, one rule).
CALC makes ALL &L choices (exhaustive, exploring every rule). The branch node
records the universal quantification over rule selections.

### 3.5 Cycle Detection

```
  Δ ∈ pathVisited
  ───────────────────────────────── CYCLE
  Σ; Δ ⊢_fwd cycle(Δ) : A
```

The state Δ has been seen earlier on the current root-to-here path.
This is a back-edge in the DFS tree, preventing infinite loops.

**Implementation detail:** Cycle detection uses `computeNumericHash(state)` —
a 32-bit XOR hash of all linear fact (hash,count) pairs and persistent fact
hashes. The set `pathVisited` stores these numeric hashes. False positives
(hash collision → missed exploration) are possible but improbable at 32 bits.
See §7.2 for analysis.

### 3.6 Depth Bound

```
  depth ≥ maxDepth
  ───────────────────────────────── BOUND
  Σ; Δ ⊢_fwd bound(Δ) : A
```

Depth limit reached. The tree is truncated. This ensures finiteness but
sacrifices completeness (bounded completeness only).

---

## 4. Relationship to Existing Frameworks

### 4.1 Simmons' SLS (2012)

**Source:** "Substructural Logical Specifications" — CMU-CS-12-142 (PhD thesis).

SLS is a logical framework based on ordered linear lax logic. It provides:

- **Structural focalization:** A synthesis of Andreoli's focused sequent calculi
  and Watkins's hereditary substitution. Defines restricted "focused derivations"
  that form the basis of the logical framework.
- **Rewriting interpretation:** Forward reasoning in substructural logics interpreted
  as multiset rewriting. Logic programming rules act as rewrite rules.
- **Logical correspondence:** Methodology for relating specification styles
  (natural semantics, destination-passing, etc.) within SLS.
- **Generative invariants:** Invariants of SLS specifications expressible in SLS itself.
- **Cost semantics:** Via "Linear Logical Algorithms" (Simmons & Pfenning, ICALP 2008) —
  the abstract running time counts prefix firings, with an interpreter executing
  in time proportional to this count.

**Relationship to CALC:**

| SLS concept | CALC equivalent | Gap |
|---|---|---|
| Ordered linear lax logic | ILL with monad (implicit) | SLS has ordering; CALC is multiset |
| Structural focalization | Strategy stack layers | SLS is logic-level; CALC is compiled |
| Prefix firing cost | Rule firing count per path | Same concept, different formalization |
| Logical correspondence | N/A | CALC doesn't formalize spec styles |
| Generative invariants | N/A | Future: metaproofs (TODO_0008) |
| Committed choice execution | `run()` in forward.js | Identical semantics |

**Key difference:** SLS gives a SINGLE execution trace (committed choice).
CALC's execution tree is the **universal quantification** over all possible
SLS traces from the same initial state. Each root-to-leaf path in CALC's tree
IS a valid SLS trace.

**Is CALC's judgment an extension of SLS?** Yes — CALC extends SLS by:
1. Adding exhaustive exploration (∀ over rule choices, producing a tree)
2. Adding ⊕ in consequents (fork nodes, not present in CLF/SLS)
3. Adding loli continuations (dynamic rules in state)
4. Dropping ordered context (CALC uses multiset, SLS uses ordered)

The extension is conservative: restricting CALC to committed choice (single
match, no ⊕) recovers the SLS trace semantics.

### 4.2 Andreoli Focusing (1992)

**Source:** "Logic Programming with Focusing Proofs in Linear Logic" — JLC 2(3):297-347.

Focusing eliminates redundant proof search by classifying connectives:

| Polarity | Connectives | Phase | Behavior |
|---|---|---|---|
| Asynchronous (negative) | ⊸, &, ⊤, ?, ⊥, ∀ | Inversion | Right-intro invertible → apply eagerly |
| Synchronous (positive) | ⊗, 1, !, ⊕, ∃, 0 | Focus | Right-intro requires choice |

Proof search alternates between:
- **Inversion phase:** Apply all invertible rules (no choice, deterministic)
- **Focus phase:** Choose a formula, decompose synchronously until blur

**Atom polarity determines computation direction** (Chaudhuri & Pfenning 2006):
- Positive atoms → forward chaining (facts derived bottom-up)
- Negative atoms → backward chaining (goals decomposed top-down)

**Mapping to CALC's execution tree:**

| Focusing concept | CALC equivalent | Implementation |
|---|---|---|
| Inversion phase | Deterministic step / fork | `findAllMatches` returns 1 match |
| Focus phase | Rule selection | `strategy.getCandidateRules` |
| Choice of focus formula | Which rule to apply | `findMatch` / `findAllMatches` |
| Synchronous decomposition | `tryMatch` + `provePersistentGoals` | Pattern matching + persistent proving |
| Blur (return to inversion) | After match succeeds | After `mutateState` |

**Stéphan's caveat (ICLP 2018, §4):** The ω_l system's two phases (non-focused /
focused) RESEMBLE Andreoli's focusing but are NOT identical. ω_l phases are about
**constraint activation** (which fact to try), while focusing is about **connective
polarity** (which rule shape to decompose). Stéphan suggests translating ω_l proofs
into focusing proofs as future work — this would "understand the semantics of CHR
in terms of synchronous and asynchronous connectors."

**For CALC:** The strategy stack's phases map more naturally to Stéphan's ω_l phases:
- **Non-focused phase** = `findAllMatches` scanning candidates via strategy stack
- **Focused phase** = `tryMatch` + `provePersistentGoals` on a specific rule+fact pair
- **Rule selection via &** = strategy stack ordering (first-match-wins = &L₁ / &L₂)

Formalizing via Stéphan's framework may be more tractable than via Andreoli directly,
because Andreoli's focusing is about **proof-level** structure while CALC's strategy
stack is about **operational** structure (they coincide for this fragment, but the
Stéphan path has ready-made theorems).

### 4.3 Stéphan's ω_l (ICLP 2018)

**Source:** "A New Proof-Theoretical Linear Semantics for CHR" — OASIcs 4:1-4:17.

The key innovation: instead of translating CHR states to ILL and showing entailment
(Betz's approach), Stéphan defines sequent calculi where CHR derivations **are**
proof trees. Each rule application = an inference rule in the calculus.

**Two sequent forms:**

```
Non-focused:  (Γ ▸ Ω_# ◁ S_↑ ⊢ S_↓)
              Process goal Ω_# using program Γ,
              consuming from up-store S_↑, producing down-store S_↓

Focused:      (Γ ! Δ ▷ a ◁ S_↑ ⊢ S_↓)
              Focused on identified constraint a,
              trying rules Δ from program Γ
```

**Six inference rules:**

| Rule | Notation | Meaning | CALC equivalent |
|---|---|---|---|
| true | — | Axiom: goal is empty, done | Quiescence in `run()` |
| ⊗_L | tensor-left | Split goal into head + tail | `expandItem` splitting tensor |
| W | Weakening | Skip a rule (doesn't match) | Rule doesn't match in `tryMatch` |
| F | Focus | Select a constraint to activate | `findMatch` picks a fact |
| ↑ | Inactivate | Store constraint unchanged | Fact stays in state |
| \\⟺ | Apply | Fire simpagation rule | `applyMatch` / `mutateState` |

**Hidden Cut insight:** The ⊗_L rule is actually a **hidden cut** — it splits
resources between a "lemma" (left subproof — solve one constraint) and its "use"
(right subproof — solve the rest). This is exactly what `expandItem` does when it
distributes tensor components to separate state slots.

**Crucial translation difference from Betz:**

```
Betz:    program = !r₁ ⊗ !r₂ ⊗ ... ⊗ !rₙ   (all rules always available via !)
Stéphan: program = r₁ & r₂ & ... & rₙ        (rule selection = &L choice)
```

Stéphan's & translation elegantly captures committed choice: picking a rule is
an additive choice, and the unchosen rules remain available for future steps via
the structural rule of Weakening. This is more proof-theoretically natural.

**Key theorems:**
- **Theorem 7:** ω_l is sound AND complete w.r.t. ω_t (CHR abstract semantics)
- **Theorem 8:** ω_l^⊗ (deterministic variant, store as sequence) is sound but
  not complete w.r.t. ω_t (sequence ordering eliminates multiset nondeterminism)
- **Theorems 14, 15:** Translation of ω_l/ω_l^⊗ proofs to valid ILL proofs

**Mapping to CALC's execution tree:**

Each root-to-leaf path in CALC's execution tree IS an ω_l proof:
- `step(r,θ,T')` = Apply (\\⟺) inference followed by continuation
- Unused fact = Inactivate (↑) inference
- Rule doesn't match = Weakening (W) inference
- `leaf(Δ_q)` = true axiom (goal empty, quiescent)

The full execution tree = **collection of ω_l proofs sharing common prefixes**.
Branch nodes correspond to different & choices (which rule applies).

**What ω_l does NOT cover:** ⊕ in consequents. Stéphan's system covers standard
CHR, not CHR∨. Fork nodes from ⊕ are outside ω_l's scope — for that, we need
either Betz's CHR∨ results or the QCHR extension.

### 4.4 Betz & Frühwirth CHR∨ (TOCL 2013)

**Source:** "Linear-Logic Based Analysis of CHR with Disjunction" — ACM TOCL 14(1).

CHR∨ extends CHR with disjunctive rule bodies: `H ⟺ G | (B₁ ; B₂)`.
The disjunction maps to ⊕ in ILL: `(B₁ ; B₂)^L = B₁^L ⊕ B₂^L`.

**Theorem 4.8 (Soundness):** `S ↦* T ⟹ S^L ⊢_Σ T^L` — every operational
derivation corresponds to a valid ILL deduction.

CALC's ⊕-in-consequent maps exactly to CHR∨ disjunction. The soundness
theorem transfers directly (see TODO_0043 for the detailed mapping).

**What CHR∨ gives us for fork nodes:** Fork is ⊕L inversion (invertible,
case-split eagerly). Each fork child inherits the full shared context.
The ⊕ operational transition `⟨(B₁;B₂)++G, S, B, T⟩ → ⟨Bᵢ++G, S, B, T⟩`
is exactly `expandConsequentChoices` + the symexec loop.

### 4.5 QCHR: Stéphan & Barichard (TOCL 2025)

**Source:** "Quantified Constraint Handling Rules" — ACM TOCL 26(3):1-46.

Extends CHR with ∃/∀ quantified rules, building on the ω_l sequent calculus.

**New rule types:**
- **Existential simpagation:** body succeeds if ∃ value in [low,up] makes it succeed
- **Universal simpagation:** body succeeds if ∀ values in [low,up] make body succeed
- Subsumes existential/universal simplification and propagation

**Key innovation — dynamic binder:** Quantifiers generated during execution,
not declared statically. Unlike QCSP/QCSP+ which require a fixed alternation
of quantifiers, QCHR can build the binder dynamically during solving. This
allows modeling games where the number of moves is unknown a priori.

**ω_l^{∃∀} proof system:** Extends ω_l with five new inference rules/axioms:
- ∃-Apply / ∀-Apply: apply quantified simpagation to focused constraint
- ∃-elimination: finds at least one value in interval making goal succeed
- ∀-elimination: proves goal succeeds for all values in interval
- ∀-true: terminal axiom for universal quantifier

**Theorem 5.1:** ω_r^{∃∀} (operational) is sound and complete w.r.t. ω_l^{∃∀}.

**Game-tree semantics:**
- ∃ = player A (system decides, one strategy suffices) → like ⊕
- ∀ = player B (adversary, must handle all moves) → exhaustive exploration
- Execution tree = game tree with ∃/∀ branching at quantified rules
- Tabling/memoization: store previously explored states, avoid re-computation

**Performance:** QCHR++ (C++ implementation) outperforms QuaCode (QCSP solver)
by 30-100x on game benchmarks (Nim, Connect-Four, Checkers). Tabling gives
additional 100x on games with repeated states.

**Connection to CALC's execution tree — this is the most promising formalization:**

| QCHR concept | CALC equivalent | Implementation |
|---|---|---|
| ∃-branching (system decides) | ⊕ fork (case split on disjunctive consequent) | `alts.length > 1` in `explore()` |
| ∀-branching (explore everything) | Rule nondeterminism (branch node) | `matches.length > 1` in `explore()` |
| Dynamic binder | Loli continuations (rules produced at runtime) | `matchLoli` in match.js |
| Game tree | Execution tree | `explore()` return value |
| Tabling/memoization | `pathVisited` cycle detection + state hashing | `computeNumericHash` + `Set` |
| QCHR++ solver | `symexec.js explore()` | DFS with mutation+undo |

**The execution tree type IS an ω_l^{∃∀} proof:**
- ∀-branching = rule nondeterminism (CALC always plays ∀ — explore everything)
- ∃-branching = ⊕ disjunction (system decided, but symexec explores all)
- Dynamic binder = loli continuations (quantifiers generated at runtime)
- Tabling = cycle detection

When CALC adds constraint simplification (TODO_0002), infeasible branches can be
pruned: provably-false → pure ∃ (decided). Symbolic → ∀ (must handle all).

### 4.6 muMALL: Fixed Points (Baelde & Miller)

**Source:** "Least and Greatest Fixed Points in Linear Logic" — ACM TOCL 2012.

muMALL extends MALL with least (μ) and greatest (ν) fixed point operators.
Properties: cut-elimination holds, focused proof system is complete.

**Relevance to execution trees:**
- The tree's **finite depth** witnesses termination (no μ needed yet)
- The `cycle` constructor is a **back-edge** — if formalized as a cyclic proof,
  it needs a global progress condition (Brotherston & Simpson's infinitary proofs)
- For infinite-state systems (streaming, unbounded loops), μ/ν fixed points
  would extend the tree with coinductive structure
- **Not needed now** — current execution trees are finite (bounded by gas/depth).
  But the theory connects to future work on invariant induction (TODO_0008)

### 4.7 Forum (Miller 1996)

**Source:** "Forum: A Multiple-Conclusion Specification Logic."

Forum is a specification logic with the full power of linear logic, including
additives. It handles ⊕ in forward chaining via polarity-driven decomposition.
Forum is proof-theoretic (not operational) — it doesn't define an execution model,
but shows that ⊕ in forward contexts is well-founded.

CALC's ⊕-in-consequent is a restricted instance of Forum's full ⊕ handling.
Forum validates the design choice theoretically, even though no practical system
(CLF, Celf, LolliMon, Ceptre) has adopted ⊕ in forward chaining.

---

## 5. Soundness and Completeness

### 5.1 Soundness Theorem (per-constructor)

**Theorem (Soundness):** For every leaf `Δ_q` in tree T where `Σ; Δ₀ ⊢_fwd T : A`,
the state Δ_q is reachable from Δ₀ by a valid sequence of forward steps.

**Proof strategy:** Compositional, by induction on the tree structure:

- **leaf(Δ_q):** Δ_q = Δ₀ (zero steps). Trivially reachable.
- **step(r,θ,T'):** By induction, every leaf in T' is reachable from Δ' = apply(r,θ,Δ₀).
  Since Δ₀ → Δ' is a valid forward step (r matches with θ), prepending this step
  gives reachability from Δ₀. Validity of the step follows from the Betz/Frühwirth
  soundness theorem (Theorem 4.8, TOCL 2013): rule application = valid ILL deduction.
- **fork(T₁,T₂):** Each Tᵢ explores one ⊕ alternative. By CHR∨ soundness,
  each alternative is a valid continuation. Every leaf in T₁ ∪ T₂ is reachable.
- **branch(rᵢ:Tᵢ):** Each Tᵢ is the subtree after applying rᵢ. By induction,
  leaves in each Tᵢ are reachable from apply(rᵢ,θᵢ,Δ₀). Since each rᵢ matches
  Δ₀, prepending the step gives reachability.
- **cycle(Δ):** Δ is on the current path → already shown reachable by the
  ancestor that first visited it. No new leaves.
- **bound(Δ):** Truncation. Δ is reachable (it's the state at depth maxDepth),
  but we don't know what happens beyond. Soundness holds vacuously (no leaf claim).

**Per-step soundness follows from:**
1. `tryMatch` correctness: pattern matching produces valid substitutions
2. `provePersistentGoals` correctness: persistent antecedents are legitimately provable
3. `mutateState` correctness: resource accounting preserves the ILL derivation
4. `matchLoli` correctness: loli-left is a valid ILL derivation step
5. `expandConsequentChoices` correctness: ⊕L inversion produces valid alternatives

### 5.2 Completeness Theorem

**Theorem (Completeness, for finite states):** Every quiescent state reachable from
Δ₀ appears as a leaf in the tree T where `Σ; Δ₀ ⊢_fwd T : A`.

**Depends on TODO_0042.** Completeness requires:

1. **Match completeness:** `findAllMatches(Σ, Δ)` returns ALL applicable rules.
   - Strategy stack correctness: fingerprint + disc-tree + predicate layers don't miss rules
   - Loli scanning: `findAllMatches` scans all lolis in state (after TODO_0041, done)
   - **Critical assumption:** each rule has a SINGLE match per state. If a rule can
     match the same state in multiple ways (different substitutions), only one is found.
     For EVM rules (dispatch by opcode), this holds. For general rules, multi-match
     completeness would require backtracking in `tryMatch` — not currently implemented.

2. **No false cycle detection:** Hash collisions in `pathVisited` can cause missed
   states. See §7.2 for collision probability analysis.

3. **Termination:** The state space must be finite and the depth bound sufficient.
   For EVM with bounded gas, the state space is finite (gas decreases monotonically).

**Completeness conditions:**

| Condition | Status | Notes |
|---|---|---|
| Strategy stack covers all rules | ✓ (by construction) | Catch-all layer handles unclaimed rules |
| Loli scanning complete | ✓ (after TODO_0041) | `findAllMatches` scans all loli tags |
| Single-match per rule | Assumed | Holds for EVM dispatch; general case needs multi-match |
| No hash collisions | Probabilistic | See §7.2 |
| Sufficient depth bound | User-provided | Must exceed longest trace |
| Finite state space | Program-dependent | EVM: gas bound; general: may diverge |

### 5.3 Connection to QCHR Completeness

QCHR Theorem 5.1 states: ω_r^{∃∀} is sound and complete w.r.t. ω_l^{∃∀}.

If we establish the mapping CALC ↔ QCHR (§4.5), we get completeness of CALC's
operational semantics (`explore()`) w.r.t. the proof-theoretical semantics
(ω_l^{∃∀}). This is the strongest available completeness result for the full
tree (covering both ∀-branching and ∃-branching).

---

## 6. Implementation Mapping (Code Paths)

### 6.1 explore() ↔ Inference Rules

```
explore(state, rules, opts):                    -- Top-level: build tree
│
├── pathVisited.has(hash)?  →  CYCLE rule      -- §3.5
├── depth >= maxDepth?      →  BOUND rule      -- §3.6
│
├── findAllMatches(state, rules, calc, strategy, idx)
│   │                                          -- Finds all applicable rules + lolis
│   ├── strategy.getCandidateRules(state, idx) -- Fingerprint + disc-tree + predicate
│   │   └── per candidate: tryMatch(rule, state, calc)
│   │       ├── matchAllLinear(...)            -- Match linear patterns
│   │       │   ├── matchOnePattern(...)       -- Delta/secondary/general strategies
│   │       │   └── provePersistentGoals(...)  -- State lookup → FFI → backward
│   │       └── resolveExistentials(...)       -- Fresh evars for ∃ slots
│   └── matchLoli(h, state, calc)             -- Loli continuation scanning
│
├── matches.length === 0?   →  LEAF rule       -- §3.1
│
└── for each match m:                          -- BRANCH rule (§3.4)
    ├── m.rule.consequentAlts.length <= 1?
    │   └── mutateState → go(depth+1) → undoMutate    -- STEP rule (§3.2)
    └── m.rule.consequentAlts.length > 1?
        └── for each alt: mutateState → go(depth+1) → undoMutate  -- FORK rule (§3.3)
```

### 6.2 Key Functions and Their Proof-Theoretic Roles

| Function | File | LOC | Proof role |
|---|---|---|---|
| `explore()` | symexec.js:387-486 | 100 | Tree construction (all rules) |
| `findAllMatches()` | strategy.js:200-226 | 27 | ∀-quantification over rules |
| `tryMatch()` | match.js:586-623 | 38 | Focused phase (match one rule) |
| `matchAllLinear()` | match.js:519-578 | 60 | Linear resource matching |
| `provePersistentGoals()` | match.js:269-355 | 87 | Guard proving (3-level) |
| `matchLoli()` | match.js:636-716 | 81 | Loli-left (dynamic rule firing) |
| `mutateState()` | symexec.js:284-348 | 65 | State transition (cut) |
| `undoMutate()` | symexec.js:354-368 | 15 | Backtracking (tree DFS) |
| `expandConsequentChoices()` | compile.js:118+ | ~30 | ⊕L inversion |
| `computeNumericHash()` | symexec.js:108-118 | 11 | Cycle detection hash |

### 6.3 Mutation+Undo Pattern

The implementation uses **mutable state** with undo logs, not immutable snapshots.
This is an implementation optimization (O(1) per mutation vs O(n) per snapshot)
that doesn't affect semantics:

```
DFS:  mutateState(state, ...) → log
      go(depth+1, childCtx)         -- recursive exploration
      undoMutate(state, log)         -- restore parent state
```

The undo log records `[TYPE, hash, oldValue, ...]` triples. Restoration iterates
backward. The pattern also applies to the stateIndex (`makeChildCtx`/`undoIndexChanges`).

**Proof obligation:** mutateState + undoMutate is idempotent: `undo(mutate(Δ, r, θ)) = Δ`.
This is verified by the engine tests and is straightforward from the log structure.

---

## 7. Technical Analysis

### 7.1 Tree Size Bounds

For a program with R rules, B maximum branching factor, and D maximum depth:

```
Worst case: O(R^D)    — every state has R applicable rules, each explored
With ⊕:     O((R·F)^D) — F = max fork factor per rule (typically 2)
EVM:        O(2^K)     — K = number of symbolic branch points (eq/iszero/jumpi)
```

The EVM bound is tight: each symbolic comparison creates a binary fork.
For the multisig contract, K ≈ 6, giving 2^6 = 64 leaves (actual: ~43 after pruning).

### 7.2 Hash Collision Analysis

Cycle detection uses 32-bit XOR hash (`computeNumericHash`). The hash function:

```javascript
hashPair(h, count) = scramble(h * 2654435761 ^ count * 2246822519)
stateHash = XOR of hashPair(hash, count) for all facts
```

**Collision probability:** For N distinct states visited on one path, the probability
of at least one false collision is approximately `N² / (2 · 2³²)` (birthday paradox).

| Path length N | Collision probability |
|---|---|
| 100 | ~0.0001% |
| 1000 | ~0.01% |
| 10000 | ~1.2% |
| 65536 | ~50% |

For EVM execution (paths < 1000 steps), collision risk is negligible.
For very deep explorations, upgrading to 64-bit hash or string-based comparison
would be needed.

**Impact of false positive:** A hash collision causes `explore()` to return
`{type:'cycle'}` for a state that is NOT actually a cycle. This means a subtree
is missed → completeness violation. Soundness is unaffected (no false leaves added).

### 7.3 Single-Match Limitation

`tryMatch` returns at most ONE match per rule per state. If a rule can match
the same state in multiple ways (different substitutions binding different facts),
only the first match is found.

**For EVM:** This is correct — opcode dispatch uniquely determines the match.
Each rule has a discriminator (opcode) and typically a unique pc fact, giving
exactly one match per applicable rule.

**For general programs:** Multi-match rules need backtracking in `tryMatch`
or an explicit enumeration of all matches. This is a completeness gap for
non-EVM programs. CHR systems handle this via constraint IDs and partner search.

---

## 8. Implementation Options

### 8.1 Option A: QCHR-Based Formalization (Recommended)

**Approach:** Map CALC's tree to ω_l^{∃∀} proofs directly.

**Pros:**
- Ready-made soundness+completeness theorems (Theorem 5.1)
- Handles both ∀-branching (rules) and ∃-branching (⊕) in one framework
- Dynamic binder = loli continuations (natural fit)
- Game-tree semantics provides intuitive understanding
- Published, peer-reviewed framework (TOCL 2025)

**Cons:**
- QCHR doesn't cover CALC's strategy stack optimizations (indexing, preserved-skip)
- Need to formalize the CALC → QCHR mapping precisely
- QCHR uses value intervals [low,up]; CALC uses symbolic terms (different ∃ mechanism)

**Steps:**
1. Define translation CALC state → QCHR state
2. Define translation CALC rule → QCHR rule (simpagation with disjunction)
3. Show `explore()` execution ≈ QCHR solving
4. Apply Theorem 5.1 to get soundness+completeness
5. Write as `doc/theory/execution-tree-judgment.md`

**Estimated effort:** ~2-3 focused sessions.

### 8.2 Option B: Direct ω_l Extension

**Approach:** Extend ω_l with ⊕ and ∀-branching directly.

**Pros:**
- More precise match to CALC's actual structure
- Stéphan's ω_l is simpler than full QCHR
- The & program structure maps cleanly

**Cons:**
- Need to add ⊕ to ω_l ourselves (no published result)
- Need to prove soundness+completeness ourselves
- More original work needed

**Steps:**
1. Define ω_l + ⊕ (add disjunction transition from CHR∨)
2. Define ω_l + ∀ (add universal branching for exhaustive exploration)
3. Prove soundness: each tree node = valid ω_l inference
4. Prove completeness: every ω_l proof has a corresponding tree path
5. Write as `doc/theory/execution-tree-judgment.md`

**Estimated effort:** ~4-5 focused sessions (more original proof work).

### 8.3 Option C: Compositional (Mix Existing Results)

**Approach:** Use different frameworks for different tree nodes.

- **step/leaf:** Betz soundness (Theorem 4.8) for single-step validity
- **fork:** CHR∨ soundness for ⊕ (Betz TOCL 2013)
- **branch:** Universal quantification over rule choices (elementary set theory)
- **cycle/bound:** Finiteness arguments (not proof-theoretic)

**Pros:**
- Uses established results directly (no new proofs)
- Each node type has independent justification
- Simplest to write

**Cons:**
- No unified framework
- Doesn't capture the tree AS a proof object
- Less theoretically satisfying

**Steps:**
1. For each constructor, cite the relevant theorem
2. Compose via induction on tree depth
3. Write as `doc/theory/execution-tree-judgment.md`

**Estimated effort:** ~1-2 focused sessions.

### 8.4 Recommendation

**Option A (QCHR) for the formal writeup, with Option C as the quick path.**

Option C gives immediate results with minimal proof effort — good for grounding
the implementation. Option A gives the strongest theoretical result and connects
CALC to the most advanced framework in the CHR lineage. Option B is only worth
pursuing if we find gaps that QCHR can't cover.

---

## 9. Tasks

- [ ] **Write inference rules** for each tree constructor (§3, drafted above)
- [ ] **Prove soundness:** every leaf reachable (§5.1, compositional per-constructor)
- [ ] **Prove completeness:** every reachable quiescent state is a leaf (depends on TODO_0042)
- [ ] **Choose formalization path:** Option A (QCHR) vs Option B (ω_l extension) vs Option C (compositional)
- [ ] **QCHR mapping:** Define precise translation CALC → QCHR (if Option A)
- [ ] **Connect to SLS:** Show CALC's tree = universal quantification over SLS traces (§4.1)
- [ ] **Connect to focusing:** Formalize strategy stack as focusing strategy (§4.2)
- [ ] **Analyze single-match limitation:** Characterize programs where single-match = complete (§7.3)
- [ ] **Write up** as `doc/theory/execution-tree-judgment.md`

---

## 10. References

### Primary Sources

- `doc/theory/0001_exhaustive-forward-chaining.md` — proposed judgment (informal), Q5+Q6
- `doc/research/0007_chr-linear-logic.md` — CHR survey, §2.4 (ω_l), §2.5 (QCHR), §10.2-10.3
- [TODO_0042](0042_exhaustive-exploration-completeness.md) — completeness of exploration
- [TODO_0043](0043_chr-linear-logic-mapping.md) — CHR∨ soundness (⊕ justification), §7-8

### Papers

- Andreoli (1992) "Logic Programming with Focusing Proofs in Linear Logic" JLC 2(3):297-347
- Betz, Frühwirth (2013) "Linear-Logic Based Analysis of CHR with Disjunction" ACM TOCL 14(1)
- Barichard, Stéphan (2025) "Quantified Constraint Handling Rules" ACM TOCL 26(3):1-46
- Stéphan (2018) "A New Proof-Theoretical Linear Semantics for CHR" ICLP 2018, OASIcs 4:1-4:17
- Simmons (2012) "Substructural Logical Specifications" CMU-CS-12-142
- Simmons, Pfenning (2008) "Linear Logical Algorithms" ICALP 2008
- Chaudhuri, Pfenning, Price (2006) "A Focusing Inverse Method Theorem Prover" CADE-21
- Liang, Miller (2009) "Focusing and Polarization" TCS 410(46):4747-4768
- Watkins, Cervesato, Pfenning, Walker (2004) "CLF" LNCS 3085
- Baelde, Miller (2012) "Least and Greatest Fixed Points in Linear Logic" ACM TOCL
- Miller (1996) "Forum: A Multiple-Conclusion Specification Logic"
- Betz (2014) "A Unified Analytical Foundation for CHR" PhD thesis, Ulm
- Simmons (2014) "Structural Focalization" ACM TOCL

### Implementation (Code)

- `lib/engine/symexec.js` — `explore()`, tree construction, mutation+undo
- `lib/engine/strategy.js` — `findAllMatches()`, strategy stack
- `lib/engine/match.js` — `tryMatch()`, `provePersistentGoals()`, `matchLoli()`
- `lib/engine/forward.js` — `run()`, `applyMatch()` (committed-choice variant)
- `lib/engine/compile.js` — `expandConsequentChoices()`, `expandItem()`
