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
starred: true
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

## 3. Object/Meta Distinction and Verification Architecture

### 3.1 The Three Levels

```
Level 3 (meta-meta): "The implementation is correct"
    Claim ABOUT the JS code. Cannot be proved inside the system.
    Trust model: testing, inspection, or verified extraction.

Level 2 (meta):      Σ; Δ ⊢_fwd T
    Execution tree judgment. Claims about all reachable states.
    Side conditions reference the ABSTRACT matching function.
    This is what TODO_0045 formalizes.

Level 1 (object):    Δ₀ ⊢_ILL Δ_q
    Individual ILL entailment. Each step is a sequent transformation.
    This is what the kernel (L1, kernel.js) can verify.
```

The inference rules below are **Level 2 (meta-level) rules**. They describe
the tree construction algorithm abstractly. Side conditions like "no rule
matches Δ" are meta-level assertions, NOT something derived inside ILL.

This is the standard approach: Stéphan's ω_l, Simmons' SLS, and CLF all
define meta-level judgments with side conditions about matching/applicability.
The side conditions are properties OF the program and state, checked externally.

### 3.2 What "Proving Soundness" Actually Means

There is a **verification gap** between three things:

1. **The abstract algorithm** (on paper): "find all matching rules, apply each,
   recurse." Described by the inference rules below.
2. **The JS implementation** (`explore()`, `findAllMatches()`, etc.): ~1500 LOC
   of JavaScript implementing the algorithm.
3. **The ILL derivation**: each individual step is a valid sequent transformation.

**Soundness of the abstract algorithm** (Level 2 → Level 1) is provable on paper:
"IF the matching function correctly identifies applicable rules and IF apply
correctly transforms state, THEN each leaf is ILL-entailed by the initial state."
This is a theorem about the abstract algorithm, not about JavaScript.

**Faithfulness of the implementation** (Level 3 → Level 2) is the hard part.
There are four approaches, each with a different trust boundary:

| Approach | Trust boundary | What you prove | What you trust |
|---|---|---|---|
| **A. Paper proof + trusted impl** | JS code = algorithm | Algorithm correct (on paper) | JS faithfully implements algorithm |
| **B. Proof certificates + kernel** | Only the L1 kernel | Nothing about explore() | 200 LOC kernel checks each step |
| **C. Property-based testing** | Test harness | Statistical confidence | Test coverage is adequate |
| **D. Verified extraction** | Proof assistant | Everything | Coq/Lean/Agda |

### 3.3 Approach B: Proof Certificates (the de Bruijn Way)

This is the most practical high-assurance approach for CALC. The idea:

**Don't trust `explore()` at all. Have it emit certificates. Trust only the kernel.**

```
explore() produces:  Tree T  +  for each path p in T, a certificate C_p

Certificate C_p = sequence of (rule, θ, consumed, produced) tuples

Kernel checks each step:
  for each (rule, θ, consumed, produced) in C_p:
    1. consumed ⊆ current_state        (resources available)
    2. θ = unify(rule.antecedent, consumed)  (substitution valid)
    3. produced = substitute(rule.consequent, θ)  (output correct)
    4. persistent antecedents are provable    (guards hold)
    ✓ → advance state
    ✗ → reject certificate (bug in explore)
```

**Soundness is FREE:** If the kernel accepts a certificate, the path is sound
by construction. Bugs in `explore()`, `findAllMatches()`, `tryMatch()`, the
strategy stack, preserved-skip, mutation+undo — none of them matter. The kernel
is the single point of trust.

**Completeness remains an oracle claim:** The kernel can verify "this path is
valid" but NOT "no paths were missed." Completeness requires trusting that
`findAllMatches()` returns ALL applicable rules. This is an inherent limitation —
you cannot verify a negative ("nothing was missed") via a positive certificate.

**What CALC already has:** The L1 kernel (`lib/prover/kernel.js`: `verifyStep`,
`verifyTree`) already checks individual proof steps. The gap: it operates on
backward-chaining proof trees, not forward-chaining execution traces. Extending
it to verify forward step certificates is ~50-100 LOC.

### 3.4 What We Can and Cannot Prove

| Property | Provable? | How | Trust boundary |
|---|---|---|---|
| **Per-step soundness** | Yes (paper) | Betz Theorem 4.8 | The abstract step is valid ILL |
| **Per-step soundness** | Yes (machine) | Kernel verifies certificate | Only 200 LOC kernel |
| **Tree soundness** | Yes (paper) | Induction over tree (§5.1) | Abstract algorithm correct |
| **Tree soundness** | Yes (machine) | Kernel verifies every path | Only 200 LOC kernel |
| **Completeness** | Partially (paper) | Under assumptions (§5.2) | `findAllMatches` is complete |
| **Completeness** | No (machine) | Can't verify a negative | Trust `findAllMatches` |
| **JS faithfulness** | No (without Coq) | Can't prove JS correct | Trust or test |

**The honest answer:** At some point you trust an oracle. The question is
WHERE you draw the trust boundary:

- **Minimal trust (Approach B):** Trust only `verifyStep` (~200 LOC). Everything
  else is untrusted and checked. Soundness is machine-verified per path.
  Completeness requires trusting `findAllMatches`.
- **Medium trust (Approach A):** Trust that the JS implements the paper algorithm.
  Soundness is proved on paper. Tested via engine tests (124 tests).
- **Maximum trust (Approach D):** Formalize in Coq, extract to OCaml/JS. Trust
  only the Coq kernel. Enormous effort, not practical short-term.

### 3.5 Meta-Level Inference Rules

These rules describe the **abstract algorithm**. Side conditions are meta-level
assertions about the abstract matching function `matches(Σ, Δ)`, NOT about the
JS implementation. The JS implementation is claimed to faithfully implement
this abstract function — that claim is the trust boundary (or verified via
certificates per §3.3).

**Notation:**
- `matches(Σ, Δ)` — abstract function returning the set of all (rule, θ) pairs
  where rule r ∈ Σ matches state Δ with substitution θ. Meta-level, not in ILL.
- `apply(r, θ, Δ)` — abstract function applying rule r with substitution θ to
  state Δ, consuming linear resources and producing consequent. Meta-level.
- `alts(r, θ)` — alternatives from ⊕ in rule r's consequent. Meta-level.

#### LEAF (Quiescence)

```
  matches(Σ, Δ) = ∅
  ─────────────────────────────── LEAF
  Σ; Δ ⊢_fwd leaf(Δ)
```

Side condition: no rule in Σ matches Δ. This is an assertion about the
abstract matching function. The JS `findAllMatches()` computes this; the
kernel does not check it (it's a completeness concern, not soundness).

#### STEP (Deterministic)

```
  matches(Σ, Δ) = {(r, θ)}    |alts(r, θ)| = 1
  Δ' = apply(r, θ, Δ)
  Σ; Δ' ⊢_fwd T
  ───────────────────────────────────────────── STEP
  Σ; Δ ⊢_fwd step(r, θ, T)
```

One rule, one alternative. The step Δ → Δ' is verifiable by the kernel
(ILL derivation). The continuation T is recursive.

#### FORK (⊕ Case Split)

```
  (r, θ) ∈ matches(Σ, Δ)    alts(r, θ) = {a₁, ..., aₖ}    k > 1
  ∀i. Δᵢ = apply(r, θ, Δ, aᵢ)
  ∀i. Σ; Δᵢ ⊢_fwd Tᵢ
  ──────────────────────────────────────────────────── FORK
  Σ; Δ ⊢_fwd step(r, θ, fork(T₁, ..., Tₖ))
```

⊕L inversion: the consequent has ⊕, so all alternatives are explored.
Each Δ → Δᵢ is independently verifiable by the kernel.

#### BRANCH (∀ Over Rules)

```
  matches(Σ, Δ) = {(r₁,θ₁), ..., (rₙ,θₙ)}    n ≥ 1
  ∀i. Σ; apply(rᵢ, θᵢ, Δ) ⊢_fwd Tᵢ
  ──────────────────────────────────────────────── BRANCH
  Σ; Δ ⊢_fwd branch(r₁:T₁, ..., rₙ:Tₙ)
```

All applicable rules explored. Note: STEP is the special case n=1, k=1.
BRANCH with forks is the general case (each rᵢ may itself have forks).

The universal quantification "for all applicable rules" is the meta-level
claim that cannot be kernel-checked. The kernel can verify each path
(soundness) but not that ALL paths are present (completeness).

#### CYCLE / BOUND (Terminal)

```
  Δ ∈ path                           depth ≥ maxDepth
  ──────────────── CYCLE              ──────────────────── BOUND
  Σ; Δ ⊢_fwd cycle(Δ)               Σ; Δ ⊢_fwd bound(Δ)
```

Both are terminal: no further exploration. Neither makes a leaf claim
(no quiescent state asserted). Soundness is vacuous. These are pragmatic
truncations, not proof-theoretic constructs.

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

### 5.1 The Verification Gap — What Can Be Proved and How

There are two separate questions:

**Q1 (Abstract soundness):** "Is the abstract algorithm correct?"
— IF `matches()` returns a valid (r,θ) pair, AND `apply()` correctly transforms
state, THEN every leaf is ILL-entailed by the initial state.
This is provable on paper by induction on the tree. It's a theorem about the
**abstract algorithm** described in §3.5, not about JavaScript.

**Q2 (Implementation faithfulness):** "Does the JS code implement the algorithm?"
— Does `findAllMatches()` compute the same set as abstract `matches()`?
— Does `mutateState()` compute the same state as abstract `apply()`?
This is NOT provable without formalizing the JS. At some point, you trust an oracle.

**The honest position:**
- Q1 is solvable (paper proof, induction, cite Betz/Stéphan)
- Q2 is an **engineering trust boundary** — addressed by one of:
  - Approach B: emit certificates, verify with kernel (trust only kernel)
  - Approach C: property-based testing (trust test coverage)
  - Approach D: verified extraction (trust proof assistant)
  - Or simply: manual inspection + code review (trust the developer)

Every real system draws this line somewhere. CompCert trusts the Coq kernel.
GCC trusts its test suite. CALC should explicitly state its trust boundary.

### 5.2 Soundness of the Abstract Algorithm (Q1)

**Theorem (Soundness):** For every leaf `Δ_q` in tree T where `Σ; Δ₀ ⊢_fwd T`,
the state Δ_q is reachable from Δ₀ by a valid sequence of ILL derivation steps.

**Proof:** By induction on the tree structure.

- **leaf(Δ_q):** Δ_q = Δ₀ (zero steps). Trivially reachable via reflexivity.

- **step(r,θ,T'):** The step Δ₀ → Δ' is a valid ILL derivation by
  Betz/Frühwirth Theorem 4.8: rule application = valid ILL deduction
  (simpagation maps to linear implication). By induction hypothesis,
  every leaf in T' is reachable from Δ'. Composing gives reachability from Δ₀.

- **fork(T₁,...,Tₖ):** Each Tᵢ explores one ⊕ alternative. Each Δ → Δᵢ is
  independently a valid ILL step (⊕L inversion, which is sound — Betz TOCL 2013
  Theorem 4.8 covers CHR∨ disjunction). By induction, leaves in each Tᵢ are
  reachable from Δᵢ, hence from Δ₀.

- **branch(rᵢ:Tᵢ):** Each rᵢ independently matches Δ₀. Each Δ₀ → apply(rᵢ,θᵢ,Δ₀)
  is a valid ILL step (same as step case). By induction, leaves in each Tᵢ are
  reachable. Note: the universal quantification ("all rules explored") is NOT
  needed for soundness — soundness only says "every leaf in the tree IS reachable",
  not "every reachable state IS a leaf."

- **cycle(Δ) / bound(Δ):** No leaf claim. Soundness holds vacuously.

**What this proof assumes (the oracle):**
1. `matches(Σ, Δ)` returns VALID matches — every (r,θ) pair it returns actually
   satisfies: θ unifies r's antecedent with facts in Δ, and persistent antecedents
   are provable. This is the **per-step validity** assumption.
2. `apply(r, θ, Δ)` correctly computes the resulting state.

These are assumptions about the ABSTRACT functions, not about JS code.
For the JS: Approach B (certificates + kernel) eliminates assumption 1 entirely.

### 5.3 Soundness via Certificates (Eliminating the Oracle)

With proof certificates (§3.3), soundness becomes **machine-checkable**:

```
For each root-to-leaf path p = [(r₁,θ₁), (r₂,θ₂), ..., (rₙ,θₙ)]:
  Δ₀ →[r₁,θ₁] Δ₁ →[r₂,θ₂] Δ₂ → ... → Δₙ = leaf

  The kernel verifies each step Δᵢ →[rᵢ₊₁,θᵢ₊₁] Δᵢ₊₁:
    - consumed resources exist in Δᵢ
    - substitution θ is valid
    - produced resources match rule consequent
    - persistent antecedents are provable

  If ALL steps verify → path is sound. No trust in explore() needed.
```

**Trust boundary:** Only the kernel (~200 LOC). Everything else — `explore()`,
`findAllMatches()`, `tryMatch()`, the strategy stack, mutation+undo — is
untrusted code whose output is checked by the kernel.

**Soundness theorem (certificate version):** If the kernel accepts all path
certificates in tree T, then every leaf in T is reachable from Δ₀ by valid
ILL derivation steps. Proof: each kernel-verified step is a valid ILL inference
(by correctness of `verifyStep`). Composition of valid steps gives reachability.

**What the kernel CAN'T check:** Completeness. The kernel verifies "this path
is valid" but not "no paths were missed." That requires trusting `findAllMatches`.

### 5.4 Completeness (Inherently Requires an Oracle)

**Theorem (Completeness, for finite states):** Every quiescent state reachable
from Δ₀ appears as a leaf in the tree T where `Σ; Δ₀ ⊢_fwd T`.

**This theorem is inherently about the implementation.** It says: the algorithm
(and hence the code) doesn't MISS any reachable state. You cannot verify this
via certificates — you'd need a certificate for something that DOESN'T exist
(a missed state), which is a logical impossibility.

**Completeness requires trusting:**

1. **Match completeness:** `matches(Σ, Δ)` returns ALL applicable (r,θ) pairs.
   For the abstract algorithm, this is definitional. For the JS implementation,
   this is the oracle claim. Mitigations:
   - Strategy stack has a catch-all layer (no rule falls through)
   - Loli scanning covers all loli-tagged facts (after TODO_0041)
   - **Known gap:** single-match-per-rule (§7.3) — limits completeness to
     programs where rules match uniquely. Holds for EVM.

2. **No false cycle detection:** Hash collisions in `pathVisited` cause missed
   subtrees. Mitigation: 32-bit XOR hash has negligible collision probability
   for paths < 1000 steps (§7.2). Not a proof, a probabilistic argument.

3. **Sufficient depth/termination:** The depth bound must exceed the longest
   trace, and the state space must be finite. For EVM with bounded gas, gas
   decreases monotonically → finite. For general programs: undecidable.

**Completeness conditions:**

| Condition | Nature | Verifiable? |
|---|---|---|
| `matches()` returns all valid pairs | Oracle claim | Testing only (Approach C) |
| Strategy stack doesn't drop rules | Structural (catch-all layer) | Code inspection |
| Loli scanning covers all lolis | Implementation detail | Code inspection + tests |
| Single-match suffices | Program property | Provable per-program (EVM: yes) |
| No hash collisions | Probabilistic | Statistical argument |
| Depth bound sufficient | User parameter | User responsibility |
| State space finite | Program property | Gas bound for EVM; undecidable generally |

### 5.5 Connection to QCHR Completeness

QCHR Theorem 5.1 states: ω_r^{∃∀} is sound and complete w.r.t. ω_l^{∃∀}.

This theorem is about the ABSTRACT QCHR operational semantics ω_r^{∃∀}, not
about any specific implementation (QCHR++ is C++, CALC is JS). It says: "the
abstract algorithm explores exactly the right set of states."

If we establish the mapping CALC's abstract algorithm ↔ QCHR's ω_r^{∃∀}, we
inherit completeness at the ABSTRACT level. The implementation gap (Level 3 → Level 2
from §3.1) remains — it always does, in every system. The value of the QCHR
mapping is: it gives us the strongest known completeness result for the abstract
algorithm, covering both ∀-branching and ∃-branching in one framework.

### 5.6 Practical Recommendation

**For CALC's trust model:**

1. **Soundness:** Implement Approach B (certificates + kernel). Cost: ~100 LOC
   to extend L1 kernel for forward step verification. Benefit: machine-checked
   soundness with minimal trust boundary.

2. **Completeness:** Accept as an oracle claim, backed by:
   - Paper proof that the abstract algorithm is complete (via QCHR Theorem 5.1)
   - Engine tests (124 tests) as statistical confidence
   - Structural argument (catch-all strategy layer)
   - Per-program analysis for specific rule sets (EVM: deterministic dispatch)

3. **Document the trust boundary explicitly:** "Soundness is kernel-verified.
   Completeness assumes `findAllMatches` is faithful to the abstract `matches()`
   function. This assumption is tested but not machine-verified."

This is an honest, defensible position — stronger than most practical systems.

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
