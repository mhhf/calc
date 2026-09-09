---
title: "Parametric Forward Chaining: the Eigenvariable Semantics of Existentials"
created: 2026-09-08
modified: 2026-09-10
summary: "Existentials in forward-rule consequents have exactly one semantics — eigenvariable opening (CLF let-binding) — and eager witness computation is a separate, admissible rule (forced elimination) whose side condition is uniqueness: ground inputs × functional predicate, the forward-fragment transplant of Twelf's uniqueness modes. States denote their satisfiable groundings; the b1588c6e collapse is the violation class 'witness capture' (eliminating an unforced parameter from one conjunct's isolated instance), which fabricates leaves outside the denotation while dropping leaves inside it. The framework-level prize is parametric adequacy: for well-moded, guard-covering programs, parametric exploration is a sound and complete abstraction of ground execution — symbolic-execution correctness proved once at the logic level, not per language. The theory exposes two unmanifested engine gaps no test on the current corpus can reach: uniqueness is unchecked at the lookup/clause tiers (G1) and tell-consistency of ground theory-atoms is unchecked (G2)."
tags: [linear-logic, forward-chaining, proof-theory, symbolic-execution, existential, modes, clf, engine-theory]
category: "Proof Theory"
paper: "Open disposition. Candidate homes: a standalone certified-symbolic-execution paper (theorem 3 as the spine, the EVM engine as evaluation, kernel-checkable path certificates as the differentiator vs hevm/KEVM), or the toolbox paper §7 boundary-theorem family (forced elimination as another certified fast path). The mode system that discharges Theorem 3's hypothesis is the open research artifact and would anchor the standalone paper."
unique_contribution: "Five results not in the literature or prior CALC docs: (1) forced elimination as an admissible rule over the CLF eigenvariable semantics — eliminating a parameter by substitution preserves the state's denotation iff the parameter's constraint set has a unique theory-witness (groundness × functionality; Twelf-style uniqueness modes moved to the forward fragment), making every engine fast path an implementation of one rule with one checkable side condition; (2) the violation class WITNESS CAPTURE — instantiating an unforced parameter from one conjunct's isolated instance — with the precise damage statement: fabricated leaves outside the denotation plus dropped leaves inside it (simultaneous soundness and completeness failure), of which the b1588c6e collapse is an instance; (3) a parametric-adequacy statement for CLF-style committed-choice forward chaining: under well-modedness (parameters flow only into opaque positions or guard-covering ⊕-branches), the parametric LTS is a sound+complete abstraction of the ground LTS — symbolic-execution correctness at framework grain; (4) two engine obligations the theory exposes that testing on functional-only corpora cannot: per-predicate uniqueness certification for the lookup/clause tiers (G1) and tell-consistency checking for ground theory-atoms (G2); (5) the mode check that discharges result (3)'s hypothesis — a load-time abstract interpretation over predicate-argument-position freeness whose soundness theorem (Theorem 4) makes well-modedness a checked program property rather than an assumed one, so symbolic-execution adequacy holds by a per-program static check plus one metatheorem."
references:
  - "Watkins, Cervesato, Pfenning & Walker (2002/2004). A Concurrent Logical Framework (CLF). CMU-CS-02-101 + LFM 2004 — ∃ in the monad opened by let-pattern with a fresh parameter; the semantics §1 adopts."
  - "López, Pfenning, Polakow & Watkins (2005). Monadic Concurrent Linear Logic Programming (LolliMon). PPDP 2005."
  - "Schack-Nielsen & Schürmann (2008). Celf — a logical framework for deductive and concurrent systems. IJCAR 2008 — instantiates monadic ∃ by unification (narrowing-style); contrast with the opaque-parameter discipline here."
  - "Simmons (2012). Substructural logical specifications (SLS). CMU PhD thesis."
  - "Martens (2015). Ceptre: a language for modeling generative interactive systems. AIIDE 2015 — forward ∃ as fresh-name generation, i.e. permanent opening, never elimination."
  - "Saraswat (1993). Concurrent Constraint Programming. MIT Press — ask/tell; §4's tell-consistency."
  - "Jaffar & Maher (1994). Constraint logic programming: a survey. JLP — the constraint-store reading of parametric states."
  - "Hanus (2013). Functional logic programming: from theory to Curry — residuation (suspend on non-ground) vs narrowing; forced elimination is residuation's eager complement."
  - "Rohwedder & Pfenning (1996). Mode and termination checking for higher-order logic programs. ESOP; Twelf %unique — uniqueness modes, the side condition of Theorem 1 in its native habitat."
  - "Somogyi, Henderson & Conway (1996). The execution algorithm of Mercury. JLP — mode systems for logic programs."
  - "Muthukumar & Hermenegildo (1991). Combined determination of sharing and freeness of program variables through abstract interpretation. ICLP — the freeness/groundness (Pos) domain §6's parameter-flow analysis instantiates."
  - "Bruynooghe (1991). A practical framework for the abstract interpretation of logic programs. JLP — the abstract-interpretation frame §6's least-fixpoint taint computation sits in."
  - "King (1976). Symbolic execution and program testing. CACM — the ground/symbolic lifting, per-language; Theorem 3 is the framework-level version."
  - "Roşu (2017). Matching logic. LMCS — K's model-theoretic route to symbolic execution; here the route is proof-theoretic (eigenvariables + linearity for frames)."
  - "Bruni et al. (2024). Skolemization for intuitionistic linear logic. IJCAR — why witness terms (Skolem functions) are not the mechanism; supports TODO_0002's eigenvariable decision."
  - "THY_0001 (exhaustive forward chaining — the world-set the denotation refines), THY_0016 (partial evaluation as cut elimination — forced elimination is its runtime instance), THY_0035 (the family-parametric judgment ⊢_fwd whose axiom A3 this document is the full theory of), TODO_0002 (the eigenvariable decision this document gives the metatheory for), TODO_0005 (constraint propagation = the engine's future consistency/pruning layer), TODO_0307 (the incident, isolation, and implementation corollary)."
---

# Parametric Forward Chaining: the Eigenvariable Semantics of Existentials

**Scope.** The metatheory behind TODO_0002's design decision and TODO_0307's
incident: what a consequent existential MEANS in committed-choice linear
multiset rewriting, when a witness may be computed eagerly, what precisely
went wrong in b1588c6e, and what remains between the current engine and the
ideal. Programs are forward rules over a persistent theory 𝒯 (backward
clauses, equational theories, FFI-specified functions); the running model is
the EVM instance, but every statement is calculus-generic.

## 1. One rule, not two: ∃-opening

A forward rule, after monadic decomposition, has the shape

    r : Πy⃗. A₁ ⊗ … ⊗ Aₙ ⊸ {∃x⃗. (!Q₁ ⊗ … ⊗ !Qₖ ⊗ F₁ ⊗ … ⊗ Fₘ)}

with y⃗ bound by matching, x⃗ existential, Qᵢ persistent (theory-)atoms and
Fⱼ linear. A **state** is ⟨Ξ; Γ; Δ⟩ — a set of parameters Ξ (eigenvariables),
persistent atoms Γ and a linear multiset Δ over Σ ∪ Ξ.

The semantics of firing is the CLF let-binding, and it is the ONLY firing
rule:

    (∃-open)   fire r under θ  ⟹  Ξ' = Ξ ∪ {c⃗} fresh,
               Γ' = Γ ∪ {Qᵢ[θ, c⃗/x⃗]},  Δ' = (Δ ∖ θA⃗) ∪ {Fⱼ[θ, c⃗/x⃗]}

There is no witness search in the logic. Ceptre implements exactly this rule
and nothing else (fresh-name generation); Celf instead instantiates by
unification — a narrowing discipline this framework deliberately rejects
(TODO_0002; parameters are opaque, constraints are flat, resolution is a
separate concern).

**Denotation.** Worlds live under grounding, not in the syntax:

    ⟦⟨Ξ; Γ; Δ⟩⟧ = { ⟨Γ; Δ⟩[σ]  :  σ : Ξ → ground Σ-terms,  𝒯 ⊨ Γ_𝒯[σ] }

where Γ_𝒯 are the theory-atoms of Γ. A leaf with unsatisfiable constraints
denotes ∅ (an infeasible path — noise, not a world). All completeness and
soundness claims below are about denotations, never about syntactic states.

## 2. Forced elimination: the admissible second rule

Eager computation ("C := x + K when x is ground") is not part of ∃-opening;
it is a separate, admissible rule:

    (force)    if 𝒯 ⊢ ∃!x. C_c(x) with witness t,  then
               ⟨Ξ ∪ {c}; Γ; Δ⟩  ⟶  ⟨Ξ; Γ[t/c]; Δ[t/c]⟩

where C_c ⊆ Γ is the constraint set mentioning c.

**Theorem 1 (forced elimination preserves denotation).**
If c is forced with witness t, then ⟦⟨Ξ∪{c}; Γ; Δ⟩⟧ = ⟦⟨Ξ; Γ[t/c]; Δ[t/c]⟩⟧.
*Proof sketch.* (⊇) any grounding of the eliminated state extends to the
parametric one by σ(c) := t; the constraints hold by 𝒯 ⊢ C[t]. (⊆) any
admissible σ for the parametric state satisfies 𝒯 ⊨ C[σ(c)]; uniqueness
gives σ(c) ≡_𝒯 t, so σ factors through the substitution. ∎

**The side condition decomposes.** ∃!-derivability in practice splits into
**groundness of the constraint's input positions** × **functionality of the
predicate in those positions** — precisely a mode + uniqueness declaration
(Twelf's %unique, Mercury's determinism), evaluated at runtime on the
groundness half and certified per-predicate on the functionality half. The
engine's tiered resolver (FFI → state lookup → compiled clauses → full
clauses) is, in this light, a stack of *implementations of (force)*, each
obligated to the same side condition. THY_0016's frame applies verbatim:
(force) is a runtime cut — the constraint atom cut against its unique
derivation — and eager resolution is partial evaluation of the deferred
semantics, sound exactly on the forced fragment.

**What (force) is not.** It is not choice. A parameter whose constraint set
has several 𝒯-witnesses (`∃x. !edge(a,x)` with two edges) denotes several
worlds; eliminating it by ANY single witness strictly shrinks the denotation.
Choice belongs to ⊕ — the connective exhaustive exploration enumerates —
never to ∃. This is the sharpest formulation of the repo's existing
discipline that branching is structural.

## 3. The violation class: witness capture

Define **witness capture**: eliminating an unforced parameter c by a term
obtained from ONE element of C_c in isolation — proving Qᵢ[t] for some t
(or matching a stored instance of Qᵢ) while the remaining constraints in
C_c are neither derived nor checked, and asserting them at t regardless.

Damage statement: witness capture (i) fabricates a leaf outside the
denotation whenever some Qⱼ[t] is 𝒯-unsatisfiable — the state contains
asserted false knowledge — and (ii) drops every leaf whose groundings had
σ(c) ≠ t. Soundness and completeness fail simultaneously, and downstream
guard-branches degenerate (a captured-concrete value decides ⊕-branches
that the denotation splits).

The b1588c6e incident is an exact instance: `∃C,C'. !plus(x,K,C) ⊗
!to256(C,C')` with x parametric; `plus` correctly unresolvable; the
implementation attempted `to256(C,C')` with C still an *unbound pattern
slot* — syntactically a wildcard, matching the unrelated stored fact
`to256(0,0)` — capturing C := 0 and asserting the unsatisfiable
`plus(x,K,0)`. The 31-world denotation collapsed to 2 fabricated leaves.
The operational root is an ordering violation of §1: the implementation
resolved before opening, so between the two phases the existential was
neither a parameter (opaque) nor forced (justified) but a hole. The
repair — open at the moment determination fails, eliminate only under
(force) — is the implementation corollary, not the theory (TODO_0307 S0;
tests/engine/existential-eigenvariable.test.js pins it with a four-mode
equivalence gate, the executable shadow of Theorems 1–2).

## 4. Ask, tell, and the two unmanifested gaps

Premise theory-atoms are **asks** (backward-provable side conditions);
consequent theory-atoms are **tells** (constraint assertions on parameters,
or knowledge claims when ground). The ask/tell reading (Saraswat) makes two
engine obligations visible that the current corpus — where every ∃-chained
predicate happens to be functional and every ground tell true — cannot
witness in any test:

**G1 (uniqueness is unchecked).** The lookup and clause tiers implement
(force) gated on groundness alone. On a relational predicate they commit to
the first witness — silent denotation loss, the completeness half of
witness capture. Obligation: per-predicate functionality certification
(declared uniqueness modes + a load-time determinism lint over clause sets;
the repo's datasort fence f3 is the established precedent for exactly this
check shape), with non-certified predicates permanently deferred.

**G2 (tell-consistency is unchecked).** A ground tell of a false theory-atom
(assert `lt(7,5)`) creates a zombie leaf — denotation ∅ — that exploration
counts as a world. Decidable at assertion time by the ask machinery itself;
absent. Obligation: ground tells of 𝒯-predicates are checked, and failure
kills the branch (the sound reading of an inconsistent tell). Parametric
tells accumulate; their consistency is the province of propagation
(TODO_0005: substitute on binding, re-check touched constraints, prune on
derived contradiction — sound refinement of the denotation, never loss).

*Discharged for the declared-decidable fragment (task #80).* The
EqNeqSolver's own class — the calculus-declared constraint predicates
(`cc.domain.constraintPreds` = {eq, neq}), for which the solver is a
complete decision procedure — is now checked at exploration's single-alt
tell path (the multi-alt ⊕ path already SAT-filtered its guards). An
inconsistent ground eq/neq tell prunes the branch to a `dead` node; the
solver already accumulates these tells, so the check is a consult of state
it was already maintaining. Two pieces of the obligation remain, each the
mode system's (§5): (i) *predicates beyond eq/neq* — extending the checked
fragment needs the per-predicate totality/uniqueness certification of G1
(fail-to-prove = false only for a certified-closed-world predicate); (ii)
*the exec committed-choice path* — explore's leaf-set carries the
reachable-world semantics a zombie violates, whereas exec runs one path and
a single-alt false tell there is ill-formed input, caught properly by
load-time well-modedness rather than a runtime prune. Impl:
`lib/engine/explore.js` single-alt block + `lib/engine/constraint.js`
(`feedPers` returns the recognized-constraint count); pins:
`tests/engine/g2-tell-consistency.test.js`.

## 5. Parametric adequacy: the framework-level theorem

Call a program **well-moded** when parameters reach only (i) opaque
positions — carried, stored, compared for identity — or (ii) scrutinee
positions of ⊕-branches whose guard alternatives **cover** the value space
and tell the corresponding constraint (the jumpi discipline: `(!neq C 0 ⊗ …)
⊕ (!eq C 0 ⊗ …)`). No rule pattern-matches structure against a parameter.

**Theorem 3 (parametric adequacy — statement; proof obligations open).**
For a well-moded program with certified-functional forced steps:
(sound) every ground trace from S[σ] is the σ-instance of a parametric
trace from S; (complete) every parametric leaf denotes exactly the set of
its reachable groundings. Consequently the leaf denotations partition the
ground world-set: parametric exploration IS symbolic execution, correct by
construction.
*Proof shape.* Per-step lifting: a ground firing either matches without
inspecting σ(Ξ) — the same rule fires parametrically — or inspects a value
at a guard-covered scrutinee, where coverage supplies the alternative whose
tell σ satisfies. (force) steps commute with grounding by Theorem 1. The
converse direction instantiates traces and discards unsatisfiable-guard
prefixes. ∎(sketch)

Two honest remarks. First, well-modedness was, until §6, a hypothesis
rather than a checked property. §6 specifies the **mode system** that
verifies it (parameter-flow analysis + guard-coverage checking against 𝒯)
as a load-time static analysis, and its Theorem 4 states the discharge: an
accepted program is well-moded, so Theorem 3 applies to it. Building that
checker (task #81 / P7) is the reason this document is a program, not just
a post-mortem.
Second, the theorem quantifies over programs of the framework — the
per-language adequacy proofs of the symbolic-execution literature (King
1976 onward; matching logic's per-semantics route) collapse here into one
metatheorem plus a per-program mode check. Combined with kernel-checked
path certificates (which no production symbolic executor offers), that is
the paper-grade claim.

## 6. The mode system: deciding well-modedness

Theorem 3's hypothesis — a *well-moded* program with *certified-functional*
forced steps — is decidable by a load-time static analysis over the compiled
rule set. This section specifies it (the artifact §5 names) and states its
soundness (Theorem 4). It is the metatheory of task #81 / P7; the
implementation is a presence-gated fence beside the datasort/priors/sort
validators (`lib/engine/well-moded.js`), surfaced warn-first
(`calc.wellModedLint`) then as a hard load error once the corpus is
confirmed inside the accepted set. The hypothesis has two independent
halves, checked separately.

### 6.1 Functionality certification (the "certified-functional forced steps" half)

Fix a predicate p with a **mode** m_p partitioning its argument positions
into inputs I(p) and outputs O(p) — declared `@mode p(+,+,-)` or inherited
from the FFI mode table (`parsedModes`; `+`↦in, `−`↦out), the one
vocabulary. p is **functional at m_p** iff every ground input tuple has at
most one 𝒯-witness on O(p) — Theorem 1's side condition, per predicate.
Certification is either:

- **Clausal (the f3-generalisation).** The defining clauses of p are
  **input-disjoint**: the input-position projections of any two clause heads
  are non-unifiable, so no ground input selects two clauses. Datasort fence
  f3 ("one clause per (datasort, head)") is this check at I(p) = the whole
  head; the general form projects heads onto I(p) first. Input-disjointness
  gives ≤ 1 firing clause per ground input; with each clause's body itself
  certified (structural induction over the well-founded recursion argument —
  f3's SCC discipline, `datasort-mass.js` fence f4), ≤ 1 clause ⇒ ≤ 1
  witness. Totality (≥ 1) is *not* required: a partial functional predicate
  simply fails to force and the step defers — sound, precision-only.
- **Axiomatic (the documented carve-out).** The Group-B FFI predicates
  (`string_concat`, `fixed_mul`, `sha3_compute`, …) have no inductive
  clauses by design; each is certified by its spec property (FFI-audit
  §4.1, `compareMode: 'spec'`), not by the lint.

A predicate that is neither is **not certified-functional**. The soundness
lever (§4, G1) is that such a predicate must never be *forced*: the checker
rejects any program in which a **forcing goal** — a persistent goal that
determines an existential slot (`compile.js` Phase G `existentialGoals`) —
names a non-certified predicate. For the corpus this is vacuous: every
∃-chained predicate is FFI-moded and clausally input-disjoint. The rule is a
sound over-approximation of the runtime FORCE/DEFER decision (`existential.js`
`_hasSymbolic`), which turns on runtime groundness the checker does not
track: *any* forcing goal could see ground inputs, so *every* forcing goal's
predicate must certify.

### 6.2 Well-modedness (the parameter-flow half)

Parameters (eigenvariables) are born at ∃-opening and, under (∃-open) with
deferral, ride the state inside produced facts. Well-modedness (§5) bounds
where they may go. The check is an abstract interpretation whose domain is
**parameter-freeness over predicate-argument positions**:

- **Positions.** Pos = {⟨p,i⟩ : p a predicate, 1 ≤ i ≤ arity(p)}, finite.
- **Abstract state.** T ⊆ Pos — the positions that *may* hold a term
  containing a parameter. Ordered by ⊆, ⊥ = ∅.
- **Sources.** For rule r with existential slot c (conservatively, every
  ∃-slot may defer), each consequent-produced fact p(…) with c occurring in
  argument i seeds ⟨p,i⟩ ∈ T (occurrences nested under constructors
  included — an evar beneath `cons` still taints the carrying position).
- **Transfer (produce/consume fixpoint).** For each rule r: consuming
  p(t₁…tₙ) in r's LHS with ⟨p,i⟩ ∈ T marks the metavars of tᵢ as *tainted
  in r*; producing q(u₁…uₘ) with a tainted metavar in uⱼ adds ⟨q,j⟩ to T.
  Iterate to the least fixpoint (finite Pos ⇒ termination).

T over-approximates, across all reachable states, the positions a parameter
can occupy (a post-fixpoint of the concrete flow, by induction on firing
sequences). Well-modedness then reads off two violation conditions:

- **(V1) structural match.** Some rule's *linear* LHS pattern p(t₁…tₙ) has a
  constructor-headed (non-variable) subterm at argument i with ⟨p,i⟩ ∈ T. A
  committed-choice match would decompose a parameter's structure — the exact
  negation of §5's "no rule pattern-matches structure against a parameter",
  and the shape of the b1588c6e capture (an unbound slot matched a stored
  constructor).
- **(V2) uncovered guard.** A tainted metavar is the scrutinee of a ⊕ whose
  guards are not **covering** or not **mutually exclusive** under 𝒯 (§6.3).

Everything else a parameter may do — be carried into another fact (opaque),
be compared for identity in a *deferring* ask (a flat accumulated
constraint, never a match), be an input to a *deferred* (non-ground) goal —
is well-moded. The one place a parameter's value bears on control flow is
the ⊕-scrutinee, and V2 is the guard that it does so only under coverage.

### 6.3 Guard-coverage decision

For a ⊕ whose per-alternative guards (the constraint-predicate tells
`alts[i].persistent`, `compile.js expandConsqChoices`) constrain a tainted
scrutinee, **coverage** is 𝒯-validity of the guard disjunction over the
scrutinee and **exclusion** is pairwise 𝒯-UNSAT — both decided by the
declared constraint theory's procedure. For the declared fragment
`cc.domain.constraintPreds` = {eq, neq} the EqNeqSolver (G2's machinery,
`constraint.js`) is complete: the jumpi split `!neq C 0 ⊕ !eq C 0` covers
(∀C. C ≠ 0 ∨ C = 0) and excludes (C ≠ 0 ∧ C = 0 ⊢ ⊥). A ⊕ whose
scrutinee-deciding guards fall outside the declared fragment is **not**
certified-covering — the same eq/neq boundary G2 stops at, and the reason
task #84 (lt/gt totality) is filed separately.

### 6.4 Soundness of the check

**Theorem 4 (mode-check soundness).** If the checker accepts P — (a) every
forcing goal names a certified-functional predicate (§6.1), (b) no V1, (c)
every tainted ⊕ is certified-covering (V2 absent) — then P is well-moded
with certified-functional forced steps, and Theorem 3 holds of P: parametric
exploration of P is a sound and complete abstraction of ground execution.
*Proof sketch.* (a) is the forced-step premise of Theorem 3 verbatim
(Theorem 1's side condition holds at every force). For well-modedness: T is
a post-fixpoint of the concrete parameter-flow — every firing produces
parameters only into positions its source rule already contributes to T, and
every consumed parameter's onward occurrences are the transfer's image — so
any reachable parametric position lies in T. Given ¬V1, no reachable
committed-choice match inspects a parametric position's structure; given
¬V2, every reachable parametric ⊕-scrutinee is covered and its taken branch
tells a 𝒯-satisfiable guard. These are §5's clauses (i),(ii); Theorem 3's
per-step lifting then applies. ∎(sketch)

**Direction of imprecision.** The analysis is a sound over-approximation: T
may mark a position parametric that no run instantiates so, so the checker
may *reject a well-moded program* (a false positive discharged by an
annotation or a refactor) — never *accept an ill-moded one*. Non-certified
predicates are permanently deferred (precision, never soundness). This is
the G2/deferral direction: rejecting-more and deferring-more both cost
completeness, never correctness, and the corpus — well-moded and functional
(§4) — sits strictly inside the accepted set, which the P2/P4 regression
gate pins.

**Provenance.** The domain is logic programming's freeness/groundness
abstraction (Muthukumar–Hermenegildo; the Pos lattice); what is new is its
target — discharging a *symbolic-execution adequacy* theorem at framework
grain, so that abstract interpretation of the specification language
certifies the engine's correctness as a symbolic executor, once, for every
calculus and every object language it hosts.

## 7. Positioning summary

CLF/LolliMon/SLS give §1's rule; Ceptre implements opening-only; Celf
instantiates by unification (narrowing) where this framework residuates
(Curry's suspend, made eager-when-forced). CLP/CCP supply the ask/tell and
constraint-store reading of parametric states. Twelf/Mercury supply the
uniqueness/determinism technology for (force)'s side condition. Matching
logic reaches symbolic execution model-theoretically per semantics; the
route here is proof-theoretic and framework-generic, with linearity
discharging the frame problem that reachability logics carry axiomatically.
Bruni et al. close the Skolem alternative on soundness grounds, confirming
TODO_0002. To our knowledge, the combination — eigenvariable forward
chaining + forced elimination with uniqueness certification + adequacy over
guard-covering programs — is not in the literature.
