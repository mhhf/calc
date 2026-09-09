---
title: "Parametric Forward Chaining: the Eigenvariable Semantics of Existentials"
created: 2026-09-08
modified: 2026-09-08
summary: "Existentials in forward-rule consequents have exactly one semantics — eigenvariable opening (CLF let-binding) — and eager witness computation is a separate, admissible rule (forced elimination) whose side condition is uniqueness: ground inputs × functional predicate, the forward-fragment transplant of Twelf's uniqueness modes. States denote their satisfiable groundings; the b1588c6e collapse is the violation class 'witness capture' (eliminating an unforced parameter from one conjunct's isolated instance), which fabricates leaves outside the denotation while dropping leaves inside it. The framework-level prize is parametric adequacy: for well-moded, guard-covering programs, parametric exploration is a sound and complete abstraction of ground execution — symbolic-execution correctness proved once at the logic level, not per language. The theory exposes two unmanifested engine gaps no test on the current corpus can reach: uniqueness is unchecked at the lookup/clause tiers (G1) and tell-consistency of ground theory-atoms is unchecked (G2)."
tags: [linear-logic, forward-chaining, proof-theory, symbolic-execution, existential, modes, clf, engine-theory]
category: "Proof Theory"
paper: "Open disposition. Candidate homes: a standalone certified-symbolic-execution paper (theorem 3 as the spine, the EVM engine as evaluation, kernel-checkable path certificates as the differentiator vs hevm/KEVM), or the toolbox paper §7 boundary-theorem family (forced elimination as another certified fast path). The mode system that discharges Theorem 3's hypothesis is the open research artifact and would anchor the standalone paper."
unique_contribution: "Four results not in the literature or prior CALC docs: (1) forced elimination as an admissible rule over the CLF eigenvariable semantics — eliminating a parameter by substitution preserves the state's denotation iff the parameter's constraint set has a unique theory-witness (groundness × functionality; Twelf-style uniqueness modes moved to the forward fragment), making every engine fast path an implementation of one rule with one checkable side condition; (2) the violation class WITNESS CAPTURE — instantiating an unforced parameter from one conjunct's isolated instance — with the precise damage statement: fabricated leaves outside the denotation plus dropped leaves inside it (simultaneous soundness and completeness failure), of which the b1588c6e collapse is an instance; (3) a parametric-adequacy statement for CLF-style committed-choice forward chaining: under well-modedness (parameters flow only into opaque positions or guard-covering ⊕-branches), the parametric LTS is a sound+complete abstraction of the ground LTS — symbolic-execution correctness at framework grain; (4) two engine obligations the theory exposes that testing on functional-only corpora cannot: per-predicate uniqueness certification for the lookup/clause tiers (G1) and tell-consistency checking for ground theory-atoms (G2)."
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

Two honest remarks. First, well-modedness is a hypothesis, not yet a
checked property: the **mode system** that verifies it (parameter-flow
analysis + guard-coverage checking against 𝒯) is the open research
artifact, and the reason this document is a program, not just a post-mortem.
Second, the theorem quantifies over programs of the framework — the
per-language adequacy proofs of the symbolic-execution literature (King
1976 onward; matching logic's per-semantics route) collapse here into one
metatheorem plus a per-program mode check. Combined with kernel-checked
path certificates (which no production symbolic executor offers), that is
the paper-grade claim.

## 6. Positioning summary

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
