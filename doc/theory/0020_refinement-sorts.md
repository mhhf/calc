---
title: "Refinement Sorts over a Content-Addressed Store"
created: 2026-08-20
modified: 2026-08-20
summary: "Rung 1 of CALC's sort ladder (TODO_0011): subsorts, classifiers and bounded sort variables as EXTRINSIC (Curry-style) refinements over the closed-world checker. Membership is a provable judgment — subsort declarations are persistent facts, the loader MATERIALIZES their reflexive-transitive closure as ground `subsort` facts (the one-time deduction), and the compiled DAG is the same closure as an index. In-logic subsort queries are total fact lookups. Classifier-quantified rules are predicative schemas over declared finite classes, expanded at load and erased at runtime (proof irrelevance). Bounded sort variables give Haskell-class-style instance selection by least-upper-bound solving, with strictness as instance absence."
tags: [sorts, refinement-types, subsorting, order-sorted-algebra, membership, type-checking, till, classifiers]
category: "Type Theory"
unique_contribution: "Three design results: (1) content addressing FORCES extrinsic sorts — intrinsic (Church-style) sorts would rehash the world on every new membership declaration and break subsumption (5:bin ≠ 5:q), so refinement (not annotation) is the only sort discipline compatible with a hash-consed term store; (2) the FFI principle lifted one level — 'the sort table is optimization, membership proof is semantics' — realized as CLOSURE MATERIALIZATION: a committed-choice (first-solution) backchainer cannot complete a recursive transitive-closure query, so the loader performs the deduction once at load and injects the closure as ground facts, making in-logic subsort queries total without tabling or backtracking; (3) strictness-as-instance-absence for bounded sort variables: whether mixed-sort goals are legal is not a checker mode but a fact about which clause instances exist, read off clause-head classification."
references:
  - "Lovas & Pfenning (2009). Refinement Types as Proof Irrelevance. TLCA — the extrinsic anchor."
  - "Goguen & Meseguer (1992). Order-Sorted Algebra I. TCS — subsort DAGs, preregularity."
  - "Meseguer (1997). Membership Equational Logic — membership as provable judgment; rung 1 is its decidable fragment."
  - "Martens (2015). Ceptre — linear logic programming without Π; the sortless baseline."
  - "TODO_0011 — the sort ladder (rung 1 signed off 2026-08-20); TODO_0265 Phase 6 — the closed-world checker this refines."
  - "doc/documentation/term-resource-proposition.md — membership is KNOWLEDGE (a !-proposition), per the Term/Resource/Proposition principle."
---

# Refinement Sorts over a Content-Addressed Store

Rung 1 of the TODO_0011 ladder. The Phase-6 closed-world checker (TODO_0265)
verifies arity and string-equal sorts; this extension gives it a vocabulary —
subsorts, classifiers, bounded sort variables — without changing the kernel,
the store, or the runtime engine. TILL-EXCLUSIVE by residence: the machinery is
a till prelude any calculus may import; ILL stays sortless. Available to every
logic, imposed on none.

## 1. Why extrinsic (the content-addressing argument)

CALC terms are hashes: one value, one node, `5` is THE five. An intrinsic
(Church-style) discipline — sort baked into the term, `Store.put("5:bin")` —
fails twice:

1. **Subsumption dies.** With sort-in-hash, `5:bin ≠ 5:q`, so every use of a
   natural at a rational position needs an explicit coercion node — and under
   content addressing `emb(5) ≠ 5` re-opens the cross-representation matching
   problem the equational theories exist to solve, one level up.
2. **Declarations would rehash the world.** Memberships are many and open:
   a new declaration classifying `5` would change 5's hash and invalidate
   every stored fact about it.

So sorts are EXTRINSIC refinements (Curry-style; Lovas–Pfenning): a term may
inhabit many sorts, membership is a judgment, and checking is erased after
load (proof irrelevance — the engine never sees a sort). Intrinsic typing
still exists where it belongs: at constructor granularity, in the tag.
Doctrine: entirely different domains → different constructors (intrinsic);
refinement and classification → membership (extrinsic).

## 2. The judgments

Three judgments, kept distinct (conflating them makes every pair of sorts
comparable through the meta-sort):

| judgment | meaning | decision |
|---|---|---|
| `s ≤ t` | subsort order | reachability in the declared edge DAG, reflexive-transitive; plus classifier ≤ `type` |
| `n : sort` | sort-hood of a name | definitional — the name is used as a sort |
| `M : s` | term membership | least sort of M (syntax-directed) then ≤ |

Least sorts are functions by construction: the loader rejects duplicate
declarations, so every constructor has exactly one declared sort
(preregularity holds trivially at rung 1 — the Maude least-sort table exists
without a check). Literals classify via the calculus config (binlit → bin,
ratlit → q), which is the static face of the same eq-theory bridge that makes
`binlit 5` and `i (o (i e))` one value.

## 3. Declarations are facts; the table is an index

`bin <: q.` desugars to a persistent unit clause `sedge bin q` over machinery
predicates declared in an ordinary logic file (the sorts prelude):

```
sort: type.
sedge:   (a: sort) -> (b: sort) -> type.
subsort: (a: sort) -> (b: sort) -> type.
subsort/refl: subsort S S.
```

The compiled ancestor-set index the checker consults is the
reflexive-transitive closure of the sedge facts — the FFI principle one level
up: the table is optimization, membership proof is semantics.

**The materialized closure.** CALC's backchainer is committed-choice per
subgoal: it backtracks over clause alternatives of the current goal but
commits to the first solution of each premise (the mode discipline the
numeric clause corpus is written for). Under first-solution commitment a
recursive closure clause (`subsort S U <- sedge S T <- subsort T U`) answers
only for paths the first `sedge S T` candidate happens to start — transitive
closure over a multi-out-edge node needs either full backtracking or tabling,
and the engine deliberately has neither. The resolution is not to weaken the
claim, nor to bolt a certificate checker beside the prover, but to move the
deduction to WHERE it terminates: the loader computes the closure ONCE at
load (a finite fixpoint over a small DAG) and injects every strict pair as
an ordinary ground fact `subsort a b`. The facts are the theorems of that
one-time deduction; `subsort/refl` supplies the reflexive base. In-logic
premises like `!subsort X resource` are then answered totally by fact lookup
— enumeration of unbound queries comes for free, and the committed-choice
caveat is GONE, not worked around. Correctness is cross-checked three ways
in the fuzz suite (tests/sorts-fuzz.test.js: compiled table ≡ live
backward-prover query ≡ independent reachability on random DAGs, including
the multi-out-edge shape a recursive clause used to lose).

## 4. Classifiers: predicative quantification over declared classes

`resource: sort.` declares a classifier — a refinement of the proposition
sort. `wood: resource.` is then a membership fact, and wood remains an
ordinary atomic proposition (`resource ≤ type`; term sorts like `bin` do NOT
refine `type` — a numeral is not a resource). This is the disciplined form of
the rejected `kind: (x: type) -> …` leak: one may not quantify over ALL
propositions (impredicative, and the checker still bans argument sort
`type`), but one may quantify over a declared, finite CLASS:

```
spoil: (r: resource) r@Q * after (Q + 20) -o { I }.
```

expands at load into one ground rule per member — compile-time schema
expansion, in the same elaboration slot as `$`-desugaring. Decidability is
the closed world: the class is a finite declared set. Zero runtime cost:
expanded rules are ordinary content-addressed rules; the classifier is erased.
(Empty classes, non-classifier quantification, and binder shadowing are load
errors — a schema must never silently expand to nothing.)

## 5. Bounded sort variables and instances

`sub: (s <: q) (a: s) -> (b: s) -> (r: s) -> type.` binds one sort variable
shared by all annotated positions. At each application the checker solves
`s := lub(least sorts of determinable arguments)` over the closed DAG and
requires an INSTANCE at s — where the instance set is read off clause-head
classification: a head patterning on `rat(_,_)` is a frac instance, a head of
bare variables an instance at the bound. Consequences:

- `sub a b D` with naturals solves s = bin; the result metavar D is checked
  at bin, not at the bound — goal sorts refine downstream.
- `sub a c D` mixing bin and frac solves s = q; with instances {bin, frac}
  there is no instance at q — a load error naming the candidates and the
  remedy (coerce explicitly, or declare an instance at q).
- **Strictness is instance absence, not a checker mode:** declaring a
  bound-level clause (a head of bare variables with internal coercions)
  makes mixed goals legal; deleting it makes them errors. What is legal is a
  fact about the program, read from the program.

The coherence OBLIGATION — same-name instances must agree on sort overlaps —
is undecidable in general and is enforced instrumentally (the FFI ∥ clause ∥
BigInt fuzz harness compares per instance), not at load. The collapse verdict
for the numeric namespace, now LANDED (the §3 dispatch rider):
plus/mul/lt/le/eq/neq/eq_bool share one name each across the tower — bin.ill's
clauses are the bin instance (its concrete signature becomes a DECLARED
instance of the bounded-var principal via loader promotion), rat.ill's /q
clauses the coercion instances, and the FFI face dispatches the same way
(bin fast path, rational fallback, advisory-failure composition). sub and
div never collapse: bin sub is saturating monus and bin div Euclidean, while
qsub is checked and qdiv field division — they disagree on the shared
subsort, so coherence forbids the shared name (the Integral/Fractional cut).

**Instance clauses must be head-constrained (a committed-choice theorem).**
Under first-solution commitment, a bound-level instance clause with a BARE
head (`plus U V R <- to_q U … <- plus X Y N <- …`) is order-fragile: if
candidate enumeration offers it before the bin clauses on a pure-bin goal,
its recursive premise regresses to the same goal (denominators 1) and
resolution diverges — observed as a live hang, not a hypothetical. The
resolution is structural, not ordering: instance clauses pattern their heads
on their sort's own constructors (`plus (rat A B) V R` / `plus U (rat C D) R`),
so goals outside the instance can never enter them, and termination is
order-independent. The instance AT THE BOUND — what makes mixed-sort goals
legal for the checker — is then a declared instance SIGNATURE, not a bare
clause: legality is signature-level knowledge, operational coverage is
head-constrained clauses, and the two never conflict.

## 6. Value fences: the decidable shadow of conditional membership

Grade sorts (`delay`, `count`, `weight <: grade` in till.calc, joined to the
numeric tower by `… <: q` in the prelude) refine positions whose membership
is value-dependent: a rational literal is a delay iff nonnegative, a count
iff integral, a weight iff in [0,1]. Full conditional memberships are MEL
proper (rung 2, undecidable at load in general); rung 1 keeps exactly the
decidable shadow: for GROUND LITERALS, membership in a refinement sort is
decided by a per-sort value fence in the calculus config. Non-literal terms
still go through least-sort + ≤. The former hardcoded grade grammar in the
checker survives only as the sortless fallback.

## 7. Metatheory

**Decidability.** Everything is finite: ≤ is DAG reachability; lub is
intersection of ancestor sets plus minimality (unique-minimal required,
else a reported failure); metavar constraint sets are satisfiable iff some
sort lies below all bounds (finite enumeration); classifier expansion is
finite by the closed world. No unification in types, no binders in sorts.

**Conservativity.** Presence-gated twice: a calculus without a sorts config,
or a program without sort declarations, takes the sortless path — string
equality, bit-identical to the pre-rung-1 checker (the ILL suite is the
regression witness). Sorted mode also closes a historical blind spot:
premise-less facts (loader pass 1) are now checked; sortless mode retains
the blind spot deliberately.

**Soundness (subject reduction, sketch).** Well-sorted rules preserve
well-sortedness of states: a rule's consequent is checked under the same
metavar constraint sets as its antecedent, so any instantiation that matches
a well-sorted state instantiates metavars at sorts below their bounds, and
produced facts are well-sorted by substitution. Eq-theory canonicalization
preserves membership because literal classification and constructor sorts
agree across representations (binlit ↔ i/o/e at bin; ratlit ↔ rat(N,D) at
≤ q). Erasure is trivial: no runtime component reads a sort.

## 8. Position in the design space

The 2D map (TODO_0011): a MEMBERSHIP axis (string sorts → subsorts/
classifiers → provable membership / MEL) and a DEPENDENCY axis (simple →
indexed families → Π). Rung 1 moves only on the first. Π does not subsume
it — dependent type theories have no subtyping, so `bin <: q` becomes
explicit coercions at every site (§1's argument again), which is precisely
why Lovas–Pfenning refinements exist beside Twelf's Π. Rung 2 (GADT-style
indexed families: `building: level -> sort`) moves on the second axis,
breaks load-time enumeration (infinite families ⇒ symbolic checking), and
waits for its first genuinely unbounded customer.
