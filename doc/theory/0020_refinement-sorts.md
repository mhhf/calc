---
title: "Refinement Sorts over a Content-Addressed Store"
created: 2026-08-20
modified: 2026-08-20
summary: "Rung 1 of CALC's sort ladder (TODO_0011): subsorts, classifiers and bounded sort variables as EXTRINSIC (Curry-style) refinements over the closed-world checker. Membership is a provable judgment — subsort declarations are persistent facts, the compiled DAG is an index, and the backward prover certifies path certificates (table decides, proof certifies). Classifier-quantified rules are predicative schemas over declared finite classes, expanded at load and erased at runtime (proof irrelevance). Bounded sort variables give Haskell-class-style instance selection by least-upper-bound solving, with strictness as instance absence."
tags: [sorts, refinement-types, subsorting, order-sorted-algebra, membership, type-checking, till, classifiers]
category: "Type Theory"
unique_contribution: "Three design results: (1) content addressing FORCES extrinsic sorts — intrinsic (Church-style) sorts would rehash the world on every new membership declaration and break subsumption (5:bin ≠ 5:q), so refinement (not annotation) is the only sort discipline compatible with a hash-consed term store; (2) the FFI principle lifted one level — 'the sort table is optimization, membership proof is semantics' — realized as certificate checking: a committed-choice (first-solution) backchainer cannot complete the naive transitive closure query, but it CAN verify the reflexive base and every edge hop of a path the compiled index produces, giving prover-backed positives without tabling; (3) strictness-as-instance-absence for bounded sort variables: whether mixed-sort goals are legal is not a checker mode but a fact about which clause instances exist, read off clause-head classification."
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
sedge: (a: sort) -> (b: sort) -> type.
leq:   (a: sort) -> (b: sort) -> type.
leq/refl: leq S S.
leq/step: leq S U <- sedge S T <- leq T U.
```

The compiled ancestor-set index the checker consults is an INDEX over exactly
these clauses — the FFI principle one level up: the table is optimization,
membership proof is semantics.

**The certificate turn.** CALC's backchainer is committed-choice per subgoal:
it backtracks over clause alternatives of the current goal but commits to the
first solution of each premise (the mode discipline the numeric clause corpus
is written for). Under first-solution commitment the naive query `leq a b` is
complete only for paths the first `sedge a T` candidate happens to start —
transitive closure over a multi-out-edge node needs either full backtracking
or tabling, and the engine deliberately has neither. The resolution is not to
weaken the claim but to change WHO searches: the index (a decision procedure)
finds the path `a <: s₁ <: … <: b`; the prover CERTIFIES it — the reflexive
base and every hop are proved against the clauses. Positives are therefore
backed end-to-end by proof search over logic files; the negative side is the
index's completeness, cross-checked by independent reachability enumeration
in the fuzz suite (tests/sorts-fuzz.test.js: table ≡ certified proof ≡
reachability on random DAGs).

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
BigInt fuzz harness compares per instance), not at load. The recorded
collapse verdict for the numeric namespace: plus/mul/lt/le/eq may share names
cleanly; sub only after choosing one overlap semantics (bin sub is saturating
monus, qsub is checked); div/qdiv never (Euclidean vs field). The RUNTIME
name collapse is the separable dispatch rider of TODO_0011 §3 and has not
landed — the prelude keeps split q-names with honest q sorts.

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
