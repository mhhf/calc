---
title: "Graded μMALL and the Unification of CALC's Calculi"
created: 2026-09-11
modified: 2026-09-11
summary: "A factorization of CALC's calculi (ill/till/gill/will/sill/fill/rill/grill/sax) as points in a THREE-AXIS parameter space — a mode preorder (structural), a resource semiring (grades), and μ/ν fixpoints — and the corresponding target of unification: a single graded μMALL over the existing mode layer, of which each calculus is an instance/specification. The keystone that the axes actually COMPOSE is grade × fixpoint: the fill exponential-as-fixpoint νX.(A&(1&(X⊗X))) is the free commutative comonoid computed coinductively, and the graded exponential !_ω is the same object with ω a grade fixpoint (ω = 1 ⊕ ω⊗ω). This is now machine-checked in the grill calculus: graded coinductive signals, graded inductive streams, and grade arithmetic under fixpoints all prove and kernel-verify, with the cyclic-proof GTC unchanged. Adjoint logic is analyzed as the tool for the SEPARATE cut-elimination-for-free metatheorem, not a prerequisite for the combination; a roadmap sequences the remaining bricks."
tags: [unification, graded-modality, muMALL, fixed-points, adjoint-logic, coinduction, cyclic-proofs, linear-logic, proof-theory, roadmap, metatheory]
category: "Proof theory"
unique_contribution: "The explicit three-axis factorization (mode preorder × resource semiring × μ/ν) of CALC's whole family of calculi as INSTANCES of one graded μMALL, together with the machine-checked demonstration (the grill calculus) that the grade and fixpoint axes COMPOSE soundly — graded coinductive signals νX.(A & !!_d X) and graded inductive streams μX.(A ⊕ !!_d X) prove and kernel-verify through the UNCHANGED cyclic-proof GTC — and the identification of the unbounded exponential as a grade fixpoint (ω = μw.(1 ⊕ w⊗w)) presented coinductively by fill's ν-encoding, which the same calculus checks against the exponential's laws. Distinct from adjoint logic (which addresses only the mode axis and is orthogonal to fixpoints, per Baelde–Miller) and from graded modal type theory (which lacks fixpoints): the contribution is that CALC already holds each axis AS DATA, so the unification is a composition of existing mechanisms rather than a new logic, and the first composition brick is discharged."
references:
  - "THY_0042 (fill: μ/ν + cyclic proofs + the exponential-as-fixpoint correction); THY_0043 (rill: the ○ next-time modality)"
  - "TODO_0064 (the four-axis expressiveness roadmap this refines); TODO_0284 (gill: grade algebras as data); TODO_0009/0203 (fixpoints)"
  - "Melliès–Tabareau–Tasson, ICALP 2009 (the free exponential = free commutative comonoid)"
  - "Baelde, TOCL 2012 + Baelde–Miller, LPAR 2007 (fixpoints strictly subsume exponentials — the separation making μMALL the most fundamental axis)"
  - "Gaboardi–Katsumata–Orchard–Breuvart–Uustalu, ICFP 2016 (graded (co)monads — structural rules as semiring operations)"
  - "Licata–Shulman–Riley, FSCD 2017; Pruiksma–Pfenning (adjoint logic — the mode axis); TODO_0012/0013 (MTDC / Belnap cut-for-free)"
---

# Graded μMALL and the Unification of CALC's Calculi

## 1. The claim

CALC's calculi are not a heap of separate logics; they are **points in one parameter
space**. The target of unification is a single **graded μMALL over the existing mode
layer**, of which `ill`, `till`, `gill`, `will`, `sill`, `fill`, `rill`, `grill`,
`sax` are **instances / specifications**. The space has three orthogonal axes, and
CALC already represents each **as data**:

| Axis | Governs | Parametrized by | Where it lives now |
|---|---|---|---|
| **Structural / mode** | which structural rules hold, per zone | a **mode preorder** | `family/` (lnl, sax); `contextStructure` from `@position_modes` + `@structural` |
| **Grade / quantitative** | usage / cost / time annotation | a **resource semiring** | gill (grade algebras as data); `!_g`, `{B}@d`, `!!_d` |
| **Fixpoint / recursion** | inductive & coinductive structure | **μ/ν** + a trace condition | fill/rill; `@category fixpoint` → GTC |

A calculus is a tuple `(mode preorder, grade semiring, fixpoint discipline,
connective signature)`. The generic engine (`lib/`, cc-port, role-gating, the
parametric `⊢_fwd` of THY_0035, the mode system of THY_0039, the kernel) is already
the "one engine, calculi as specs" substrate for the *operational/soundness* layer;
what remains is to unify the *logical* layer.

## 2. Why the axes are orthogonal (and why adjoint logic is not the whole story)

The unification is **wide, not tall** — a product, not a subsumption tower. The
established facts (TODO_0064's lattice):

- `muMALL ⊃ exponentials` (Baelde–Miller separation) — fixpoints subsume `!`, so the
  **fixpoint axis is the most fundamental**; grading is an orthogonal refinement.
- `muMALL ⊥ MTDC` (modes ≠ fixed points) — **adjoint logic does not subsume
  fixpoints**. It addresses only the mode axis (`bang = ↓↑`, `monad = ↑↓`, `○` a
  K-box), and provably not the others.

So "adjoint logic unifies everything" is false. What adjoint logic / MTDC uniquely
buys is a **metatheorem** — cut-elimination *for free per instance* (Belnap;
TODO_0012), replacing the hand-proved three-cut induction each calculus pays. That
is valuable but **separate from and orthogonal to combining grades and fixpoints**,
and it is a large surgery (THY_0032's seven-site map). Conclusion: **adjoint logic
is overkill for the near-term unification and is deferred**; the mode axis is already
present as the family layer.

## 3. The keystone: grade × fixpoint compose (machine-checked in grill)

The one non-obvious question is whether the grade and fixpoint axes actually
compose. They do. The bridge is a classical fact plus a fixpoint:

- **`!A` is the free commutative comonoid on `A`** (Melliès–Tabareau–Tasson); its
  structural rules *are* comonoid structure (weakening = discard, contraction =
  duplicate).
- **fill constructs that comonoid coinductively:** `!A = νX.(A & (1 & (X ⊗ X)))` —
  `A` = dereliction, `1` = weakening, `X ⊗ X` = contraction, `ν` = unbounded
  multiplicity. It is the free commutative comonoid as a final coalgebra.
- **The graded route tracks multiplicity with a semiring `R`** (`!_w`); the semiring
  operations are the structural rules (`0`=weaken, `1`=derelict, `+`=contract,
  `·`=dig). The full `!` is `!_ω`, and **`ω` is a grade fixpoint**: `ω = 1 ⊕ ω⊗ω`.
  fill's ν-encoding is precisely `!_ω` taken in the *types* instead of the semiring.
  The two agree exactly when `R` is fixpoint-complete (contains `ω`, like QTT's
  `{0,1,ω}`); when it is not, the type-level μ/ν route constructs it.

**`grill` (this work) is the calculus where both axes coexist** — `@extends gill`
(the graded surface) plus fill's μ/ν, with `deriveRoles` arming `lfp`/`gfp` beside
the grade roles and **no engine change**. Machine-checked, kernel- and GTC-verified:

- a **graded coinductive signal** `!a ⊢ νX.(a & !!_d X)` (a signal whose tail is
  reachable at cost `d` each tick);
- a **graded inductive stream** `a ⊢ μX.(a ⊕ !!_d X)`;
- **grade arithmetic under a fixpoint** (`!!_2 ⊢ !!_5` cost subsumption inside the
  composed calculus);
- the **cyclic-proof GTC is unchanged** — grades ride inside the fixpoint body,
  `νR`-on-`ν` remains the trace progress, and context conservation compares the
  graded pool modulo theory;
- the ν-encoding **validates the exponential's laws** (`enc ⊢ a` dereliction,
  `enc ⊢ a⊗a` contraction, `!a ⊢ enc`), confirming grades and the fixpoint-`!`
  are the same object. (The reverse `enc ⊢` *primitive*-`!` meets the pre-existing
  promotion-from-linear focus corner and is left open — a prover-completeness gap,
  not a soundness one.)

Soundness is pinned: the composition manufactures no false proof (unprovables
refused; a battery invariant asserts every `grill` success is kernel-valid).

One integration finding worth recording: the cheap single-connective fork pattern
(rill) does **not** compose trivially over a base that carries a *theory engine* —
the sequent-rules parser auto-derives μ/ν as de-Bruijn prefixes from `@category
fixpoint`, so an explicit `binders` map (which the forward parser wants) breaks the
rules' `mu A`. Composing axes touches the loader/theory plumbing, not just
declarations.

## 4. Roadmap

The unification is closer than the branch structure suggests: **two-and-a-half axes
are already in place** — grades (gill), fixpoints (fill/rill), modes (family layer,
un-adjoint-ified). The sequenced remaining bricks, cheapest first:

1. **grill (done):** the first grade×fixpoint calculus; the composition is sound and
   machine-checked (§3).
2. **Deepen the grade↔fixpoint bridge:** discharge more of `!_ω ≅ νX.(A&(1&(X⊗X)))`
   (the encoding⊢primitive-! direction needs the promotion focus corner recovered —
   the same class as THY_0042 §4's exhaustive fix); state it as a theorem.
3. **Graded ○ / temporal:** fold rill's ○ into the graded frame (`○ = a temporally
   graded box`, no dereliction at tick > 0) and add ○-elimination (temporal cut) —
   the FRP consumption side (TODO_0203).
4. **The metatheorem (the adjoint/MTDC prize, deferred):** a single parametric
   cut-elimination over `(modes × semiring × fixpoints)` via a display calculus
   (TODO_0012/0013), turning "calculi as specs" from an operational fact into a
   proof-theoretic one. This is where adjoint logic finally earns its cost — and it
   is better-scoped once the axes are already combined.

The end state: one declarative surface `(mode preorder × resource semiring × μ/ν ×
connectives)` and one adequacy theorem, with today's calculi as rows in a table —
each paying, by role-gating, only for the axes it declares (the firewall discipline
that keeps ILL's EVM path free of every feature it does not use).
