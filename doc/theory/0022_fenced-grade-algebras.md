---
title: "Fenced Grade Algebras: Graded Residuation for Consumable Grades"
created: 2026-08-21
modified: 2026-08-21
summary: "till's grades (delay on {A}@d, count on !_k A, weight on A +[q] B) each live inside a valid range — the FENCE (delay ≥ 0, count ∈ ℕ, weight ∈ [0,1]). This document makes the fence an algebraic property instead of a per-rule obligation: a fenced grade algebra (G, ⊕, 0, ≤, V, ⊖) is an ordered commutative monoid with a validity predicate and a PARTIAL residual a ⊖ b (the h with b ⊕ h = a, defined only when a valid one exists — undefined ⇒ the rule is simply inapplicable). Validity is closed under the exposed operations, so Grade Preservation — every grade in every reachable state is valid — holds by construction for all rules, including future ones; the old per-rule guards (F >= E, K >= 1) are derived lemmas, now deleted from till.rules. The residual's in-logic reading is backward `plus H E F` over the sorted domain: no clause constructs a negative residual, so the fence is derivational. Residuation is identified as the exact price of INTERNALIZING time as grades: the labeled/absolute pole (IMTL, timed MSR) is accumulation-only but pays with 2D judgments, constraint stores, and proof-splitting; the graded/relative pole pays with one partial operation."
tags: [linear-logic, graded-types, lax-monad, till, proof-theory, residuated-monoids, refinement-sorts, timed-rewriting, soundness]
category: "Timed Rewriting"
unique_contribution: "Three claims, checked against the literature (novelty sweep 2026-08-21, incl. a direct read of IMTL PPDP'23): (1) OPERATIONALLY PARTIAL grade subtraction — a residual whose undefinedness means dynamic rule inapplicability during proof search. No published graded modal system has this: BLL splits !^(n+m) but never peels by computing n−1; Granule/QTT/GrMDTT are semiring-only, and Granule's grade subtraction exists only inside its static SMT constraint solving (failure = type error, never rule inapplicability). (2) The labeled↔graded design axis for metric time, with residuation as the exact price of label-freedom: IMTL (de Sá–Toninho–Pfenning PPDP'23) is the labeled pole — absolute intervals, additive-only rules, constraint store, a proof-branching split rule — and has NO residuated rule; till is the graded pole — label-free judgments, one partial ⊖. (3) The adequacy bridge STATEMENT between an absolute-stamp forward scheduler (accumulation-only, timed-MSR-shaped) and a relative-grade backward calculus (residuated): timed MSR has no backward calculus, IMTL has no operational semantics, CLF has no grades — the bridge generalizes CLF adequacy to the quantitative temporal setting."
references:
  - "TODO_0273 — grade-fence soundness (the research record this document distills; round-2 code probes)"
  - "THY_0018 — The Delay-Graded Lax Monad (monad_l/monad_r; the adequacy bridge lands there)"
  - "THY_0020 — Refinement Sorts (rung 1; the fences are rung-2 value membership)"
  - "THY_0021 — Weighted Additive Disjunction (the weight instance; closed under ·, needs no ⊖)"
  - "de Sá, Toninho & Pfenning (2023). Intuitionistic Metric Temporal Logic. PPDP (the labeled pole; read directly — no residuated rule)"
  - "Kanovich, Kirigin, Nigam, Scedrov & Talcott (2016). Timed Multiset Rewriting. FORMATS (F@t facts, Time@T → Time@(T+1) tick — accumulation-only forward)"
  - "Girard, Scedrov & Scott (1992). Bounded Linear Logic. TCS (!^n splits by addition, never peels by subtraction)"
  - "Orchard, Liepelt & Eades (2019). Quantitative Program Reasoning with Graded Modal Types. ICFP (semiring grades; subtraction only as SMT artifact)"
  - "Atkey (2018). Syntax and Semantics of Quantitative Type Theory. LICS (semiring-only grades)"
  - "Jung et al. (2018). Iris from the Ground Up. JFP (resource-algebra validity V; frame-preserving update)"
  - "Galatos, Jipsen, Kowalski & Ono (2007). Residuated Lattices. Elsevier (the residual)"
  - "Amer (1984). Equationally complete classes of commutative monoids with monus (the clamping sibling ∸, not adopted)"
  - "Lovas & Pfenning (2010). Refinement Types for Logical Frameworks. LMCS (rung-1 ancestry; propositional sorts only)"
  - "Hermenegildo et al. — Ciao assertions (properties-as-predicates; static-what-you-can, run-the-predicate otherwise = our option-C shape)"
  - "Flanagan (2006). Hybrid Type Checking. POPL (static/dynamic fence split is completeness, never soundness)"
  - "Watkins, Cervesato, Pfenning & Walker (2002). A Concurrent Logical Framework I. CMU-CS-02-101 (the ungraded adequacy this generalizes)"
---

# Fenced Grade Algebras

**Status.** Definition + on-paper proofs; the algebra and its consequences ARE
implemented and fuzzed (`calculus/till/calculus-config.js` residual,
`lib/prover/rule-interpreter.js` partial defs, `lib/engine/timed/timed.js`
fire-time fence, `tools/fuzz-till.js` residual legs). The adequacy bridge (§6)
is a statement, not yet a proof — same honesty boundary as THY_0018 §8.

## 1. The object

A **fenced grade algebra** is `(G, ⊕, 0, ≤, V, ⊖)`:

- `(G, ⊕, 0)` a commutative monoid, `≤` a partial order (⊕ monotone);
- `V ⊆ G` the **fence** (validity predicate), with `0 ∈ V` and V closed
  under ⊕;
- `⊖` the **partial residual**: `a ⊖ b` = the `h ∈ V` with `b ⊕ h = a`,
  **undefined** when no such h exists.

This is the graded analogue of an Iris resource algebra (V = validity) and a
residuated commutative monoid restricted to its valid cone. till's instances:

| grade  | carrier | ⊕ | fence V            | ⊖ |
|--------|---------|---|--------------------|---|
| delay  | ℚ       | + | v ≥ 0              | a−b when a ≥ b, else undefined |
| count  | ℚ       | + | v ∈ ℕ              | a−b when a ≥ b (ℕ-closed), else undefined |
| weight | ℚ       | · | 0 ≤ v ≤ 1          | none — [0,1] is closed under ·, no rule subtracts weight |

That weight needs no ⊖ is a theorem of its signature, not an omission: the only
weight operations are multiplication and complement 1−w, both [0,1]-closed
(THY_0021).

## 2. Grade Preservation

**Theorem (Grade Preservation).** If every grade literal in a loaded program
satisfies its fence, and every rule constructs grades only through ⊕ and ⊖,
then every grade in every reachable state — forward execution and backward
search alike — satisfies its fence.

*Proof.* Induction over rule firings / rule applications. Base: literals are
fence-checked at load (`lib/engine/type-check.js`). Step: a constructed grade
is either `a ⊕ b` (V closed under ⊕) or `a ⊖ b` (in V by definition when
defined; when undefined the rule did not fire, so no grade was constructed).
Each firing is thus a frame-preserving update for V. ∎

The force of the theorem is quantification over **future** rules: it holds for
any rule an author writes, because the algebra exposes no operation that can
leave V. Per-rule guards (`F >= E` on `monad_l`, `K >= 1` on the
`!` peels) are derived lemmas — they were deleted from `till.rules` when
`effect.sub` (total, signed) was replaced by `effect.residual` (partial).
Partiality IS the guard.

## 3. Where each case discharges (implementation map)

- **Backward** (TODO_0273 theory premises): a rule states `<- !qsub F E H` —
  a goal over the numeric theory, discharged by the engine backchainer at
  premise-computation time (FFI face as O(1) fast path). Underivable (F < E,
  qsub is checked) ⇒ premise computation returns null ⇒ rule inapplicable.
  `{A}@4` from `{{A}@2}@3` stays refuted with no side condition.
- **Forward** (`convert.js:desugarTimed`): grade expressions lower onto the
  in-logic sorted predicates (`after (Q+D)` ⇒ persistent goal `!plus Q D Q$0`);
  `plus` over bin/ℕ cannot produce a negative or fractional value, `qsub` is
  checked (fails on negative), state stamps are `activation ⊕ delay`. The
  scheduler adds a fire-time value fence (delay ≥ 0) as defense-in-depth next
  to the tag-only `isStamp` check.
- **Static layer** (optional, unbuilt): fences are QF_LRA/QF_LIA — decidable —
  so load-time discharge of symbolic linear grade computations is possible
  (Liquid/DML recipe). It is an accelerator, never the semantics: ground fence
  checking is evaluation, always available (Flanagan's split is completeness,
  not soundness), and nonlinear data-dependent grades (`base / level`) are
  dynamic-only by mathematics — the existential theory of ℚ is open.

## 4. The residual is backward plus (the in-logic reading)

`a ⊖ b` is definitionally "the H with `b + H = a`" — a **derivability**
statement: `plus H b a` over the sorted domain. Over bin naturals no clause
constructs a negative H, so the fence is *derivational*: inapplicability =
non-derivability. This grounds the algebra in the FFI principle (theory is
semantics, everything faster is an optimization) as a three-face agreement,
fuzzed in `tools/fuzz-till.js`:

1. **clause face** (semantics): SLD over `plus`/`qsub` clauses — sound in every
   mode; *search-incomplete* in solve-for-addend mode (the carry clause
   `plus/s4` orders `plus M N Q` before `inc Q R`, leaving two free variables
   in the recursive subgoal — divergence to the depth bound is possible);
2. **FFI face** (decision procedure): first-argument-free mode `plus H b a` is
   complete — success ⟺ a ≥ b, H = a − b, refuses negatives;
3. **algebra face** (fast path): `effect.residual`, O(1), must agree with
   `qsub` on definedness (null ⟺ a < b) and value.

## 5. Residuation is the price of internalization

Metric time has two proof-theoretic poles:

| | labeled / absolute (IMTL, timed MSR) | graded / relative (till) |
|---|---|---|
| judgment | `A^[a,b]`, present time on turnstile | `{A}@d` — label-free |
| arithmetic in rules | addition + ≤ constraints only | ⊕ and one partial ⊖ |
| bookkeeping | constraint store Ω; `split` rule **branches the proof** when Ω cannot order two times | none |
| subtraction | only inside the constraint grammar; no rule computes a residual | `monad_l`: `H := F ⊖ E` |

The `monad_l` residual is the labeled system's world-shift arithmetic
(`E + H = F`) folded into the grade. Choosing grades buys compositional,
label-free judgments and pays with exactly one partial operation — this
document is the receipt.

## 6. The adequacy bridge (statement)

till's forward scheduler is accumulation-only (absolute monotone stamps,
timed-MSR-shaped); its backward calculus is residuated (relative grades).
**Claim:** operational stamps are the least derivable grades — each `@fire`
trace at horizon T corresponds to a backward derivation whose residual
accounting reproduces the stamp arithmetic, and conversely (THY_0018 Theorem 1
form). Proving this generalizes CLF's adequacy to the quantitative temporal
setting; no prior work bridges the two poles (timed MSR has no backward
calculus, IMTL no operational semantics, CLF no grades). Status: the
stamped/bridge direction is THY_0018 Theorem 1 (proved); the PURE-calculus
side is THY_0023 Theorems 10–11 (work adequacy — the residuated backward
fragment computes total work Σ, and max-plus makespan is exactly the stamp
coeffect's contribution). Mechanisation deferred (TODO_0270).

## 7. Deliberately not adopted

- **Clamping monus ∸** (a ∸ b = 0 when b ≥ a, Amer 1984): trivially
  V-preserving but silently wrong for the scheduler (a too-late resource must
  make the rule *inapplicable*, not free). If a clamp-style rule ever appears
  (farm-speedup with a floor), ∸ enters as a SECOND named operation chosen per
  use-site — never as the meaning of `-`.
- **Full liquid-style refinement types**: overkill for three linear fences;
  the sort system (THY_0020) plus this algebra is the minimal sound design.
  Revisit only if CALC verifies value-indexed program properties (gas bounds).
