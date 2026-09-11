---
title: "Fixed Points and Cyclic Proofs, Machine-Checked"
created: 2026-09-10
modified: 2026-09-11
summary: "Native least/greatest fixed points (μ/ν) added to CALC's ILL as declared connectives, with a cyclic-proof system whose soundness is a TRUSTED global-trace-condition checker (lib/prover/gtc-check.js) — the cyclic-proof twin of the per-step kernel and the forward-tree checker. A recurring ν-succedent closes coinductively as a back-edge (nu_cycle bud → companion); the untrusted search only guesses the back-edge, and checkGTC certifies context conservation + νR/μL progress over the whole tree. Coinduction is thereby machine-checked (`!a ⊢ νX.(a & X)` proves and kernel-verifies). A corollary corrects the folklore Baelde encoding for the intuitionistic linear setting."
tags: [fixed-points, coinduction, cyclic-proofs, muMALL, proof-theory, certificates, focusing, linear-logic]
category: "Proof theory"
unique_contribution: "A machine-checked cyclic-proof system for intuitionistic linear μMALL in which soundness is a small, adversarially-fuzzed TRUSTED checker (the focused-discipline global trace condition), separated from an untrusted proof search — the SAX untrusted-search/trusted-check discipline applied to coinduction. Two secondary contributions: (1) the observation that under Andreoli focusing the GTC collapses from a Büchi thread condition to an O(cycle-length) 'the cycle contains a νR-on-ν or μL-on-μ unfold step' check, PLUS an ILL-specific context-conservation clause (linear pool multiset-equal modulo theory at bud and companion) with no classical analogue; (2) a correction to the folklore exponential encoding: `!A = νX.(A & X)` (as stated in the CALC roadmap and much of the literature's shorthand) FAILS to give contraction in intuitionistic LINEAR logic — a linear `&` cannot duplicate — and the honest encoding is `!A = νX.(A & (1 & (X ⊗ X)))`, which is validated here (dereliction + contraction machine-checked)."
references:
  - "TODO_0009 / TODO_0203 / TODO_0064 Axis 3 (the fixed-points frontier; this is rungs 2-3: cyclic proofs + native μ/ν)"
  - "Baelde, 'Least and greatest fixed points in linear logic', ACM TOCL 2012 (the μMALL rules and the exponentials-as-fixpoints result this corrects for ILL)"
  - "Baelde, Doumane, Saurin, 'Infinitary proof theory: the multiplicative additive case', CSL 2016 (the global trace condition, here specialized to the focused intuitionistic discipline)"
  - "Nollet, Saurin, Tasson, FoSSaCS 2019 (thread-validity ≡ size-change; why the progress condition is the right one)"
  - "THY_0041 / lib/prover/forward-check.js (the forward-tree checker — the sibling untrusted-search/trusted-check certificate; the `cycle` constructor is the forward operational analogue)"
  - "TODO_0309 / doc/documentation/sax-family.md (the explicit-cut untrusted-search / trusted-kernel discipline this reuses for back-edges)"
---

# Fixed Points and Cyclic Proofs, Machine-Checked

## 1. What this adds

CALC could not state induction, coinduction, liveness, or bisimulation: MALL
has no recursion. This work adds least/greatest fixed points **μ/ν** to ILL as
declared connectives, and a **cyclic-proof** system for reasoning about them —
so a coinductive fact like "from a persistent `a`, the signal `νX.(a & X)` is
available forever" is not just expressible but **machine-checked**.

The design keeps CALC's founding discipline: *the search is untrusted; a small
checker in the TCB decides soundness.* For fixed points that checker is
`lib/prover/gtc-check.js` — the cyclic-proof twin of the per-step kernel
(`kernel.js`) and the forward-tree checker (`forward-check.js`, THY_0041).

## 2. μ/ν as data

`mu` (positive) and `nu` (negative) are unary de-Bruijn binder connectives
(`calculus/ill/ill.calc`), the exact `exists`/`forall` template. Their four
rules (`ill.rules`) are **unfold** rules realizing σX.F = F[σX.F/X]
(Knaster–Tarski) through one new `@binding unfold` mode: the witness is the
*whole* principal σX.F, so the premise `debruijnSubst(body, 0, σX.F)` is a single
deterministic substitution the kernel re-derives hash-identically. μ is positive
(μL invertible, μR focus), ν negative (νR invertible, νL focus). No engine
literal names them in the progress check — the progress condition is read by
role (`roles.lfp`/`roles.gfp`); the bud-closing marker is the literal
`nu_cycle`.

A subtlety this exposed and fixed in the kernel: `verifyTree` used to *degrade*
any binding rule to a leftover-count check (it cannot reproduce a fresh
eigenvariable). Unfold has **no** fresh variable, so degrading it would accept a
forged unfolding — a soundness hole. The degradation is now restricted to
`eigenvariable`/`metavar`; unfold is checked exactly.

## 3. Cyclic proofs and the global trace condition

A cyclic pre-proof closes some leaves (**buds**) back to an ancestor
(**companion**) instead of an axiom. The focused prover, under `cyclicProofs`,
emits a `nu_cycle` bud when a ν-succedent sequent recurs on its path; it guesses
the back-edge and nothing more. Soundness is `checkGTC`:

> A back-edge (bud B, companion C) is sound iff **(A) context conservation** —
> the consumable (linear) pool of B equals that of C as a multiset *modulo
> theory* (eq-theory canonicalization, never raw hash) and the succedents agree;
> persistent formulas are unconstrained — and **(B) progress** — the cycle
> carries a νR-on-ν or μL-on-μ unfold step.

(A) is the ILL-specific clause with no classical analogue: without it a cycle
could manufacture or destroy linear resources across the back-edge. In this
prover's focused discipline, (A) is *structurally satisfied* by construction:
companions are identified by `Seq.hash` equality, making bud and companion
content-identical sequents, so (A) holds trivially; the `checkGTC` test for (A)
is defense-in-depth for synthetic/external inputs (e.g. fuzz-generated trees),
while progress (B) is the live discriminating condition. (B) is the
Baelde–Doumane–Saurin trace condition; in this prover's design, a bud closes
against a content-identical companion (hash-identity discipline), so the
formula-thread relation is the identity along the cycle and the condition
collapses to the O(cycle-length) "has a progressing unfold" check — no Büchi
automaton. (This collapse follows from the hash-identity companion discipline —
an observation about this prover's design, not a general property of Andreoli
focusing.) νL and μR are the wrong side and never count. The checker is conservative (rejects more, never accepts
more), imports only `kernel/`, and is adversarially fuzzed (`tools/fuzz-gtc.js`:
every valid record accepted, every mutant across five unsoundness classes
rejected). `checkCyclicProof` reconstructs each back-edge *from* the
kernel-verified tree, so a buggy search cannot smuggle an unsound edge past it;
`kernel.verifyTree` runs it as a post-walk step, making cyclic proofs
kernel-verifiable end to end.

## 4. Corollary: the exponential encoding, corrected for ILL

The roadmap (and a common shorthand for Baelde 2012) states `!A = νX.(A & X)`.
In intuitionistic **linear** logic this is false for contraction: a linear `&`
cannot duplicate its resource, so `νX.(a & X) ⊢ a ⊗ a` is **unprovable**. The
honest encoding carries a multiplicative body,

$$!A \;:=\; \nu X.\,\big(A \mathbin{\&} (1 \mathbin{\&} (X \otimes X))\big),$$

whose `X ⊗ X` lets a left-ν unfold into two independent copies (contraction) and
whose `1` is the weakening alternative. Machine-checked (Inc-5a): dereliction
`!a ⊢ a`, contraction `!a ⊢ !a ⊗ !a`, and reuse `!a ⊢ a ⊗ a` all hold and
kernel-verify for this encoding and fail for the naive one. Contraction here is
*finite* — the left ν unfolds on demand; the genuinely *cyclic* half is the dual
construction of an unbounded signal from persistent resources.

Multiplicative weakening `!a ⊢ 1` is now **recovered and machine-checked** (Inc-5b).
It exposed a pre-existing focus-*completeness* corner (not a soundness gap, and
orthogonal to μ/ν): after ν-unfold, reaching `1` needs `with_l2` then `with_l1`,
ending at `1 ⊢ 1`, but the committed focused search commits to `with_l1` first —
whose `one_r` leaves `a` unspent — and never reconsiders, because the leftover only
fails the linear-emptiness check at the *root*. This is the additive don't-know
nondeterminism under a linear-resource constraint that committed-choice search
cannot see (the same phenomenon the prover already documented at its `copyContext`
additive branch). The fix is an opt-in **exhaustive** search (`opts.exhaustive`,
`lib/prover/focused.js`): a success continuation offers every candidate to the root
constraint, so a non-dischargeable leftover drives backtracking into `with_l1`/
`with_l2`. It is a separate driver — the committed path (and therefore ILL's EVM
proof search) is byte-identical: the CPS driver is structurally unreachable without
`opts.exhaustive`, and a stash-comparison micro-benchmark on ILL proofs showed no
difference. Soundness is untouched because the returned tree is still kernel- and
GTC-verified (an invariant pinned by a battery test: every exhaustive success is
kernel-valid). Because premises are searched as CPS continuations, the path-scoped
loop-detection set must drop a node's key before its continuation searches a
*sibling* (not a descendant) and restore it on backtrack — otherwise two
identical-hash additive branches (`A & A`) self-detect a spurious loop; that scoping
is handled in `searchK`, so the driver stays complete for additive backtracking.
`!a ⊢ 1`, and the minimal witness `a & 1 ⊢ 1`, now prove and kernel-verify under it, while
the genuinely unprovable (`a, b ⊢ a & b`; naive-encoding contraction) stay refused.

## 5. Scope

Soundness is machine-checked; completeness is bounded and honest. The search's
loop detection cuts at the first ν-recurrence and defers to the GTC — a
GTC-rejected cycle fails the attempt rather than triggering a different-structure
retry (a stated completeness sacrifice). Inductive cyclic proofs on μ (the μL
half of progress) are supported by the checker but the search currently emits
back-edges only for the ν (coinductive) case; Park-style induction with a
supplied invariant, and co-LP for clause-defined coinductive predicates in the
SLD engine, are the adjacent mechanisms.
