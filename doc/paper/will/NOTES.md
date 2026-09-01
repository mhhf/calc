# NOTES.md — Internal Submission Notes
## "Weight in the Endsequent: Cut Admissibility for a Measure-Weighted Existential by Draw-Token Internalization"

NOT for inclusion in the PDF. Source of truth for the theory content is
THY_0027 (cut admissibility, focused system) with THY_0026 (measure side,
T1–T3) and RES_0140 (the design chronicle); the paper is their referee-grain
projection plus the two arguments THY_0027 left at sketch grain
(focalization completeness, driver adequacy — §6 and §7 of the paper).

Build: `pdflatex main && bibtex main && pdflatex main && pdflatex main`.
Compiles clean (only the benign `scit` font-shape warning).

---

## 1. Reviewer-Facing Weak Points (Honest Self-Review)

1. **No mechanized proofs.** Theorem 3.1 (cut + exact trace conservation)
   is on-paper, adversarially audited (two independent passes, one
   load-bearing repair — the (f′) audit trail is IN the paper as a
   feature). The internalization makes the will-own layer small (ILL + 3
   rules), so the mechanization burden is the graded base — same
   highest-leverage investment as the till paper's.

2. **Focalization base cases are cited, not re-proved.** §6 works ONLY the
   new cases (token passivity, left-wave principality, the ∃_ρ-R
   permutation table, suspension) and cites Andreoli/Laurent/
   Miller–Saurin/Simmons for the MALL machinery. A referee may want the
   full system spelled out in an appendix; the suspension discipline
   (synthetic-atom ∃_ρ, forced by no-cloning) is the part to defend —
   note the scope trick: for boundary judgments suspension is vacuous, so
   N's canonicity never depends on it.

3. **Adequacy leans on the companion stack.** Settle-segment exactness and
   trace elaboration are imported from the till paper; T1–T3 (measure
   identification, Chi–Geman convergence, sampler unbiasedness) from
   THY_0026. The adequacy proof here contributes: post-hoc grounding
   soundness (bias monotonicity), the fixed-policy bijection, and policy
   independence via the tree-is-not-a-schedule argument. If THY_0026 is
   not public at submission time, T1–T3 must be inlined or the mass
   corollary weakened.

4. **Cor. 5.3's example is the &-left form** and is executable
   (tests/will-prover.test.js pins both proofs, including the
   synthetic-atom id). The ⊕-right form mentioned in passing is NOT in
   the implemented gill fragment (bare ⊕ is not even in gill's surface —
   only woplus `+[q]`); THY_0027 §5's ⊕ example lives in ill.rules. If a
   referee asks for ⊕, adding it to the gill surface is a small design
   task (parser + 3 rules), tracked but not required by any claim.

5. **Conflict-freedom as an adequacy hypothesis** may read as dodging
   concurrency. The honest framing (in the paper): a genuine scheduling
   conflict is ADVERSARIAL nondeterminism with no mass semantics, and the
   engine errors loudly rather than silently double-counting — the
   hypothesis is checked, not assumed.

6. **The ℂ face is a remark, not a result.** Keep it one paragraph;
   any expansion invites a quantum-logic referee fight the paper does not
   need.

## 2. Claim boundaries (novelty audit 2026-09-01, from THY_0027)

Theorem-level priority believed INTACT: endsequent-weight mechanism, exact
cut conservation for a measure-weighted existential, no-promotion for
draws, identity-expansion failure. Idea-level relatives all cited and
distinguished in §9: PRISM msw (persistent/memoized, no proof theory),
Dahlqvist–Kozen (denotational only), time/error credits (anonymous,
additive), nominal freshness (no weight), Di Guardia–Ehrhard–Faggian
(probabilities in boxes), Green–Tannen (monomials over trees vs. one
monomial per endsequent).

## 3. Evaluation numbers (pinned by the artifact, 2026-09-01)

- WFC case study: 41/81 beaches carry mass, total 217 of unconstrained
  625 = 5⁴ — matches brute-force enumeration (test:
  tests/engine/will-wfc.test.js; the number in §8.3).
- certifyCollapse: 8 pins (unbiased, bias-interleaved, rung-2 PCFG,
  skolem ∃-closure, correlation, doctored-weight + truncated-⟨Θ⟩ tamper
  rejection) — tests/engine/will-certify-collapse.test.js.
- will-prover: 25 kernel-verified derivations pinning §3–§5 patterns.
- Full fast suite ≈3.5k tests at the time of writing; "~90 will-specific"
  in §8.4 counts will-prover + draw-check + certify-collapse + decimate +
  wfc + priors + scaffold additions.

## 4. TODO-verify citations

refs.bib entries marked TODO-verify: OrchardLiepeltEades2019 (article
no.), FujiiKatsumataMillies2016 (volume/pages), DiGuardiaEF2024 (author
list), CharguerraudPottier2017 (year), Eris2024 (SPLIT into Eris error
credits [Aguirre et al.] and Tachis expected cost [Haselwarter et al.] —
currently one merged entry, must be fixed before submission),
GradelTannen2024 (version), Laurent2004 (citation form).

## 5. Venue

POPL-shaped (proof theory + certified implementation). acmart conversion
deferred until venue choice, same as the till paper. If the till paper is
under review at the same venue, the two must cross-cite as companion
submissions; §2 of this paper is written to be readable without it (the
two load-bearing base facts are restated).
