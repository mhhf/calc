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

4. **Cor. 5.3: both forms are executable** (tests/will-prover.test.js).
   The &-left form pins both proofs including the synthetic-atom id; the
   ⊕-right form landed 2026-09-01 (surface ⊕ added to gill.calc +
   oplus_r1/r2/oplus_l in gill.rules — commit 94c3abae; till keeps
   "oplus/zero stay absent"). The paper's FORMAL counting fragment still
   states ⊕ as a routine extension (the focalization proof's case table
   doesn't enumerate it) — if a referee asks, the ⊕ permutation cases
   are the standard MALL ones plus nothing token-specific (⊕R touches
   no token; ⊕L shares Δ like &R).

5. **Conflict-freedom as an adequacy hypothesis** may read as dodging
   concurrency. The honest framing (in the paper): a genuine scheduling
   conflict is ADVERSARIAL nondeterminism with no mass semantics, and the
   engine errors loudly rather than silently double-counting — the
   hypothesis is checked, not assumed.

6. **The ℂ face is a remark, not a result.** Keep it one paragraph;
   any expansion invites a quantum-logic referee fight the paper does not
   need.

7a. **Future-work section is now stale-in-our-favor (THY_0030,
   2026-09-02).** The draft lists inside-mass conditioning as future
   work; it is now proved+shipped (datasorts, exact inside masses,
   zero-variance importance identity, certified conditioning states —
   "grades on formulas, draws in the zone, conditioning in the sort
   slot"). Before submission either update the future-work paragraph
   to cite the result or fold a one-paragraph summary into the
   discussion; it strengthens the sequel-paper trailer either way.

7. **Remark candidate (THY_0029, 2026-09-02): the mass-splitting box
   dissolves.** Companion to the paper's §3g-style dissolution remark:
   the conjectured weight-graded contraction □_{r+s}A ⊢ □_rA ⊗ □_sA
   adds no content — counts split via the counted bang (derivable, exact
   conservation), masses factorize via ⊗-context splitting of the token
   zone (multiplicative), sums live at ∃_ρ/⊕; token-backed boxes are
   definable as ⟨Θ⟩ ⊗ A, unbacked ones violate weight conservation, and
   the contraction shape would clone a draw (no-cloning, refuted
   executably: one token cannot serve two ⊗-channels). One paragraph in
   the discussion/positioning section; strengthens the "weight in the
   endsequent" thesis — two independently conjectured connectives (the
   two-semiring judgment, the weight box) both dissolved into it.

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
- will-prover: 26 kernel-verified derivations + 14 refutations pinning
  §3–§5 patterns (incl. the THY_0029 splitting-law block, 2026-09-02).
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
