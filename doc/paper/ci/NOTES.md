# NOTES.md — Internal Submission Notes
## "Runs Certify Their Independence: Conditional Independence on Dynamic Derivation Forests"

NOT for inclusion in the PDF. Source of truth: THY_0031 (definitions,
criterion, soundness, genericity) with THY_0028 (single-counting /
certificate visibility), THY_0029 (splitting laws), THY_0030
(conditioning by restriction); TODO_0302 is the plan, RES_0142 the
positioning sweep this paper's related-work section compresses.

Build: `pdflatex main && bibtex main && pdflatex main && pdflatex main`.
Compiles clean (12 pp draft).

---

## 0. PROVENANCE — read before anything else

This draft was ASSEMBLED AUTONOMOUSLY (2026-09-02, same session that
produced THY_0031, its two adversarial audits, and certifyCI). Denis
has NOT yet read THY_0031 or this draft. The gates, in order:

1. Denis reads THY_0031 (the M4′ human gate) — findings flow back here.
2. Denis reads the will paper (its own standing gate, TODO_0279 §2) —
   this paper leans on it for the calculus, cut admissibility, driver
   adequacy (Lemma "locality" cites its Cor. 7.2 machinery), and
   certificates.
3. Only then venue/acmart/submission mechanics.

## 1. Reviewer-Facing Weak Points (Honest Self-Review)

1. **Lemma locality (L1) is imported.** Its three legs are stated
   inline but the underlying driver-adequacy bijection is the will
   paper's; a referee may want the configuration-level restatement
   spelled out in an appendix. The cohort-multiplicity key expansion
   is load-bearing for its injectivity.

2. **The moral-graph lemma is cited, not re-proved** (Lauritzen Prop
   3.25 / Verma–Pearl). Pure graph theory; fine, but the VIRTUAL nodes
   (O_F, V_e) must be argued to satisfy the DAG hypotheses — one
   paragraph to add if asked (they are sinks; edges respect key
   well-foundedness).

3. **Soundness-not-completeness may read as weakness.** The framing
   that carries it: CSI-separation is already sound-not-complete on
   static LDAGs; will adds the erasure refutation showing completeness
   is structurally unattainable — refusal-with-witness-walk is the
   honest verdict shape.

4. **The mass-child discipline is the paper's most attackable novelty**
   — a referee from the BN world may claim "that's just soft
   evidence." The response is in the text: yes, and NO normalized
   framework needs it for BARE EXISTENCE or DROP or SURVIVAL, because
   normalization hides exactly the totals that restriction semantics
   exposes; the three exact counterexamples (16≠4, 8≠16, 0/4/4/8) are
   two-line programs anyone can run.

5. **certifyCI is v1**: static quotient over-connects multi-instance
   rules (WFC-scale programs will over-refuse); timed-window and
   dynamic-rule programs are loud fences. Framed as "the executable
   witness", not "the tool".

6. **Genericity converse is partial** (directed faithful chains only).
   The refutation theorem (value-erasing chains) is the interesting
   half and is complete; say so plainly if asked.

## 2. Claim boundaries (from RES_0142, verified 2026-09-02)

Five axes verified open before the theorem was proved: dynamic
execution-generated forests; exact ℚ unnormalized grades; per-run
kernel-checkable certificates; random existence of variables;
collider-correct run-level separation. Closest per axis:
DiGuardia–Ehrhard–Evrard–Faggian Thm 7.1 (fixed proof-net), DIBI Thm
V.1 (qualitative, program-level), Fritz–Klingler Thm 34 (fixed string
diagrams, needs conditionals), BLOG/CBN (per-world, no CI calculus),
Rueckschloss–Weitkämper (fixed Herbrand). The positioning sentence of
the abstract is RES_0142 §9's, verbatim by design.

## 3. Evaluation numbers (pinned by the artifact)

- tests/engine/will-ci.test.js: 22 tests — seven programs, exact
  masses hand-verified then engine-confirmed; certifyCI verdicts on
  all (4 certifications, 8 refusals incl. the documented-incomplete
  one).
- Companion pins: will-decimate (evidence discipline),
  will-prover (splitting laws), will-datasorts (conditioning,
  zero-variance ≡ 8/3, 2, 32/15), will-certify-collapse (8 pins incl.
  tamper rejections), WFC 41/81 / 217/625.

## 4. TODO-verify citations

ALL entries re-verify before submission (drafted from RES_0142's
verified list, but page/volume details unchecked): Lauritzen1996
(Prop number), VermaPearl1988 (venue form), Shachter1998 (title
"The Rational Pastime ..."), Winskel1987 (currently uncited in text —
cut or cite in §6), MilchCBN2005 (author order), TillPaper title
placeholder MUST be synced with doc/paper/till.

## 5. Venue

Same POPL-shaped family as the companions; must cross-cite both. The
three-paper arc (till → will → this) wants a coordinated story;
decide after the till paper's Zenodo/arXiv step.
