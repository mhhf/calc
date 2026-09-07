# Paper

Four papers (the till → will → ci arc, plus a stub):

**"Settle Optimality: Semiring Shortest-Distance under Linear Consumption"**
— `settle-optimality.md` (markdown master, TODO_0284 Phase T). The
choice-freedom/contention-freedom split, T1 confluence + T2 σ*-optimality,
the E1 separation witness (`calculus/gill/tests/forward/contention.gill`),
the termination proposition, and §8.4 the product instance (TODO_0285 P6:
the C4 split, lex transfer, materialized per-fact Pareto frontier,
frontier adequacy for `settleFrontier` — discharging the former ⟨open⟩
Pareto obligation; the focused-frontier gap resolved 2026-09-07:
witness W-gap + tied-contention adequacy, machine-checked by
`certifyContention`'s `tiedContention` level), and §8.5 the usage-axis
factorization (THY_0034: conservation axes never ride stamps — the
broadcast no-go; trace measures / linear tokens / chooser /
term-computed delays as the complete slot routing). Prior-art
positioning: hq research 0138 Part A.
THY_0033 §1's routed-column equivalence is deliberately NOT in any paper
yet — held for the eventual toolbox/systems paper (see THY_0033
frontmatter `paper:`).

ONE unified till paper (merge of the former proof-theory and systems drafts,
2026-08-23 — the split drafts live in git history):

**"A Delay-Graded Lax Monad: Timed Multiset Rewriting with Proven-Exact
Acceleration"** — `till/main.tex` (LaTeX is the master). Two movements:
proof theory (THY_0018/0019/0022/0023: graded lax sequent calculus, cut
elimination, work adequacy) and the engine it provably enables
(THY_0024/0025: labelled states, cohort firing, orbit certificates,
measured results). Refinement sorts (THY_0020) and the full probabilistic
judgment (THY_0021) are deliberately out of scope. Tracked in TODO_0270.

`till/NOTES.md` holds internal submission notes: reviewer-facing weak
points, the merge disposition table, and the `% TODO-verify` bib entries
that need field checks before submission.

Build (`article` class — acmart swap is mechanical at venue choice;
`mathpartir.sty` vendored; needs only pdflatex + bibtex):

```sh
cd till
pdflatex -interaction=nonstopmode main.tex && bibtex main \
  && pdflatex -interaction=nonstopmode main.tex \
  && pdflatex -interaction=nonstopmode main.tex
```

**"Weight in the Endsequent: Cut Admissibility for a Measure-Weighted
Existential by Draw-Token Internalization"** — `will/main.tex`
(THY_0026/0027 at referee grain + certifyCollapse evaluation; tracked in
TODO_0283 via TODO_0279 §2). Same build recipe, in `will/`.

**"Runs Certify Their Independence: Conditional Independence on Dynamic
Derivation Forests"** — `ci/main.tex` (the sequel: THY_0028 + 0029 +
0030 + 0031 as its four movements; TODO_0302 M7). DRAFT ASSEMBLED
AUTONOMOUSLY 2026-09-02 — see `ci/NOTES.md` §0 for the gate order
(Denis's reads of THY_0031 and the will paper come first). Same build
recipe, in `ci/`.
