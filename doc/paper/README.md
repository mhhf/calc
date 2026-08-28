# Paper

Two papers:

**"Settle Optimality: Semiring Shortest-Distance under Linear Consumption"**
— `settle-optimality.md` (markdown stub, TODO_0284 Phase T). The
choice-freedom/contention-freedom split, T1 confluence + T2 σ*-optimality,
the E1 separation witness (`calculus/gill/tests/forward/contention.gill`),
and the termination proposition. Prior-art positioning: hq research 0138
Part A.

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
