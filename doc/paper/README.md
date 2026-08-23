# Papers

Two papers from the till line of work. Markdown files are the content
masters; each LaTeX directory is the typeset submission artifact
(`article` class — acmart swap is mechanical once a venue is chosen).

| Paper | Master | LaTeX | Todo |
|---|---|---|---|
| The Delay-Graded Lax Monad (proof theory: sequent rules, cut elimination, adequacy) | `till-paper.md` | `till-monad/` | TODO_0270 |
| till at Scale (systems: labelled states, orbit certificates, cohort firing, measured results) | `till-scale.md` | `till-scale/` | TODO_0278 §Paper |

Build (pdflatex + bibtex; `mathpartir.sty` is vendored per directory):

```sh
cd till-monad   # or till-scale
pdflatex -interaction=nonstopmode main.tex && bibtex main \
  && pdflatex -interaction=nonstopmode main.tex \
  && pdflatex -interaction=nonstopmode main.tex
```

Bib entries carrying a `% TODO-verify` comment need their fields checked
against the actual publications before submission.
