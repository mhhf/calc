---
title: Book Authoring Guide
summary: How to write chapters — frontmatter, widget blocks, style, validation. Not a chapter.
---

# Book Authoring Guide

Chapters are plain markdown in `doc/book/`, named `NN_slug.md` (NN = global
chapter number, 01–21). They render at `/book/<slug>` with hydrated widgets.

**Validate every chapter before you're done:**

```
node tools/validate-chapter.js doc/book/NN_slug.md
```

It machine-checks frontmatter, every `{prove}` goal (parse + provability),
`{rule}` names, `{formula}`/`{calc}` parses, quiz shape, wiki-links, and
referenced program files. A chapter is not finished until it passes.

## Frontmatter (all required)

```
---
title: What Is a Proof?
part: 1
partTitle: Proofs as Trees
chapter: 1
summary: One sentence shown on the course index card.
---
```

## Style

- Undergrad level. Simple language, short sentences, minimal examples,
  step by step. Introduce ONE idea at a time and immediately let the reader
  try it in a widget.
- Concrete before abstract: start from a scenario (vending machine, coins,
  recipes), then name the connective.
- Every chapter: motivation → concept in small steps → interactive
  exercises → a quiz → "What you learned" recap → links to deeper repo docs
  (theory/def/documentation) via wiki-links.
- Use `$...$` inline math and `$$...$$` display math (KaTeX). ASCII
  connectives in code spans: `*` tensor, `-o` loli, `&` with, `+` oplus,
  `!` bang, `I` one, `zero`. LaTeX: \otimes \multimap \& \oplus.
- Headings: `##` sections, `###` subsections. No `#` (the page adds the title).

## Widget blocks

### Interactive prover (the core widget)

    ```{prove}
    goal: P, P -o Q |- Q
    title: Modus ponens
    hint: Click the sequent, then decompose the implication on the left.
    id: ch2-mp
    rules: id, loli_l
    ```

- `goal` (required): a sequent `Γ |- C`. MUST be provable — the validator
  runs the auto prover on it.
- `rules` (optional): comma-separated whitelist shown to the learner.
  Omit for full palette. Rule names: id, tensor_r, tensor_l, loli_r,
  loli_l, with_r, with_l1, with_l2, oplus_r1, oplus_r2, oplus_l, one_r,
  one_l, zero_l, promotion, dereliction, absorption, copy, monad_r,
  monad_l, exists_r, exists_l, forall_r, forall_l.
- `id` (optional): stable exercise id — records learner progress.
- `mode`: `unfocused` (default) or `focused` (shows Focus/Blur steps).

**Prover limits (important):** linear-zone `!P` supports dereliction
(`!P |- P`) and per-hypothesis use, but the auto prover does NOT find
weakening/contraction proofs like `Q, !P |- Q` or `!P |- P * P`. Write
bang exercises in the shapes that work: `!P |- P`, `!P, !Q |- P * Q`,
`!(P -o Q), P |- Q`, `!P, !P |- P * P`, chains like
`!(a -o b), !(b -o c), a |- c`. The validator rejects unprovable goals.

### Rule cards

    ```{rule tensor_r}
    ```

Or several: names one per line in the body. Renders the abstract rule(s)
as \cfrac cards.

### Formula playground

    ```{formula}
    A -o (B * C)
    ```

Editable formula input with KaTeX + AST view. Body = initial formula.

### Quiz

    ```{quiz, id=ch1-q1}
    Q: In `P, Q |- R`, what must be used exactly once?
    - [x] every hypothesis on the left
    - [ ] only P
    - [ ] nothing — hypotheses are optional
    explanation: Linear hypotheses are resources: each is consumed exactly once.
    ```

Multiple `Q:` sections allowed. `$...$`, `` `code` ``, `*em*` work in
questions/options. More than one `[x]` → multi-select.

### Exercise / solution callouts

    ```{exercise, title=Swap the pair}
    Prove that tensor is commutative using the widget below.
    ```

    ```{solution}
    Apply `tensor_l` first — it splits the pair into two hypotheses —
    then `tensor_r`, sending P to the right premise and Q to the left.
    ```

Bodies are markdown (no nested fenced blocks).

### Static rendered formula

    ```{calc}
    (A -o B) * !C
    ```

### Execution widgets (Parts II+, server-backed)

    ```{exec ill}
    file: calculus/ill/tests/forward/debug-demo.ill
    query: symex
    maxSteps: 20
    title: Stepping a tiny program
    ```

Or inline source (no `file:` line — the body IS a small .ill program; give
it a directive whose left-hand side seeds the state, e.g.
`#expect_go a => c .`). Steps through firings with state diffs. Keep inline
programs tiny (a few rules); use `file:` for anything real.

    ```{game till}
    file: calculus/till/game/PP2.till
    title: Paragon Pioneers
    ```

    ```{collapse will}
    file: calculus/will/game/WFC.will
    seed: 7
    title: Beach WFC
    ```

### Also available

`{proof ill}` (static proof-tree block, body = sequent — see
doc/documentation/proof-blocks.md), `{katex}`, `{mermaid}`, `{graphviz}`.

## Wiki-links

`[[theory/0018_delay-graded-lax-monad|the till theory doc]]`,
`[[def/0005_internal-vs-external-choice]]`, `[[docs/lax-monad]]`.
Folder prefix required for cross-folder links; the validator resolves them.

## Sequent syntax quick reference

- `P |- Q` — one linear hypothesis. `P, Q |- R` — two.
- Atoms are capitalized or lowercase identifiers; both are fine.
- Precedence: `-o` 50 < `*` 60 < `+` 65 < `&` 70 < `!` 80; parenthesize
  when in doubt.
- There is no empty-left shorthand issue: `|- P -o P` works.
