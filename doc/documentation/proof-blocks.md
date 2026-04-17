---
title: Proof Blocks
summary: Embed live proof-tree visualizations in markdown with `{proof <calculus> [profile]}`
---

# Proof Blocks

Fenced code blocks of the form ` ```{proof <calculus> [profile]} ` render the
proof of the enclosed sequent as an interactive tree. The prover runs on the
server (cached on disk), and the client renders the tree in one of five
interchangeable layouts.

## Syntax

    ```{proof ill}
    A, A -o B |- B
    ```

- First positional token: calculus name (today: `ill`)
- Second positional token (optional): execution profile (TODO_0212)
- Body: any sequent in that calculus's surface syntax

## Layouts

The header bar offers a toggle between:

- **Bussproofs** — conclusion at the bottom, premises stacked above rule-bars
- **Gentzen** — same shape with explicit rule-name chips on each bar
- **Tactic** — linear pre-order traversal (Coq/Isabelle style)
- **Indented** — foldable indent-per-depth, scales better for deep trees
- **Flipped** — root at top, premises nested below

Selection is persisted per browser in `localStorage`.

## Examples

### Identity

```{proof ill}
A |- A
```

### Tensor introduction

```{proof ill}
A, B |- A * B
```

### Modus ponens via loli

```{proof ill}
A, A -o B |- B
```

### Bang + tensor

```{proof ill}
!A, !A |- A * A
```

### With-introduction (external choice, requires same resources for both)

```{proof ill}
A |- A & A
```

### Bang then loli

```{proof ill}
!(A -o B), A |- B
```

### An unprovable sequent

```{proof ill}
A |- B
```

## Deep / wide trees — viewer defaults

The Phase A defaults (TODO_0213) are visible in the examples below. Each
of the five layouts (see the tabs top-right) collapses premises past
depth 3 into a clickable `⋮` stub; the **skeleton** toggle hides sequent
text and renders only the rule chips. See
[`large-proof-trees.md`](large-proof-trees.md) for the design notes.

### Tensor associativity (7 nodes, depth 5)

Small enough to render fully, deep enough that depth-folding kicks in at
the leaves.

```{proof ill}
(A * B) * C |- A * (B * C)
```

### Loli currying (7 nodes, depth 5)

```{proof ill}
A * B -o C |- A -o (B -o C)
```

### Wide tensor — 8-way split (15 nodes, depth 8)

First proof where the default fold actually hides subtrees; click a `⋮`
stub to expand. Toggle **skeleton** to see the branching shape.

```{proof ill}
A1, A2, A3, A4, A5, A6, A7, A8 |- A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8
```

## Architecture

The pipeline is:

```
{proof <cal> <profile>}   ──►  POST /api/proof   ──►  proof-tree/v1 JSON
                                      │
                                      ▼
                              lib/prover/prove-source.js
                                      │   reads cache out/doc-cache/<hash>.json
                                      │   miss → calculus.parseSequent → prover.prove
                                      │        → serialize-tree → write cache
                                      ▼
                              ProofBlock.tsx (client)
                                      │   fetches tree, feeds to renderLayout()
                                      ▼
                               5 layouts (pure functions of the tree)
```

The `proof-tree/v1` format is documented in `lib/prover/serialize-tree.js`.
Same JSON renders identically regardless of layout — the format is the
contract between prover and renderer.

## Cache behaviour

Keys hash `(calculus, profile, trimmed-source, format-version)` into a
16-char hex digest stored at `out/doc-cache/<key>.json`. Edit the sequent,
change calculus, or bump the format version → new cache file; old entries
age out (no automatic eviction — wipe the directory on a clean rebuild).
