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
- Second positional token (optional): **mode** — `sequent` (default),
  `backchain`, or `forward`
- Third positional token (optional): execution **profile** — `default` or
  `teaching` (see *Backchain mode* below)
- Body: any sequent (sequent mode) or predicate atom (backchain mode)

If the second token isn't a known mode it's treated as a profile for
backward compatibility with pre-Phase-C `{proof ill verified}` blocks.

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

## Backchain mode — proving against a program

`{proof ill backchain}` switches from focused sequent search to SLD
backchaining against a user-supplied program, loaded via a
`#import(path)` header. Paths resolve under `calculus/ill/` (the
sandbox root) — absolute paths and paths that escape the root are
rejected. Edits to any imported file invalidate the cache
automatically (transitive content hashes in the key).

The body of the block is a **predicate atom**, not a sequent — the
backchainer derives a proposition from clause / type / FFI evidence.

### Plus via FFI (default: opaque leaf)

```{proof ill backchain}
#import(programs/bin.ill)

plus (i e) (i e) R
```

Default mode uses the FFI fast path where available; it shows the goal
resolved to a single opaque `ffi` node. Use `teaching` profile to see
the full derivation:

### Plus via clause expansion (teaching profile)

```{proof ill backchain teaching}
#import(programs/bin.ill)

plus (i e) (i e) R
```

`teaching` forces clause resolution (`useFFI: false`) so the full
`plus/*` ladder is visible.

## Deep / wide trees — viewer defaults

The Phase A + B defaults (TODO_0213) are visible in the examples below.
Each of the five layouts (see the tabs top-right) collapses premises past
depth 3 into a clickable `⋮` stub; the **skeleton** toggle hides sequent
text and renders only the rule chips; the **search** box matches rules
and sequent text (substring, case-insensitive) — prefix with `/` for
regex (e.g. `/tensor|loli/`). Matches highlight yellow, their ancestors
force-expand so nothing stays hidden, and the first hit scrolls into
view. ESC clears the query. See [`large-proof-trees.md`](large-proof-trees.md)
for the design notes.

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

Keys hash `(calculus, profile, mode, imports-digest, body, format-version)`
into a 16-char hex digest stored at `out/doc-cache/<key>.json`. Edit the
sequent, change calculus/mode/profile, or touch any imported `.ill`
file → new key; old entries age out (no automatic eviction — wipe the
directory on a clean rebuild).

The `imports-digest` is computed from `convert.buildImportTree` over
the transitive dependency graph of each `#import`, so editing a file
two hops deep still invalidates correctly.
