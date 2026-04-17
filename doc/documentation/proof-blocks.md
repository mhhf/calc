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

### Real-program proof — `exp 3 15` via bin.ill (627 nodes, depth 43)

The `exp 3 15 R` goal derives `3¹⁵ = 14 348 907` by iterated multiplication
against the clauses in `programs/bin.ill` (itself transitively imported by
`evm.ill`, the multisig contract, and the solc-symbolic fixtures). With
the `teaching` profile it expands into a 627-node tree — the canonical
large-proof example backing the 500-node acceptance target in
[TODO_0213](https://hq.denis.page/todo/0213).

Open the block with **lazy** on (default) to ship only the top 3 levels
over the wire; click any blue `↓` stub to fetch a subtree on demand.
**Skeleton** mode collapses the arithmetic text so the branching shape is
readable end-to-end.

```{proof ill backchain teaching}
#import(programs/bin.ill)

exp (i (i e)) (i (i (i (i e)))) R
```

## Deep / wide trees — viewer defaults

The Phase A + B + C toggles (TODO_0213) live in the header bar and
persist per-browser in `localStorage`:

- **search** — substring match across rules + rendered sequent text,
  case-insensitive. Prefix with `/` for regex (e.g. `/tensor|loli/`).
  Matches highlight yellow, ancestors force-expand so nothing stays
  hidden, first hit scrolls into view, ESC clears.
- **skeleton** — hide sequent text, render rule chips only. Useful for
  orienting on proof *structure* at high density.
- **pan + zoom** — drag the proof body to pan, wheel to zoom
  (`0.1×–4×`, cursor-centered). Preserves text selection and Ctrl+F.
- **lazy** — ship only the top 3 levels of the tree; each deep
  subtree becomes a blue `↓` fetch button that pulls its contents on
  click. Wire savings: 65–93% raw, 34–63% gzipped on the
  `tensor_N` family.
- Every layout also collapses premises past depth 3 into a grey `⋮`
  fold-stub regardless of the lazy toggle.

See [`large-proof-trees.md`](large-proof-trees.md) for the design
notes and measured savings.

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

### Wide tensor — 32-way split (63 nodes, depth 32)

Deep enough that lazy mode pays its rent: full JSON is 19 KB, lazy JSON
is 4 KB. Flip the **lazy** toggle and expand a `↓` stub to watch a
subtree fetch on click.

```{proof ill}
A1, A2, A3, A4, A5, A6, A7, A8, A9, A10, A11, A12, A13, A14, A15, A16, A17, A18, A19, A20, A21, A22, A23, A24, A25, A26, A27, A28, A29, A30, A31, A32 |- A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8 * A9 * A10 * A11 * A12 * A13 * A14 * A15 * A16 * A17 * A18 * A19 * A20 * A21 * A22 * A23 * A24 * A25 * A26 * A27 * A28 * A29 * A30 * A31 * A32
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
