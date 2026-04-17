---
title: Large Proof Tree Display
tags: [ui, proof-tree, performance, documentation]
---

# Large Proof Tree Display

Working notes for TODO_0213. The proof-viewer layouts in
[`src/ui/components/proof-block/`](../../src/ui/components/proof-block/)
render fine on inline teaching examples (~2–20 nodes). This note tracks
what breaks once real calc proofs start landing — binary arithmetic,
EVM bytecode, multisig verification — where trees are expected to
reach hundreds or thousands of nodes.

## Baseline measurements

`node tools/proof-size-probe.js` sizes a set of representative
backward proofs (proof-tree/v1 JSON over the `auto` strategy):

| Sequent                                   | Nodes | Depth | JSON bytes |
| ----------------------------------------- | ----: | ----: | ---------: |
| `\|- A -o A` (id)                         |     2 |     2 |        419 |
| `A, B \|- A * B` (tensor intro)           |     3 |     2 |        605 |
| `A, A -o B \|- B` (modus ponens)          |     3 |     2 |        594 |
| `(A*B)*C \|- A*(B*C)` (tensor assoc)      |     7 |     5 |      1 332 |
| `A*B -o C \|- A -o (B -o C)` (curry)      |     7 |     5 |      1 308 |
| `A,…,H \|- A*…*H` (8-wide tensor)         |    15 |     8 |      3 073 |

All inline ILL proofs stay tiny — the naive bussproofs/Gentzen
renderers handle them comfortably. The regime that motivates TODO_0213
only appears once `#import`-backed programs (binary arithmetic, EVM
model, multisig verification) are wired into the proof pipeline. Those
use the directive loader (`tools/directive-loader.js`) rather than the
`proveSource` entrypoint used by the doc viewer, so this note's
benchmarks are a floor — not a ceiling.

## Strategy bet

The full menu of approaches is enumerated in
[TODO_0213](https://hq.denis.page/todo/0213). This note picks the
subset worth building first.

**Always-on defaults** (every layout, no toggle):

- **Depth folding** — `IndentedLayout` already takes a `foldThreshold`
  (default 6). Lift it to all five layouts by collapsing premises past
  `N = 3` into a clickable `⋮` stub. `bussproofs` / `gentzen` / `flipped`
  render the elided subtree as a compact "N rules / depth D" badge;
  `tactic` as a single `…` line; `indented` reuses its existing fold.
- **Skeleton summary** — a second global mode (toggle in the header
  beside the layout tabs) that drops sequent text and renders only
  rule names. Keeps branching structure visible at ~10× density.
- **Per-node stats badge** — hover reveals `nodes / depth / branching`
  for the subtree rooted at that node. Non-invasive; always on.

**Opt-in via toggle** (deferred unless benchmark demands):

- Search-to-focus (rule/formula text search → snap + expand).
- Lazy subtree load (server emits root + N levels; browser fetches
  deeper subtrees on demand using proof-tree/v1 node IDs).
- Canvas pan/zoom (Miro/Figma-style surface for presentation mode).

**Not in scope**:

- Virtualization (engineering cost high; only pays off above ~10 000
  DOM nodes — we'd hit layout/paint walls from CSS long before that).
- Content-hash elision of identical subproofs (powerful but confusing;
  defer until users ask).
- Streaming / incremental render (couples viewer to live prover; out
  of scope for static doc pipeline).
- Binary serialization (JSON currently dominated by formula pool, not
  tree shape; revisit when JSON parse becomes measurable).

## Rollout

1. **Measurement** — probe script in place
   (`tools/proof-size-probe.js`); extend to cover imported programs
   once a ≥500-node target lands.
2. **Always-on defaults** — lift depth-fold to all layouts; add the
   skeleton toggle beside the existing layout tab-bar.
3. **Benchmark** — pick a real heavy proof (likely
   `!mul`/`!sha3`/`!plus` on wide binary), capture first-paint and
   expand/collapse latency in Chromium.
4. **Opt-in modes** — search, lazy load, canvas — each gated behind
   actual observed pain.

## Related

- [`doc/documentation/proof-blocks.md`](proof-blocks.md) — viewer
  architecture + `{proof ill}` block syntax.
- TODO_0040 — the viewer itself.
- TODO_0213 — full design deliberation / menu of approaches.
