---
title: Large Proof Tree Display
tags: [ui, proof-tree, performance, documentation]
---

# Large Proof Tree Display

Design + rollout notes for the proof-viewer
([`src/ui/components/proof-block/`](../../src/ui/components/proof-block/))
scaling from inline teaching examples (~2–20 nodes) to real program
proofs (~10³ nodes: EVM bytecode, multisig, solc-symbolic execution).

Two complementary concerns:

1. **Payload** — how much JSON crosses the wire and lives in memory.
2. **Render** — how much DOM we build, how fast interactions stay.

We separate them because a 500-node tree is a render problem; a
100 000-node trace is a payload problem. The strategies below are
tagged by which constraint they address, so features can be layered
in as the measured bottleneck shifts.

## Baseline measurements

`node tools/proof-size-probe.js` sizes a set of representative backward
proofs (proof-tree/v1 JSON over the `auto` strategy) across three
shape families:

| Sequent family                      | Width | Nodes | Depth | JSON   |
| ----------------------------------- | ----: | ----: | ----: | -----: |
| `id`, `tensor`, `modus_ponens`      |     — |   2–3 |     2 | ≤0.6 K |
| `tensor_assoc`, `loli_curry`        |     — |     7 |     5 | ≈1.3 K |
| `A₁,…,Aₙ ⊢ A₁*…*Aₙ` (wide tensor)   |     8 |    15 |     8 |  3.1 K |
|                                     |    16 |    31 |    16 |  7.4 K |
|                                     |    32 |    63 |    32 | 19.6 K |
|                                     |    64 |   127 |    64 | 57.8 K |
|                                     |   128 |   255 |   128 |  197 K |
| `A,A⊸B,…,Y⊸Z ⊢ Z` (impl chain)     |     4 |     7 |     4 |  1.3 K |
|                                     |     8 |    15 |     8 |  2.8 K |
|                                     |    16 |    31 |    16 |  6.1 K |
|                                     |    32 |    65 |    33 | 14.3 K |
| `A ⊸ (B ⊸ … ⊸ (A*…*H))` (curry-8)   |     — |    23 |    16 |  4.6 K |
| `mul N N` (bin.ill, teaching)       |   255 |   150 |    23 |   28 K |
|                                     | 65535 |   618 |    47 |  119 K |
| `exp 3 N` (bin.ill, teaching)       |    15 |   627 |    43 |  118 K |

**Takeaway.** Base ILL focused proof search already hits **255-node,
depth-128** trees on wide-tensor goals with zero program imports.
Backchain mode against `bin.ill` with the `teaching` profile (FFI off,
full clause expansion) scales well past that — `exp 3 15` expands to
**627 nodes** (depth 43, 118 KB raw, 16 KB gzipped), `mul 65535 65535`
to **618 nodes** (depth 47). These are the canonical fixtures that hit
the 500-node acceptance target for
[TODO_0213](https://hq.denis.page/todo/0213). `bin.ill` is the
arithmetic layer transitively imported by `evm.ill` and the
multisig / solc-symbolic programs, so the same clauses fire there at
scale — the `zk/sequent-certifier/tests/fixtures/solc_symbolic_*.json`
fixtures already contain `faCount=192` chip segments, which is a rough
proxy for 200+ proof rule applications per contract symbolic run.

## Strategy menu — with decisions

The full menu of approaches from [TODO_0213](https://hq.denis.page/todo/0213),
annotated with decision + rationale + what it buys us. The goal is not
to ship all of them — the goal is to know *when* we'd add each and
*why*. Order is rough implementation priority within each tier.

### Tier 1 — always on (no toggle)

**Depth folding** *(shipped, Phase A)*
- What: subtrees beyond depth `N=3` collapse to a clickable `⋮` stub
  with a `{nodes · depth}` badge. `DEFAULT_FOLD_DEPTH=3` in
  `ProofBlock.tsx`. All five layouts honour it.
- Why: O(viewport) DOM regardless of tree size; read-top-down matches
  how proofs are consumed.
- Scale: good up to ≈5000 nodes before the unfolded "skin" of the tree
  stresses CSS layout.

**Skeleton summary** *(shipped, Phase A)*
- What: header toggle; drops sequent text, renders rule chips only.
  10–20× density on wide trees.
- Why: orient on proof structure without parsing formulas;
  complementary to depth folding.

**Per-subtree stats badges** *(shipped, Phase A)*
- What: `nodes · ↓depth` chip on fold-stubs and rule-chip tooltips.
  Precomputed once per tree (`stats.ts`).
- Why: preview what's hiding behind a fold before expanding.

**Exact-substring search with `/regex/` escape** *(shipped, Phase B)*
- What: search box in the header. Matches against rule names + rendered
  sequent text, case-insensitive. `/` prefix → regex mode
  (`/plus|inc/`, `/\\bsha3\\b/`). Matches highlight yellow; their
  ancestor path force-expands so nothing hides; first match scrolls
  into view via `element.scrollIntoView`. ESC clears.
- Why we chose exact over fuzzy: proof text is formal operators + rule
  names + numeric indices. Fuzzy scoring scatters false positives and
  is opaque. Exact is predictable and zero-config; regex covers the
  rare power-user query.
- Implementation: `search.ts` pure function `(tree, query) →
  {matches, ancestors, first, count, error}`. Pre-order DFS, one
  `renderSequent` per node per keystroke; negligible at tensor128
  (<1 ms in Chromium). Re-runs only on `query()` change.

### Tier 2 — opt-in toggles (payload + render help for 10³–10⁴ nodes)

**Lazy subtree load** *(shipped, Phase C)*
- What: `POST /api/proof` accepts an `elideBelowDepth` number; the
  serializer post-processor (`lib/prover/serialize-tree.js
  :elideBelowDepth`) replaces nodes at depth ≥ N with `{elided:true,
  premises:[]}` stubs that keep their real FNV-1a `id`. The header
  `lazy` toggle (persisted under `calc.proofBlock.lazy`) flips
  `LAZY_ELIDE_DEPTH=3` into that parameter. Elided stubs render as a
  blue `↓` FetchButton; clicking routes through `POST /api/proof/subtree
  { source, nodeId, elideBelowDepth }` which re-elides the returned
  subtree at the same depth for recursive expansion.
- Why: turns wire payload from O(tree) to O(viewport-touch). The
  server caches the **full** tree JSON under `sha256(calc, profile,
  mode, imports, body)` — `elideBelowDepth` is a pure view transform
  applied *after* cache read, so switching lazy on/off never
  invalidates cache and `nodeId` lookups always resolve.
- Measured savings (fresh cache, `tensor_assoc` family at
  `elideBelowDepth=3`):

  | fixture   | full KB | gz KB | lazy KB | lazy gz | save | gz-save |
  | --------- | ------: | ----: | ------: | ------: | ---: | ------: |
  | tensor16  |     7.2 |   0.8 |     2.5 |     0.5 |  65% |     34% |
  | tensor32  |    19.1 |   1.5 |     4.1 |     0.8 |  78% |     46% |
  | tensor64  |    56.5 |   2.9 |     7.4 |     1.3 |  87% |     55% |
  | tensor128 |   192.3 |   6.5 |    14.1 |     2.4 |  93% |     63% |

**Canvas pan/zoom wrapper** *(shipped, Phase C)*
- What: `PanZoom.tsx` — toggle in the header wraps the laid-out tree
  in a CSS-transform container. Drag = pan (translate); wheel =
  zoom (scale, cursor-centered, `scale ∈ [0.1, 4]`). Interactive
  targets (button, anchor, input, `role="tab"`) are excluded from
  drag. Reset button + zoom-% badge. State persists per-browser in
  `calc.proofBlock.panzoom`.
- Why CSS transform over SVG/Canvas: preserves text selection,
  browser Ctrl+F, a11y tree, and reuses every layout (bussproofs,
  gentzen, …) unchanged. Browser compositor handles the transform in
  GPU → cheap. SVG/Canvas rewrite would duplicate five layouts and
  break copy-paste.
- Math: cursor-centered zoom uses `t_new = t_old + (s_old − s_new)·p0`
  where `p0` is the cursor position relative to the container origin.
  This keeps the pixel under the cursor pinned across wheel deltas.

### Tier 3 — future / measured-demand only

**Virtualization** — render only viewport nodes, recycle DOM on scroll.
- Pays off above ~10 000 DOM nodes; breaks our inline/flexbox layouts
  which rely on intrinsic sizing. Would require per-layout measurement
  pass. Punt until browsers stop coping.

**Content-hash elision of identical subproofs** — collapse duplicate
subtrees into one render with multiplicity counter (`×32`).
- Huge on repetitive proofs (EVM init × 256 word bits). Confusing for
  beginners. Add only behind an explicit "merge duplicates" toggle
  once users ask for it.

**Streaming / incremental render** — server emits tree depth-first as
proof search progresses; root appears before leaves.
- Couples viewer to live prover. Good for interactive debuggers, out
  of scope for static doc pipeline. Revisit when the live-prove UI
  (TODO_0040) gets its own canvas.

**Binary serialization (MessagePack / protobuf)** — smaller wire +
parse cost for very large trees.
- Payload currently dominated by formula pool, not tree shape; JSON
  parse is not yet a measurable bottleneck. Revisit if Tier 2 lazy
  load can't close the gap on solc-symbolic traces.

## Rollout

### Phase A — always-on defaults *(shipped, commit `daf04f0`)*

Depth folding, skeleton mode, per-subtree stats. See
[`proof-blocks.md`](proof-blocks.md) for usage.

### Phase B — search + this design doc *(this pass)*

- `search.ts` + header input, highlight, force-expand, scroll-into-view
- Rewritten design doc with tier annotations + deferred-work plans

### Phase C — real-world programs + opt-in toggles *(shipped)*

Acceptance target: **proof viewer renders a bin.ill / evm.ill proof
without blowing past a 2 s first-paint budget.** Met on all current
fixtures — tensor128 renders 7 visible nodes at fold-depth 3 in under
100 ms first paint, 2.4 KB over the wire with `lazy` on.

1. **`#import` wiring + backchain mode** — `lib/prover/prove-source.js`
   parses `#import <path>` headers, loads clause tables through
   `convert.buildImportTree`, and routes `provePersistent` via
   `lib/engine/backchain.js`. The cache key incorporates a SHA-256
   digest over each imported file's content so edits invalidate. A
   new `mode: 'backchain'` covers pure SLD queries (e.g.
   `!plus e (i e) R`) that the focused sequent prover doesn't handle
   directly.

2. **Lazy subtree load** — Tier 2 above. 93% payload saving on
   tensor128, 63% after gzip.

3. **Canvas pan/zoom** — Tier 2 above. Toggle-driven, zero cost off.

4. **Benchmark fixture** — `tools/proof-viewer-bench.js` enumerates
   the `tensor_N` / `chain_N` / `plus_N_N` / `loli_curry` matrix plus
   three real-program backchain fixtures (`mul_255_255`,
   `mul_65535_65535`, `exp_3_15`) that exercise the arithmetic layer
   of `bin.ill` — the same clauses fired at scale by `evm.ill` and the
   multisig / solc-symbolic programs. `exp_3_15` (627 nodes, depth 43)
   is the canonical 500-node acceptance fixture; embedded live in
   [`proof-blocks.md`](proof-blocks.md) so every doc rebuild
   re-exercises the full viewer pipeline end-to-end.

### Phase D — optimize the real measured hotspot *(deferred)*

Phase C cleared the 2 s budget on every current fixture. Phase D
(virtualization / hash-elision / streaming / binary) stays deferred
until a measured regression on a real-program proof justifies it.

## Related

- [`doc/documentation/proof-blocks.md`](proof-blocks.md) — viewer
  architecture + `{proof ill}` block syntax.
- TODO_0040 — the viewer itself.
- TODO_0213 — design deliberation / menu of approaches.
