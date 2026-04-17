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

**Takeaway.** Base ILL focused proof search already hits **255-node,
depth-128** trees on wide-tensor goals with zero program imports. The
real-world regime (`#import bin.ill` / `evm.ill` / multisig / solc
symbolic) is expected one to two orders of magnitude larger — the
`zk/sequent-certifier/tests/fixtures/solc_symbolic_*.json` fixtures
already contain `faCount=192` chip segments, which is a rough proxy
for 200+ proof rule applications per contract symbolic run.

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

**Lazy subtree load** *(deferred, Phase C)*
- What: new `/api/proof/subtree` endpoint. Initial payload is root +
  first N levels; each fold-stub carries the node ID as a fetch key.
  Expanding a stub fetches its subtree on demand.
- Why: turns payload from O(tree) to O(viewport-touch). Pairs
  naturally with depth folding (same boundary). Stable node IDs are
  already in proof-tree/v1 (`id` field, FNV-1a of the sequent).
- When it earns its keep: JSON ≥ ~500 KB (measured) or initial
  time-to-first-paint > 200 ms on a cold cache.
- Work: (1) add `lazyDepth?: number` to `POST /api/proof`; serializer
  truncates at `lazyDepth`, elided nodes get `elided: true` +
  `childCount`; (2) add `POST /api/proof/subtree` keyed on
  `(cacheKey, nodeId)`; (3) client toggle in header persists to
  localStorage; fold-stub click routes to fetch when `elided`.

**Canvas pan/zoom wrapper** *(deferred, Phase C)*
- What: toggle button wraps the existing layout in a CSS-transform
  container. Drag = pan (translate); wheel = zoom (scale, cursor-
  centered). Reset button. Does **not** re-render as SVG/Canvas —
  we keep the DOM layout.
- Why CSS transform over SVG/Canvas: preserves text selection,
  browser Ctrl+F, a11y tree, and reuses every layout (bussproofs,
  gentzen, …) unchanged. Browser compositor handles the transform in
  GPU → cheap. SVG/Canvas rewrite would duplicate five layouts and
  break copy-paste.
- When it earns its keep: trees wider than the viewport where
  horizontal scroll is awkward (bussproofs / flipped > 12 columns).

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

### Phase C — real-world programs + opt-in toggles *(next)*

Bounded by acceptance: **the proof viewer renders a bin.ill / evm.ill
proof without blowing past a 2 s first-paint budget.**

1. **`#import` wiring in the viewer**

   Today `lib/prover/prove-source.js` calls `calculus.loadILL()` and
   parses a sequent against the core ILL rules only — user program
   clauses (`plus/z1`, `evm/add`, …) never enter the calculus context.

   Integration path (backward-prover):
   - Parse `#import <path>` lines at the top of the proof block source.
   - For each path, call `mde.load(path, { cache:true })` (the
     forward-engine loader already walks `@extends` / `#import` chains
     via `convert.buildImportTree`) to produce a compiled clause table.
   - Extend the cache key to include
     `sha256(source ‖ import_path ‖ file_mtime_or_content)` for each
     import so edits invalidate correctly.
   - Route `provePersistent` in `focused.js` through the backchainer
     (`lib/engine/backchain.js`) with the imported clause table — that
     is where the "does `!plus 3 4 7` hold?" question is actually
     answered today for the forward engine.
   - Error surface: missing import → structured error response;
     client shows "import not found: foo.ill" below the block.

   Unit test: `tests/prove-source.test.js` (new) — `!plus e (i e) R
   ⊢ R = i e` with `#import calculus/ill/programs/bin.ill` proves in
   <1 s, produces a tree, and the same source without `#import`
   fails with a clear `provePersistent` miss.

2. **Lazy subtree load** (as described in Tier 2 above).

3. **Canvas pan/zoom** (as described in Tier 2 above).

4. **Real-world benchmark fixture**

   Pick one of
   `calculus/ill/programs/multisig_nocall_solc_symbolic.ill` or a
   chunk from the solc fixtures, embed it as a doc example, measure
   first-paint + expand latency with + without each Tier 2 toggle.
   Numbers go into this doc.

### Phase D — optimize the real measured hotspot *(after C)*

Whichever of {virtualization, hash-elision, streaming, binary} closes
the gap on the Phase C benchmark wins. If Phase C lands us within
target, Phase D stays deferred.

## Related

- [`doc/documentation/proof-blocks.md`](proof-blocks.md) — viewer
  architecture + `{proof ill}` block syntax.
- TODO_0040 — the viewer itself.
- TODO_0213 — design deliberation / menu of approaches.
