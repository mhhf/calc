/**
 * Five interchangeable layouts over a single `proof-tree/v1` tree. All
 * renderers are pure functions of the JSON + formula pool; no shared mutable
 * state, so swapping the active layout is a re-render, not a re-fetch.
 *
 * Layouts:
 *   - bussproofs   — classical bottom-up stacked rule-bars
 *   - gentzen      — same shape with rule labels on the right edge
 *   - tactic       — linear pre-order traversal (Coq/Isabelle style)
 *   - indented     — compact indent-per-depth, foldable
 *   - flipped      — top-down: root at top, premises nested below
 *
 * Shared render options:
 *   - slugs       rule → /def slug mapping (turns rule labels into <a>)
 *   - skeleton    boolean; when true, sequents are dropped — rule chips and
 *                 tree structure only. 10–20× density on wide trees.
 *   - foldDepth   subtrees deeper than this collapse to a click-to-expand
 *                 stub badged with {nodes · depth}. See
 *                 doc/documentation/large-proof-trees.md for the motivating
 *                 measurements (tensor128 lands at depth 128).
 *   - stats       precomputed per-subtree stats Map (see stats.ts); used to
 *                 label fold-stubs and power rule-chip tooltips.
 */
import { For, Show, createSignal } from 'solid-js';
import type { ProofNode, ProofTreeV1, ProofLayout } from './types';
import { renderSequent } from './formula';
import type { StatsMap } from './stats';
import { badge as statsBadge, tooltip as statsTooltip } from './stats';
import type { SearchIndex } from './search';
import { EMPTY_SEARCH } from './search';

type Pool = ProofTreeV1['formulas'];
type RuleSlugs = Record<string, string>;

export interface RenderOpts {
  slugs: RuleSlugs;
  skeleton: boolean;
  foldDepth: number;
  stats: StatsMap;
  /** Search result: matching node ids + their ancestors. */
  search: SearchIndex;
}

// Highlight style for nodes that match the active search. Applied to the
// sequent line (or the rule chip in skeleton mode) across every layout.
const MATCH_BG = '#fff3a8';
const MATCH_OUTLINE = '1px solid #d4a900';

// Placeholder glyph shown in place of the sequent when skeleton mode is on.
const SKELETON_GLYPH = '·';

// Wrap a rule label in an <a> to `/def/<slug>` when the slug is known; fall
// back to plain <span> otherwise. Keeps styles identical so layouts don't
// have to branch.
function ruleChip(props: {
  rule: string;
  opts: RenderOpts;
  nodeId?: string;
  class?: string;
  style?: string;
}) {
  const slug = props.opts.slugs[props.rule];
  const subStats = props.nodeId ? props.opts.stats.get(props.nodeId) : undefined;
  const title = slug
    ? `${props.rule} — open definition${subStats ? ` · ${statsTooltip(subStats)}` : ''}`
    : `Rule: ${props.rule}${subStats ? ` · ${statsTooltip(subStats)}` : ''}`;
  const common = {
    class: `calc-proof-rule ${props.class || ''}`.trim(),
    'data-rule': props.rule,
    title,
    style: props.style,
  };
  if (slug) {
    return (
      <a href={`/def/${slug}`} {...common} style={`${props.style || ''};text-decoration:none`}>
        {props.rule}
      </a>
    );
  }
  return <span {...common}>{props.rule}</span>;
}

// Clickable fold-stub. Shared across all layouts; each layout positions it
// in the place where the hidden premise subtree would have rendered. The
// button preserves focus management (real <button type="button">) and
// exposes stats both visually (badge) and through title (full tooltip).
function FoldButton(props: {
  onClick: () => void;
  nodeId: string;
  opts: RenderOpts;
  /** Optional extra CSS on top of the default chip styling. */
  style?: string;
}) {
  const s = props.opts.stats.get(props.nodeId);
  return (
    <button
      type="button"
      class="calc-proof-fold"
      aria-expanded={false}
      onClick={props.onClick}
      title={`Expand — ${statsTooltip(s)}`}
      style={`font-family:ui-monospace,monospace;font-size:0.75em;padding:0.1em 0.4em;border:1px dashed #aaa;background:#f6f6fa;color:#555;border-radius:3px;cursor:pointer;white-space:nowrap;${props.style || ''}`}
    >
      ⋮ {statsBadge(s)}
    </button>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Bussproofs — conclusion at the bottom, rule bar above it with premises
// stacked above the bar. Classical mathematical convention.
// ──────────────────────────────────────────────────────────────────────────
function BussNode(props: { node: ProofNode; pool: Pool; depth: number; opts: RenderOpts }) {
  const { node, pool, opts } = props;
  const [expanded, setExpanded] = createSignal(false);
  const shouldFold = () =>
    props.depth >= opts.foldDepth &&
    node.premises.length > 0 &&
    !expanded() &&
    !forceOpen(node.id, opts);
  const seq = () =>
    opts.skeleton ? SKELETON_GLYPH : renderSequent(node.sequent, pool);
  return (
    <div data-proof-node={node.id} class="buss-node" style="display:inline-flex;flex-direction:column;align-items:center;margin:0 0.75em;vertical-align:bottom">
      <Show when={node.premises.length > 0}>
        <Show
          when={!shouldFold()}
          fallback={
            <div style="padding:0 0.5em 0.35em 0.5em">
              <FoldButton onClick={() => setExpanded(true)} nodeId={node.id} opts={opts} />
            </div>
          }
        >
          <div class="buss-premises" style="display:flex;flex-direction:row;align-items:flex-end">
            <For each={node.premises}>
              {(p) => <BussNode node={p} pool={pool} depth={props.depth + 1} opts={opts} />}
            </For>
          </div>
        </Show>
        <div
          class="buss-bar"
          style="border-top:1px solid currentColor;width:100%;min-width:4em;position:relative;margin-top:0.15em;padding-top:0.1em"
        >
          <Show when={node.rule}>
            {ruleChip({
              rule: node.rule!,
              opts,
              nodeId: node.id,
              class: 'buss-rule',
              style: 'position:absolute;right:-0.25em;top:-0.55em;transform:translateX(100%);font-size:0.75em;font-style:italic;color:#888;white-space:nowrap;padding-left:0.25em',
            })}
          </Show>
        </div>
      </Show>
      <div class="buss-seq" style={`padding:0.15em 0.3em;font-family:ui-monospace,monospace;white-space:nowrap${matchStyle(node.id, opts)}`}>
        {seq()}
      </div>
    </div>
  );
}

function BussproofsLayout(props: { tree: ProofTreeV1; opts: RenderOpts }) {
  return (
    <div class="proof-layout-bussproofs" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <BussNode node={props.tree.root} pool={props.tree.formulas} depth={0} opts={props.opts} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Gentzen — like bussproofs but explicit rule-name chip to the right of every
// bar (redundant with bussproofs' in-margin label, but visually louder).
// ──────────────────────────────────────────────────────────────────────────
function GentzenNode(props: { node: ProofNode; pool: Pool; depth: number; opts: RenderOpts }) {
  const { node, pool, opts } = props;
  const [expanded, setExpanded] = createSignal(false);
  const shouldFold = () =>
    props.depth >= opts.foldDepth &&
    node.premises.length > 0 &&
    !expanded() &&
    !forceOpen(node.id, opts);
  const seq = () =>
    opts.skeleton ? SKELETON_GLYPH : renderSequent(node.sequent, pool);
  return (
    <div data-proof-node={node.id} class="gentzen-node" style="display:inline-flex;flex-direction:column;align-items:stretch;margin:0 0.5em">
      <Show when={node.premises.length > 0}>
        <Show
          when={!shouldFold()}
          fallback={
            <div style="padding:0 0.5em 0.3em 0.5em;text-align:center">
              <FoldButton onClick={() => setExpanded(true)} nodeId={node.id} opts={opts} />
            </div>
          }
        >
          <div style="display:flex;flex-direction:row;align-items:flex-end;justify-content:center">
            <For each={node.premises}>
              {(p) => <GentzenNode node={p} pool={pool} depth={props.depth + 1} opts={opts} />}
            </For>
          </div>
        </Show>
        <div style="display:flex;flex-direction:row;align-items:center;gap:0.5em;border-top:1px solid currentColor;margin-top:0.15em;padding-top:0.1em">
          <div style="flex:1" />
          <Show when={node.rule}>
            {ruleChip({
              rule: node.rule!,
              opts,
              nodeId: node.id,
              style: 'font-size:0.7em;background:#eef;color:#225;border:1px solid #99c;border-radius:3px;padding:0 0.3em;white-space:nowrap',
            })}
          </Show>
        </div>
      </Show>
      <div style={`padding:0.15em 0.3em;font-family:ui-monospace,monospace;text-align:center;white-space:nowrap${matchStyle(node.id, opts)}`}>
        {seq()}
      </div>
    </div>
  );
}

function GentzenLayout(props: { tree: ProofTreeV1; opts: RenderOpts }) {
  return (
    <div class="proof-layout-gentzen" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <GentzenNode node={props.tree.root} pool={props.tree.formulas} depth={0} opts={props.opts} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Tactic — linear pre-order traversal: `apply <rule>; …`. Coq/Isabelle style.
// Skeleton mode drops the sequent column; fold-stubs condense subtrees
// deeper than foldDepth into a single expandable `…` line.
// ──────────────────────────────────────────────────────────────────────────
function TacticEntry(props: { node: ProofNode; pool: Pool; depth: number; opts: RenderOpts }) {
  const { node, pool, opts } = props;
  const [expanded, setExpanded] = createSignal(false);
  const shouldFold = () =>
    props.depth >= opts.foldDepth &&
    node.premises.length > 0 &&
    !expanded() &&
    !forceOpen(node.id, opts);
  const pad = '  '.repeat(props.depth);
  const ruleName = node.rule || 'goal';
  const spacer = ' '.repeat(Math.max(1, 14 - ruleName.length));
  const slug = node.rule ? opts.slugs[node.rule] : undefined;
  const stats = opts.stats.get(node.id);
  const seq = () =>
    opts.skeleton ? '' : renderSequent(node.sequent, pool);
  const hl = matchStyle(node.id, opts);
  return (
    <>
      <span data-proof-node={node.id} style={hl}>
        <span>{pad}</span>
        <Show when={slug} fallback={<span>{ruleName}</span>}>
          <a href={`/def/${slug}`} class="calc-proof-rule" data-rule={ruleName}
             title={`${ruleName} — ${statsTooltip(stats)}`}
             style="text-decoration:none;color:#225">{ruleName}</a>
        </Show>
        <span>{spacer}{seq()}</span>
      </span>
      <span>{'\n'}</span>
      <Show when={shouldFold()} fallback={
        <For each={node.premises}>
          {(p) => <TacticEntry node={p} pool={pool} depth={props.depth + 1} opts={opts} />}
        </For>
      }>
        <span>{'  '.repeat(props.depth + 1)}</span>
        <button
          type="button"
          class="calc-proof-fold"
          onClick={() => setExpanded(true)}
          title={`Expand — ${statsTooltip(stats)}`}
          style="font-family:inherit;font-size:inherit;background:#f0f0f5;color:#555;border:1px dashed #aaa;border-radius:3px;padding:0 0.4em;cursor:pointer"
        >⋯ {statsBadge(stats)}</button>
        <span>{'\n'}</span>
      </Show>
    </>
  );
}

function TacticLayout(props: { tree: ProofTreeV1; opts: RenderOpts }) {
  return (
    <pre class="proof-layout-tactic" style="font-family:ui-monospace,monospace;font-size:0.85em;line-height:1.5;padding:1rem;background:#f8f8f8;border-radius:4px;overflow-x:auto;white-space:pre;margin:0">
      <TacticEntry node={props.tree.root} pool={props.tree.formulas} depth={0} opts={props.opts} />
    </pre>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Indented — foldable tree. `foldDepth` is the initial open-depth; subtrees
// below that start collapsed, same semantics as the other layouts now.
// ──────────────────────────────────────────────────────────────────────────
function IndentedNode(props: { node: ProofNode; pool: Pool; depth: number; opts: RenderOpts }) {
  const { node, pool, depth, opts } = props;
  const [open, setOpen] = createSignal(depth < opts.foldDepth);
  const seq = () =>
    opts.skeleton ? '' : renderSequent(node.sequent, pool);
  const hasKids = node.premises.length > 0;
  const stats = opts.stats.get(node.id);
  // Force-open whenever this subtree contains a search match.
  const isOpen = () => open() || forceOpen(node.id, opts);
  return (
    <div data-proof-node={node.id} style={`margin-left:${depth * 1.25}em;font-family:ui-monospace,monospace;font-size:0.9em;line-height:1.5`}>
      <div style={`display:flex;gap:0.5em;align-items:baseline;white-space:nowrap${matchStyle(node.id, opts)}`}>
        <Show when={hasKids}>
          <button
            type="button"
            onClick={() => setOpen(!open())}
            title={statsTooltip(stats)}
            style="border:none;background:none;font-family:inherit;cursor:pointer;padding:0;width:1em;color:#666"
            aria-label={isOpen() ? 'collapse' : 'expand'}
          >
            {isOpen() ? '▾' : '▸'}
          </button>
        </Show>
        <Show when={!hasKids}>
          <span style="width:1em">·</span>
        </Show>
        <Show when={node.rule}>
          {ruleChip({
            rule: node.rule!,
            opts,
            nodeId: node.id,
            style: 'color:#4a6;font-style:italic',
          })}
        </Show>
        <Show when={hasKids && !isOpen()}>
          <span style="color:#999;font-size:0.85em">{statsBadge(stats)}</span>
        </Show>
        <span>{seq()}</span>
      </div>
      <Show when={isOpen() && hasKids}>
        <For each={node.premises}>
          {(p) => <IndentedNode node={p} pool={pool} depth={depth + 1} opts={opts} />}
        </For>
      </Show>
    </div>
  );
}

function IndentedLayout(props: { tree: ProofTreeV1; opts: RenderOpts }) {
  return (
    <div class="proof-layout-indented" style="padding:0.5rem">
      <IndentedNode node={props.tree.root} pool={props.tree.formulas} depth={0} opts={props.opts} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Flipped — root at top, premises below. Same data, inverted.
// ──────────────────────────────────────────────────────────────────────────
function FlippedNode(props: { node: ProofNode; pool: Pool; depth: number; opts: RenderOpts }) {
  const { node, pool, opts } = props;
  const [expanded, setExpanded] = createSignal(false);
  const shouldFold = () =>
    props.depth >= opts.foldDepth &&
    node.premises.length > 0 &&
    !expanded() &&
    !forceOpen(node.id, opts);
  const seq = () =>
    opts.skeleton ? SKELETON_GLYPH : renderSequent(node.sequent, pool);
  return (
    <div data-proof-node={node.id} class="flipped-node" style="display:inline-flex;flex-direction:column;align-items:center;margin:0 0.75em">
      <div style={`padding:0.15em 0.3em;font-family:ui-monospace,monospace;white-space:nowrap${matchStyle(node.id, opts)}`}>
        {seq()}
      </div>
      <Show when={node.premises.length > 0}>
        <div
          style="border-bottom:1px solid currentColor;width:100%;min-width:4em;position:relative;margin-bottom:0.15em;padding-bottom:0.1em"
        >
          <Show when={node.rule}>
            {ruleChip({
              rule: node.rule!,
              opts,
              nodeId: node.id,
              style: 'position:absolute;right:-0.25em;bottom:-0.55em;transform:translateX(100%);font-size:0.75em;font-style:italic;color:#888;white-space:nowrap',
            })}
          </Show>
        </div>
        <Show
          when={!shouldFold()}
          fallback={
            <div style="padding:0.3em 0.5em">
              <FoldButton onClick={() => setExpanded(true)} nodeId={node.id} opts={opts} />
            </div>
          }
        >
          <div style="display:flex;flex-direction:row;align-items:flex-start">
            <For each={node.premises}>
              {(p) => <FlippedNode node={p} pool={pool} depth={props.depth + 1} opts={opts} />}
            </For>
          </div>
        </Show>
      </Show>
    </div>
  );
}

function FlippedLayout(props: { tree: ProofTreeV1; opts: RenderOpts }) {
  return (
    <div class="proof-layout-flipped" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <FlippedNode node={props.tree.root} pool={props.tree.formulas} depth={0} opts={props.opts} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Public dispatch
// ──────────────────────────────────────────────────────────────────────────
const DEFAULT_OPTS: RenderOpts = {
  slugs: {},
  skeleton: false,
  foldDepth: Infinity,
  stats: new Map(),
  search: EMPTY_SEARCH,
};

// A node is "forced open" when it or any descendant matches the active
// search — ensures matches are never hidden behind a fold-stub.
function forceOpen(id: string, opts: RenderOpts): boolean {
  return opts.search.ancestors.has(id) || opts.search.matches.has(id);
}
function matchStyle(id: string, opts: RenderOpts): string {
  return opts.search.matches.has(id)
    ? `;background:${MATCH_BG};outline:${MATCH_OUTLINE};border-radius:3px`
    : '';
}

export function renderLayout(
  layout: ProofLayout,
  tree: ProofTreeV1,
  opts: Partial<RenderOpts> = {},
) {
  const full: RenderOpts = { ...DEFAULT_OPTS, ...opts };
  switch (layout) {
    case 'bussproofs': return <BussproofsLayout tree={tree} opts={full} />;
    case 'gentzen':    return <GentzenLayout tree={tree} opts={full} />;
    case 'tactic':     return <TacticLayout tree={tree} opts={full} />;
    case 'indented':   return <IndentedLayout tree={tree} opts={full} />;
    case 'flipped':    return <FlippedLayout tree={tree} opts={full} />;
  }
}
