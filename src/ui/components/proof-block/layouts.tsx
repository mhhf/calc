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
 */
import { For, Show, createSignal } from 'solid-js';
import type { ProofNode, ProofTreeV1, ProofLayout } from './types';
import { renderSequent } from './formula';

type Pool = ProofTreeV1['formulas'];

// ──────────────────────────────────────────────────────────────────────────
// Bussproofs — conclusion at the bottom, rule bar above it with premises
// stacked above the bar. Classical mathematical convention.
// ──────────────────────────────────────────────────────────────────────────
function BussNode(props: { node: ProofNode; pool: Pool }) {
  const { node, pool } = props;
  const seq = renderSequent(node.sequent, pool);
  return (
    <div class="buss-node" style="display:inline-flex;flex-direction:column;align-items:center;margin:0 0.75em;vertical-align:bottom">
      <Show when={node.premises.length > 0}>
        <div class="buss-premises" style="display:flex;flex-direction:row;align-items:flex-end">
          <For each={node.premises}>{(p) => <BussNode node={p} pool={pool} />}</For>
        </div>
        <div
          class="buss-bar"
          style="border-top:1px solid currentColor;width:100%;min-width:4em;position:relative;margin-top:0.15em;padding-top:0.1em"
        >
          <Show when={node.rule}>
            <span
              class="buss-rule calc-proof-rule"
              data-rule={node.rule!}
              title={`Rule: ${node.rule}`}
              style="position:absolute;right:-0.25em;top:-0.55em;transform:translateX(100%);font-size:0.75em;font-style:italic;color:#888;white-space:nowrap;padding-left:0.25em"
            >
              {node.rule}
            </span>
          </Show>
        </div>
      </Show>
      <div class="buss-seq" style="padding:0.15em 0.3em;font-family:ui-monospace,monospace;white-space:nowrap">
        {seq}
      </div>
    </div>
  );
}

function BussproofsLayout(props: { tree: ProofTreeV1 }) {
  return (
    <div class="proof-layout-bussproofs" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <BussNode node={props.tree.root} pool={props.tree.formulas} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Gentzen — like bussproofs but explicit rule-name chip to the right of every
// bar (redundant with bussproofs' in-margin label, but visually louder).
// ──────────────────────────────────────────────────────────────────────────
function GentzenNode(props: { node: ProofNode; pool: Pool }) {
  const { node, pool } = props;
  const seq = renderSequent(node.sequent, pool);
  return (
    <div class="gentzen-node" style="display:inline-flex;flex-direction:column;align-items:stretch;margin:0 0.5em">
      <Show when={node.premises.length > 0}>
        <div style="display:flex;flex-direction:row;align-items:flex-end;justify-content:center">
          <For each={node.premises}>{(p) => <GentzenNode node={p} pool={pool} />}</For>
        </div>
        <div style="display:flex;flex-direction:row;align-items:center;gap:0.5em;border-top:1px solid currentColor;margin-top:0.15em;padding-top:0.1em">
          <div style="flex:1" />
          <Show when={node.rule}>
            <span
              class="calc-proof-rule"
              data-rule={node.rule!}
              title={`Rule: ${node.rule}`}
              style="font-size:0.7em;background:#eef;color:#225;border:1px solid #99c;border-radius:3px;padding:0 0.3em;white-space:nowrap"
            >
              {node.rule}
            </span>
          </Show>
        </div>
      </Show>
      <div style="padding:0.15em 0.3em;font-family:ui-monospace,monospace;text-align:center;white-space:nowrap">
        {seq}
      </div>
    </div>
  );
}

function GentzenLayout(props: { tree: ProofTreeV1 }) {
  return (
    <div class="proof-layout-gentzen" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <GentzenNode node={props.tree.root} pool={props.tree.formulas} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Tactic — linear pre-order traversal: `apply <rule>; …`. Coq/Isabelle style.
// ──────────────────────────────────────────────────────────────────────────
function collectTactic(node: ProofNode, pool: Pool, depth: number, out: string[]) {
  const seq = renderSequent(node.sequent, pool);
  const rule = node.rule || 'goal';
  const pad = '  '.repeat(depth);
  out.push(`${pad}${rule.padEnd(14)}${seq}`);
  for (const p of node.premises) collectTactic(p, pool, depth + 1, out);
}

function TacticLayout(props: { tree: ProofTreeV1 }) {
  const lines: string[] = [];
  collectTactic(props.tree.root, props.tree.formulas, 0, lines);
  return (
    <pre class="proof-layout-tactic" style="font-family:ui-monospace,monospace;font-size:0.85em;line-height:1.5;padding:1rem;background:#f8f8f8;border-radius:4px;overflow-x:auto;white-space:pre">
      {lines.join('\n')}
    </pre>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Indented — foldable tree (depth fold at init, click to expand).
// ──────────────────────────────────────────────────────────────────────────
function IndentedNode(props: { node: ProofNode; pool: Pool; depth: number; foldThreshold: number }) {
  const { node, pool, depth, foldThreshold } = props;
  const [open, setOpen] = createSignal(depth < foldThreshold);
  const seq = renderSequent(node.sequent, pool);
  const hasKids = node.premises.length > 0;
  return (
    <div style={`margin-left:${depth * 1.25}em;font-family:ui-monospace,monospace;font-size:0.9em;line-height:1.5`}>
      <div style="display:flex;gap:0.5em;align-items:baseline;white-space:nowrap">
        <Show when={hasKids}>
          <button
            type="button"
            onClick={() => setOpen(!open())}
            style="border:none;background:none;font-family:inherit;cursor:pointer;padding:0;width:1em;color:#666"
            aria-label={open() ? 'collapse' : 'expand'}
          >
            {open() ? '▾' : '▸'}
          </button>
        </Show>
        <Show when={!hasKids}>
          <span style="width:1em">·</span>
        </Show>
        <Show when={node.rule}>
          <span style="color:#4a6;font-style:italic">{node.rule}</span>
        </Show>
        <span>{seq}</span>
      </div>
      <Show when={open() && hasKids}>
        <For each={node.premises}>
          {(p) => <IndentedNode node={p} pool={pool} depth={depth + 1} foldThreshold={foldThreshold} />}
        </For>
      </Show>
    </div>
  );
}

function IndentedLayout(props: { tree: ProofTreeV1; foldThreshold?: number }) {
  return (
    <div class="proof-layout-indented" style="padding:0.5rem">
      <IndentedNode
        node={props.tree.root}
        pool={props.tree.formulas}
        depth={0}
        foldThreshold={props.foldThreshold ?? 6}
      />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Flipped — root at top, premises below. Same data, inverted.
// ──────────────────────────────────────────────────────────────────────────
function FlippedNode(props: { node: ProofNode; pool: Pool }) {
  const { node, pool } = props;
  const seq = renderSequent(node.sequent, pool);
  return (
    <div class="flipped-node" style="display:inline-flex;flex-direction:column;align-items:center;margin:0 0.75em">
      <div style="padding:0.15em 0.3em;font-family:ui-monospace,monospace;white-space:nowrap">
        {seq}
      </div>
      <Show when={node.premises.length > 0}>
        <div
          style="border-bottom:1px solid currentColor;width:100%;min-width:4em;position:relative;margin-bottom:0.15em;padding-bottom:0.1em"
        >
          <Show when={node.rule}>
            <span style="position:absolute;right:-0.25em;bottom:-0.55em;transform:translateX(100%);font-size:0.75em;font-style:italic;color:#888;white-space:nowrap">
              {node.rule}
            </span>
          </Show>
        </div>
        <div style="display:flex;flex-direction:row;align-items:flex-start">
          <For each={node.premises}>{(p) => <FlippedNode node={p} pool={pool} />}</For>
        </div>
      </Show>
    </div>
  );
}

function FlippedLayout(props: { tree: ProofTreeV1 }) {
  return (
    <div class="proof-layout-flipped" style="overflow-x:auto;padding:1rem 0.5rem;text-align:center">
      <FlippedNode node={props.tree.root} pool={props.tree.formulas} />
    </div>
  );
}

// ──────────────────────────────────────────────────────────────────────────
// Public dispatch
// ──────────────────────────────────────────────────────────────────────────
export function renderLayout(layout: ProofLayout, tree: ProofTreeV1) {
  switch (layout) {
    case 'bussproofs': return <BussproofsLayout tree={tree} />;
    case 'gentzen':    return <GentzenLayout tree={tree} />;
    case 'tactic':     return <TacticLayout tree={tree} />;
    case 'indented':   return <IndentedLayout tree={tree} />;
    case 'flipped':    return <FlippedLayout tree={tree} />;
  }
}
