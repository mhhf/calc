/**
 * ForwardTrace — viewer for `forward-trace/v1` payloads (mode: symex | exec).
 *
 * Sibling of the backward-proof viewer (ProofBlock.tsx). The backward one
 * ships a full proof tree and renders it through one of five layouts;
 * this one ships:
 *
 *   • a tree SKELETON (just rule names + structural type — no state),
 *   • a LEAVES array (per-leaf final state + status + step count),
 *
 * and fetches per-leaf TRACE steps lazily via POST /api/proof/leaf-trace
 * to keep first paint small. Real programs blow past 2000 tree nodes and
 * 8000+ trace steps — inlining traces would be megabytes over the wire.
 *
 * Navigation model:
 *   1. The header shows counts (nodes / leaves / depth / steps).
 *   2. The tree pane shows the branching skeleton; single-child chains
 *      collapse into breadcrumb trails (`rule1 → rule2 → rule3`) to keep
 *      density high. Click a leaf to select it.
 *   3. The leaves pane lists every leaf with its status badge and final
 *      state; click to select.
 *   4. The trace pane shows the selected leaf's rule-application sequence
 *      (lazy-fetched on first selection, cached thereafter).
 */
import { createMemo, createResource, createSignal, For, Show } from 'solid-js';
import { renderFormula } from './formula';
import type {
  ForwardTraceV1,
  ForwardNode,
  ForwardLeafSummary,
  ForwardLeafDetail,
  LeafStatus,
  FormulaAST,
} from './types';

interface Props {
  source: string;
  calculus: string;
  profile: string;
  tree: ForwardTraceV1;
}

type Pool = Record<string, FormulaAST>;

const STATUS_COLOR: Record<LeafStatus, { fg: string; bg: string; border: string }> = {
  STOP:     { fg: '#1b5e20', bg: '#e8f5e9', border: '#a5d6a7' },
  REVERT:   { fg: '#8a6d0b', bg: '#fff8e1', border: '#ffe082' },
  INVALID:  { fg: '#b71c1c', bg: '#ffebee', border: '#ef9a9a' },
  RUNNING:  { fg: '#0d47a1', bg: '#e3f2fd', border: '#90caf9' },
  STUCK:    { fg: '#4a148c', bg: '#f3e5f5', border: '#ce93d8' },
  NO_STATE: { fg: '#555',    bg: '#f5f5f5', border: '#ddd'    },
};

function statusPill(s: LeafStatus) {
  const c = STATUS_COLOR[s] || STATUS_COLOR.NO_STATE;
  return (
    <span
      style={`display:inline-block;padding:0 0.4em;border-radius:3px;font-size:0.75em;font-weight:600;color:${c.fg};background:${c.bg};border:1px solid ${c.border}`}
    >
      {s}
    </span>
  );
}

function renderState(
  state: { linear: Array<[string, number]>; persistent: string[] } | undefined,
  pool: Pool,
  opts: { maxEntries?: number } = {},
): string {
  if (!state) return '(no state)';
  const max = opts.maxEntries ?? 40;
  const parts: string[] = [];
  for (const [ref, n] of state.linear) {
    if (parts.length >= max) { parts.push('…'); break; }
    const txt = renderFormula(ref, pool);
    parts.push(n === 1 ? txt : `${txt}×${n}`);
  }
  for (const ref of state.persistent) {
    if (parts.length >= max) { parts.push('…'); break; }
    parts.push('!' + renderFormula(ref, pool));
  }
  return parts.length === 0 ? '∅' : parts.join(' · ');
}

/**
 * Collapse single-child branches into `rule1 → rule2 → rule3 → child`
 * chains. Returns the "effective" prefix of rule labels and the first
 * branching descendant. Cuts the visual depth of an EVM trace from
 * hundreds of rows to tens.
 */
function collapseChain(node: ForwardNode): { rules: string[]; tip: ForwardNode } {
  const rules: string[] = [];
  let cur: ForwardNode = node;
  while (cur.type === 'branch' && cur.children.length === 1) {
    rules.push(String(cur.children[0].rule));
    cur = cur.children[0].child;
  }
  return { rules, tip: cur };
}

/** Recursive tree row — collapsed single-child chains, click leaves to select. */
function TreeNode(props: {
  node: ForwardNode;
  depth: number;
  selectedLeaf: () => number | null;
  onLeafClick: (i: number) => void;
  rulePrefix?: string[];
}) {
  const chain = createMemo(() => collapseChain(props.node));
  const [expanded, setExpanded] = createSignal(props.depth < 2);

  return (
    <Show
      when={chain().tip.type === 'branch' && (chain().tip as { children: unknown[] }).children.length > 1}
      fallback={
        <TerminalRow
          node={chain().tip}
          depth={props.depth}
          rules={[...(props.rulePrefix || []), ...chain().rules]}
          selectedLeaf={props.selectedLeaf}
          onLeafClick={props.onLeafClick}
        />
      }
    >
      <BranchRow
        node={chain().tip}
        depth={props.depth}
        rules={[...(props.rulePrefix || []), ...chain().rules]}
        expanded={expanded}
        toggle={() => setExpanded((v) => !v)}
        selectedLeaf={props.selectedLeaf}
        onLeafClick={props.onLeafClick}
      />
    </Show>
  );
}

function ChainBreadcrumb(props: { rules: string[] }) {
  return (
    <Show when={props.rules.length > 0}>
      <span style="color:#888;font-family:monospace;font-size:0.85em">
        {props.rules.join(' → ')}
        <span style="color:#bbb"> → </span>
      </span>
    </Show>
  );
}

function TerminalRow(props: {
  node: ForwardNode;
  depth: number;
  rules: string[];
  selectedLeaf: () => number | null;
  onLeafClick: (i: number) => void;
}) {
  const indent = `${props.depth * 1.2}em`;
  if (props.node.type === 'leaf') {
    const idx = props.node.leafIndex;
    const st = props.node.status;
    return (
      <div
        style={`padding:2px 4px 2px ${indent};cursor:pointer;border-radius:3px;${props.selectedLeaf() === idx ? 'background:#fff3c4;' : ''}`}
        onClick={() => props.onLeafClick(idx)}
      >
        <ChainBreadcrumb rules={props.rules} />
        <span style="font-family:monospace;font-size:0.85em">
          leaf #{idx}
        </span>
        {' '}
        {statusPill(st)}
      </div>
    );
  }
  // bound / cycle / memo / dead — terminal marker
  return (
    <div style={`padding:2px 4px 2px ${indent};color:#888;font-family:monospace;font-size:0.85em`}>
      <ChainBreadcrumb rules={props.rules} />
      <span style="font-style:italic">[{props.node.type}]</span>
    </div>
  );
}

function BranchRow(props: {
  node: ForwardNode;
  depth: number;
  rules: string[];
  expanded: () => boolean;
  toggle: () => void;
  selectedLeaf: () => number | null;
  onLeafClick: (i: number) => void;
}) {
  const indent = `${props.depth * 1.2}em`;
  const childCount = () => (props.node.type === 'branch' ? props.node.children.length : 0);
  return (
    <>
      <div style={`padding:2px 4px 2px ${indent};cursor:pointer;user-select:none`} onClick={props.toggle}>
        <span style="color:#558;font-weight:600;margin-right:0.25em">{props.expanded() ? '▾' : '▸'}</span>
        <ChainBreadcrumb rules={props.rules} />
        <span style="font-family:monospace;font-size:0.85em;color:#334">
          {childCount()} branches
        </span>
      </div>
      <Show when={props.expanded() && props.node.type === 'branch'}>
        <For each={(props.node as { children: Array<{ rule: string; child: ForwardNode }> }).children}>
          {(c) => (
            <TreeNode
              node={c.child}
              depth={props.depth + 1}
              selectedLeaf={props.selectedLeaf}
              onLeafClick={props.onLeafClick}
              rulePrefix={[String(c.rule)]}
            />
          )}
        </For>
      </Show>
    </>
  );
}

async function fetchLeafTrace(args: {
  source: string;
  calculus: string;
  profile: string;
  leafIndex: number;
}): Promise<{ ok: boolean; leaf?: ForwardLeafDetail; error?: string }> {
  const res = await fetch('/api/proof/leaf-trace', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(args),
  });
  if (!res.ok) return { ok: false, error: `HTTP ${res.status}` };
  return res.json();
}

export function ForwardTrace(props: Props) {
  const [selectedLeaf, setSelectedLeaf] = createSignal<number | null>(null);

  // Trace fetch is per-selected-leaf. createResource auto-refetches when
  // `selectedLeaf()` changes; cached trace from a prior selection stays
  // in the component state via `traceCache`.
  const traceCache = new Map<number, ForwardLeafDetail>();
  const [leafDetail] = createResource(
    () => selectedLeaf(),
    async (idx) => {
      if (idx === null) return null;
      const cached = traceCache.get(idx);
      if (cached) return cached;
      const r = await fetchLeafTrace({
        source: props.source,
        calculus: props.calculus,
        profile: props.profile,
        leafIndex: idx,
      });
      if (r.ok && r.leaf) {
        traceCache.set(idx, r.leaf);
        return r.leaf;
      }
      return null;
    },
  );

  const leaves = () => props.tree.leaves;
  const stats = () => props.tree.stats;
  const pool = () => props.tree.formulas;

  const selectedSummary = createMemo<ForwardLeafSummary | null>(() => {
    const idx = selectedLeaf();
    if (idx === null) return null;
    return leaves().find((l) => l.leafIndex === idx) || null;
  });

  return (
    <div style="font-size:0.9em">
      {/* Stats bar */}
      <div style="display:flex;gap:0.8em;flex-wrap:wrap;padding:0.3em 0.6em;background:#fafafa;border-bottom:1px solid #eee;font-size:0.8em;color:#555">
        <span><strong>{stats().totalNodes}</strong> nodes</span>
        <span><strong>{stats().leafCount}</strong> leaves</span>
        <span>depth <strong>{stats().maxDepth}</strong></span>
        <span><strong>{stats().totalTraceSteps}</strong> trace steps</span>
        <span>max trace len <strong>{stats().maxTraceLen}</strong></span>
      </div>

      {/* Initial state */}
      <Show when={props.tree.initial && (props.tree.initial.linear.length > 0 || props.tree.initial.persistent.length > 0)}>
        <div style="padding:0.4em 0.6em;border-bottom:1px solid #eee;font-size:0.8em">
          <span style="color:#888;margin-right:0.4em">initial:</span>
          <span style="font-family:monospace;color:#334">
            {renderState(props.tree.initial, pool())}
          </span>
        </div>
      </Show>

      {/* Three-pane layout: tree | leaves | trace */}
      <div style="display:grid;grid-template-columns:minmax(0,1fr) minmax(0,1fr) minmax(0,1.2fr);gap:0;border-top:1px solid #eee">
        {/* Tree pane */}
        <div style="border-right:1px solid #eee;max-height:600px;overflow:auto">
          <div style="padding:0.3em 0.6em;border-bottom:1px solid #f0f0f0;background:#fafafa;font-size:0.75em;color:#888;position:sticky;top:0">
            tree
          </div>
          <div style="padding:0.3em 0">
            <TreeNode
              node={props.tree.tree}
              depth={0}
              selectedLeaf={selectedLeaf}
              onLeafClick={setSelectedLeaf}
            />
          </div>
        </div>

        {/* Leaves pane */}
        <div style="border-right:1px solid #eee;max-height:600px;overflow:auto">
          <div style="padding:0.3em 0.6em;border-bottom:1px solid #f0f0f0;background:#fafafa;font-size:0.75em;color:#888;position:sticky;top:0">
            leaves ({leaves().length})
          </div>
          <For each={leaves()}>
            {(leaf) => (
              <div
                style={`padding:0.3em 0.5em;cursor:pointer;border-bottom:1px solid #f5f5f5;${selectedLeaf() === leaf.leafIndex ? 'background:#fff3c4;' : ''}`}
                onClick={() => setSelectedLeaf(leaf.leafIndex)}
              >
                <div style="display:flex;align-items:center;gap:0.4em;margin-bottom:0.15em">
                  <span style="font-family:monospace;font-size:0.85em;color:#667">#{leaf.leafIndex}</span>
                  {statusPill(leaf.status)}
                  <span style="color:#999;font-size:0.8em">{leaf.stepCount} steps</span>
                </div>
                <div style="font-family:monospace;font-size:0.72em;color:#555;word-break:break-word;line-height:1.3">
                  {renderState(leaf.state, pool(), { maxEntries: 8 })}
                </div>
              </div>
            )}
          </For>
        </div>

        {/* Trace pane */}
        <div style="max-height:600px;overflow:auto">
          <div style="padding:0.3em 0.6em;border-bottom:1px solid #f0f0f0;background:#fafafa;font-size:0.75em;color:#888;position:sticky;top:0">
            trace
          </div>
          <Show
            when={selectedLeaf() !== null}
            fallback={
              <div style="padding:1em;color:#999;font-style:italic">
                Select a leaf to view its trace.
              </div>
            }
          >
            <Show when={leafDetail.loading}>
              <div style="padding:0.6em;color:#888;font-style:italic;font-size:0.85em">Loading trace…</div>
            </Show>
            <Show when={!leafDetail.loading && leafDetail()}>
              {(() => {
                const d = leafDetail()!;
                const sum = selectedSummary();
                const tracePool = { ...pool(), ...d.formulas };
                return (
                  <div>
                    <div style="padding:0.4em 0.6em;border-bottom:1px solid #f0f0f0;font-size:0.8em">
                      <span style="font-family:monospace;color:#667">leaf #{d.leafIndex}</span>
                      {' '}
                      {statusPill(d.status)}
                      <span style="color:#999;margin-left:0.4em">· {d.stepCount} steps</span>
                    </div>
                    <Show when={sum}>
                      <div style="padding:0.4em 0.6em;border-bottom:1px solid #f5f5f5;font-size:0.75em;color:#555">
                        <span style="color:#888;margin-right:0.3em">final:</span>
                        <span style="font-family:monospace">
                          {renderState(d.state, tracePool, { maxEntries: 40 })}
                        </span>
                      </div>
                    </Show>
                    <div>
                      <For each={d.trace}>
                        {(step) => (
                          <div style="padding:0.25em 0.6em;border-bottom:1px solid #f9f9f9;font-size:0.78em;display:grid;grid-template-columns:3em 1fr;gap:0.5em">
                            <span style="color:#aaa;font-family:monospace;text-align:right">{step.step}</span>
                            <div>
                              <div style="font-family:monospace;color:#224;font-weight:600">{step.ruleName}</div>
                              <Show when={step.consumed.length > 0}>
                                <div style="color:#777;font-family:monospace;font-size:0.92em;margin-top:0.1em">
                                  consumed:{' '}
                                  {step.consumed.map(([ref, n]) => {
                                    const txt = renderFormula(ref, tracePool);
                                    return n === 1 ? txt : `${txt}×${n}`;
                                  }).join(' · ')}
                                </div>
                              </Show>
                            </div>
                          </div>
                        )}
                      </For>
                    </div>
                  </div>
                );
              })()}
            </Show>
            <Show when={!leafDetail.loading && !leafDetail()}>
              <div style="padding:0.6em;color:#a33;font-size:0.85em">Failed to load trace.</div>
            </Show>
          </Show>
        </div>
      </div>
    </div>
  );
}
