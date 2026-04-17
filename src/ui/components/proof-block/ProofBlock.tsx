/**
 * ProofBlock — client-side hydrator for `{proof <calculus> [profile]}` blocks
 * embedded in markdown.
 *
 * Contract:
 *   The markdown processor (src/ui/lib/markdown.ts) emits a placeholder div
 *   with `data-processor="proof-tree"` plus calculus/profile attributes and a
 *   child <script type="application/x-calc-proof-source"> holding the raw
 *   source. `hydrateProofBlocks(root)` finds those divs, mounts a ProofBlock
 *   component into each, and the component fetches POST /api/proof to turn
 *   source → proof-tree/v1 JSON on first render.
 *
 *   Layout selection persists per-browser in localStorage. Switching layouts
 *   never re-fetches — the tree JSON is the shared source of truth, and each
 *   renderer is a pure function.
 */
import { createEffect, createMemo, createSignal, createResource, Show, For } from 'solid-js';
import { render } from 'solid-js/web';
import { renderLayout } from './layouts';
import { PROOF_LAYOUTS } from './types';
import { computeStats, tooltip as statsTooltip } from './stats';
import { buildSearch, EMPTY_SEARCH } from './search';
import type { ProofLayout, ProofTreeV1 } from './types';

const LS_LAYOUT = 'calc.proofBlock.layout';
const LS_SKELETON = 'calc.proofBlock.skeleton';

// Phase A default: fold beyond depth 3. Deep enough to show the overall
// shape of most proofs without pre-expanding ladders hundreds of levels
// deep (`tensor128` weighs in at depth 128 — see
// doc/documentation/large-proof-trees.md).
const DEFAULT_FOLD_DEPTH = 3;

function readLayout(): ProofLayout {
  try {
    const raw = localStorage.getItem(LS_LAYOUT);
    if (raw && PROOF_LAYOUTS.some((l) => l.id === raw)) return raw as ProofLayout;
  } catch {}
  return 'bussproofs';
}

function writeLayout(l: ProofLayout) {
  try { localStorage.setItem(LS_LAYOUT, l); } catch {}
}

function readSkeleton(): boolean {
  try { return localStorage.getItem(LS_SKELETON) === '1'; } catch { return false; }
}

function writeSkeleton(on: boolean) {
  try { localStorage.setItem(LS_SKELETON, on ? '1' : '0'); } catch {}
}

interface ProofApiResult {
  ok: boolean;
  tree?: ProofTreeV1;
  error?: string;
  cacheHit?: boolean;
}

async function fetchProof(args: {
  source: string;
  calculus: string;
  profile: string;
  mode: string;
}): Promise<ProofApiResult> {
  const res = await fetch('/api/proof', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify(args),
  });
  if (!res.ok) return { ok: false, error: `HTTP ${res.status}` };
  return res.json();
}

// Module-level singleton — rule→slug map derived from the doc-manifest's
// `def/` folder entries. Each rule doc is slugged `<NNNN>_rule-<name>`, so we
// build `{ <name>: "<NNNN>_rule-<name>" }` once per session. Returns {} on
// failure so layouts fall back to plain (unlinked) chips.
let ruleSlugPromise: Promise<Record<string, string>> | null = null;
function fetchRuleSlugs(): Promise<Record<string, string>> {
  if (!ruleSlugPromise) {
    ruleSlugPromise = fetch('/api/doc-manifest')
      .then((r) => (r.ok ? r.json() : {}))
      .then((m: Record<string, string[]>) => {
        const slugs: string[] = m['def'] || m['/def'] || [];
        const out: Record<string, string> = {};
        for (const s of slugs) {
          const mm = s.match(/^(\d+)_rule-(.+)$/);
          if (mm) out[mm[2]] = s;
        }
        return out;
      })
      .catch(() => ({}));
  }
  return ruleSlugPromise;
}

export function ProofBlock(props: {
  source: string;
  calculus: string;
  profile: string;
  mode: string;
}) {
  const [result] = createResource(
    () => ({ source: props.source, calculus: props.calculus, profile: props.profile, mode: props.mode }),
    fetchProof,
  );
  const [ruleSlugs] = createResource(fetchRuleSlugs);
  const [layout, setLayout] = createSignal<ProofLayout>(readLayout());
  const [skeleton, setSkeleton] = createSignal<boolean>(readSkeleton());
  // Search state is ephemeral — not persisted, not cached across mounts. A
  // single input box drives both substring + `/regex/` modes; the index is
  // derived lazily so idle blocks pay zero cost.
  const [query, setQuery] = createSignal('');
  let bodyRef: HTMLDivElement | undefined;

  // Stats recompute only when the tree changes — not on layout / skeleton /
  // fold toggles. Keeps click-to-expand O(1) for known-size subtrees.
  const stats = createMemo(() => {
    const r = result();
    return r && r.ok && r.tree ? computeStats(r.tree.root) : new Map();
  });
  const rootStats = () => {
    const r = result();
    if (!r || !r.ok || !r.tree) return undefined;
    return stats().get(r.tree.root.id);
  };

  // Search index — recomputes on (tree, query). Cheap enough to inline: a
  // single pre-order walk with a substring test per node, no allocations
  // in the hot path beyond the two Sets. `renderSequent` cost is paid once
  // per node per query edit; for the 255-node tensor128 tree that's ≪1 ms.
  const search = createMemo(() => {
    const r = result();
    if (!r || !r.ok || !r.tree) return EMPTY_SEARCH;
    return buildSearch(r.tree, query());
  });

  // When the search index resolves to a concrete first match, scroll its
  // DOM node into view. The layouts tag each node with `data-proof-node`
  // so we can find them without a react-style ref registry.
  createEffect(() => {
    const s = search();
    if (!s.first || !bodyRef) return;
    const el = bodyRef.querySelector<HTMLElement>(
      `[data-proof-node="${CSS.escape(s.first)}"]`,
    );
    if (el && typeof el.scrollIntoView === 'function') {
      el.scrollIntoView({ block: 'nearest', inline: 'nearest', behavior: 'smooth' });
    }
  });

  return (
    <div class="calc-proof-block" style="border:1px solid #ddd;border-radius:6px;margin:1em 0;background:#fff">
      <div class="calc-proof-header" style="display:flex;align-items:center;gap:0.5em;padding:0.4em 0.6em;border-bottom:1px solid #eee;background:#fafafa;font-size:0.8em;color:#666">
        <span style="font-weight:600">proof</span>
        <span style="opacity:0.7">·</span>
        <span>{props.calculus}</span>
        <Show when={props.mode !== 'sequent'}>
          <span style="opacity:0.7">·</span>
          <span>{props.mode}</span>
        </Show>
        <Show when={props.profile !== 'default'}>
          <span style="opacity:0.7">·</span>
          <span>{props.profile}</span>
        </Show>
        <Show when={rootStats()}>
          <span
            style="opacity:0.7"
            title={statsTooltip(rootStats())}
          >
            · {rootStats()!.nodes}n · ↓{rootStats()!.depth}
          </span>
        </Show>
        <div style="flex:1" />
        <input
          type="search"
          placeholder="search · /regex/"
          value={query()}
          aria-label="Search nodes"
          title="Substring match across rules + sequent text. Prefix with / for regex (e.g. /plus|inc/)."
          onInput={(e) => setQuery(e.currentTarget.value)}
          onKeyDown={(e) => { if (e.key === 'Escape') { setQuery(''); (e.currentTarget as HTMLInputElement).blur(); } }}
          style="font-size:inherit;font-family:inherit;padding:0.1em 0.4em;border:1px solid #ccc;border-radius:3px;width:10em;margin-right:0.4em"
        />
        <Show when={query()}>
          <span
            style={`font-size:0.85em;color:${search().error ? '#a33' : search().count === 0 ? '#999' : '#558'};margin-right:0.4em;white-space:nowrap`}
            title={search().error || ''}
          >
            {search().error ? 'regex err' : `${search().count} hit${search().count === 1 ? '' : 's'}`}
          </span>
        </Show>
        <button
          type="button"
          aria-pressed={skeleton()}
          title={skeleton() ? 'Show sequents' : 'Skeleton: rule names only'}
          onClick={() => { const v = !skeleton(); setSkeleton(v); writeSkeleton(v); }}
          style={`font-size:inherit;padding:0.1em 0.45em;border:1px solid ${skeleton() ? '#558' : '#ccc'};background:${skeleton() ? '#e4e6f5' : '#fff'};color:${skeleton() ? '#224' : '#555'};border-radius:3px;cursor:pointer;font-family:inherit;margin-right:0.4em`}
        >
          skeleton
        </button>
        <div role="tablist" aria-label="Layout" style="display:flex;gap:0.25em">
          <For each={PROOF_LAYOUTS}>
            {(l) => (
              <button
                type="button"
                role="tab"
                aria-selected={layout() === l.id}
                onClick={() => { setLayout(l.id); writeLayout(l.id); }}
                style={`font-size:inherit;padding:0.1em 0.45em;border:1px solid ${layout() === l.id ? '#558' : '#ccc'};background:${layout() === l.id ? '#e4e6f5' : '#fff'};color:${layout() === l.id ? '#224' : '#555'};border-radius:3px;cursor:pointer;font-family:inherit`}
              >
                {l.label}
              </button>
            )}
          </For>
        </div>
      </div>
      <div class="calc-proof-body" ref={bodyRef}>
        <Show when={result.loading}>
          <div style="padding:1em;color:#888;font-style:italic">Proving…</div>
        </Show>
        <Show when={result.error}>
          <pre style="padding:1em;color:#a33;white-space:pre-wrap;margin:0">Error: {String(result.error)}</pre>
        </Show>
        <Show when={result() && !result()!.ok}>
          <pre style="padding:1em;color:#a33;white-space:pre-wrap;margin:0;font-size:0.85em">
            {result()!.error || 'Proof failed (no tree)'}
          </pre>
        </Show>
        <Show when={result() && result()!.ok && result()!.tree}>
          {renderLayout(layout(), result()!.tree!, {
            slugs: ruleSlugs() || {},
            skeleton: skeleton(),
            foldDepth: DEFAULT_FOLD_DEPTH,
            stats: stats(),
            search: search(),
          })}
        </Show>
      </div>
      <Show when={result() && result()!.cacheHit}>
        <div style="font-size:0.7em;color:#aaa;padding:0.2em 0.6em;border-top:1px solid #eee">
          cache hit
        </div>
      </Show>
    </div>
  );
}

/**
 * Find every placeholder div emitted by the markdown processor and mount a
 * ProofBlock into it. Idempotent — already-hydrated divs are skipped.
 */
export function hydrateProofBlocks(root: HTMLElement) {
  const divs = root.querySelectorAll<HTMLDivElement>(
    'div.client-render[data-processor="proof-tree"]:not([data-hydrated])',
  );
  for (const div of Array.from(divs)) {
    // Source lives in a hidden <pre>; reading .textContent correctly
    // decodes HTML entities (unlike a <script>, which is raw-text state).
    const source = div.querySelector('.client-source')?.textContent || '';
    const calculus = div.dataset.calculus || 'ill';
    const profile = div.dataset.profile || 'default';
    const mode = div.dataset.mode || 'sequent';
    div.dataset.hydrated = '1';
    div.innerHTML = '';
    render(() => <ProofBlock source={source} calculus={calculus} profile={profile} mode={mode} />, div);
  }
}
