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
import { createSignal, createResource, Show, For } from 'solid-js';
import { render } from 'solid-js/web';
import { renderLayout } from './layouts';
import { PROOF_LAYOUTS } from './types';
import type { ProofLayout, ProofTreeV1 } from './types';

const LS_KEY = 'calc.proofBlock.layout';

function readLayout(): ProofLayout {
  try {
    const raw = localStorage.getItem(LS_KEY);
    if (raw && PROOF_LAYOUTS.some((l) => l.id === raw)) return raw as ProofLayout;
  } catch {}
  return 'bussproofs';
}

function writeLayout(l: ProofLayout) {
  try { localStorage.setItem(LS_KEY, l); } catch {}
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
}) {
  const [result] = createResource(
    () => ({ source: props.source, calculus: props.calculus, profile: props.profile }),
    fetchProof,
  );
  const [ruleSlugs] = createResource(fetchRuleSlugs);
  const [layout, setLayout] = createSignal<ProofLayout>(readLayout());

  return (
    <div class="calc-proof-block" style="border:1px solid #ddd;border-radius:6px;margin:1em 0;background:#fff">
      <div class="calc-proof-header" style="display:flex;align-items:center;gap:0.5em;padding:0.4em 0.6em;border-bottom:1px solid #eee;background:#fafafa;font-size:0.8em;color:#666">
        <span style="font-weight:600">proof</span>
        <span style="opacity:0.7">·</span>
        <span>{props.calculus}</span>
        <Show when={props.profile !== 'default'}>
          <span style="opacity:0.7">·</span>
          <span>{props.profile}</span>
        </Show>
        <div style="flex:1" />
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
      <div class="calc-proof-body">
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
          {renderLayout(layout(), result()!.tree!, ruleSlugs() || {})}
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
    const sourceId = div.dataset.sourceId;
    const scriptEl = sourceId ? document.getElementById(sourceId) : null;
    const source = scriptEl?.textContent || div.querySelector('.client-source')?.textContent || '';
    const calculus = div.dataset.calculus || 'ill';
    const profile = div.dataset.profile || 'default';
    div.dataset.hydrated = '1';
    div.innerHTML = '';
    render(() => <ProofBlock source={source} calculus={calculus} profile={profile} />, div);
  }
}
