import { createSignal, For, Show, onMount } from 'solid-js';

// Governance sandbox (TODO_0318 S1) — a live dill context you drive as ADMIN
// (the mint authority) or as an ACTOR (a principal confined to its own says-zone,
// the operational NI-1). Talks to the /api/gov/* server (src/server/gov-api.js).

type Row = { zone: string; text: string; count: number };
type Consensus = { decided?: boolean; winner?: number | null; ranking?: Array<{ x: number; val: number; seq: number; approvers: number }>; error?: string };
type View = {
  rows: Row[];
  zones: Record<string, string[]>;
  shares: Array<{ k: number; s: number }>;
  votes: Array<{ k: number; p: number; x: number; w: number }>;
  candidates: Array<{ p: number; x: number; seq: number }>;
  currents: Array<{ n: number; t: number }>;
  proposals: number[];
  consensus: Record<string, Consensus>;
  kernel: string;
  kernelParams: Record<string, unknown>;
  kernels: string[];
  program: string;
  timeline: Array<{ n: number; actor: string; action: string; detail: unknown }>;
};

const PROGRAMS = [
  { path: 'calculus/dill/tests/forward/company_cake.ill', query: 'expect_cake', label: 'Company buys cake (quorum → asset at C)' },
  { path: 'calculus/dill/programs/name_the_org.ill', query: 'run', label: 'Name the org (range-vote → argmax)' },
  { path: 'calculus/dill/tests/forward/elect_a_rule.ill', query: 'expect_bold', label: 'Elect a rule (governed program)' },
  { path: 'calculus/dill/prelude/governance.ill', query: '', label: 'Blank prelude (build your own)' },
];

async function api(route: string, body: Record<string, unknown>) {
  const res = await fetch(`/api/gov/${route}`, {
    method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify(body),
  });
  return res.json();
}

const card = 'bg-white dark:bg-gray-800 rounded-lg p-4 shadow-sm border border-gray-200 dark:border-gray-700';
const btn = 'px-3 py-1.5 rounded text-sm font-medium border border-gray-300 dark:border-gray-600 hover:bg-gray-100 dark:hover:bg-gray-700';
const input = 'w-full px-2 py-1.5 rounded border border-gray-300 dark:border-gray-600 bg-transparent font-mono text-sm';

export default function Governance() {
  const [id, setId] = createSignal<string | null>(null);
  const [view, setView] = createSignal<View | null>(null);
  const [role, setRole] = createSignal<string>('admin');
  const [program, setProgram] = createSignal(PROGRAMS[0]);
  const [msg, setMsg] = createSignal<string>('');
  const [injectText, setInjectText] = createSignal('says 1 (stake 3 (1/2))');
  const [queryText, setQueryText] = createSignal('says 1 (stake 3 w) |- says 3 (money m)');
  const [queryResult, setQueryResult] = createSignal<string>('');

  const apply = (r: any) => {
    if (!r?.ok) { setMsg(`⚠ ${r?.error || 'error'}`); return false; }
    setMsg('');
    if (r.id) setId(r.id);
    if (r.view) setView(r.view);
    return true;
  };

  async function start() {
    const p = program();
    setMsg('starting…');
    apply(await api('start', { program: p.path, query: p.query || null }));
  }
  onMount(start);

  const roles = () => {
    const v = view();
    const principals = new Set<string>();
    if (v) {
      for (const k of Object.keys(v.zones)) principals.add(k);
      for (const s of v.shares) principals.add(String(s.k));
    }
    return ['admin', ...[...principals].sort((a, b) => Number(a) - Number(b))];
  };

  async function inject() {
    if (!id()) return;
    apply(await api('inject', { id: id(), role: role() === 'admin' ? 'admin' : Number(role()), fact: injectText() }));
  }
  async function settle() { if (id()) apply(await api('settle', { id: id() })); }
  async function setKernel(k: string) { if (id()) apply(await api('kernel', { id: id(), kernel: k })); }
  async function enact(p: number) { const r = await api('enact', { id: id(), p }); apply(r) || setMsg(`⚠ ${r?.error}`); }
  async function runQuery() {
    if (!id()) return;
    const r = await api('query', { id: id(), sequent: queryText() });
    setQueryResult(r?.ok ? (r.provable ? '✓ provable' : '✗ not provable') : `⚠ ${r?.error}`);
  }

  return (
    <div class="max-w-7xl mx-auto p-4 space-y-4">
      <header class="flex flex-wrap items-center gap-3">
        <h1 class="text-xl font-semibold">Governance sandbox</h1>
        <select class={input.replace('w-full', 'w-auto')} onChange={(e) => { const p = PROGRAMS.find(x => x.path === e.currentTarget.value); if (p) { setProgram(p); } }}>
          <For each={PROGRAMS}>{(p) => <option value={p.path} selected={p.path === program().path}>{p.label}</option>}</For>
        </select>
        <button class={btn} onClick={start}>↻ Load</button>
        <Show when={msg()}><span class="text-sm text-amber-600 dark:text-amber-400 font-mono">{msg()}</span></Show>
      </header>

      {/* role switcher — the operational NI-1: an actor may touch only its says-zone */}
      <div class="flex flex-wrap items-center gap-2">
        <span class="text-sm text-gray-500">Acting as:</span>
        <For each={roles()}>{(r) => (
          <button class={btn} classList={{ 'bg-blue-600 text-white border-blue-600': role() === r }} onClick={() => setRole(r)}>
            {r === 'admin' ? 'Admin (mint)' : `Actor ${r}`}
          </button>
        )}</For>
      </div>

      <div class="grid grid-cols-1 lg:grid-cols-3 gap-4">
        {/* context panel */}
        <section class={card + ' lg:col-span-2'}>
          <h2 class="font-semibold mb-2">Context</h2>
          <Show when={view()} fallback={<p class="text-sm text-gray-500">no session</p>}>
            <div class="space-y-3">
              <For each={Object.entries(view()!.zones)}>{([k, facts]) => (
                <div>
                  <div class="text-xs uppercase tracking-wide text-gray-500">zone — principal {k}</div>
                  <ul class="font-mono text-sm pl-3">
                    <For each={facts}>{(f) => <li>{f}</li>}</For>
                  </ul>
                </div>
              )}</For>
              <details>
                <summary class="text-xs uppercase tracking-wide text-gray-500 cursor-pointer">all facts ({view()!.rows.length})</summary>
                <ul class="font-mono text-xs pl-3 mt-1">
                  <For each={view()!.rows}>{(r) => <li classList={{ 'text-gray-500': r.zone === 'persistent' }}>{r.zone === 'persistent' ? '! ' : ''}{r.text}{r.count > 1 ? ` ×${r.count}` : ''}</li>}</For>
                </ul>
              </details>
            </div>
          </Show>
        </section>

        {/* consensus + kernel */}
        <section class={card}>
          <h2 class="font-semibold mb-2">Consensus</h2>
          <div class="flex items-center gap-2 mb-3">
            <span class="text-sm text-gray-500">kernel</span>
            <select class={input.replace('w-full', 'w-auto')} onChange={(e) => setKernel(e.currentTarget.value)}>
              <For each={view()?.kernels || []}>{(k) => <option value={k} selected={k === view()?.kernel}>{k}</option>}</For>
            </select>
          </div>
          <Show when={(view()?.proposals || []).length} fallback={<p class="text-sm text-gray-500">no proposals</p>}>
            <For each={view()!.proposals}>{(p) => {
              const c = () => view()!.consensus[String(p)] || {};
              return (
                <div class="mb-3 border-t border-gray-100 dark:border-gray-700 pt-2">
                  <div class="flex items-center justify-between">
                    <span class="font-mono text-sm">proposal {p}</span>
                    <button class={btn} onClick={() => enact(p)}>Enact →</button>
                  </div>
                  <div class="text-sm">
                    winner: <span class="font-mono font-semibold">{c().winner ?? '—'}</span>
                    {c().decided === false ? <span class="text-amber-600"> (undecided)</span> : null}
                  </div>
                  <ul class="text-xs font-mono text-gray-600 dark:text-gray-400">
                    <For each={c().ranking || []}>{(e) => <li>x={e.x} val={e.val.toFixed(3)} seq={e.seq} approvers={e.approvers}</li>}</For>
                  </ul>
                </div>
              );
            }}</For>
          </Show>
          <Show when={(view()?.currents || []).length}>
            <div class="mt-2 text-sm">
              <div class="text-xs uppercase tracking-wide text-gray-500">current cells</div>
              <For each={view()!.currents}>{(c) => <div class="font-mono">n={c.n} → {c.t}</div>}</For>
            </div>
          </Show>
        </section>
      </div>

      <div class="grid grid-cols-1 lg:grid-cols-3 gap-4">
        {/* inject */}
        <section class={card}>
          <h2 class="font-semibold mb-2">Inject <span class="text-xs text-gray-500">as {role() === 'admin' ? 'admin' : `actor ${role()}`}</span></h2>
          <input class={input} value={injectText()} onInput={(e) => setInjectText(e.currentTarget.value)} placeholder="says 1 (stake 3 (1/2))" />
          <div class="flex gap-2 mt-2">
            <button class={btn} onClick={inject}>Inject</button>
            <button class={btn} onClick={settle}>Settle ▶</button>
          </div>
          <p class="text-xs text-gray-500 mt-2">Actors may inject only <code>says K (…)</code> for their own K (poss_l at the boundary). Admin mints any zone.</p>
        </section>

        {/* query */}
        <section class={card}>
          <h2 class="font-semibold mb-2">Query <span class="text-xs text-gray-500">(backward, entity-veil)</span></h2>
          <input class={input} value={queryText()} onInput={(e) => setQueryText(e.currentTarget.value)} placeholder="A |- B" />
          <div class="flex items-center gap-2 mt-2">
            <button class={btn} onClick={runQuery}>Prove</button>
            <span class="font-mono text-sm">{queryResult()}</span>
          </div>
          <p class="text-xs text-gray-500 mt-2">Proves a sequent against dill's rules (poss_l): e.g. <code>says 1 (stake 3 w) ⊬ says 3 (money m)</code>.</p>
        </section>

        {/* timeline */}
        <section class={card}>
          <h2 class="font-semibold mb-2">Timeline</h2>
          <Show when={(view()?.timeline || []).length} fallback={<p class="text-sm text-gray-500">no actions yet</p>}>
            <ol class="text-xs font-mono space-y-0.5 max-h-64 overflow-auto">
              <For each={view()!.timeline}>{(t) => <li><span class="text-gray-500">{t.n}.</span> [{t.actor}] {t.action}</li>}</For>
            </ol>
          </Show>
        </section>
      </div>
    </div>
  );
}
