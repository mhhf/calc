/**
 * TimedGame — interactive timed-ILL session (the web face of tools/till-shell.js).
 *
 * Markdown usage:
 *   ```{game till}
 *   file: calculus/till/game/PP2.till
 *   init: init          (optional — #init directive name)
 *   title: Paragon Pioneers
 *   ```
 *
 * Drives a server-side session: settle to a horizon, render observable
 * state + menus (with-projections), click an alternative to choose it.
 */
import { createSignal, For, Show, onMount, onCleanup } from 'solid-js';
import ErrorBoundary from '../common/ErrorBoundary';
import { parseSpecBody, type WidgetProps } from '../../lib/hydrateWidgets';

interface GameAlt { index: number; label: string; enabled: boolean }
interface GameMenu { index: number; fact: string; alts: GameAlt[] }
interface GameView {
  ok: boolean;
  error?: string;
  id?: string;
  t?: number;
  state?: { text: string; count: number }[];
  menus?: GameMenu[];
  pending?: string[];
  events?: string[];
  quiescent?: boolean;
}

const SPEC_KEYS = ['file', 'init', 'title', 'step'];

export default function TimedGame(props: WidgetProps) {
  const spec = parseSpecBody(props.body, SPEC_KEYS);
  const calculus = props.args[0] || 'till';
  const stepSize = spec.step ? Number(spec.step) : 1;

  const [view, setView] = createSignal<GameView | null>(null);
  const [busy, setBusy] = createSignal(false);
  const [log, setLog] = createSignal<string[]>([]);
  let sessionId: string | null = null;

  async function call(path: string, body: Record<string, unknown>): Promise<GameView> {
    const res = await fetch(path, {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body),
    });
    return res.json();
  }

  function applyView(v: GameView) {
    setView(v);
    if (v.events && v.events.length) {
      setLog((prev) => [...prev, ...v.events!].slice(-40));
    }
  }

  async function start() {
    setBusy(true);
    try {
      const v = await call('/api/run/game/start', {
        calculus,
        file: spec.file?.trim(),
        init: spec.init?.trim(),
      });
      if (v.ok && v.id) sessionId = v.id;
      applyView(v);
      setLog([]);
    } catch (e: any) {
      setView({ ok: false, error: e.message || 'request failed' });
    } finally {
      setBusy(false);
    }
  }

  async function advance(dt: number) {
    if (!sessionId || busy()) return;
    setBusy(true);
    try {
      applyView(await call(`/api/run/game/act`, { id: sessionId, action: 'settle', t: (view()?.t || 0) + dt }));
    } catch (e: any) {
      setView({ ok: false, error: e.message });
    } finally {
      setBusy(false);
    }
  }

  async function choose(menuIndex: number, altIndex: number) {
    if (!sessionId || busy()) return;
    setBusy(true);
    try {
      applyView(await call(`/api/run/game/act`, { id: sessionId, action: 'choose', menuIndex, altIndex, t: view()?.t || 0 }));
    } catch (e: any) {
      setView({ ok: false, error: e.message });
    } finally {
      setBusy(false);
    }
  }

  onMount(start);
  onCleanup(() => {
    if (sessionId) {
      fetch('/api/run/game/act', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ id: sessionId, action: 'end' }),
      }).catch(() => {});
    }
  });

  return (
    <ErrorBoundary>
      <div class="not-prose my-6 rounded-lg border border-amber-200 dark:border-amber-900 bg-amber-50/30 dark:bg-amber-950/20 overflow-hidden">
        <div class="flex items-center justify-between px-4 py-2 bg-amber-100/60 dark:bg-amber-900/30 border-b border-amber-200 dark:border-amber-900">
          <span class="text-xs font-semibold uppercase tracking-wide text-amber-700 dark:text-amber-300">
            {spec.title || 'Timed game'} {view()?.t !== undefined ? `— t = ${view()!.t}` : ''}
          </span>
          <div class="flex items-center gap-1.5">
            <button
              onClick={() => advance(stepSize)}
              disabled={busy() || !view()?.ok}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
            >
              +{stepSize}s
            </button>
            <button
              onClick={() => advance(stepSize * 10)}
              disabled={busy() || !view()?.ok}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
            >
              +{stepSize * 10}s
            </button>
            <button
              onClick={start}
              disabled={busy()}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
            >
              Restart
            </button>
          </div>
        </div>

        <Show when={!view()}>
          <div class="p-4 text-sm text-gray-500">Starting session…</div>
        </Show>
        <Show when={view() && !view()!.ok}>
          <div class="p-4 text-sm text-red-600 dark:text-red-400">Game unavailable: {view()!.error}</div>
        </Show>

        <Show when={view()?.ok}>
          <div class="grid md:grid-cols-2 gap-0">
            {/* State + pending */}
            <div class="p-4 border-r border-amber-100 dark:border-amber-900/50">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">Resources</div>
              <ul class="space-y-0.5 text-xs font-mono">
                <For each={view()!.state || []}>
                  {(f) => (
                    <li>
                      <Show when={f.count > 1}><span class="text-amber-600 dark:text-amber-400">{f.count}×</span>{' '}</Show>
                      {f.text}
                    </li>
                  )}
                </For>
              </ul>
              <Show when={(view()!.pending || []).length > 0}>
                <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mt-3 mb-1">In flight</div>
                <ul class="space-y-0.5 text-xs font-mono text-gray-500">
                  <For each={view()!.pending!}>{(f) => <li>{f}</li>}</For>
                </ul>
              </Show>
            </div>
            {/* Menus + log */}
            <div class="p-4">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">Actions</div>
              <Show
                when={(view()!.menus || []).length > 0}
                fallback={<div class="text-xs text-gray-400 italic">No choices available — advance time.</div>}
              >
                <div class="space-y-2">
                  <For each={view()!.menus!}>
                    {(menu) => (
                      <div>
                        <div class="text-xs font-mono text-gray-600 dark:text-gray-300 mb-1">{menu.fact}</div>
                        <div class="flex flex-wrap gap-1.5">
                          <For each={menu.alts}>
                            {(alt) => (
                              <button
                                onClick={() => choose(menu.index, alt.index)}
                                disabled={busy() || !alt.enabled}
                                class="px-2 py-1 text-xs rounded border transition-colors"
                                classList={{
                                  'bg-amber-600 text-white border-amber-700 hover:bg-amber-700': alt.enabled,
                                  'bg-gray-100 dark:bg-gray-800 text-gray-400 border-gray-200 dark:border-gray-700 cursor-not-allowed': !alt.enabled,
                                }}
                              >
                                {alt.label}
                              </button>
                            )}
                          </For>
                        </div>
                      </div>
                    )}
                  </For>
                </div>
              </Show>
              <Show when={log().length > 0}>
                <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mt-3 mb-1">Events</div>
                <ul class="space-y-0.5 text-xs font-mono text-gray-500 max-h-40 overflow-y-auto">
                  <For each={log()}>{(e) => <li>{e}</li>}</For>
                </ul>
              </Show>
            </div>
          </div>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
