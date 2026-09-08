/**
 * CollapseView — interactive decimation (wave-function-collapse) session.
 *
 * Markdown usage:
 *   ```{collapse will}
 *   file: calculus/will/game/WFC.will
 *   seed: 7            (optional)
 *   title: Beach WFC
 *   ```
 *
 * Drives a server-side collapse session over calc.collapseView /
 * calc.collapseDraw: waves sorted by entropy, click to draw, restart
 * on contradiction.
 */
import { createSignal, For, Show, onMount } from 'solid-js';
import ErrorBoundary from '../common/ErrorBoundary';
import { parseSpecBody, type WidgetProps } from '../../lib/hydrateWidgets';

interface WaveMember { label: string; weight: string }
interface Wave { index: number; fact: string; entropy: number; members: WaveMember[] }
interface CollapseViewData {
  ok: boolean;
  error?: string;
  id?: string;
  waves?: Wave[];
  drawn?: string[];
  state?: string[];
  contradiction?: boolean;
  attempts?: number;
  done?: boolean;
}

const SPEC_KEYS = ['file', 'seed', 'title'];

export default function CollapseView(props: WidgetProps) {
  const spec = parseSpecBody(props.body, SPEC_KEYS);
  const calculus = props.args[0] || 'will';

  const [view, setView] = createSignal<CollapseViewData | null>(null);
  const [busy, setBusy] = createSignal(false);
  let sessionId: string | null = null;

  async function call(body: Record<string, unknown>): Promise<CollapseViewData> {
    const res = await fetch('/api/run/collapse/act', {
      method: 'POST',
      headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(body),
    });
    return res.json();
  }

  async function start() {
    setBusy(true);
    try {
      const res = await fetch('/api/run/collapse/start', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          calculus,
          file: spec.file?.trim(),
          seed: spec.seed ? Number(spec.seed) : undefined,
        }),
      });
      const v: CollapseViewData = await res.json();
      if (v.ok && v.id) sessionId = v.id;
      setView(v);
    } catch (e: any) {
      setView({ ok: false, error: e.message || 'request failed' });
    } finally {
      setBusy(false);
    }
  }

  async function act(action: string, waveIndex?: number) {
    if (!sessionId || busy()) return;
    setBusy(true);
    try {
      setView(await call({ id: sessionId, action, waveIndex }));
    } catch (e: any) {
      setView({ ok: false, error: e.message });
    } finally {
      setBusy(false);
    }
  }

  onMount(start);

  return (
    <ErrorBoundary>
      <div class="not-prose my-6 rounded-lg border border-rose-200 dark:border-rose-900 bg-rose-50/30 dark:bg-rose-950/20 overflow-hidden">
        <div class="flex items-center justify-between px-4 py-2 bg-rose-100/60 dark:bg-rose-900/30 border-b border-rose-200 dark:border-rose-900">
          <span class="text-xs font-semibold uppercase tracking-wide text-rose-700 dark:text-rose-300">
            {spec.title || 'Collapse'}
            <Show when={(view()?.attempts || 0) > 1}> — attempt {view()!.attempts}</Show>
          </span>
          <div class="flex items-center gap-1.5">
            <button
              onClick={() => act('auto')}
              disabled={busy() || !view()?.ok || view()?.done}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
            >
              Auto-collapse
            </button>
            <button
              onClick={() => act('draw')}
              disabled={busy() || !view()?.ok || view()?.done}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
              title="Draw the minimum-entropy wave"
            >
              Draw next
            </button>
            <button
              onClick={() => (sessionId ? act('restart') : start())}
              disabled={busy()}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
              title="Reset all waves; the next draws use a fresh attempt counter"
            >
              Restart
            </button>
          </div>
        </div>

        <Show when={!view()}>
          <div class="p-4 text-sm text-gray-500">Starting session…</div>
        </Show>
        <Show when={view() && !view()!.ok}>
          <div class="p-4 text-sm text-red-600 dark:text-red-400">Collapse unavailable: {view()!.error}</div>
        </Show>

        <Show when={view()?.ok}>
          <Show when={view()!.contradiction}>
            <div class="px-4 py-2 text-sm text-red-700 dark:text-red-300 bg-red-50 dark:bg-red-900/20 border-b border-red-200 dark:border-red-800">
              Contradiction — a wave has no admissible member left. Restart to try another seed path.
            </div>
          </Show>
          <div class="grid md:grid-cols-2 gap-0">
            {/* Waves (entropy-sorted) */}
            <div class="p-4 border-r border-rose-100 dark:border-rose-900/50">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">
                Open waves (lowest entropy first)
              </div>
              <Show
                when={(view()!.waves || []).length > 0}
                fallback={<div class="text-xs text-gray-400 italic">
                  {view()!.done ? 'All waves collapsed.' : 'No open waves.'}
                </div>}
              >
                <div class="space-y-2">
                  <For each={view()!.waves!}>
                    {(w) => (
                      <div class="rounded border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 p-2">
                        <div class="flex items-center justify-between mb-1">
                          <span class="text-xs font-mono text-gray-700 dark:text-gray-300">{w.fact}</span>
                          <span class="text-[10px] text-gray-400">H = {w.entropy.toFixed(2)}</span>
                        </div>
                        <div class="flex flex-wrap gap-1">
                          <For each={w.members}>
                            {(m) => (
                              <span class="px-1.5 py-0.5 text-[10px] rounded bg-rose-100 dark:bg-rose-900/40 text-rose-700 dark:text-rose-300 font-mono">
                                {m.label} <span class="opacity-60">{m.weight}</span>
                              </span>
                            )}
                          </For>
                        </div>
                        <button
                          onClick={() => act('draw', w.index)}
                          disabled={busy()}
                          class="mt-1.5 px-2 py-0.5 text-[10px] rounded bg-rose-600 text-white hover:bg-rose-700 disabled:opacity-40"
                        >
                          Draw this wave
                        </button>
                      </div>
                    )}
                  </For>
                </div>
              </Show>
            </div>
            {/* Drawn + residual state */}
            <div class="p-4">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">Drawn</div>
              <ul class="space-y-0.5 text-xs font-mono">
                <For each={view()!.drawn || []}>{(d) => <li class="text-green-700 dark:text-green-400">{d}</li>}</For>
              </ul>
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mt-3 mb-1">State</div>
              <ul class="space-y-0.5 text-xs font-mono max-h-56 overflow-y-auto">
                <For each={view()!.state || []}>{(f) => <li>{f}</li>}</For>
              </ul>
              <Show when={view()!.done && !view()!.contradiction}>
                <div class="mt-3 px-3 py-2 rounded bg-green-50 dark:bg-green-900/20 border border-green-200 dark:border-green-800 text-sm text-green-700 dark:text-green-400 font-medium">
                  ✓ Fully collapsed — one concrete world drawn.
                </div>
              </Show>
            </div>
          </div>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
