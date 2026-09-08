/**
 * ForwardStepper — step through a forward execution trace.
 * Implemented against POST /api/run/exec (see server.js run API).
 */
import { createSignal, createResource, createMemo, For, Show } from 'solid-js';
import ErrorBoundary from '../common/ErrorBoundary';
import { parseSpecBody, type WidgetProps } from '../../lib/hydrateWidgets';

interface ExecStep {
  step: number;
  rule: string;
  consumed: string[];
  produced: string[];
  state: string[];
}

interface ExecResult {
  ok: boolean;
  error?: string;
  steps?: ExecStep[];
  initial?: string[];
  final?: string[];
  quiescent?: boolean;
}

const SPEC_KEYS = ['file', 'query', 'maxSteps', 'title'];

export default function ForwardStepper(props: WidgetProps) {
  const spec = parseSpecBody(props.body, SPEC_KEYS);
  // Either `file:` + `query:` reference a repo program, or the body (when it
  // has no file:) is inline program source.
  const inline = !spec.file ? props.body : null;
  const [cursor, setCursor] = createSignal(0);

  const [result] = createResource<ExecResult>(async () => {
    try {
      const res = await fetch('/api/run/exec', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({
          calculus: props.args[0] || 'ill',
          file: spec.file?.trim(),
          query: spec.query?.trim(),
          source: inline || undefined,
          maxSteps: spec.maxSteps ? Number(spec.maxSteps) : undefined,
        }),
      });
      return await res.json();
    } catch (e: any) {
      return { ok: false, error: e.message || 'request failed' };
    }
  });

  const steps = createMemo(() => result()?.steps || []);
  const shown = createMemo(() => steps().slice(0, cursor()));
  const currentState = createMemo(() => {
    const c = cursor();
    if (c === 0) return result()?.initial || [];
    return steps()[c - 1]?.state || [];
  });

  return (
    <ErrorBoundary>
      <div class="not-prose my-6 rounded-lg border border-teal-200 dark:border-teal-900 bg-teal-50/30 dark:bg-teal-950/20 overflow-hidden">
        <div class="flex items-center justify-between px-4 py-2 bg-teal-100/60 dark:bg-teal-900/30 border-b border-teal-200 dark:border-teal-900">
          <span class="text-xs font-semibold uppercase tracking-wide text-teal-700 dark:text-teal-300">
            {spec.title || 'Forward execution'}
          </span>
          <Show when={result()?.ok}>
            <div class="flex items-center gap-1.5">
              <button
                onClick={() => setCursor(Math.max(0, cursor() - 1))}
                disabled={cursor() === 0}
                class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
              >
                ← Back
              </button>
              <span class="text-xs text-gray-500 font-mono">{cursor()}/{steps().length}</span>
              <button
                onClick={() => setCursor(Math.min(steps().length, cursor() + 1))}
                disabled={cursor() >= steps().length}
                class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
              >
                Step →
              </button>
              <button
                onClick={() => setCursor(steps().length)}
                disabled={cursor() >= steps().length}
                class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 disabled:opacity-40"
              >
                Run all
              </button>
            </div>
          </Show>
        </div>

        <Show when={result.loading}>
          <div class="p-4 text-sm text-gray-500">Running…</div>
        </Show>
        <Show when={result() && !result()!.ok}>
          <div class="p-4 text-sm text-red-600 dark:text-red-400">
            Execution unavailable: {result()!.error}
          </div>
        </Show>

        <Show when={result()?.ok}>
          <div class="grid md:grid-cols-2 gap-0">
            {/* Fired rules so far */}
            <div class="p-4 border-r border-teal-100 dark:border-teal-900/50">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">Fired rules</div>
              <Show when={shown().length > 0} fallback={<div class="text-xs text-gray-400 italic">No steps yet — press Step.</div>}>
                <ol class="space-y-1 text-xs font-mono">
                  <For each={shown()}>
                    {(s, i) => (
                      <li
                        class="px-2 py-1 rounded"
                        classList={{ 'bg-teal-100 dark:bg-teal-900/40 font-semibold': i() === cursor() - 1 }}
                      >
                        {s.step}. {s.rule}
                        <Show when={i() === cursor() - 1}>
                          <div class="mt-1 font-normal text-red-600 dark:text-red-400">
                            <For each={s.consumed}>{(f) => <div>− {f}</div>}</For>
                          </div>
                          <div class="font-normal text-green-600 dark:text-green-400">
                            <For each={s.produced}>{(f) => <div>+ {f}</div>}</For>
                          </div>
                        </Show>
                      </li>
                    )}
                  </For>
                </ol>
              </Show>
            </div>
            {/* Current state */}
            <div class="p-4">
              <div class="text-xs font-medium text-gray-500 dark:text-gray-400 mb-2">
                State {cursor() === steps().length && result()?.quiescent ? '(quiescent)' : `after step ${cursor()}`}
              </div>
              <ul class="space-y-0.5 text-xs font-mono">
                <For each={currentState()}>{(f) => <li>{f}</li>}</For>
              </ul>
            </div>
          </div>
        </Show>
      </div>
    </ErrorBoundary>
  );
}
