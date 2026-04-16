/**
 * Slide-over detail panel for a selected component.
 *
 * Used by every view — when the user clicks a ComponentBox, this panel
 * shows the full metadata and provides cross-view navigation links
 * ("view in Trust / Specificity / Pipeline / Atlas / Deep Dive").
 */

import { Show, For, createEffect, onCleanup } from 'solid-js';
import { A } from '@solidjs/router';
import type { Component } from '../data/types';
import { TRUST_COLORS, DEEPDIVE_ACCENT, MODE_LABEL } from '../data/palette';
import { TrustBadge, SpecificityBadge, StageBadge, ModeBadge } from './Badge';
import { DEEP_DIVES } from '../data/meta';

interface Props {
  component: Component | null;
  onClose: () => void;
}

/** Build an href that preserves the #comp= hash so cross-view nav keeps the selection. */
function withHash(path: string): string {
  if (typeof window === 'undefined') return path;
  return path + (window.location.hash || '');
}

export default function DetailPanel(props: Props) {
  const dive = () => DEEP_DIVES.find(d => d.id === props.component?.deepDive);

  // Global ESC handler active only while a component is selected.
  createEffect(() => {
    if (!props.component) return;
    const onKey = (e: KeyboardEvent) => {
      if (e.key === 'Escape') { e.preventDefault(); props.onClose(); }
    };
    document.addEventListener('keydown', onKey);
    onCleanup(() => document.removeEventListener('keydown', onKey));
  });

  return (
    <Show when={props.component}>
      {(c) => (
        <>
          {/* Backdrop */}
          <div
            class="fixed inset-0 bg-black/20 dark:bg-black/40 z-40 animate-fade-in"
            onClick={props.onClose}
            aria-hidden="true"
          />
          {/* Panel */}
          <aside
            class="fixed top-0 right-0 bottom-0 w-full sm:w-[440px] bg-white dark:bg-gray-800 shadow-2xl border-l border-gray-200 dark:border-gray-700 z-50 overflow-y-auto animate-slide-in"
            role="dialog"
            aria-label={`Details for ${c().name}`}
          >
            <header class={`px-5 py-4 border-b border-gray-200 dark:border-gray-700 ${TRUST_COLORS[c().trust].bg}`}>
              <div class="flex items-start justify-between gap-3">
                <div class="flex-1 min-w-0">
                  <div class="font-mono text-xs text-gray-500 dark:text-gray-400">{c().id}</div>
                  <h3 class={`text-lg font-bold truncate ${TRUST_COLORS[c().trust].text}`}>{c().name}</h3>
                  <p class="text-sm text-gray-700 dark:text-gray-300 mt-1">{c().summary}</p>
                </div>
                <button
                  type="button"
                  onClick={props.onClose}
                  class="shrink-0 p-1 text-gray-500 hover:text-gray-800 dark:hover:text-gray-200 rounded-md hover:bg-white/50 dark:hover:bg-gray-700/50"
                  aria-label="Close details"
                >
                  <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12" />
                  </svg>
                </button>
              </div>
            </header>

            <div class="px-5 py-4 space-y-5">
              {/* Badges */}
              <section>
                <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Tags</h4>
                <div class="flex flex-wrap gap-1.5">
                  <TrustBadge trust={c().trust} />
                  <SpecificityBadge specificity={c().specificity} />
                </div>
              </section>

              {/* Stages */}
              <section>
                <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Pipeline Stages</h4>
                <div class="flex flex-wrap gap-1.5">
                  <For each={c().stages}>{(s) => <StageBadge stage={s} />}</For>
                </div>
              </section>

              {/* Modes */}
              <section>
                <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Execution Modes</h4>
                <div class="flex flex-wrap gap-1.5">
                  <For each={c().modes}>{(m) => <ModeBadge mode={MODE_LABEL[m]} />}</For>
                </div>
              </section>

              {/* Files */}
              <section>
                <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Files</h4>
                <ul class="space-y-1">
                  <For each={c().files}>
                    {(f) => (
                      <li class="font-mono text-xs text-gray-800 dark:text-gray-200 bg-gray-100 dark:bg-gray-900/50 px-2 py-1 rounded break-all">
                        {f}
                      </li>
                    )}
                  </For>
                </ul>
              </section>

              {/* Details (if present) */}
              <Show when={c().details}>
                <section>
                  <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Notes</h4>
                  <p class="text-sm text-gray-700 dark:text-gray-300 leading-relaxed">{c().details}</p>
                </section>
              </Show>

              {/* Cross-view navigation */}
              <section class="pt-4 border-t border-gray-200 dark:border-gray-700">
                <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Cross-View Navigation</h4>
                <div class="grid grid-cols-2 gap-2">
                  <A href={withHash('/overview/trust')} class="nav-chip">Trust Stack</A>
                  <A href={withHash('/overview/specificity')} class="nav-chip">Specificity Tree</A>
                  <A href={withHash('/overview/pipeline')} class="nav-chip">Pipeline</A>
                  <A href={withHash('/overview/atlas')} class="nav-chip">Atlas</A>
                </div>
                <Show when={dive()}>
                  {(d) => (
                    <A
                      href={withHash(`/overview/${d().slug}`)}
                      class={`mt-3 block w-full rounded-md border border-gray-200 dark:border-gray-700 bg-gray-50 dark:bg-gray-900/40 px-3 py-2 text-center text-sm font-semibold hover:bg-gray-100 dark:hover:bg-gray-800 ${DEEPDIVE_ACCENT[d().id]}`}
                    >
                      Deep Dive → {d().title}
                    </A>
                  )}
                </Show>
              </section>
            </div>
          </aside>
        </>
      )}
    </Show>
  );
}
