/**
 * Embedded detail panel for a selected component.
 *
 * Renders inline in the page flow (NOT a slide-over) — when the user clicks
 * a ComponentBox or a LayerBand component, this panel appears at the top of
 * the page with the full metadata and cross-view navigation links.
 *
 * No modal, no backdrop, no ESC handler. Close button removes the hash
 * selection; the panel scrolls itself into view on new selection.
 */

import { Show, For, createEffect } from 'solid-js';
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
  let ref: HTMLElement | undefined;

  // When selection changes to a new component, bring the detail card into view.
  createEffect(() => {
    if (!props.component || !ref) return;
    // Only scroll if the card is off-screen above/below the viewport; avoid
    // jerky scrolls when user clicks a component that's already on-screen.
    const rect = ref.getBoundingClientRect();
    if (rect.top < 0 || rect.bottom > window.innerHeight) {
      ref.scrollIntoView({ block: 'start' });
    }
  });

  return (
    <Show when={props.component}>
      {(c) => {
        const p = TRUST_COLORS[c().trust];
        return (
          <section
            ref={(el) => (ref = el)}
            class={`rounded-xl border-2 ${p.border} bg-white dark:bg-gray-800 shadow-sm overflow-hidden scroll-mt-24`}
            aria-label={`Details for ${c().name}`}
          >
            {/* Header */}
            <header class={`px-6 py-5 border-b ${p.border} ${p.bg}`}>
              <div class="flex items-start justify-between gap-4">
                <div class="min-w-0">
                  <div class="font-mono text-xs text-gray-600 dark:text-gray-400">{c().id}</div>
                  <h3 class={`text-xl font-bold mt-0.5 ${p.text}`}>{c().name}</h3>
                  <p class="text-sm text-gray-700 dark:text-gray-300 mt-2 max-w-3xl leading-relaxed">{c().summary}</p>
                </div>
                <button
                  type="button"
                  onClick={props.onClose}
                  class="shrink-0 p-1.5 text-gray-500 hover:text-gray-800 dark:hover:text-gray-200 rounded-md hover:bg-white/60 dark:hover:bg-gray-700/50"
                  aria-label="Close details"
                >
                  <svg class="w-5 h-5" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                    <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M6 18L18 6M6 6l12 12" />
                  </svg>
                </button>
              </div>
            </header>

            {/* Body — 2-column grid on md+ so the card stays compact */}
            <div class="px-6 py-5 grid grid-cols-1 md:grid-cols-2 gap-x-8 gap-y-6">
              {/* Left column: taxonomy */}
              <div class="space-y-5">
                <section>
                  <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Tags</h4>
                  <div class="flex flex-wrap gap-1.5">
                    <TrustBadge trust={c().trust} />
                    <SpecificityBadge specificity={c().specificity} />
                  </div>
                </section>

                <section>
                  <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Pipeline stages</h4>
                  <div class="flex flex-wrap gap-1.5">
                    <For each={c().stages}>{(s) => <StageBadge stage={s} />}</For>
                  </div>
                </section>

                <section>
                  <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Execution modes</h4>
                  <div class="flex flex-wrap gap-1.5">
                    <For each={c().modes}>{(m) => <ModeBadge mode={MODE_LABEL[m]} />}</For>
                  </div>
                </section>

                <Show when={c().details}>
                  <section>
                    <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">Notes</h4>
                    <p class="text-sm text-gray-700 dark:text-gray-300 leading-relaxed">{c().details}</p>
                  </section>
                </Show>
              </div>

              {/* Right column: files + navigation */}
              <div class="space-y-5">
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

                <section>
                  <h4 class="text-[11px] uppercase tracking-wider text-gray-500 dark:text-gray-400 mb-2">See this component in…</h4>
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
                        Deep dive → {d().title}
                      </A>
                    )}
                  </Show>
                </section>
              </div>
            </div>
          </section>
        );
      }}
    </Show>
  );
}
