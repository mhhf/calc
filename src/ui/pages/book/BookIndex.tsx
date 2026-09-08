/**
 * BookIndex — course table of contents: parts, chapters, progress.
 */
import { createResource, createMemo, createSignal, For, Show } from 'solid-js';
import { A } from '@solidjs/router';
import { fetchBook, groupParts, romanPart } from '../../lib/book';
import { progress, isChapterComplete, completedCount } from '../../state/progress';

export default function BookIndex() {
  const [chapters] = createResource(fetchBook);
  const [filter, setFilter] = createSignal('');
  const parts = createMemo(() => {
    const q = filter().trim().toLowerCase();
    const all = chapters() || [];
    const filtered = q
      ? all.filter(c => `${c.title} ${c.summary}`.toLowerCase().includes(q))
      : all;
    return groupParts(filtered);
  });

  const total = createMemo(() => (chapters() || []).length);
  const done = createMemo(() => {
    progress(); // subscribe
    return completedCount((chapters() || []).map(c => c.slug));
  });

  return (
    <div class="mx-auto px-6 py-8" style="max-width: 880px">
      <header class="mb-8">
        <h1 class="text-3xl font-bold text-gray-900 dark:text-white mb-2">
          The CALC Book
        </h1>
        <p class="text-gray-600 dark:text-gray-400 max-w-2xl">
          An interactive course on linear logic and the CALC system — from your
          first sequent proof to timed, graded, probabilistic, and certified
          execution. Every chapter has live widgets: build proofs by clicking,
          run programs, play the games.
        </p>
        <Show when={total() > 0}>
          <input
            type="search"
            value={filter()}
            onInput={(e) => setFilter(e.currentTarget.value)}
            placeholder="Filter chapters…"
            class="mt-4 w-full max-w-xs px-3 py-1.5 text-sm rounded border border-gray-300 dark:border-gray-600 bg-white dark:bg-gray-900 text-gray-900 dark:text-gray-100 focus:outline-none focus:ring-2 focus:ring-blue-500"
          />
          <div class="mt-4 flex items-center gap-3">
            <div class="flex-1 max-w-xs h-2 rounded-full bg-gray-200 dark:bg-gray-700 overflow-hidden">
              <div
                class="h-full bg-green-500 transition-all"
                style={{ width: `${(done() / total()) * 100}%` }}
              />
            </div>
            <span class="text-sm text-gray-500 dark:text-gray-400">
              {done()}/{total()} chapters
            </span>
          </div>
        </Show>
      </header>

      <Show when={chapters.loading}>
        <p class="text-gray-500">Loading…</p>
      </Show>

      <Show when={!chapters.loading && total() === 0}>
        <p class="text-gray-500 dark:text-gray-400">
          No chapters found — the book content lives in <code>doc/book/</code>.
        </p>
      </Show>

      <div class="space-y-8">
        <For each={parts()}>
          {(part) => (
            <section>
              <h2 class="text-lg font-semibold text-gray-900 dark:text-white mb-3 flex items-baseline gap-2">
                <span class="text-sm font-mono text-gray-400">Part {romanPart(part.part)}</span>
                <span>{part.title}</span>
              </h2>
              <ol class="space-y-2">
                <For each={part.chapters}>
                  {(ch) => (
                    <li>
                      <A
                        href={`/book/${ch.slug}`}
                        class="group flex items-start gap-3 px-4 py-3 rounded-lg border border-gray-200 dark:border-gray-700 bg-white dark:bg-gray-800 hover:border-blue-300 dark:hover:border-blue-700 hover:shadow-sm transition-all"
                      >
                        <span
                          class="mt-0.5 w-6 h-6 shrink-0 rounded-full flex items-center justify-center text-xs font-semibold"
                          classList={{
                            'bg-green-100 dark:bg-green-900/40 text-green-700 dark:text-green-400':
                              isChapterComplete(ch.slug),
                            'bg-gray-100 dark:bg-gray-700 text-gray-500 dark:text-gray-400':
                              !isChapterComplete(ch.slug),
                          }}
                        >
                          {isChapterComplete(ch.slug) ? '✓' : ch.chapter}
                        </span>
                        <span class="min-w-0">
                          <span class="block font-medium text-gray-900 dark:text-gray-100 group-hover:text-blue-600 dark:group-hover:text-blue-400">
                            {ch.title}
                          </span>
                          <Show when={ch.summary}>
                            <span class="block text-sm text-gray-500 dark:text-gray-400 mt-0.5">
                              {ch.summary}
                            </span>
                          </Show>
                        </span>
                      </A>
                    </li>
                  )}
                </For>
              </ol>
            </section>
          )}
        </For>
      </div>
    </div>
  );
}
