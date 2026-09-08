/**
 * BookChapter — one chapter: sidebar navigation, rendered markdown with
 * hydrated widgets, prev/next, mark-complete.
 */
import { createResource, createMemo, For, Show } from 'solid-js';
import { A, useParams, useNavigate } from '@solidjs/router';
import { processDocument } from '../../lib/markdown';
import { hydrateWidgets } from '../../lib/hydrateWidgets';
import { fetchBook, groupParts, romanPart, type BookChapterMeta } from '../../lib/book';
import { progress, isChapterComplete, setChapterComplete } from '../../state/progress';

let manifestPromise: Promise<Record<string, string[]>> | null = null;
function fetchDocManifest(): Promise<Record<string, string[]>> {
  if (!manifestPromise) {
    manifestPromise = fetch('/api/doc-manifest')
      .then(r => (r.ok ? r.json() : {}))
      .catch(() => ({}));
  }
  return manifestPromise;
}

async function fetchAndProcess(slug: string) {
  const [res, manifest] = await Promise.all([
    fetch(`/api/docs/book/${slug}`),
    fetchDocManifest(),
  ]);
  if (!res.ok) throw new Error(`Chapter not found: ${res.status}`);
  const markdown = await res.text();
  return processDocument(markdown, { basePath: '/book', slug, manifest });
}

export default function BookChapter() {
  const params = useParams<{ slug: string }>();
  const navigate = useNavigate();

  const [doc] = createResource(() => params.slug, fetchAndProcess);
  const [chapters] = createResource(fetchBook);
  const parts = createMemo(() => groupParts(chapters() || []));

  const flat = createMemo<BookChapterMeta[]>(() => chapters() || []);
  const idx = createMemo(() => flat().findIndex(c => c.slug === params.slug));
  const prev = createMemo(() => (idx() > 0 ? flat()[idx() - 1] : null));
  const next = createMemo(() => (idx() >= 0 && idx() < flat().length - 1 ? flat()[idx() + 1] : null));
  const meta = createMemo(() => (idx() >= 0 ? flat()[idx()] : null));

  const complete = createMemo(() => {
    progress(); // subscribe
    return isChapterComplete(params.slug);
  });

  function markDoneAndAdvance() {
    setChapterComplete(params.slug, true);
    const n = next();
    if (n) {
      navigate(`/book/${n.slug}`);
      window.scrollTo(0, 0);
    }
  }

  return (
    <div class="flex min-h-full">
      {/* Sidebar */}
      <aside
        class="w-64 shrink-0 border-r border-gray-200 dark:border-gray-700 bg-gray-50/50 dark:bg-gray-900/40 hidden lg:block"
      >
        <div class="sticky top-0 max-h-screen overflow-y-auto p-4">
          <A href="/book" class="block text-sm font-semibold text-gray-900 dark:text-white mb-4 hover:text-blue-600">
            ← The CALC Book
          </A>
          <For each={parts()}>
            {(part) => (
              <div class="mb-4">
                <div class="text-[11px] font-semibold uppercase tracking-wide text-gray-400 dark:text-gray-500 mb-1.5">
                  {romanPart(part.part)}. {part.title}
                </div>
                <ul class="space-y-0.5">
                  <For each={part.chapters}>
                    {(ch) => (
                      <li>
                        <A
                          href={`/book/${ch.slug}`}
                          class="flex items-center gap-1.5 px-2 py-1 rounded text-[13px] transition-colors"
                          classList={{
                            'bg-blue-100 dark:bg-blue-900/40 text-blue-800 dark:text-blue-300 font-medium':
                              ch.slug === params.slug,
                            'text-gray-600 dark:text-gray-400 hover:bg-gray-100 dark:hover:bg-gray-800':
                              ch.slug !== params.slug,
                          }}
                        >
                          <span class="w-4 shrink-0 text-[11px] text-gray-400">
                            {isChapterComplete(ch.slug) ? '✓' : ch.chapter}
                          </span>
                          <span class="truncate">{ch.title}</span>
                        </A>
                      </li>
                    )}
                  </For>
                </ul>
              </div>
            )}
          </For>
        </div>
      </aside>

      {/* Content */}
      <div class="flex-1 min-w-0">
        <div class="mx-auto px-6 py-6" style="max-width: 860px">
          {/* Mobile breadcrumb */}
          <div class="lg:hidden mb-4">
            <A href="/book" class="text-sm text-blue-600 hover:underline">← The CALC Book</A>
          </div>

          <Show when={doc.loading}>
            <p class="text-gray-500">Loading…</p>
          </Show>
          <Show when={doc.error}>
            <p class="text-red-500">Error: {doc.error?.message}</p>
          </Show>

          <Show when={doc()}>
            {(d) => (
              <>
                <header class="mb-6">
                  <Show when={meta()}>
                    <div class="text-xs font-mono text-gray-400 mb-1">
                      Part {romanPart(meta()!.part || 0)} · Chapter {meta()!.chapter}
                    </div>
                  </Show>
                  <h1 class="text-3xl font-bold text-gray-900 dark:text-white">
                    {d().title}
                  </h1>
                </header>

                <article
                  ref={(el) => {
                    requestAnimationFrame(() => hydrateWidgets(el, { slug: params.slug }));
                  }}
                  class="prose-research book-content"
                  innerHTML={d().html}
                />

                {/* Footer nav */}
                <footer class="mt-12 pt-6 border-t border-gray-200 dark:border-gray-700">
                  <div class="flex items-center justify-center mb-6">
                    <button
                      onClick={markDoneAndAdvance}
                      class="px-4 py-2 rounded-lg font-medium transition-colors"
                      classList={{
                        'bg-green-600 text-white hover:bg-green-700': !complete(),
                        'bg-green-100 dark:bg-green-900/30 text-green-700 dark:text-green-400 border border-green-300 dark:border-green-800': complete(),
                      }}
                    >
                      {complete() ? '✓ Completed' : next() ? 'Mark complete & continue →' : 'Mark complete'}
                    </button>
                  </div>
                  <div class="flex justify-between gap-4">
                    <Show when={prev()} fallback={<span />}>
                      <A
                        href={`/book/${prev()!.slug}`}
                        class="group flex flex-col items-start px-4 py-3 rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-300 dark:hover:border-blue-700 max-w-[45%]"
                      >
                        <span class="text-xs text-gray-400">← Previous</span>
                        <span class="text-sm font-medium text-gray-700 dark:text-gray-300 group-hover:text-blue-600 truncate">
                          {prev()!.title}
                        </span>
                      </A>
                    </Show>
                    <Show when={next()} fallback={<span />}>
                      <A
                        href={`/book/${next()!.slug}`}
                        class="group flex flex-col items-end px-4 py-3 rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-300 dark:hover:border-blue-700 max-w-[45%] ml-auto"
                      >
                        <span class="text-xs text-gray-400">Next →</span>
                        <span class="text-sm font-medium text-gray-700 dark:text-gray-300 group-hover:text-blue-600 truncate">
                          {next()!.title}
                        </span>
                      </A>
                    </Show>
                  </div>
                </footer>
              </>
            )}
          </Show>
        </div>
      </div>
    </div>
  );
}
