import { createEffect, createMemo, createResource, createSignal, For, Show } from 'solid-js';
import { A, useLocation } from '@solidjs/router';
import DocFolderNav from '../components/layout/DocFolderNav';

interface DocEntry {
  slug: string;
  title: string;
  summary: string;
  tags: string[];
  status: string;
}

const FOLDER_LABELS: Record<string, string> = {
  theory: 'Theory',
  def: 'Definitions',
  docs: 'Documentation',
};

/** Extract the 4-digit doc number from slug like "0007_chr-..." */
function docId(slug: string): string | null {
  const m = slug.match(/^(\d{4})/);
  return m ? `DOC_${m[1]}` : null;
}

async function fetchDocs(folder: string): Promise<DocEntry[]> {
  const res = await fetch(`/api/docs/${folder}`);
  if (!res.ok) throw new Error(`Failed to fetch docs: ${res.status}`);
  return res.json();
}

export default function DocIndex() {
  const location = useLocation();
  const folder = () => location.pathname.split('/')[1]; // e.g. "research"
  const [docs] = createResource(folder, fetchDocs);

  const [selected, setSelected] = createSignal<Set<string>>(new Set());

  // Reset tag selection when switching folders
  createEffect(() => {
    folder(); // track
    setSelected(new Set<string>());
  });

  /** Tag → document count in this folder (sorted by count desc, then name). */
  const allTags = createMemo<[string, number][]>(() => {
    const ds = docs();
    if (!ds) return [];
    const counts: Record<string, number> = {};
    for (const d of ds) for (const t of d.tags || []) counts[t] = (counts[t] || 0) + 1;
    return Object.entries(counts).sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]));
  });

  const filtered = createMemo<DocEntry[]>(() => {
    const ds = docs() || [];
    const sel = selected();
    if (sel.size === 0) return ds;
    return ds.filter(d => {
      for (const t of sel) if (!d.tags?.includes(t)) return false;
      return true;
    });
  });

  function toggleTag(t: string) {
    setSelected(prev => {
      const next = new Set(prev);
      if (next.has(t)) next.delete(t); else next.add(t);
      return next;
    });
  }

  return (
    <div class="mx-auto p-6" style="max-width: 1280px">
      <DocFolderNav />
      <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-6">
        {FOLDER_LABELS[folder()] || folder()}
      </h2>

      <Show when={docs.loading}>
        <p class="text-gray-500">Loading...</p>
      </Show>

      <Show when={docs.error}>
        <p class="text-red-500">Error: {docs.error?.message}</p>
      </Show>

      <Show when={allTags().length > 0}>
        <div class="mb-5">
          <div class="flex items-center gap-3 mb-2">
            <span class="text-xs font-semibold tracking-wide uppercase text-gray-500 dark:text-gray-400">
              Filter by tag
            </span>
            <Show when={selected().size > 0}>
              <button
                type="button"
                onClick={() => setSelected(new Set<string>())}
                class="text-xs text-blue-600 dark:text-blue-400 hover:underline"
              >
                Clear ({selected().size})
              </button>
            </Show>
            <Show when={selected().size > 0}>
              <span class="text-xs text-gray-500 dark:text-gray-400">
                {filtered().length} of {docs()?.length ?? 0} match
              </span>
            </Show>
          </div>
          <div class="flex flex-wrap gap-1.5">
            <For each={allTags()}>
              {([tag, count]) => {
                const active = () => selected().has(tag);
                return (
                  <button
                    type="button"
                    onClick={() => toggleTag(tag)}
                    aria-pressed={active()}
                    class="inline-flex items-center gap-1 px-2 py-0.5 text-xs rounded border transition-colors"
                    classList={{
                      'bg-blue-600 border-blue-600 text-white hover:bg-blue-700': active(),
                      'bg-gray-100 dark:bg-gray-700 border-gray-200 dark:border-gray-600 text-gray-700 dark:text-gray-300 hover:border-blue-400': !active(),
                    }}
                  >
                    <span>{tag}</span>
                    <span
                      class="text-[10px] tabular-nums"
                      classList={{
                        'text-blue-100': active(),
                        'text-gray-400 dark:text-gray-500': !active(),
                      }}
                    >
                      {count}
                    </span>
                  </button>
                );
              }}
            </For>
          </div>
        </div>
      </Show>

      <Show when={docs() && filtered().length === 0}>
        <p class="text-sm text-gray-500 dark:text-gray-400 py-8 text-center">
          No documents match the selected tags.
        </p>
      </Show>

      <Show when={filtered().length > 0}>
        <div class="space-y-3">
          <For each={filtered()}>
            {(doc) => {
              const id = docId(doc.slug);
              return (
                <div class="relative p-4 bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-400 dark:hover:border-blue-500 transition-colors">
                  {/* Overlay anchor: whole card is clickable EXCEPT where relative z-10 elements sit */}
                  <A
                    href={`/${folder()}/${doc.slug}`}
                    class="absolute inset-0 rounded-lg focus:outline-none focus:ring-2 focus:ring-blue-500"
                    aria-label={doc.title}
                  />
                  <div class="relative flex items-start justify-between gap-4 pointer-events-none">
                    <div class="min-w-0">
                      <h3 class="font-semibold text-gray-900 dark:text-white truncate">
                        {id && <span class="font-mono text-xs text-gray-400 mr-2">{id}</span>}
                        {doc.title}
                      </h3>
                      <Show when={doc.summary}>
                        <p class="text-sm text-gray-600 dark:text-gray-400 mt-1 line-clamp-2">
                          {doc.summary}
                        </p>
                      </Show>
                    </div>
                    <Show when={doc.status}>
                      <span
                        class="shrink-0 px-2 py-0.5 text-xs rounded"
                        classList={{
                          'bg-gray-200 text-gray-700 dark:bg-gray-700 dark:text-gray-300': doc.status === 'draft' || doc.status === 'review',
                          'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400': doc.status === 'stable',
                        }}
                      >
                        {doc.status}
                      </span>
                    </Show>
                  </div>
                  <Show when={doc.tags?.length}>
                    <div class="relative flex flex-wrap gap-1 mt-2 z-10 w-fit">
                      <For each={doc.tags}>
                        {(tag) => {
                          const active = () => selected().has(tag);
                          return (
                            <button
                              type="button"
                              onClick={() => toggleTag(tag)}
                              class="px-1.5 py-0.5 text-xs rounded transition-colors"
                              classList={{
                                'bg-blue-600 text-white': active(),
                                'bg-gray-100 dark:bg-gray-700 text-gray-600 dark:text-gray-400 hover:bg-blue-100 dark:hover:bg-blue-900/30': !active(),
                              }}
                            >
                              {tag}
                            </button>
                          );
                        }}
                      </For>
                    </div>
                  </Show>
                </div>
              );
            }}
          </For>
        </div>
      </Show>
    </div>
  );
}
