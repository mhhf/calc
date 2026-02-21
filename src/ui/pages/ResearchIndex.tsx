import { createResource, createSignal, createMemo, For, Show } from 'solid-js';
import { A, useLocation } from '@solidjs/router';

interface DocEntry {
  slug: string;
  title: string;
  summary: string;
  tags: string[];
  status: string;
  modified: string;
  category: string;
}

const FOLDER_LABELS: Record<string, string> = {
  research: 'Research',
  theory: 'Theory',
  def: 'Definitions',
};

/** Fixed display order for research categories (matches INDEX.md sections) */
const CATEGORY_ORDER = [
  'Motivation',
  'Key Insights',
  'Ownership',
  'Proof Theory',
  'Multi-Type Framework',
  'Related Paradigms',
  'Implementation',
  'Performance',
  'Semantic Foundations',
  'Reference',
  'Symbolic Execution',
  'Forward Chaining',
  'Uncategorized',
];

async function fetchDocs(folder: string): Promise<DocEntry[]> {
  const res = await fetch(`/api/docs/${folder}`);
  if (!res.ok) throw new Error(`Failed to fetch docs: ${res.status}`);
  return res.json();
}

export default function ResearchIndex() {
  const location = useLocation();
  const folder = () => location.pathname.split('/')[1];
  const [docs] = createResource(folder, fetchDocs);
  const [activeTag, setActiveTag] = createSignal<string | null>(null);
  const [tagsExpanded, setTagsExpanded] = createSignal(false);
  const TAG_COLLAPSE_LIMIT = 16;

  /** Tag frequency map across all docs */
  const tagCounts = createMemo(() => {
    const counts: Record<string, number> = {};
    for (const doc of docs() || []) {
      for (const tag of doc.tags || []) {
        counts[tag] = (counts[tag] || 0) + 1;
      }
    }
    return counts;
  });

  /** Tags with count >= 2, sorted by frequency descending, then alphabetically */
  const sortedTags = createMemo(() =>
    Object.entries(tagCounts())
      .filter(([, count]) => count >= 2)
      .sort((a, b) => b[1] - a[1] || a[0].localeCompare(b[0]))
      .map(([tag]) => tag)
  );

  /** Visible tags (collapsed or expanded) */
  const visibleTags = createMemo(() => {
    const all = sortedTags();
    if (tagsExpanded() || all.length <= TAG_COLLAPSE_LIMIT) return all;
    return all.slice(0, TAG_COLLAPSE_LIMIT);
  });

  /** Docs filtered by active tag */
  const filteredDocs = createMemo(() => {
    const all = docs() || [];
    const tag = activeTag();
    if (!tag) return all;
    return all.filter(d => d.tags?.includes(tag));
  });

  /** Docs grouped by category, ordered by CATEGORY_ORDER */
  const groupedDocs = createMemo(() => {
    const groups: Record<string, DocEntry[]> = {};
    for (const doc of filteredDocs()) {
      const cat = doc.category || 'Uncategorized';
      (groups[cat] ??= []).push(doc);
    }
    // Sort docs within each group alphabetically by title
    for (const cat of Object.keys(groups)) {
      groups[cat].sort((a, b) => a.title.localeCompare(b.title));
    }
    // Return ordered array of [category, docs[]]
    const ordered: [string, DocEntry[]][] = [];
    for (const cat of CATEGORY_ORDER) {
      if (groups[cat]) ordered.push([cat, groups[cat]]);
    }
    // Any categories not in CATEGORY_ORDER (before Uncategorized)
    for (const cat of Object.keys(groups)) {
      if (!CATEGORY_ORDER.includes(cat)) {
        ordered.push([cat, groups[cat]]);
      }
    }
    return ordered;
  });

  return (
    <div class="mx-auto p-6" style="max-width: 1280px">
      {/* Header */}
      <div class="flex items-baseline justify-between mb-4">
        <h2 class="text-2xl font-bold text-gray-900 dark:text-white">
          {FOLDER_LABELS[folder()] || folder()}
        </h2>
        <Show when={docs()}>
          <span class="text-sm text-gray-500">
            {filteredDocs().length} document{filteredDocs().length !== 1 ? 's' : ''}
            <Show when={activeTag()}>
              {' '}matching <span class="font-medium text-blue-600 dark:text-blue-400">{activeTag()}</span>
            </Show>
          </span>
        </Show>
      </div>

      <Show when={docs.loading}>
        <p class="text-gray-500">Loading...</p>
      </Show>

      <Show when={docs.error}>
        <p class="text-red-500">Error: {docs.error?.message}</p>
      </Show>

      <Show when={docs()}>
        {/* Tag cloud */}
        <Show when={sortedTags().length > 0}>
          <div class="flex flex-wrap gap-1.5 mb-6 pb-4 border-b border-gray-200 dark:border-gray-700">
            <For each={visibleTags()}>
              {(tag) => {
                const count = () => tagCounts()[tag];
                const isActive = () => activeTag() === tag;
                return (
                  <button
                    class="px-2 py-0.5 text-xs rounded-full transition-colors cursor-pointer"
                    classList={{
                      'bg-blue-600 text-white ring-2 ring-blue-400 ring-offset-1 dark:ring-offset-gray-900': isActive(),
                      'bg-gray-100 dark:bg-gray-700 text-gray-600 dark:text-gray-400 hover:bg-gray-200 dark:hover:bg-gray-600': !isActive(),
                    }}
                    onClick={() => setActiveTag(isActive() ? null : tag)}
                  >
                    {tag} <span class="opacity-60">{count()}</span>
                  </button>
                );
              }}
            </For>
            <Show when={!tagsExpanded() && sortedTags().length > TAG_COLLAPSE_LIMIT}>
              <button
                class="px-2 py-0.5 text-xs rounded-full bg-gray-200 dark:bg-gray-600 text-gray-500 dark:text-gray-300 hover:bg-gray-300 dark:hover:bg-gray-500 cursor-pointer transition-colors"
                onClick={() => setTagsExpanded(true)}
              >
                +{sortedTags().length - TAG_COLLAPSE_LIMIT} more
              </button>
            </Show>
          </div>
        </Show>

        {/* Category index */}
        <Show when={groupedDocs().length > 0}>
          <div class="prose-research">
            <nav class="toc">
              <span class="toc-title">Index</span>
              <ul>
                <For each={groupedDocs()}>
                  {([category, categoryDocs]) => (
                    <li>
                      <a
                        href={`#section-${category.toLowerCase().replace(/\s+/g, '-')}`}
                        onClick={(e) => {
                          e.preventDefault();
                          document.getElementById(`section-${category.toLowerCase().replace(/\s+/g, '-')}`)?.scrollIntoView({ behavior: 'smooth' });
                        }}
                      >
                        {category}
                      </a>
                      <ul>
                        <For each={categoryDocs}>
                          {(doc) => (
                            <li>
                              <a
                                href={`#cat-${doc.slug}`}
                                onClick={(e) => {
                                  e.preventDefault();
                                  document.getElementById(`cat-${doc.slug}`)?.scrollIntoView({ behavior: 'smooth' });
                                }}
                              >
                                {doc.title}
                              </a>
                            </li>
                          )}
                        </For>
                      </ul>
                    </li>
                  )}
                </For>
              </ul>
            </nav>
          </div>
        </Show>

        {/* Category sections */}
        <div class="space-y-8">
          <For each={groupedDocs()}>
            {([category, categoryDocs]) => (
              <section>
                <h3
                  id={`section-${category.toLowerCase().replace(/\s+/g, '-')}`}
                  class="text-sm font-medium text-gray-400 dark:text-gray-500 uppercase tracking-wide mb-3"
                >
                  {category}
                  <span class="ml-2 text-gray-300 dark:text-gray-600">{categoryDocs.length}</span>
                </h3>
                <div class="space-y-2">
                  <For each={categoryDocs}>
                    {(doc) => (
                      <A
                        id={`cat-${doc.slug}`}
                        href={`/${folder()}/${doc.slug}`}
                        class="block p-4 bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-400 dark:hover:border-blue-500 transition-colors"
                      >
                        <div class="flex items-start justify-between gap-4">
                          <div class="min-w-0 flex-1">
                            <h4 class="font-semibold text-gray-900 dark:text-white truncate">
                              {doc.title}
                            </h4>
                            <Show when={doc.summary}>
                              <p class="text-sm text-gray-600 dark:text-gray-400 mt-1 line-clamp-2">
                                {doc.summary}
                              </p>
                            </Show>
                          </div>
                          <div class="shrink-0 flex items-center gap-2">
                            <Show when={doc.status}>
                              <span
                                class="px-2 py-0.5 text-xs rounded"
                                classList={{
                                  'bg-yellow-100 text-yellow-800 dark:bg-yellow-900/30 dark:text-yellow-400': doc.status === 'draft',
                                  'bg-blue-100 text-blue-800 dark:bg-blue-900/30 dark:text-blue-400': doc.status === 'review',
                                  'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400': doc.status === 'stable',
                                }}
                              >
                                {doc.status}
                              </span>
                            </Show>
                            <Show when={doc.modified}>
                              <span class="text-xs text-gray-400 dark:text-gray-500 tabular-nums">
                                {doc.modified}
                              </span>
                            </Show>
                          </div>
                        </div>
                        <Show when={doc.tags?.length}>
                          <div class="flex flex-wrap gap-1 mt-2">
                            <For each={doc.tags}>
                              {(tag) => (
                                <span
                                  class="px-1.5 py-0.5 text-xs rounded"
                                  classList={{
                                    'bg-blue-100 dark:bg-blue-900/30 text-blue-700 dark:text-blue-300': activeTag() === tag,
                                    'bg-gray-100 dark:bg-gray-700 text-gray-600 dark:text-gray-400': activeTag() !== tag,
                                  }}
                                >
                                  {tag}
                                </span>
                              )}
                            </For>
                          </div>
                        </Show>
                      </A>
                    )}
                  </For>
                </div>
              </section>
            )}
          </For>
        </div>
      </Show>
    </div>
  );
}
