import { createResource, For, Show } from 'solid-js';
import { A, useLocation } from '@solidjs/router';

interface DocEntry {
  slug: string;
  title: string;
  summary: string;
  tags: string[];
  status: string;
}

const FOLDER_LABELS: Record<string, string> = {
  research: 'Research',
  dev: 'Development',
  docs: 'Documentation',
};

async function fetchDocs(folder: string): Promise<DocEntry[]> {
  const res = await fetch(`/api/docs/${folder}`);
  if (!res.ok) throw new Error(`Failed to fetch docs: ${res.status}`);
  return res.json();
}

export default function DocIndex() {
  const location = useLocation();
  const folder = () => location.pathname.split('/')[1]; // e.g. "research"
  const [docs] = createResource(folder, fetchDocs);

  return (
    <div class="mx-auto p-6" style="max-width: 1280px">
      <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-6">
        {FOLDER_LABELS[folder()] || folder()}
      </h2>

      <Show when={docs.loading}>
        <p class="text-gray-500">Loading...</p>
      </Show>

      <Show when={docs.error}>
        <p class="text-red-500">Error: {docs.error?.message}</p>
      </Show>

      <Show when={docs()}>
        <div class="space-y-3">
          <For each={docs()}>
            {(doc) => (
              <A
                href={`/${folder()}/${doc.slug}`}
                class="block p-4 bg-white dark:bg-gray-800 rounded-lg border border-gray-200 dark:border-gray-700 hover:border-blue-400 dark:hover:border-blue-500 transition-colors"
              >
                <div class="flex items-start justify-between gap-4">
                  <div class="min-w-0">
                    <h3 class="font-semibold text-gray-900 dark:text-white truncate">
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
                        'bg-yellow-100 text-yellow-800 dark:bg-yellow-900/30 dark:text-yellow-400': doc.status === 'draft',
                        'bg-blue-100 text-blue-800 dark:bg-blue-900/30 dark:text-blue-400': doc.status === 'review',
                        'bg-green-100 text-green-800 dark:bg-green-900/30 dark:text-green-400': doc.status === 'stable',
                      }}
                    >
                      {doc.status}
                    </span>
                  </Show>
                </div>
                <Show when={doc.tags?.length}>
                  <div class="flex flex-wrap gap-1 mt-2">
                    <For each={doc.tags}>
                      {(tag) => (
                        <span class="px-1.5 py-0.5 text-xs bg-gray-100 dark:bg-gray-700 text-gray-600 dark:text-gray-400 rounded">
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
      </Show>
    </div>
  );
}
