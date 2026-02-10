import { createResource, For, Show } from "solid-js";
import { A } from "@solidjs/router";
import { Title } from "@solidjs/meta";

// Research document metadata
interface ResearchDoc {
  slug: string;
  title: string;
  description: string;
  tags: string[];
}

// Fetch research index from API
async function fetchResearchIndex(): Promise<ResearchDoc[]> {
  const response = await fetch("/api/research");
  return response.json();
}

export default function ResearchIndex() {
  const [docs] = createResource(fetchResearchIndex);

  return (
    <>
      <Title>Research Index - CALC</Title>

      <div class="prose">
        <h1>Research Document Index</h1>
        <p class="text-gray-400">
          Cross-reference and summary of research documents on linear logic,
          display calculus, ownership semantics, and proof theory.
        </p>

        <Show when={docs.loading}>
          <div class="text-gray-500">Loading research index...</div>
        </Show>

        <Show when={docs.error}>
          <div class="text-red-400">Error loading index: {docs.error?.message}</div>
        </Show>

        <Show when={docs()}>
          <div class="space-y-4 mt-8">
            <For each={docs()}>
              {(doc) => (
                <div class="bg-gray-900 border border-gray-800 rounded-lg p-4 hover:border-gray-700 transition-colors">
                  <A
                    href={`/research/${doc.slug}`}
                    class="text-lg font-medium text-blue-400 hover:text-blue-300"
                  >
                    {doc.title}
                  </A>
                  <p class="text-gray-400 text-sm mt-1">{doc.description}</p>
                  <div class="mt-2">
                    <For each={doc.tags}>
                      {(tag) => <span class="tag">{tag}</span>}
                    </For>
                  </div>
                </div>
              )}
            </For>
          </div>
        </Show>
      </div>
    </>
  );
}
