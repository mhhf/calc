import { createMemo, createResource, For, Show } from 'solid-js';
import { A, useParams, useLocation } from '@solidjs/router';
import { processDocument } from '../lib/markdown';

type Backlink = { folder: string; slug: string; title: string };
type BacklinkIndex = Record<string, Backlink[]>;

// Session-level singleton — manifest rarely changes and is shared across pages.
let backlinksPromise: Promise<BacklinkIndex> | null = null;
function fetchBacklinks(): Promise<BacklinkIndex> {
  if (!backlinksPromise) {
    backlinksPromise = fetch('/api/backlinks')
      .then(r => (r.ok ? r.json() : {}))
      .catch(() => ({}));
  }
  return backlinksPromise;
}

async function fetchAndProcess(args: { folder: string; slug: string }) {
  const res = await fetch(`/api/docs/${args.folder}/${args.slug}`);
  if (!res.ok) throw new Error(`Not found: ${res.status}`);
  const markdown = await res.text();
  const basePath = `/${args.folder}`;
  return processDocument(markdown, { basePath, slug: args.slug });
}

export default function DocPage() {
  const params = useParams<{ slug: string }>();
  const location = useLocation();
  const folder = () => location.pathname.split('/')[1];
  const [doc] = createResource(
    () => ({ folder: folder(), slug: params.slug }),
    fetchAndProcess,
  );
  const [backlinks] = createResource(fetchBacklinks);

  const incoming = createMemo<Backlink[]>(() => {
    const idx = backlinks();
    if (!idx) return [];
    return idx[`${folder()}/${params.slug}`] || [];
  });

  function hydrateBlocks(el: HTMLElement) {
    const mermaidBlocks = el.querySelectorAll('.client-render[data-processor="mermaid"]');
    if (mermaidBlocks.length > 0) {
      import('https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs' as any).then(({ default: mermaid }: any) => {
        mermaid.initialize({ startOnLoad: false, theme: 'neutral' });
        mermaidBlocks.forEach(async (block: Element, i: number) => {
          const source = block.querySelector('.client-source')?.textContent || '';
          try {
            const { svg } = await mermaid.render(`mermaid-${i}`, source);
            block.innerHTML = svg;
          } catch {}
        });
      }).catch(() => {});
    }
  }

  return (
    <div class="mx-auto px-6 py-6" style="max-width: 960px">
      <A
        href={`/${folder()}`}
        class="inline-flex items-center gap-1 text-sm text-blue-600 hover:underline mb-4"
      >
        &larr; Back
      </A>

      <Show when={doc.loading}>
        <p class="text-gray-500">Loading...</p>
      </Show>

      <Show when={doc.error}>
        <p class="text-red-500">Error: {doc.error?.message}</p>
      </Show>

      <Show when={doc()}>
        {(d) => (
          <div class="doc-card px-10 py-8">
            <h1 class="text-2xl font-bold text-gray-900 dark:text-white mb-6">
              {d().title}
            </h1>
            <article
              ref={(el) => {
                requestAnimationFrame(() => hydrateBlocks(el));
              }}
              class="prose-research"
              innerHTML={d().html}
            />

            <Show when={incoming().length > 0}>
              <nav
                aria-label="Referenced by"
                class="mt-10 pt-6 border-t border-gray-200 dark:border-gray-700"
              >
                <h2 class="text-sm font-semibold tracking-wide uppercase text-gray-500 dark:text-gray-400 mb-3">
                  Referenced by
                </h2>
                <ul class="space-y-1.5">
                  <For each={incoming()}>
                    {(b) => (
                      <li>
                        <A
                          href={`/${b.folder}/${b.slug}`}
                          class="inline-flex items-baseline gap-2 text-sm text-blue-600 dark:text-blue-400 hover:underline"
                        >
                          <span class="font-mono text-xs text-gray-400">{b.folder}</span>
                          <span>{b.title}</span>
                        </A>
                      </li>
                    )}
                  </For>
                </ul>
              </nav>
            </Show>
          </div>
        )}
      </Show>
    </div>
  );
}
