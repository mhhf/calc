import { createResource, Show } from 'solid-js';
import { A, useParams, useLocation } from '@solidjs/router';
import { processDocument } from '../lib/markdown';

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
            <h1 class="text-2xl font-bold text-gray-900 mb-6">
              {d().title}
            </h1>
            <article
              ref={(el) => {
                requestAnimationFrame(() => hydrateBlocks(el));
              }}
              class="prose-research"
              innerHTML={d().html}
            />
          </div>
        )}
      </Show>
    </div>
  );
}
