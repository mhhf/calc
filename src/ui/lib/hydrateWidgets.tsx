/**
 * Widget hydration — mounts interactive Solid components into the
 * `.client-render` placeholder divs emitted by markdown.ts.
 *
 * One entry point for every client-rendered block: course widgets
 * (widget-prove, widget-formula, widget-quiz, widget-exec, widget-game,
 * widget-collapse), proof trees, and mermaid diagrams.
 */
import { render } from 'solid-js/web';
import type { Component } from 'solid-js';

export interface WidgetCtx {
  /** Chapter/doc slug — namespaces exercise progress. */
  slug: string;
}

export interface WidgetProps {
  body: string;
  args: string[];
  options: Record<string, string>;
  slug: string;
}

// Lazy component registry — each widget loads only when a page uses it.
const registry: Record<string, () => Promise<{ default: Component<WidgetProps> }>> = {
  prove: () => import('../components/widgets/EmbedProve'),
  formula: () => import('../components/widgets/FormulaPlayground'),
  quiz: () => import('../components/widgets/Quiz'),
  exec: () => import('../components/widgets/ForwardStepper'),
  game: () => import('../components/widgets/TimedGame'),
  collapse: () => import('../components/widgets/CollapseView'),
};

export function hydrateWidgets(root: HTMLElement, ctx: WidgetCtx) {
  // Course widgets
  const widgetEls = root.querySelectorAll<HTMLElement>('.client-render[data-processor^="widget-"]');
  widgetEls.forEach((el) => {
    if (el.dataset.hydrated) return;
    el.dataset.hydrated = '1';
    const kind = (el.dataset.processor || '').replace(/^widget-/, '');
    const loader = registry[kind];
    if (!loader) return;
    const body = el.querySelector('.client-source')?.textContent || '';
    const args = (el.dataset.args || '').split(/\s+/).filter(Boolean);
    let options: Record<string, string> = {};
    try {
      options = JSON.parse(el.dataset.options || '{}');
    } catch { /* malformed options — widget gets none */ }
    loader()
      .then(({ default: Comp }) => {
        el.innerHTML = '';
        render(() => <Comp body={body} args={args} options={options} slug={ctx.slug} />, el);
      })
      .catch((e) => {
        el.innerHTML = `<pre class="error">widget "${kind}" failed to load: ${e?.message || e}</pre>`;
      });
  });

  // Proof trees (shared with DocPage)
  const proofEls = root.querySelectorAll('.client-render[data-processor="proof-tree"]');
  if (proofEls.length > 0) {
    import('../components/proof-block/ProofBlock')
      .then(({ hydrateProofBlocks }) => hydrateProofBlocks(root))
      .catch((e) => console.error('proof-block hydration failed', e));
  }

  // Mermaid diagrams (shared with DocPage)
  const mermaidEls = root.querySelectorAll('.client-render[data-processor="mermaid"]');
  if (mermaidEls.length > 0) {
    import('https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs' as any)
      .then(({ default: mermaid }: any) => {
        mermaid.initialize({ startOnLoad: false, theme: 'neutral' });
        mermaidEls.forEach(async (block: Element, i: number) => {
          const source = block.querySelector('.client-source')?.textContent || '';
          try {
            const { svg } = await mermaid.render(`mermaid-w-${i}`, source);
            block.innerHTML = svg;
          } catch { /* diagram error — leave source visible */ }
        });
      })
      .catch(() => {});
  }
}

/**
 * Parse a `key: value` widget body. Lines that don't start with a known key
 * continue the previous value (multi-line hints etc.).
 */
export function parseSpecBody(body: string, keys: string[]): Record<string, string> {
  const spec: Record<string, string> = {};
  let current: string | null = null;
  for (const line of body.split('\n')) {
    const m = line.match(/^(\w+)\s*:\s*(.*)$/);
    if (m && keys.includes(m[1])) {
      current = m[1];
      spec[current] = m[2];
    } else if (current !== null && line.trim() !== '') {
      spec[current] += '\n' + line;
    }
  }
  return spec;
}
