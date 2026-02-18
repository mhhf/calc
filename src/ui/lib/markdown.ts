/**
 * Hybrid Markdown Processor
 *
 * Uses `marked` for core markdown parsing with highlight.js for syntax
 * highlighting. Special code blocks (graphviz, katex, mermaid, calc)
 * are extracted before parsing and re-injected after.
 *
 * Code block syntax:
 *   ```{graphviz}     - Server-rendered GraphViz
 *   ```{mermaid}      - Client-side Mermaid (hydrated)
 *   ```{calc}         - Server-rendered CALC formula
 *   ```{katex}        - Server-rendered KaTeX math
 *   ```javascript     - Syntax highlighted code block
 */

import { Marked } from 'marked';
import { markedHighlight } from 'marked-highlight';
import hljs from 'highlight.js';
import katex from 'katex';

// Types
export interface Frontmatter {
  title?: string;
  created?: string;
  modified?: string;
  summary?: string;
  tags?: string[];
  status?: 'draft' | 'review' | 'stable';
  priority?: 'HIGH' | 'MEDIUM' | 'LOW';
  [key: string]: unknown;
}

export interface ProcessedDocument {
  frontmatter: Frontmatter;
  html: string;
  title: string;
  backlinks?: string[];
}

// Configure marked with highlight.js
// basePath is set per-render before calling marked.parse()
let currentBasePath = '/research';

const marked = new Marked(
  markedHighlight({
    emptyLangClass: 'hljs',
    langPrefix: 'hljs language-',
    highlight(code, lang) {
      if (lang && hljs.getLanguage(lang)) {
        return hljs.highlight(code, { language: lang }).value;
      }
      return hljs.highlightAuto(code).value;
    },
  }),
  {
    renderer: {
      // Handle .md links and external links
      link({ href, text }) {
        if (href.endsWith('.md')) {
          href = currentBasePath + '/' + href.replace(/\.md$/, '');
        }
        if (href.startsWith('#')) {
          return `<a href="${href}">${text}</a>`;
        }
        if (href.startsWith('http://') || href.startsWith('https://')) {
          return `<a href="${href}" target="_blank" rel="noopener">${text}</a>`;
        }
        return `<a href="${href}">${text}</a>`;
      },
    },
  }
);

// Server-side processors for special code blocks
const serverProcessors: Record<string, (code: string, options?: Record<string, string>) => Promise<string> | string> = {
  katex: (code: string) => {
    try {
      return `<div class="math-block">${katex.renderToString(code.trim(), {
        displayMode: true,
        throwOnError: false
      })}</div>`;
    } catch (e) {
      return `<pre class="error">KaTeX error: ${(e as Error).message}</pre>`;
    }
  },

  graphviz: async (code: string) => {
    try {
      const { Graphviz } = await import('@hpcc-js/wasm-graphviz');
      const graphviz = await Graphviz.load();
      const svg = graphviz.dot(code.trim());
      return `<div class="graphviz-diagram">${svg}</div>`;
    } catch (e) {
      return `<pre class="error">GraphViz error: ${(e as Error).message}</pre>`;
    }
  },

  viz: async (code: string) => serverProcessors.graphviz(code),

  calc: (code: string) => {
    try {
      const { parseFormula, renderFormula } = require('./calculus');
      const formula = parseFormula(code.trim());
      const latex = renderFormula(formula, 'latex');
      return `<span class="calc-formula">${katex.renderToString(latex, {
        displayMode: true,
        throwOnError: false
      })}</span>`;
    } catch (e) {
      return `<pre class="error">CALC parse error: ${(e as Error).message}</pre>`;
    }
  },
};

const clientBlocks = ['mermaid', 'proof'];

/**
 * Parse YAML frontmatter from markdown content
 */
export function parseFrontmatter(content: string): { frontmatter: Frontmatter; body: string } {
  const match = content.match(/^---\n([\s\S]*?)\n---\n/);
  if (!match) return { frontmatter: {}, body: content };

  const frontmatter: Frontmatter = {};
  for (const line of match[1].split('\n')) {
    const i = line.indexOf(':');
    if (i === -1) continue;
    const key = line.slice(0, i).trim();
    const value = line.slice(i + 1).trim();

    if (value.startsWith('[') && value.endsWith(']')) {
      const inner = value.slice(1, -1).trim();
      frontmatter[key] = inner ? inner.split(',').map(s => s.trim().replace(/^["']|["']$/g, '')) : [];
    } else if ((value.startsWith('"') && value.endsWith('"')) || (value.startsWith("'") && value.endsWith("'"))) {
      frontmatter[key] = value.slice(1, -1);
    } else {
      frontmatter[key] = value;
    }
  }

  return { frontmatter, body: content.slice(match[0].length) };
}

function escapeHtml(text: string): string {
  return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;');
}

/**
 * Extract special code blocks (katex, graphviz, mermaid, calc) and replace
 * with placeholders. Returns the modified markdown + a map of processed blocks.
 */
async function extractSpecialBlocks(md: string): Promise<{ md: string; blocks: Map<string, string> }> {
  const blocks = new Map<string, string>();
  const regex = /```\{([^}]+)\}\n([\s\S]*?)```/g;
  let idx = 0;

  // Collect all matches first
  const matches: { full: string; optionsStr: string; code: string }[] = [];
  let m;
  while ((m = regex.exec(md)) !== null) {
    matches.push({ full: m[0], optionsStr: m[1], code: m[2] });
  }

  // Process and replace
  let result = md;
  for (const { full, optionsStr, code } of matches) {
    const parts = optionsStr.split(',').map(s => s.trim());
    const processor = parts[0];
    const options: Record<string, string> = {};
    for (let i = 1; i < parts.length; i++) {
      const [k, v] = parts[i].split('=');
      options[k.trim()] = v?.trim() || 'true';
    }

    let html: string;
    if (serverProcessors[processor]) {
      html = await Promise.resolve(serverProcessors[processor](code, options));
    } else if (clientBlocks.includes(processor)) {
      html = `<div class="client-render" data-processor="${processor}" data-options='${JSON.stringify(options)}'><pre class="client-source">${escapeHtml(code)}</pre></div>`;
    } else {
      continue; // Not a special block, let marked handle it
    }

    const placeholder = `SPECIAL_BLOCK_${idx++}`;
    blocks.set(placeholder, html);
    result = result.replace(full, `<div data-placeholder="${placeholder}"></div>`);
  }

  return { md: result, blocks };
}

/**
 * Convert wiki-style links [[doc]] to HTML links
 */
const FOLDER_TO_ROUTE: Record<string, string> = {
  research: '/research',
  dev: '/dev',
  documentation: '/docs',
};

function processWikiLinks(html: string, basePath: string): string {
  return html.replace(/\[\[([^\]|]+)(?:\|([^\]]+))?\]\]/g, (_, doc, label) => {
    const displayText = label || doc;
    if (doc.includes('/')) {
      const parts = doc.split('/').filter((p: string) => p !== '..');
      const folder = parts[0];
      const name = parts.slice(1).join('/');
      const route = FOLDER_TO_ROUTE[folder] || `/${folder}`;
      return `<a href="${route}/${name}">${displayText}</a>`;
    }
    return `<a href="${basePath}/${doc}">${displayText}</a>`;
  });
}

/**
 * Process inline math $...$ and display math $$...$$
 */
function processInlineMath(html: string): string {
  // Display math $$...$$
  html = html.replace(/\$\$([\s\S]*?)\$\$/g, (_, math) => {
    try {
      return katex.renderToString(math.trim(), { displayMode: true, throwOnError: false });
    } catch {
      return `<span class="error">Math error</span>`;
    }
  });

  // Inline math $...$ (not $$)
  html = html.replace(/(?<!\$)\$(?!\$)([^$\n]+)\$(?!\$)/g, (_, math) => {
    try {
      return katex.renderToString(math.trim(), { displayMode: false, throwOnError: false });
    } catch {
      return `<span class="error">Math error</span>`;
    }
  });

  return html;
}

/**
 * Convert markdown to HTML with all processors
 */
export async function markdownToHtml(
  markdown: string,
  options: { basePath?: string; slug?: string } = {}
): Promise<string> {
  const { basePath = '/research' } = options;

  // 1. Extract special code blocks before marked sees them
  const { md, blocks } = await extractSpecialBlocks(markdown);

  // 2. Process wiki-links in the raw markdown (before marked converts []() links)
  let processed = processWikiLinks(md, basePath);

  // 3. Run marked for core markdown → HTML
  currentBasePath = basePath;
  let html = await marked.parse(processed);

  // 4. Process inline math on the HTML
  html = processInlineMath(html);

  // 5. Restore special blocks from placeholders
  for (const [placeholder, content] of blocks) {
    html = html.replace(
      new RegExp(`<div data-placeholder="${placeholder}"></div>`),
      content
    );
  }

  return html;
}

/**
 * Process a complete markdown document
 */
export async function processDocument(
  content: string,
  options: { basePath?: string; slug?: string } = {}
): Promise<ProcessedDocument> {
  const { frontmatter, body } = parseFrontmatter(content);

  let title = frontmatter.title as string | undefined;
  if (!title) {
    const titleMatch = body.match(/^# (.+)$/m);
    title = titleMatch ? titleMatch[1] : options.slug || 'Untitled';
  }

  const html = await markdownToHtml(body, options);

  return { frontmatter, html, title };
}

/**
 * Client-side hydration for mermaid blocks
 */
export const clientHydrationScript = `
<script type="module">
  const mermaidBlocks = document.querySelectorAll('.client-render[data-processor="mermaid"]');
  if (mermaidBlocks.length > 0) {
    import('https://cdn.jsdelivr.net/npm/mermaid@10/dist/mermaid.esm.min.mjs').then(({ default: mermaid }) => {
      mermaid.initialize({ startOnLoad: false, theme: 'neutral' });
      mermaidBlocks.forEach(async (el, i) => {
        const source = el.querySelector('.client-source')?.textContent || '';
        try {
          const { svg } = await mermaid.render('mermaid-' + i, source);
          el.innerHTML = svg;
          el.classList.add('hydrated');
        } catch (e) {
          el.innerHTML = '<pre class="error">Mermaid error: ' + e.message + '</pre>';
        }
      });
    });
  }
</script>
`;
