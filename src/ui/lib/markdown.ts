/**
 * Hybrid Markdown Processor
 *
 * Server-side: graphviz, katex, calc formulas
 * Client-side: mermaid (via hydration markers)
 *
 * Code block syntax:
 *   ```{graphviz}     - Server-rendered GraphViz
 *   ```{mermaid}      - Client-side Mermaid (hydrated)
 *   ```{calc}         - Server-rendered CALC formula
 *   ```{katex}        - Server-rendered KaTeX math
 *   ```javascript     - Syntax highlighted code block
 */

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

// Server-side processors
const serverProcessors: Record<string, (code: string, options?: Record<string, string>) => Promise<string> | string> = {
  // KaTeX math rendering
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

  // GraphViz - rendered server-side via @hpcc-js/wasm-graphviz
  graphviz: async (code: string) => {
    try {
      // Dynamic import for SSR
      const { Graphviz } = await import('@hpcc-js/wasm-graphviz');
      const graphviz = await Graphviz.load();
      const svg = graphviz.dot(code.trim());
      return `<div class="graphviz-diagram">${svg}</div>`;
    } catch (e) {
      return `<pre class="error">GraphViz error: ${(e as Error).message}</pre>`;
    }
  },

  // Viz.js alias for GraphViz
  viz: async (code: string) => serverProcessors.graphviz(code),

  // CALC formula rendering
  calc: (code: string) => {
    try {
      // Use calculus module for browser-compatible parsing
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

// Client-side blocks (rendered as hydration markers)
const clientBlocks = ['mermaid', 'proof'];

/**
 * Parse YAML frontmatter from markdown content
 */
export function parseFrontmatter(content: string): { frontmatter: Frontmatter; body: string } {
  const frontmatterRegex = /^---\n([\s\S]*?)\n---\n/;
  const match = content.match(frontmatterRegex);

  if (!match) {
    return { frontmatter: {}, body: content };
  }

  const yamlContent = match[1];
  const body = content.slice(match[0].length);

  // Simple YAML parser (handles common cases)
  const frontmatter: Frontmatter = {};
  const lines = yamlContent.split('\n');

  for (const line of lines) {
    const colonIndex = line.indexOf(':');
    if (colonIndex === -1) continue;

    const key = line.slice(0, colonIndex).trim();
    let value = line.slice(colonIndex + 1).trim();

    // Handle arrays [tag1, tag2]
    if (value.startsWith('[') && value.endsWith(']')) {
      const arrayContent = value.slice(1, -1);
      frontmatter[key] = arrayContent.split(',').map(s => s.trim().replace(/^["']|["']$/g, ''));
    }
    // Handle quoted strings
    else if ((value.startsWith('"') && value.endsWith('"')) ||
             (value.startsWith("'") && value.endsWith("'"))) {
      frontmatter[key] = value.slice(1, -1);
    }
    // Handle plain values
    else {
      frontmatter[key] = value;
    }
  }

  return { frontmatter, body };
}

/**
 * Escape HTML entities
 */
function escapeHtml(text: string): string {
  return text
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

/**
 * Process code blocks - either server-render or mark for client hydration
 * Stores results in the provided array and returns placeholders
 */
async function processCodeBlocksWithPlaceholders(html: string, storage: string[]): Promise<string> {
  // Match code blocks with optional {processor, options} syntax
  // Format: ```{processor, option1=value1} or just ```processor
  const codeBlockRegex = /```(?:\{([^}]+)\}|(\w+))?\n([\s\S]*?)```/g;

  const blocks: { match: string; index: number; replacement: string }[] = [];
  let match;

  while ((match = codeBlockRegex.exec(html)) !== null) {
    const fullMatch = match[0];
    const optionsStr = match[1]; // {processor, opts}
    const langOnly = match[2];   // just processor name
    const code = match[3];

    let processor: string | undefined;
    const options: Record<string, string> = {};

    if (optionsStr) {
      // Parse {processor, opt1=val1, opt2}
      const parts = optionsStr.split(',').map(s => s.trim());
      processor = parts[0];
      for (let i = 1; i < parts.length; i++) {
        const [key, val] = parts[i].split('=');
        options[key.trim()] = val?.trim() || 'true';
      }
    } else if (langOnly) {
      processor = langOnly;
    }

    let replacement: string;

    // Check if it's a server-side processor
    if (processor && serverProcessors[processor]) {
      const result = serverProcessors[processor](code, options);
      replacement = await Promise.resolve(result);
    }
    // Check if it's a client-side block
    else if (processor && clientBlocks.includes(processor)) {
      // Render as hydration marker for client-side rendering
      replacement = `<div class="client-render" data-processor="${processor}" data-options='${JSON.stringify(options)}'><pre class="client-source">${escapeHtml(code)}</pre></div>`;
    }
    // Regular code block with syntax highlighting
    else {
      const lang = processor || '';
      // Trim trailing newline that's typically before closing ```
      const trimmedCode = code.replace(/\n$/, '');
      replacement = `<pre><code class="language-${lang}">${escapeHtml(trimmedCode)}</code></pre>`;
    }

    const index = storage.length;
    storage.push(replacement);
    blocks.push({ match: fullMatch, index, replacement: `CODE_BLOCK_${index}_PLACEHOLDER` });
  }

  // Replace all blocks (in reverse order to preserve indices)
  let result = html;
  for (let i = blocks.length - 1; i >= 0; i--) {
    result = result.replace(blocks[i].match, blocks[i].replacement);
  }

  return result;
}

/**
 * Convert wiki-style links [[doc]] to HTML links
 */
const FOLDER_TO_ROUTE: Record<string, string> = {
  research: '/research',
  dev: '/dev',
  documentation: '/docs',
};

function processWikiLinks(html: string, basePath: string = '/research'): string {
  return html.replace(/\[\[([^\]|]+)(?:\|([^\]]+))?\]\]/g, (_, doc, label) => {
    const displayText = label || doc;
    if (doc.includes('/')) {
      // Strip leading ../ segments and resolve folder
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

  // Inline math $...$  (but not $$)
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
  let html = markdown;

  // Extract code blocks first, replace with placeholders to protect from other processing
  const codeBlocks: string[] = [];
  html = await processCodeBlocksWithPlaceholders(html, codeBlocks);

  // Wiki-links
  html = processWikiLinks(html, basePath);

  // Inline code (but not in code blocks - they're already extracted)
  html = html.replace(/`([^`]+)`/g, '<code>$1</code>');

  // Headers
  html = html.replace(/^#### (.+)$/gm, '<h4>$1</h4>');
  html = html.replace(/^### (.+)$/gm, '<h3>$1</h3>');
  html = html.replace(/^## (.+)$/gm, '<h2>$1</h2>');
  html = html.replace(/^# (.+)$/gm, '<h1>$1</h1>');

  // Bold and italic
  html = html.replace(/\*\*([^*]+)\*\*/g, '<strong>$1</strong>');
  html = html.replace(/\*([^*]+)\*/g, '<em>$1</em>');

  // Links [text](url)
  html = html.replace(/\[([^\]]+)\]\(([^)]+)\)/g, (_, text, url) => {
    if (url.endsWith('.md')) {
      url = basePath + '/' + url.replace('.md', '');
    }
    if (url.startsWith('#')) {
      return `<a href="${url}">${text}</a>`;
    }
    return `<a href="${url}" target="_blank" rel="noopener">${text}</a>`;
  });

  // Blockquotes
  html = html.replace(/^> (.+)$/gm, '<blockquote>$1</blockquote>');
  html = html.replace(/<\/blockquote>\n<blockquote>/g, '\n');

  // Horizontal rules
  html = html.replace(/^---+$/gm, '<hr>');

  // Tables
  const tableRegex = /\|(.+)\|\n\|[-| ]+\|\n((?:\|.+\|\n?)+)/g;
  html = html.replace(tableRegex, (_, header, body) => {
    const headers = header.split('|').filter((h: string) => h.trim());
    const rows = body.trim().split('\n').map((row: string) =>
      row.split('|').filter((c: string) => c.trim())
    );

    let table = '<table><thead><tr>';
    headers.forEach((h: string) => {
      table += `<th>${h.trim()}</th>`;
    });
    table += '</tr></thead><tbody>';
    rows.forEach((row: string[]) => {
      table += '<tr>';
      row.forEach((cell: string) => {
        table += `<td>${cell.trim()}</td>`;
      });
      table += '</tr>';
    });
    table += '</tbody></table>';
    return table;
  });

  // Unordered lists
  html = html.replace(/^- (.+)$/gm, '<li>$1</li>');
  html = html.replace(/(<li>.*<\/li>\n?)+/g, (match) => `<ul>${match}</ul>`);

  // Ordered lists
  html = html.replace(/^\d+\. (.+)$/gm, '<li>$1</li>');

  // Process inline math
  html = processInlineMath(html);

  // Paragraphs (lines not already wrapped)
  html = html.replace(/^(?!<[a-z]|<\/|$|CODE_BLOCK_)(.+)$/gm, (_, content) => {
    if (content.trim()) {
      return `<p>${content}</p>`;
    }
    return content;
  });

  // Clean up extra newlines
  html = html.replace(/\n{3,}/g, '\n\n');

  // Restore code blocks from placeholders
  for (let i = 0; i < codeBlocks.length; i++) {
    html = html.replace(`CODE_BLOCK_${i}_PLACEHOLDER`, codeBlocks[i]);
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

  // Extract title from frontmatter or first # heading
  let title = frontmatter.title as string | undefined;
  if (!title) {
    const titleMatch = body.match(/^# (.+)$/m);
    title = titleMatch ? titleMatch[1] : options.slug || 'Untitled';
  }

  const html = await markdownToHtml(body, options);

  return {
    frontmatter,
    html,
    title,
  };
}

/**
 * Client-side hydration script (to be included in page)
 */
export const clientHydrationScript = `
<script type="module">
  // Hydrate mermaid blocks
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
