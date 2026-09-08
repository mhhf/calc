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

function slugify(text: string): string {
  return text
    .toLowerCase()
    .replace(/<[^>]*>/g, '')       // strip HTML tags
    .replace(/[^\w\s-]/g, '')      // remove non-word chars
    .replace(/\s+/g, '-')          // spaces → hyphens
    .replace(/-+/g, '-')           // collapse hyphens
    .trim();
}

// Shared highlight configuration (stateless, safe to reuse)
const highlightExtension = markedHighlight({
  emptyLangClass: 'hljs',
  langPrefix: 'hljs language-',
  highlight(code, lang) {
    if (lang && hljs.getLanguage(lang)) {
      return hljs.highlight(code, { language: lang }).value;
    }
    return hljs.highlightAuto(code).value;
  },
});

/**
 * Create a configured Marked instance for the given render context.
 * Each call produces an isolated instance — no shared mutable state.
 */
function createMarkedInstance(basePath: string, headings: { depth: number; text: string; id: string }[]) {
  return new Marked(
    highlightExtension,
    {
      renderer: {
        heading({ tokens, depth }) {
          const text = this.parser.parseInline(tokens);
          const id = slugify(text);
          if (depth <= 3) {
            headings.push({ depth, text, id });
          }
          return `<h${depth} id="${id}">${text}</h${depth}>\n`;
        },
        link({ href, text }) {
          if (href.endsWith('.md')) {
            href = basePath + '/' + href.replace(/\.md$/, '');
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
}

function buildToc(headings: { depth: number; text: string; id: string }[]): string {
  if (headings.length < 2) return '';
  const minDepth = Math.min(...headings.map(h => h.depth));

  let html = '<nav class="toc"><span class="toc-title">On this page</span><ul>';
  let currentDepth = minDepth;

  for (const h of headings) {
    while (currentDepth < h.depth) { html += '<ul>'; currentDepth++; }
    while (currentDepth > h.depth) { html += '</ul>'; currentDepth--; }
    html += `<li><a href="#${h.id}">${h.text}</a></li>`;
  }
  while (currentDepth > minDepth) { html += '</ul>'; currentDepth--; }

  html += '</ul></nav>';
  return html;
}

// Context threaded through block processors (recursive markdown, wiki-links)
interface BlockCtx {
  basePath: string;
  manifest?: Record<string, string[]>;
}

// Server-side processors for special code blocks
const serverProcessors: Record<string, (code: string, options?: Record<string, string>, positional?: string[], ctx?: BlockCtx) => Promise<string> | string> = {
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

  calc: async (code: string) => {
    try {
      const { parseFormula, renderFormula } = await import('./calculus');
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

  // ```{rule tensor_r}``` (or names in the body, one per line) — renders the
  // abstract inference rule(s) as \cfrac cards from the loaded calculus.
  rule: async (code: string, _options, positional = []) => {
    try {
      const { getManualProofAPI } = await import('./calculus');
      const api = getManualProofAPI();
      const names = [...positional, ...code.split('\n').map(s => s.trim()).filter(Boolean)];
      if (names.length === 0) return `<pre class="error">rule block: no rule name given</pre>`;
      const cards = names.map((name) => {
        let schema: { conclusion: string; premises?: string[] } | null = null;
        try {
          schema = api.getAbstractRule(name);
        } catch {
          schema = null;
        }
        if (!schema || !schema.conclusion) {
          return `<pre class="error">unknown rule: ${escapeHtml(name)}</pre>`;
        }
        const simplify = (s: string) =>
          s.replace(/\?\s*X/g, '\\Gamma').replace(/\?\s*Y/g, '\\Delta').replace(/\?\s*Z/g, '\\Sigma')
            .replace(/F\?\s*([A-Z])/g, '$1').replace(/S\?\s*([A-Z])/g, '$1')
            .replace(/--\s*:/g, '').replace(/\s+/g, ' ').trim();
        const toLatex = (s: string) =>
          s.includes('\\vdash') ? s : s.replace(/\|-/g, '\\vdash').replace(/-o/g, '\\multimap').replace(/\*/g, '\\otimes').replace(/\+/g, '\\oplus');
        const conclusion = simplify(toLatex(schema.conclusion));
        const premises = (schema.premises || []).map(p => simplify(toLatex(p)));
        const frac = premises.length === 0
          ? `\\cfrac{\\vphantom{X}}{${conclusion}}`
          : `\\cfrac{${premises.join(' \\quad ')}}{${conclusion}}`;
        const rendered = katex.renderToString(frac, { displayMode: true, throwOnError: false });
        return `<div class="rule-block"><div class="rule-block-name">${escapeHtml(name)}</div>${rendered}</div>`;
      });
      return `<div class="rule-block-row">${cards.join('')}</div>`;
    } catch (e) {
      return `<pre class="error">rule block error: ${(e as Error).message}</pre>`;
    }
  },

  // ```{exercise, title=...}``` — styled callout; body is markdown.
  exercise: async (code: string, options = {}, _positional, ctx) => {
    const inner = await markdownToHtml(code, { basePath: ctx?.basePath || '/book', manifest: ctx?.manifest, noToc: true });
    const title = options.title ? escapeHtml(options.title) : 'Exercise';
    return `<div class="book-exercise"><div class="book-exercise-title">${title}</div><div class="book-exercise-body">${inner}</div></div>`;
  },

  // ```{solution}``` — collapsed by default; body is markdown.
  solution: async (code: string, options = {}, _positional, ctx) => {
    const inner = await markdownToHtml(code, { basePath: ctx?.basePath || '/book', manifest: ctx?.manifest, noToc: true });
    const label = options.label ? escapeHtml(options.label) : 'Show solution';
    return `<details class="book-solution"><summary>${label}</summary><div class="book-solution-body">${inner}</div></details>`;
  },
};

const clientBlocks = ['mermaid', 'proof'];

// Interactive course widgets — hydrated client-side by hydrateWidgets.ts.
// Body travels raw in a hidden <pre>; each widget parses its own spec.
const widgetBlocks = ['prove', 'formula', 'quiz', 'exec', 'game', 'collapse'];

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
  return text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#39;');
}

/**
 * Extract special code blocks (katex, graphviz, mermaid, calc) and replace
 * with placeholders. Returns the modified markdown + a map of processed blocks.
 */
async function extractSpecialBlocks(md: string, ctx?: BlockCtx): Promise<{ md: string; blocks: Map<string, string> }> {
  const blocks = new Map<string, string>();
  // Match both ```{mermaid} (legacy) and ```mermaid (standard fenced)
  // Also supports positional args inside braces: ```{proof ill default}
  const regex = /```(?:\{([^}]+)\}|(mermaid|katex|graphviz|viz|calc|proof))\n([\s\S]*?)```/g;
  let idx = 0;

  // Collect all matches first
  const matches: { full: string; optionsStr: string; code: string }[] = [];
  let m;
  while ((m = regex.exec(md)) !== null) {
    matches.push({ full: m[0], optionsStr: m[1] || m[2], code: m[3] });
  }

  // Process and replace
  let result = md;
  for (const { full, optionsStr, code } of matches) {
    // The header allows a mix of whitespace-separated positional tokens and
    // comma-separated k=v options:
    //   ```{proof ill verified}        → processor=proof, args=[ill, verified]
    //   ```{graphviz, theme=dark}      → processor=graphviz, options={theme}
    //   ```mermaid                     → processor=mermaid (bare fenced form)
    const commaParts = optionsStr.split(',').map(s => s.trim());
    const headTokens = commaParts[0].split(/\s+/);
    const processor = headTokens[0];
    const positional = headTokens.slice(1);
    const options: Record<string, string> = {};
    for (let i = 1; i < commaParts.length; i++) {
      const [k, v] = commaParts[i].split('=');
      options[k.trim()] = v?.trim() || 'true';
    }

    let html: string;
    if (serverProcessors[processor]) {
      html = await Promise.resolve(serverProcessors[processor](code, options, positional, ctx));
    } else if (widgetBlocks.includes(processor)) {
      // Course widget — hydrated client-side. Positional args + k=v options
      // ride data attributes; the body rides a hidden <pre> (entity-decoded
      // via .textContent, same reasoning as the proof block below).
      html =
        `<div class="client-render widget-block" data-processor="widget-${processor}" ` +
        `data-args="${escapeHtml(positional.join(' '))}" ` +
        `data-options='${escapeHtml(JSON.stringify(options))}'>` +
        `<pre class="client-source" style="display:none">${escapeHtml(code)}</pre>` +
        `<div class="widget-loading">Loading widget…</div>` +
        `</div>`;
    } else if (processor === 'proof') {
      // `{proof <calculus> [mode] [profile]}` — client-rendered. The tree
      // itself is fetched from POST /api/proof on mount; the client renders
      // one of five layouts with a user-toggle.
      //
      // Header grammar (all positional after `proof`):
      //   1. calculus  (ill)
      //   2. mode      (sequent | backchain | forward)   — optional; default `sequent`
      //   3. profile   (default | teaching | …)          — optional; default `default`
      //
      // If token 2 is not a recognized mode we treat it as the profile
      // (backwards compat with pre-Phase-C `{proof ill verified}` blocks).
      //
      // Source travels in a hidden <pre>. We can't use a <script> tag here:
      // per HTML5 its content is "raw text state", which does NOT decode
      // character references, so escapeHtml()'d output like `A &amp; B`
      // would arrive at the prover literally — and the parser would choke
      // on the semicolon (observed: "parse error at position 6, got ';'").
      // <pre> is parsed as normal HTML, so `.textContent` decodes entities.
      const KNOWN_MODES = new Set(['sequent', 'backchain', 'forward', 'symex', 'exec']);
      const calcName = positional[0] || 'ill';
      let mode = 'sequent';
      let profile = 'default';
      if (positional[1]) {
        if (KNOWN_MODES.has(positional[1])) {
          mode = positional[1];
          if (positional[2]) profile = positional[2];
        } else {
          profile = positional[1];
        }
      }
      html =
        `<div class="client-render" data-processor="proof-tree" ` +
        `data-calculus="${escapeHtml(calcName)}" ` +
        `data-mode="${escapeHtml(mode)}" ` +
        `data-profile="${escapeHtml(profile)}">` +
        `<pre class="client-source" style="display:none">${escapeHtml(code)}</pre>` +
        `</div>`;
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
 * Convert wiki-style links [[doc]], [[folder/doc]], [[doc|Label]] to HTML links.
 *
 * When a slug manifest is supplied, targets are resolved via:
 *   1. exact slug match
 *   2. numbered-prefix suffix match ("ownership-design" → "0005_ownership-design") if unique
 *   3. otherwise rendered as <span class="wiki-broken"> to flag the broken reference
 *
 * Without a manifest, falls back to the legacy behavior (raw pass-through link).
 *
 * Must mirror the server-side resolver in src/ui/plugins/doc-scan.js exactly.
 */
const FOLDER_TO_ROUTE: Record<string, string> = {
  theory: '/theory',
  def: '/def',
  documentation: '/docs',
};

const RESOLVE_ROUTE: Record<string, string> = {
  theory: 'theory',
  def: 'def',
  docs: 'docs',
  documentation: 'docs',
};

export function resolveWikiTarget(
  raw: string,
  sourceRoute: string,
  manifest: Record<string, string[]>,
): { route: string; slug: string } | null {
  let targetRoute = sourceRoute;
  let name = raw.trim();
  if (name.includes('/')) {
    const parts = name.split('/').filter(p => p !== '..' && p.length > 0);
    if (parts.length < 2) return null;
    const resolved = RESOLVE_ROUTE[parts[0]];
    if (!resolved) return null;
    targetRoute = resolved;
    name = parts.slice(1).join('/');
  }
  const slugs = manifest[targetRoute] || [];
  if (slugs.includes(name)) return { route: targetRoute, slug: name };
  const prefixed = slugs.filter(s => /^\d{4}_/.test(s) && s.slice(5) === name);
  if (prefixed.length === 1) return { route: targetRoute, slug: prefixed[0] };
  return null;
}

function processWikiLinks(
  html: string,
  basePath: string,
  manifest?: Record<string, string[]>,
): string {
  const sourceRoute = basePath.replace(/^\//, '');
  return html.replace(/\[\[([^\]|]+)(?:\|([^\]]+))?\]\]/g, (_, doc, label) => {
    const displayText = label || doc;
    if (manifest) {
      const resolved = resolveWikiTarget(doc, sourceRoute, manifest);
      if (resolved) {
        return `<a href="/${resolved.route}/${resolved.slug}">${displayText}</a>`;
      }
      // Manifest provided but target not found — surface the broken reference.
      return `<span class="wiki-broken" title="Unresolved wiki-link: ${doc}">${displayText}</span>`;
    }
    // Legacy fallback (no manifest): pass through raw target.
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
  options: { basePath?: string; slug?: string; manifest?: Record<string, string[]>; noToc?: boolean } = {}
): Promise<string> {
  const { basePath = '/docs', manifest } = options;

  // 1. Extract special code blocks before marked sees them
  const { md, blocks } = await extractSpecialBlocks(markdown, { basePath, manifest });

  // 2. Process wiki-links in the raw markdown (before marked converts []() links)
  let processed = processWikiLinks(md, basePath, manifest);

  // 3. Run marked for core markdown → HTML (collects headings for TOC)
  const headings: { depth: number; text: string; id: string }[] = [];
  const markedInstance = createMarkedInstance(basePath, headings);
  let html = await markedInstance.parse(processed);

  // 4. Prepend TOC if enough headings
  if (!options.noToc) {
    const toc = buildToc(headings);
    if (toc) html = toc + html;
  }

  // 5. Process inline math on the HTML
  html = processInlineMath(html);

  // 6. Restore special blocks from placeholders
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
  options: { basePath?: string; slug?: string; manifest?: Record<string, string[]> } = {}
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
