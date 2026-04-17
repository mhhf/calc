/**
 * CALC Server — proof engine that serves a web UI.
 *
 * Usage:
 *   node server.js              # serve built UI from out/ui/
 *   node server.js --port 8080  # custom port
 */

const { Hono } = require('hono');
const { serve } = require('@hono/node-server');
const { serveStatic } = require('@hono/node-server/serve-static');
const fs = require('fs');
const path = require('path');
const { getCachedIndex, getCachedManifest } = require('./src/ui/plugins/doc-scan');

const app = new Hono();
const port = parseInt(process.argv.find((_, i, a) => a[i-1] === '--port') || process.env.PORT || '3000', 10);
const host = process.env.HOST || '0.0.0.0';

// API routes (proof engine state goes here)
app.get('/api/health', (c) => c.json({ status: 'ok' }));

// Documentation API
const DOC_ROOT = path.resolve(__dirname, 'doc');
const ALLOWED_FOLDERS = { theory: 'theory', def: 'def', docs: 'documentation' };

function extractFrontmatter(content) {
  const m = content.match(/^---\n([\s\S]*?)\n---\n/);
  if (!m) return {};
  const fm = {};
  for (const line of m[1].split('\n')) {
    const i = line.indexOf(':');
    if (i === -1) continue;
    const key = line.slice(0, i).trim();
    const val = line.slice(i + 1).trim();
    if (val.startsWith('[') && val.endsWith(']')) {
      const inner = val.slice(1, -1).trim();
      fm[key] = inner ? inner.split(',').map(s => s.trim().replace(/^["']|["']$/g, '')) : [];
    } else if ((val.startsWith('"') && val.endsWith('"')) || (val.startsWith("'") && val.endsWith("'"))) {
      fm[key] = val.slice(1, -1);
    } else {
      fm[key] = val;
    }
  }
  return fm;
}

// List docs in a folder
app.get('/api/docs/:folder', (c) => {
  const diskFolder = ALLOWED_FOLDERS[c.req.param('folder')];
  if (!diskFolder) return c.json({ error: 'unknown folder' }, 404);
  try {
    const folderPath = path.join(DOC_ROOT, diskFolder);
    const files = fs.readdirSync(folderPath).filter(f => f.endsWith('.md'));
    const docs = files.map(f => {
      const content = fs.readFileSync(path.join(folderPath, f), 'utf-8');
      const fm = extractFrontmatter(content);
      return { slug: f.replace(/\.md$/, ''), title: fm.title || fm.term || f.replace(/\.md$/, ''), summary: fm.summary || '', tags: fm.tags || [], status: fm.status || '', priority: fm.priority ? Number(fm.priority) : undefined, type: fm.type || undefined, depends_on: fm.depends_on || [], required_by: fm.required_by || [], cluster: fm.cluster || undefined };
    });
    return c.json(docs);
  } catch (e) {
    return c.json({ error: e.message }, 500);
  }
});

// Backlink manifest — "<route>/<slug>" → [{folder, slug, title}, ...]
app.get('/api/backlinks', (c) => {
  try {
    return c.json(getCachedIndex(DOC_ROOT));
  } catch (e) {
    return c.json({ error: e.message }, 500);
  }
});

// Doc slug manifest — { [route]: [slug, ...] } for browser-side wiki-link resolution
app.get('/api/doc-manifest', (c) => {
  try {
    return c.json(getCachedManifest(DOC_ROOT));
  } catch (e) {
    return c.json({ error: e.message }, 500);
  }
});

// Serve individual doc
app.get('/api/docs/:folder/:slug', (c) => {
  const diskFolder = ALLOWED_FOLDERS[c.req.param('folder')];
  if (!diskFolder) return c.json({ error: 'unknown folder' }, 404);
  const slug = c.req.param('slug');
  if (slug.includes('..') || slug.includes('/')) return c.json({ error: 'invalid slug' }, 400);
  const filePath = path.join(DOC_ROOT, diskFolder, slug + '.md');
  try {
    return c.text(fs.readFileSync(filePath, 'utf-8'));
  } catch {
    return c.json({ error: 'not found' }, 404);
  }
});

// Proof block API — run the prover on a sequent string and return
// proof-tree/v1 JSON. Cached on disk under out/doc-cache/.
const { proveSource, proveSubtree, extractSymexLeafTrace } = require('./lib/prover/prove-source');
const PROOF_CACHE_DIR = path.join(__dirname, 'out/doc-cache');
app.post('/api/proof', async (c) => {
  let body;
  try {
    body = await c.req.json();
  } catch {
    return c.json({ ok: false, error: 'invalid JSON body' }, 400);
  }
  const { source, calculus, profile, mode, elideBelowDepth } = body || {};
  if (typeof source !== 'string' || source.length === 0) {
    return c.json({ ok: false, error: 'source (string) required' }, 400);
  }
  if (source.length > 4096) {
    return c.json({ ok: false, error: 'source too large' }, 413);
  }
  try {
    const r = await proveSource({
      source,
      calculus: calculus || 'ill',
      profile: profile || 'default',
      mode: mode || 'sequent',
      cacheDir: PROOF_CACHE_DIR,
      elideBelowDepth: typeof elideBelowDepth === 'number' ? elideBelowDepth : undefined,
    });
    return c.json(r);
  } catch (e) {
    return c.json({ ok: false, error: e.message }, 500);
  }
});
// Lazy subtree fetch — proves (and caches) the full source first, then
// returns the subtree rooted at `nodeId`. `elideBelowDepth` (relative to
// the subtree root) allows recursive lazy expansion.
app.post('/api/proof/subtree', async (c) => {
  let body;
  try {
    body = await c.req.json();
  } catch {
    return c.json({ ok: false, error: 'invalid JSON body' }, 400);
  }
  const { source, calculus, profile, mode, nodeId, elideBelowDepth } = body || {};
  if (typeof source !== 'string' || source.length === 0) {
    return c.json({ ok: false, error: 'source (string) required' }, 400);
  }
  if (typeof nodeId !== 'string' || nodeId.length === 0) {
    return c.json({ ok: false, error: 'nodeId (string) required' }, 400);
  }
  if (source.length > 4096) {
    return c.json({ ok: false, error: 'source too large' }, 413);
  }
  try {
    const r = await proveSubtree({
      source,
      calculus: calculus || 'ill',
      profile: profile || 'default',
      mode: mode || 'sequent',
      nodeId,
      cacheDir: PROOF_CACHE_DIR,
      elideBelowDepth: typeof elideBelowDepth === 'number' ? elideBelowDepth : undefined,
    });
    return c.json(r);
  } catch (e) {
    return c.json({ ok: false, error: e.message }, 500);
  }
});

// Per-leaf trace fetch for symex/exec proofs (forward-trace/v1). Re-proves
// the source (cheap when disk cache hits) to guarantee the in-memory tree
// cache has the explore tree, then serializes one leaf's trace.
app.post('/api/proof/leaf-trace', async (c) => {
  let body;
  try {
    body = await c.req.json();
  } catch {
    return c.json({ ok: false, error: 'invalid JSON body' }, 400);
  }
  const { source, calculus, profile, leafIndex } = body || {};
  if (typeof source !== 'string' || source.length === 0) {
    return c.json({ ok: false, error: 'source (string) required' }, 400);
  }
  if (typeof leafIndex !== 'number' || leafIndex < 0) {
    return c.json({ ok: false, error: 'leafIndex (non-negative number) required' }, 400);
  }
  if (source.length > 4096) {
    return c.json({ ok: false, error: 'source too large' }, 413);
  }
  try {
    const p = await proveSource({
      source,
      calculus: calculus || 'ill',
      profile: profile || 'default',
      mode: 'symex',
      cacheDir: PROOF_CACHE_DIR,
    });
    if (!p.ok || !p.key) {
      return c.json({ ok: false, error: p.error || 'prove failed' }, 400);
    }
    const r = extractSymexLeafTrace(p.key, leafIndex, {
      calculus: calculus || 'ill',
      profile: profile || 'default',
    });
    return c.json(r);
  } catch (e) {
    return c.json({ ok: false, error: e.message }, 500);
  }
});

// Serve static UI build
app.use('/*', serveStatic({ root: './out/ui' }));

// SPA fallback: serve index.html for non-API routes
app.get('*', (c) => {
  if (c.req.path.startsWith('/api/')) return c.notFound();
  try {
    return c.html(fs.readFileSync(path.join(__dirname, 'out/ui/index.html'), 'utf-8'));
  } catch {
    return c.notFound();
  }
});

serve({ fetch: app.fetch, port, hostname: host }, () => {
  console.log(`CALC server running on http://${host}:${port}`);
});
