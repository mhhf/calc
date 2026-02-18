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

const app = new Hono();
const port = parseInt(process.argv.find((_, i, a) => a[i-1] === '--port') || '3000', 10);

// API routes (proof engine state goes here)
app.get('/api/health', (c) => c.json({ status: 'ok' }));

// Documentation API
const DOC_ROOT = path.resolve(__dirname, 'doc');
const ALLOWED_FOLDERS = { research: 'research', dev: 'dev', docs: 'documentation', todo: 'todo' };

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
      return { slug: f.replace(/\.md$/, ''), title: fm.title || f.replace(/\.md$/, ''), summary: fm.summary || '', tags: fm.tags || [], status: fm.status || '', priority: fm.priority ? Number(fm.priority) : undefined, type: fm.type || undefined, depends_on: fm.depends_on || [], required_by: fm.required_by || [] };
    });
    return c.json(docs);
  } catch (e) {
    return c.json({ error: e.message }, 500);
  }
});

// Serve individual doc
app.get('/api/docs/:folder/:slug', (c) => {
  const diskFolder = ALLOWED_FOLDERS[c.req.param('folder')];
  if (!diskFolder) return c.json({ error: 'unknown folder' }, 404);
  const filePath = path.join(DOC_ROOT, diskFolder, c.req.param('slug') + '.md');
  try {
    return c.text(fs.readFileSync(filePath, 'utf-8'));
  } catch {
    return c.json({ error: 'not found' }, 404);
  }
});

// Serve static UI build
app.use('/*', serveStatic({ root: './out/ui' }));

// SPA fallback: serve index.html for all non-file routes
app.use('/*', serveStatic({ root: './out/ui', path: 'index.html' }));

serve({ fetch: app.fetch, port }, () => {
  console.log(`CALC server running on http://localhost:${port}`);
});
