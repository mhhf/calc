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

const app = new Hono();
const port = parseInt(process.argv.find((_, i, a) => a[i-1] === '--port') || '3000', 10);

// API routes (proof engine state goes here)
app.get('/api/health', (c) => c.json({ status: 'ok' }));

// Serve static UI build
app.use('/*', serveStatic({ root: './out/ui' }));

// SPA fallback: serve index.html for all non-file routes
app.use('/*', serveStatic({ root: './out/ui', path: 'index.html' }));

serve({ fetch: app.fetch, port }, () => {
  console.log(`CALC server running on http://localhost:${port}`);
});
