/**
 * Vite plugin to serve documentation markdown files during development.
 *
 * Handles:
 *   GET /api/docs/:folder       → JSON array of { slug, title, summary, tags, modified, category, ... }
 *   GET /api/docs/:folder/:slug → raw markdown text
 *   GET /api/backlinks          → JSON { "<folder>/<slug>": [{folder, slug, title}, ...] }
 *   GET /api/doc-manifest       → JSON { [route]: [slug, ...] } for client-side wiki-link resolution
 */
import type { Plugin } from 'vite';
import fs from 'fs';
import path from 'path';
// @ts-expect-error - CJS scanner module shared with production server.js
import docScan from './doc-scan.js';
const { getCachedIndex, getCachedManifest } = docScan as {
  getCachedIndex: (root: string) => Record<string, { folder: string; slug: string; title: string }[]>;
  getCachedManifest: (root: string) => Record<string, string[]>;
};

const DOC_ROOT = path.resolve(__dirname, '../../../doc');
const PROOF_CACHE_DIR = path.resolve(__dirname, '../../../out/doc-cache');

// @ts-expect-error - CJS module shared with production server.js
import proveSourceMod from '../../../lib/prover/prove-source.js';
const { proveSource } = proveSourceMod as {
  proveSource: (opts: {
    source: string;
    calculus?: string;
    profile?: string;
    mode?: string;
    cacheDir?: string;
  }) => Promise<{ ok: boolean; tree?: unknown; key: string; cacheHit: boolean; error?: string }>;
};

const ALLOWED_FOLDERS: Record<string, string> = {
  theory: 'theory',
  def: 'def',
  docs: 'documentation',
};

function extractFrontmatter(content: string) {
  const m = content.match(/^---\n([\s\S]*?)\n---\n/);
  if (!m) return {};
  const fm: Record<string, unknown> = {};
  for (const line of m[1].split('\n')) {
    const i = line.indexOf(':');
    if (i === -1) continue;
    const key = line.slice(0, i).trim();
    let val = line.slice(i + 1).trim();
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

export default function viteDocs(): Plugin {
  return {
    name: 'vite-docs',
    configureServer(server) {
      server.middlewares.use((req, res, next) => {
        const url = req.url || '';

        // /api/backlinks — global backlink manifest
        if (url === '/api/backlinks') {
          try {
            const index = getCachedIndex(DOC_ROOT);
            res.setHeader('Content-Type', 'application/json');
            res.end(JSON.stringify(index));
          } catch (e) {
            res.statusCode = 500;
            res.end(JSON.stringify({ error: (e as Error).message }));
          }
          return;
        }

        // POST /api/proof — run prover on a sequent string, return proof-tree/v1 JSON.
        const reqAny = req as unknown as {
          method?: string;
          on: (ev: string, cb: (data?: unknown) => void) => void;
        };
        if (url === '/api/proof' && reqAny.method === 'POST') {
          let raw = '';
          reqAny.on('data', (chunk) => { raw += String(chunk); });
          reqAny.on('end', async () => {
            let body: { source?: string; calculus?: string; profile?: string; mode?: string };
            try {
              body = JSON.parse(raw || '{}');
            } catch {
              res.statusCode = 400;
              res.end(JSON.stringify({ ok: false, error: 'invalid JSON body' }));
              return;
            }
            const source = body.source;
            if (typeof source !== 'string' || source.length === 0) {
              res.statusCode = 400;
              res.end(JSON.stringify({ ok: false, error: 'source (string) required' }));
              return;
            }
            if (source.length > 4096) {
              res.statusCode = 413;
              res.end(JSON.stringify({ ok: false, error: 'source too large' }));
              return;
            }
            try {
              const r = await proveSource({
                source,
                calculus: body.calculus || 'ill',
                profile: body.profile || 'default',
                mode: body.mode || 'sequent',
                cacheDir: PROOF_CACHE_DIR,
              });
              res.setHeader('Content-Type', 'application/json');
              res.end(JSON.stringify(r));
            } catch (e) {
              res.statusCode = 500;
              res.end(JSON.stringify({ ok: false, error: (e as Error).message }));
            }
          });
          return;
        }

        // /api/doc-manifest — slug lists by folder for wiki-link resolution
        if (url === '/api/doc-manifest') {
          try {
            const manifest = getCachedManifest(DOC_ROOT);
            res.setHeader('Content-Type', 'application/json');
            res.end(JSON.stringify(manifest));
          } catch (e) {
            res.statusCode = 500;
            res.end(JSON.stringify({ error: (e as Error).message }));
          }
          return;
        }

        // Match /api/docs/:folder or /api/docs/:folder/:slug
        const m = url.match(/^\/api\/docs\/([^/]+)(?:\/(.+))?$/);
        if (!m) return next();

        const folderKey = m[1];
        const slug = m[2];
        const diskFolder = ALLOWED_FOLDERS[folderKey];
        if (!diskFolder) {
          res.statusCode = 404;
          res.end(JSON.stringify({ error: 'unknown folder' }));
          return;
        }

        const folderPath = path.join(DOC_ROOT, diskFolder);

        if (!slug) {
          // List docs in folder
          try {
            const files = fs.readdirSync(folderPath).filter(f => f.endsWith('.md'));
            const docs = files.map(f => {
              const content = fs.readFileSync(path.join(folderPath, f), 'utf-8');
              const fm = extractFrontmatter(content);
              return {
                slug: f.replace(/\.md$/, ''),
                title: (fm.title || fm.term || f.replace(/\.md$/, '')) as string,
                summary: fm.summary || '',
                tags: fm.tags || [],
                status: fm.status || '',
                modified: fm.modified || '',
                category: fm.category || '',
              };
            });
            res.setHeader('Content-Type', 'application/json');
            res.end(JSON.stringify(docs));
          } catch {
            res.statusCode = 500;
            res.end(JSON.stringify({ error: 'failed to list docs' }));
          }
          return;
        }

        // Serve individual doc
        if (slug.includes('..') || slug.includes('/')) {
          res.statusCode = 400;
          res.end(JSON.stringify({ error: 'invalid slug' }));
          return;
        }
        const filePath = path.join(folderPath, slug + '.md');
        try {
          const content = fs.readFileSync(filePath, 'utf-8');
          res.setHeader('Content-Type', 'text/plain');
          res.end(content);
        } catch {
          res.statusCode = 404;
          res.end('not found');
        }
      });
    },
  };
}
