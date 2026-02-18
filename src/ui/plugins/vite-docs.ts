/**
 * Vite plugin to serve documentation markdown files during development.
 *
 * Handles:
 *   GET /api/docs/:folder       → JSON array of { slug, title, summary, tags }
 *   GET /api/docs/:folder/:slug → raw markdown text
 */
import type { Plugin } from 'vite';
import fs from 'fs';
import path from 'path';

const DOC_ROOT = path.resolve(__dirname, '../../../doc');

const ALLOWED_FOLDERS: Record<string, string> = {
  research: 'research',
  dev: 'dev',
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
      fm[key] = val.slice(1, -1).split(',').map(s => s.trim().replace(/^["']|["']$/g, ''));
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
                title: fm.title || f.replace(/\.md$/, ''),
                summary: fm.summary || '',
                tags: fm.tags || [],
                status: fm.status || '',
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
