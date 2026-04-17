/**
 * Documentation scanner — builds the wiki-link backlink index from markdown files.
 *
 * Used by both dev server (vite-docs.ts) and production server (server.js).
 *
 * Wiki-link syntax:
 *   [[target]]          — same folder as source
 *   [[folder/target]]   — cross-folder (route: theory | def | docs | documentation)
 *   [[target|Label]]    — label stripped for resolution
 *
 * Resolution (for each [[target]]):
 *   1. Exact slug match ("0005_ownership-design")
 *   2. Numbered-prefix suffix match ("ownership-design" → "0005_ownership-design") if unique
 *   3. Otherwise skipped (unresolvable / broken link)
 *
 * Index shape:
 *   { "<route>/<slug>": [{ folder, slug, title }, ...], ... }
 *
 * Cross-folder note: in wiki-links the "docs" route and the disk folder
 * "documentation" both resolve to route key "docs" — consistent with the URL
 * scheme used elsewhere in the UI.
 */

const fs = require('fs');
const path = require('path');

const ROUTE_TO_DISK = { theory: 'theory', def: 'def', docs: 'documentation' };
const RESOLVE_ROUTE = { theory: 'theory', def: 'def', docs: 'docs', documentation: 'docs' };

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

/**
 * Scan disk for all docs across known folders.
 * Returns { byRoute: { [route]: [{ slug, title, file, content }] } }.
 */
function scanDocs(docRoot) {
  const byRoute = {};
  for (const [route, disk] of Object.entries(ROUTE_TO_DISK)) {
    const dir = path.join(docRoot, disk);
    if (!fs.existsSync(dir)) continue;
    byRoute[route] = [];
    for (const f of fs.readdirSync(dir)) {
      if (!f.endsWith('.md')) continue;
      const slug = f.replace(/\.md$/, '');
      const file = path.join(dir, f);
      const content = fs.readFileSync(file, 'utf-8');
      const fm = extractFrontmatter(content);
      const title = fm.title || fm.term || slug;
      byRoute[route].push({ slug, title, file, content });
    }
  }
  return { byRoute };
}

/**
 * Resolve a wiki-link target. Returns { route, slug } on success or null.
 */
function resolveTarget(raw, sourceRoute, byRoute) {
  let targetRoute = sourceRoute;
  let name = raw.trim();
  if (name.includes('/')) {
    const parts = name.split('/').filter(p => p !== '..' && p.length > 0);
    if (parts.length < 2) return null;
    const resolved = RESOLVE_ROUTE[parts[0]];
    if (!resolved) return null; // unknown folder (e.g. external "research")
    targetRoute = resolved;
    name = parts.slice(1).join('/');
  }
  const entries = byRoute[targetRoute] || [];
  for (const e of entries) {
    if (e.slug === name) return { route: targetRoute, slug: e.slug };
  }
  const prefixed = entries.filter(e => /^\d{4}_/.test(e.slug) && e.slug.slice(5) === name);
  if (prefixed.length === 1) return { route: targetRoute, slug: prefixed[0].slug };
  return null;
}

const WIKI_RE = /\[\[([^\]|]+)(?:\|[^\]]+)?\]\]/g;

/** Build the backlink index from a scan. Separate from scanDocs so it's testable. */
function buildBacklinkIndex(docRoot) {
  const { byRoute } = scanDocs(docRoot);
  const index = {};
  const dedup = new Set();

  for (const [sourceRoute, entries] of Object.entries(byRoute)) {
    for (const e of entries) {
      const sourceKey = `${sourceRoute}/${e.slug}`;
      WIKI_RE.lastIndex = 0;
      let m;
      while ((m = WIKI_RE.exec(e.content)) !== null) {
        const resolved = resolveTarget(m[1], sourceRoute, byRoute);
        if (!resolved) continue;
        const targetKey = `${resolved.route}/${resolved.slug}`;
        if (targetKey === sourceKey) continue;
        const dkey = `${targetKey}|${sourceKey}`;
        if (dedup.has(dkey)) continue;
        dedup.add(dkey);
        (index[targetKey] ||= []).push({
          folder: sourceRoute,
          slug: e.slug,
          title: e.title,
        });
      }
    }
  }
  for (const k of Object.keys(index)) {
    index[k].sort((a, b) => a.title.localeCompare(b.title));
  }
  return index;
}

/**
 * Cached build with mtime invalidation. Safe to call on every request;
 * re-scans only when a .md file has changed.
 */
let cache = null;
function getCachedIndex(docRoot) {
  let maxMtime = 0;
  try {
    for (const disk of Object.values(ROUTE_TO_DISK)) {
      const dir = path.join(docRoot, disk);
      if (!fs.existsSync(dir)) continue;
      for (const f of fs.readdirSync(dir)) {
        if (!f.endsWith('.md')) continue;
        const t = fs.statSync(path.join(dir, f)).mtimeMs;
        if (t > maxMtime) maxMtime = t;
      }
    }
  } catch {
    return buildBacklinkIndex(docRoot);
  }
  if (cache && cache.docRoot === docRoot && cache.mtime === maxMtime) return cache.index;
  const index = buildBacklinkIndex(docRoot);
  cache = { docRoot, mtime: maxMtime, index };
  return index;
}

/**
 * Compact slug manifest for the client: { [route]: [slug, ...] }.
 * Used by browser-side wiki-link resolution in markdown rendering.
 */
function getDocManifest(docRoot) {
  const { byRoute } = scanDocs(docRoot);
  const out = {};
  for (const [route, entries] of Object.entries(byRoute)) {
    out[route] = entries.map(e => e.slug).sort();
  }
  return out;
}

let manifestCache = null;
function getCachedManifest(docRoot) {
  let maxMtime = 0;
  try {
    for (const disk of Object.values(ROUTE_TO_DISK)) {
      const dir = path.join(docRoot, disk);
      if (!fs.existsSync(dir)) continue;
      for (const f of fs.readdirSync(dir)) {
        if (!f.endsWith('.md')) continue;
        const t = fs.statSync(path.join(dir, f)).mtimeMs;
        if (t > maxMtime) maxMtime = t;
      }
    }
  } catch {
    return getDocManifest(docRoot);
  }
  if (manifestCache && manifestCache.docRoot === docRoot && manifestCache.mtime === maxMtime) {
    return manifestCache.manifest;
  }
  const manifest = getDocManifest(docRoot);
  manifestCache = { docRoot, mtime: maxMtime, manifest };
  return manifest;
}

module.exports = {
  scanDocs,
  resolveTarget,
  buildBacklinkIndex,
  getCachedIndex,
  getDocManifest,
  getCachedManifest,
  extractFrontmatter,
};
