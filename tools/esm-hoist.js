#!/usr/bin/env node
/**
 * esm-hoist.js — Hoist indented `import ... from '...'` statements to top-level.
 *
 * The ESM codemod converted `const X = require('./y')` everywhere, including
 * lines that were indented inside functions. Those became indented `import`
 * statements, which are syntax errors. This script moves them to the top of
 * each file, deduplicates them against each other and against existing
 * top-level imports, and leaves the (now-empty) original line.
 *
 * Usage:
 *   node tools/esm-hoist.js --dry-run [files...]
 *   node tools/esm-hoist.js --apply [files...]
 *
 * If no files specified, scans lib/, tools/, tests/, benchmarks/, libexec/.
 */

'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const args = process.argv.slice(2);
const DRY = args.includes('--dry-run');
const APPLY = args.includes('--apply');
const TARGETS = args.filter(a => !a.startsWith('--'));

if (!DRY && !APPLY) {
  console.error('Usage: esm-hoist.js (--dry-run | --apply) [files...]');
  process.exit(1);
}

function walk(dir, out = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, ent.name);
    const rel = path.relative(ROOT, p);
    if (rel.startsWith('node_modules') || rel.startsWith('src/ui')
        || rel.startsWith('out') || rel.startsWith('.git')) continue;
    if (ent.isDirectory()) walk(p, out);
    else if (ent.isFile() && (p.endsWith('.js') || p.includes('/libexec/'))) out.push(p);
  }
  return out;
}

// Matches a full indented import-from line.
const RE_INDENTED_IMPORT = /^[ \t]+import\s+(?:(.+?)\s+from\s+)?(['"`])([^'"`]+)\2\s*;?\s*$/gm;

// Matches any top-level import line (for "already imported?" detection).
const RE_TOPLEVEL_IMPORT = /^import\s+(.+?)\s+from\s+(['"`])([^'"`]+)\2\s*;?\s*$/gm;

function hoistFile(filepath) {
  const src = fs.readFileSync(filepath, 'utf8');
  RE_INDENTED_IMPORT.lastIndex = 0;
  RE_TOPLEVEL_IMPORT.lastIndex = 0;

  // Collect existing top-level imports so we can dedupe against them.
  const existing = new Map(); // key: binding|spec → full line
  for (const m of src.matchAll(RE_TOPLEVEL_IMPORT)) {
    const key = `${m[1] || ''}|${m[3]}`;
    existing.set(key, m[0]);
  }

  // Collect indented imports and remove from body.
  const hoisted = [];
  const seen = new Set();
  const newSrc = src.replace(RE_INDENTED_IMPORT, (line, binding, _q, spec) => {
    const key = `${binding || ''}|${spec}`;
    if (existing.has(key) || seen.has(key)) {
      // Already imported at top-level (or seen another hoisted copy) — drop.
      return '';
    }
    seen.add(key);
    const normalized = binding
      ? `import ${binding.trim()} from '${spec}';`
      : `import '${spec}';`;
    hoisted.push(normalized);
    return '';
  });

  if (hoisted.length === 0) {
    return { src, out: src, changed: false, hoistedCount: 0 };
  }

  // Find insertion point: after the last existing top-level import, or after
  // the file-leading comment/directive block.
  const lines = newSrc.split('\n');
  let insertAt = 0;
  // Skip JSDoc/banner comments and 'use strict';
  while (insertAt < lines.length) {
    const l = lines[insertAt].trim();
    if (l.startsWith('/*') || l.startsWith('//') || l.startsWith('*') ||
        l === '' || l === '*/' || l === "'use strict';" || l === '"use strict";') {
      insertAt++;
      continue;
    }
    break;
  }
  // Then advance past existing import lines.
  while (insertAt < lines.length && /^\s*import\s/.test(lines[insertAt])) {
    insertAt++;
  }

  const before = lines.slice(0, insertAt);
  const after = lines.slice(insertAt);
  const block = ['// Hoisted by tools/esm-hoist.js:', ...hoisted, ''];
  const out = [...before, ...block, ...after].join('\n');

  return { src, out, changed: true, hoistedCount: hoisted.length };
}

function main() {
  let files = TARGETS.length
    ? TARGETS.map(f => path.resolve(f))
    : ['lib', 'tools', 'tests', 'benchmarks', 'libexec'].flatMap(d => {
        const abs = path.join(ROOT, d);
        return fs.existsSync(abs) ? walk(abs) : [];
      });

  let changed = 0;
  let totalHoisted = 0;
  for (const f of files) {
    const r = hoistFile(f);
    if (r.changed) {
      changed++;
      totalHoisted += r.hoistedCount;
      if (APPLY) fs.writeFileSync(f, r.out);
      console.log(`  ${path.relative(ROOT, f)}: +${r.hoistedCount}`);
    }
  }
  console.log(`\n${DRY ? '[dry-run]' : '[apply]'} ${changed} files, ${totalHoisted} imports hoisted`);
}

main();
