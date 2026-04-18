#!/usr/bin/env node
/**
 * esm-migrate.js — one-shot codemod from CJS to ESM.
 *
 * Applies mechanical transforms across lib/, tools/, tests/, benchmarks/,
 * and libexec/. Designed to be idempotent: running twice does not damage
 * already-migrated files.
 *
 * Usage:
 *   node tools/esm-migrate.js --dry-run                 # preview all
 *   node tools/esm-migrate.js --dry-run path/to/file.js # preview one
 *   node tools/esm-migrate.js --apply                   # write back
 *
 * What it handles (line-granularity, regex-based — fast but dumb):
 *   1. `const X = require('Y')`         → `import X from 'Y'`
 *   2. `const {a,b} = require('Y')`     → `import {a,b} from 'Y'`
 *   3. `const {a: x} = require('Y')`    → `import {a as x} from 'Y'`
 *   4. `module.exports = IDENT;`        → `export default IDENT;`
 *   5. `module.exports = {a,b};`        → `export { a, b };`
 *   6. `module.exports.X = Y;`          → `export const X = Y;` (if top-level)
 *   7. `exports.X = Y;`                 → `export const X = Y;` (if top-level)
 *   8. `__dirname` / `__filename`       → `import.meta.dirname` / `.filename`
 *   9. Relative imports get `.js` extension (resolved against filesystem).
 *  10. `require('./foo.json')`          → `import foo from './foo.json' with { type: 'json' }`
 *  11. `require.main === module`        → `import.meta.url === \`file://${process.argv[1]}\``
 *
 * What it does NOT handle (flagged for manual fix):
 *   - dynamic require(expr)   → needs `await import()` + async refactor
 *   - require() inside if/try/for — must be hoisted to top-level
 *   - module.exports.X = Y   inside a function (not top-level)
 *   - reassignments to module.exports in the same file
 *   - circular imports that relied on CJS partial-export semantics
 *
 * The codemod prints a report at the end listing skipped files with
 * reasons, so you know exactly what to fix by hand.
 */

'use strict';

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const DIRS = ['lib', 'tools', 'tests', 'benchmarks', 'libexec'];

// Files/dirs to skip (already ESM, generated, 3rd-party, or the codemod itself).
const SKIP = [
  'node_modules',
  'src/ui',
  'out',
  '.git',
  'tools/esm-migrate.js',
];

const args = process.argv.slice(2);
const DRY = args.includes('--dry-run');
const APPLY = args.includes('--apply');
const TARGET_FILES = args.filter(a => !a.startsWith('--'));

if (!DRY && !APPLY) {
  console.error('Usage: esm-migrate.js (--dry-run | --apply) [files...]');
  process.exit(1);
}

// ─── File walk ──────────────────────────────────────────────────────

function walk(dir, out = []) {
  for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
    const p = path.join(dir, ent.name);
    const rel = path.relative(ROOT, p);
    if (SKIP.some(s => rel === s || rel.startsWith(s + path.sep))) continue;
    if (ent.isDirectory()) walk(p, out);
    else if (ent.isFile() && isJsLike(p)) out.push(p);
  }
  return out;
}

function isJsLike(p) {
  if (p.endsWith('.js')) return true;
  // libexec scripts have no extension but are JS
  if (p.includes('/libexec/')) return true;
  return false;
}

// ─── Path resolution for .js extensions ──────────────────────────────

function resolveRelativeImport(fromFile, spec) {
  if (!spec.startsWith('.')) return spec; // package import
  if (spec.endsWith('.js') || spec.endsWith('.mjs') || spec.endsWith('.cjs') ||
      spec.endsWith('.json') || spec.endsWith('.node')) {
    return spec;
  }
  const fromDir = path.dirname(fromFile);
  const abs = path.resolve(fromDir, spec);
  if (fs.existsSync(abs + '.js')) return spec + '.js';
  if (fs.existsSync(path.join(abs, 'index.js'))) return spec + '/index.js';
  // already resolves without ext (file exists) — e.g. libexec shebang files
  if (fs.existsSync(abs)) return spec;
  // give up; leave untouched, manual fix
  return spec;
}

// ─── Transforms ──────────────────────────────────────────────────────

// Match `const|let|var IDENT = require('...')` — default import
const RE_REQUIRE_DEFAULT = /^(\s*)(?:const|let|var)\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*require\(\s*(['"`])([^'"`]+)\3\s*\)\s*;?\s*$/gm;

// Match `const|let|var { ... } = require('...')` — named imports (maybe with renames)
// Handles optional trailing semicolon, trailing whitespace.
const RE_REQUIRE_NAMED = /^(\s*)(?:const|let|var)\s+\{([^}]+)\}\s*=\s*require\(\s*(['"`])([^'"`]+)\3\s*\)\s*;?\s*$/gm;

// `module.exports = { a, b };` at top-level — multiline-tolerant (no nested braces)
const RE_MEXP_OBJECT = /^(\s*)module\.exports\s*=\s*\{([^{}]*)\}\s*;?\s*$/gm;

// Strip comments from a module.exports object body so simple detection works.
function stripComments(s) {
  return s
    .replace(/\/\*[\s\S]*?\*\//g, '')  // /* ... */
    .replace(/\/\/[^\n]*/g, '');        // // ...
}

// `module.exports = IDENT;` (single reference)
const RE_MEXP_SINGLE = /^(\s*)module\.exports\s*=\s*([A-Za-z_$][A-Za-z0-9_$.]*)\s*;?\s*$/gm;

// `module.exports.X = Y;`  or  `exports.X = Y;`  — top-level (indent 0)
const RE_MEXP_NAMED = /^module\.exports\.([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*;?\s*$/gm;
const RE_EXP_NAMED  = /^exports\.([A-Za-z_$][A-Za-z0-9_$]*)\s*=\s*([A-Za-z_$][A-Za-z0-9_$]*)\s*;?\s*$/gm;

// `require.main === module`  or  `module === require.main`
const RE_REQUIRE_MAIN = /\brequire\.main\s*===\s*module\b|\bmodule\s*===\s*require\.main\b/g;

// Bare `__dirname` / `__filename`
const RE_DIRNAME = /(?<![.$A-Za-z_0-9])__dirname\b/g;
const RE_FILENAME = /(?<![.$A-Za-z_0-9])__filename\b/g;

// Detects non-string require() args (dynamic — NOT migrated, just flagged)
const RE_REQUIRE_DYNAMIC = /\brequire\(\s*[^'"`)]+\)/g;

// Detects in-function require that *can* be mechanically hoisted:
// (lazy require inside a function — flagged, not rewritten)
const RE_REQUIRE_IN_FN = /^(\s{2,}|\t+).*\brequire\(\s*['"`][^'"`]+['"`]\s*\)/gm;

// Remaining require() after transforms (flag only — manual fix)
const RE_REQUIRE_LEFTOVER = /\brequire\(\s*['"`][^'"`]+['"`]\s*\)/g;

// ─── Per-file transform ─────────────────────────────────────────────

function transformFile(filepath) {
  const src = fs.readFileSync(filepath, 'utf8');
  let out = src;
  const notes = [];

  // Idempotency guard: if file already uses `import ... from` and has no
  // `require(` remaining, skip.
  const hasImports = /^import\s/m.test(src);
  const hasRequires = /\brequire\(\s*['"`]/m.test(src);
  if (hasImports && !hasRequires) {
    return { src, out: src, changed: false, notes: ['already ESM'] };
  }

  // 1. `const X = require('Y')`
  out = out.replace(RE_REQUIRE_DEFAULT, (_m, indent, ident, _q, spec) => {
    const resolvedSpec = resolveRelativeImport(filepath, spec);
    return `${indent}import ${ident} from '${resolvedSpec}';`;
  });

  // 2. `const {a,b} = require('Y')`  → `import {a,b} from 'Y';`
  //    Handles `a: x` renames → `a as x`.
  out = out.replace(RE_REQUIRE_NAMED, (_m, indent, names, _q, spec) => {
    const resolvedSpec = resolveRelativeImport(filepath, spec);
    // Normalize whitespace, convert `a: x` to `a as x`
    const normalized = names.split(',').map(n => {
      const t = n.trim();
      if (!t) return null;
      const colon = t.match(/^([A-Za-z_$][A-Za-z0-9_$]*)\s*:\s*([A-Za-z_$][A-Za-z0-9_$]*)$/);
      if (colon) return `${colon[1]} as ${colon[2]}`;
      return t;
    }).filter(Boolean).join(', ');
    return `${indent}import { ${normalized} } from '${resolvedSpec}';`;
  });

  // 3. `module.exports = { a, b };`  → `export { a, b };`
  //    Strips comments, tolerates multi-line. Only if all entries are
  //    bare idents or simple renames (`a: b`).
  out = out.replace(RE_MEXP_OBJECT, (_m, indent, body) => {
    const clean = stripComments(body);
    const entries = clean.split(',').map(s => s.trim()).filter(Boolean);
    const canRewrite = entries.every(e =>
      /^[A-Za-z_$][A-Za-z0-9_$]*$/.test(e) ||
      /^[A-Za-z_$][A-Za-z0-9_$]*\s*:\s*[A-Za-z_$][A-Za-z0-9_$]*$/.test(e));
    if (!canRewrite) {
      notes.push('module.exports object has complex entries — left untouched');
      return _m;
    }
    const exportList = entries.map(e => {
      const m2 = e.match(/^([A-Za-z_$][A-Za-z0-9_$]*)\s*:\s*([A-Za-z_$][A-Za-z0-9_$]*)$/);
      if (m2) return `${m2[2]} as ${m2[1]}`;
      return e;
    }).join(', ');
    return `${indent}export { ${exportList} };`;
  });

  // 4. `module.exports = IDENT;`  → `export default IDENT;`
  out = out.replace(RE_MEXP_SINGLE, (_m, indent, ident) => {
    return `${indent}export default ${ident};`;
  });

  // 5. Top-level `module.exports.X = Y;`  → `export const X = Y;`
  out = out.replace(RE_MEXP_NAMED, (_m, name, value) => {
    return `export const ${name} = ${value};`;
  });
  // 6. Top-level `exports.X = Y;`  → `export const X = Y;`
  out = out.replace(RE_EXP_NAMED, (_m, name, value) => {
    return `export const ${name} = ${value};`;
  });

  // 7. require.main === module  → import.meta.url === `file://${process.argv[1]}`
  out = out.replace(RE_REQUIRE_MAIN, () =>
    "import.meta.url === `file://${process.argv[1]}`");

  // 8. __dirname / __filename → import.meta.dirname / .filename
  //    Only rewrite if used at all; no-op otherwise.
  if (RE_DIRNAME.test(out)) {
    out = out.replace(RE_DIRNAME, 'import.meta.dirname');
  }
  RE_DIRNAME.lastIndex = 0;
  if (RE_FILENAME.test(out)) {
    out = out.replace(RE_FILENAME, 'import.meta.filename');
  }
  RE_FILENAME.lastIndex = 0;

  // After transforms, collect all named exports so we can also emit a
  // CJS-shape `export default { ... }`.  This preserves the semantics
  // of `const X = require('./m')` (whole-object pull) for consumers.
  // Skip if the file already has a `export default` (single-value case).
  const hasDefaultExport = /^\s*export\s+default\b/m.test(out);
  if (!hasDefaultExport) {
    const names = new Set();
    // `export { a, b as c };` — collect the binding name (what's visible after rename)
    for (const m of out.matchAll(/^\s*export\s*\{([^}]+)\}\s*;?\s*$/gm)) {
      for (const entry of m[1].split(',')) {
        const t = entry.trim();
        if (!t) continue;
        const as = t.match(/^([A-Za-z_$][A-Za-z0-9_$]*)\s+as\s+([A-Za-z_$][A-Za-z0-9_$]*)$/);
        names.add(as ? as[2] : t);
      }
    }
    // `export const X = ...;`  and  `export function X(...)` etc.
    for (const m of out.matchAll(/^\s*export\s+(?:const|let|var|function|class)\s+([A-Za-z_$][A-Za-z0-9_$]*)/gm)) {
      names.add(m[1]);
    }
    if (names.size > 0) {
      // Insert before last `export {...}` if present, else append at end.
      const defaultLine = `export default { ${[...names].join(', ')} };\n`;
      out = out.trimEnd() + '\n' + defaultLine;
    }
  }

  // Flag leftover requires
  const dyn = [...src.matchAll(RE_REQUIRE_DYNAMIC)];
  if (dyn.length) notes.push(`${dyn.length}× dynamic require() — manual fix`);

  const inFn = [...src.matchAll(RE_REQUIRE_IN_FN)];
  if (inFn.length) notes.push(`${inFn.length}× require() inside function — manual fix`);

  // After transforms, any remaining require() is by definition unhandled
  const leftover = [...out.matchAll(RE_REQUIRE_LEFTOVER)];
  if (leftover.length) notes.push(`${leftover.length}× require() remaining after transform`);

  const changed = out !== src;
  return { src, out, changed, notes };
}

// ─── Main ───────────────────────────────────────────────────────────

function main() {
  let files;
  if (TARGET_FILES.length) {
    files = TARGET_FILES.map(f => path.resolve(f));
  } else {
    files = DIRS.flatMap(d => {
      const abs = path.join(ROOT, d);
      return fs.existsSync(abs) ? walk(abs) : [];
    });
  }

  const results = files.map(f => ({ file: f, ...transformFile(f) }));

  let changed = 0;
  const withNotes = [];
  for (const r of results) {
    if (r.changed) {
      changed++;
      if (APPLY) {
        fs.writeFileSync(r.file, r.out);
      }
    }
    if (r.notes.length) withNotes.push(r);
  }

  const rel = p => path.relative(ROOT, p);

  if (DRY) {
    console.log(`[dry-run] ${changed} / ${results.length} files would change`);
  } else {
    console.log(`[apply] ${changed} / ${results.length} files written`);
  }

  if (withNotes.length) {
    console.log(`\n${withNotes.length} files have notes (manual-fix or already-ESM):`);
    for (const r of withNotes) {
      const tag = r.notes.includes('already ESM') ? '✓' : '!';
      console.log(`  ${tag} ${rel(r.file)}`);
      for (const n of r.notes) console.log(`      - ${n}`);
    }
  }
}

main();
