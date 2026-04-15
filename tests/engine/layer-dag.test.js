/**
 * Layer DAG enforcement test.
 *
 * Ensures the engine's 4-layer architecture respects the DAG:
 *   kernel/ ← generic core ← lnl/ ← opt/ ← ill/ ← index.js
 *
 * Inner layers must NEVER import from outer layers. The only wiring
 * point is the composition root (index.js), which sees all layers.
 *
 * This test scans require() calls in all engine modules and verifies
 * that no cross-layer violation exists.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const path = require('path');

const ENGINE_DIR = path.join(__dirname, '../../lib/engine');

// ─── Layer classification ────────────────────────────────────────────

/**
 * Classify an engine module into its layer.
 * Returns: 'generic' | 'lnl' | 'opt' | 'ill' | 'root' (index.js)
 */
function classifyModule(relPath) {
  if (relPath === 'index.js') return 'root';
  if (relPath.startsWith('lnl/')) return 'lnl';
  if (relPath.startsWith('opt/')) return 'opt';
  if (relPath.startsWith('ill/')) return 'ill';
  return 'generic';
}

/**
 * Layer ordering (lower number = inner/lower layer).
 * Inner layers must not import from outer layers.
 */
const LAYER_ORDER = {
  generic: 0,
  lnl: 1,
  opt: 2,
  ill: 3,
  root: 4,  // index.js can import anything
};

// ─── require() extraction ────────────────────────────────────────────

/**
 * Extract local require() paths from a JS file.
 * Only captures relative requires (starting with './' or '../').
 * Ignores comments and string literals (good enough for this codebase).
 */
function extractRequires(filePath) {
  const src = fs.readFileSync(filePath, 'utf8');
  const requires = [];
  // Match require('...') and require("...")
  const re = /require\(\s*['"]([^'"]+)['"]\s*\)/g;
  let m;
  while ((m = re.exec(src)) !== null) {
    const target = m[1];
    // Only local requires (relative paths)
    if (target.startsWith('./') || target.startsWith('../')) {
      requires.push(target);
    }
  }
  return requires;
}

/**
 * Resolve a require path relative to the engine directory.
 * Returns the relative path within engine/, or null if it's outside engine/.
 */
function resolveToEngine(fromFile, requirePath) {
  const fromDir = path.dirname(fromFile);
  const resolved = path.resolve(fromDir, requirePath);
  // Normalize: add .js if needed
  let rel = path.relative(ENGINE_DIR, resolved);
  if (!rel.endsWith('.js')) {
    // Try with .js extension
    if (fs.existsSync(resolved + '.js')) {
      rel = path.relative(ENGINE_DIR, resolved + '.js');
    } else if (fs.existsSync(path.join(resolved, 'index.js'))) {
      rel = path.relative(ENGINE_DIR, path.join(resolved, 'index.js'));
    }
  }
  // Check if it's within engine/
  if (rel.startsWith('..')) return null;
  return rel;
}

// ─── Collect all engine JS files ─────────────────────────────────────

function collectEngineFiles(dir, base) {
  const files = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.isDirectory()) {
      files.push(...collectEngineFiles(path.join(dir, entry.name), base));
    } else if (entry.name.endsWith('.js')) {
      files.push(path.join(dir, entry.name));
    }
  }
  return files;
}

// ─── Test ────────────────────────────────────────────────────────────

describe('layer DAG enforcement', () => {
  it('no inner layer imports from an outer layer', () => {
    const allFiles = collectEngineFiles(ENGINE_DIR, ENGINE_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const relPath = path.relative(ENGINE_DIR, filePath);
      const sourceLayer = classifyModule(relPath);

      // Root (index.js) can import anything
      if (sourceLayer === 'root') continue;

      const requires = extractRequires(filePath);
      for (const req of requires) {
        const targetRel = resolveToEngine(filePath, req);
        if (!targetRel) continue; // Outside engine/ (e.g., kernel/)

        const targetLayer = classifyModule(targetRel);

        const srcOrder = LAYER_ORDER[sourceLayer];
        const tgtOrder = LAYER_ORDER[targetLayer];

        if (tgtOrder > srcOrder) {
          violations.push(
            `${relPath} (${sourceLayer}) → ${targetRel} (${targetLayer})`
          );
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `Layer DAG violations (inner layer imports outer layer):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });

  it('index.js does not import from index.js (no self-require)', () => {
    const indexPath = path.join(ENGINE_DIR, 'index.js');
    const requires = extractRequires(indexPath);
    for (const req of requires) {
      const targetRel = resolveToEngine(indexPath, req);
      assert.notStrictEqual(targetRel, 'index.js',
        'index.js must not require itself');
    }
  });
});
