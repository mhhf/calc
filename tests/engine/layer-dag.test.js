/**
 * Architecture layer enforcement tests.
 *
 * Enforces three sets of layering rules by scanning require() calls:
 *
 * 1. Forward engine DAG:
 *      kernel/ <- generic core <- lnl/ <- opt/ <- ill/ <- index.js
 *    Inner layers must NEVER import from outer layers. The only wiring
 *    point is the composition root (index.js), which sees all layers.
 *
 * 2. Backward prover DAG:
 *      kernel.js <- generic.js <- focused.js <- strategy/
 *    Utility modules (pt, context, state, bridge, etc.) sit below
 *    all layers and can be imported by any layer.
 *
 * 3. Global boundary:
 *      lib/ must not import from src/ui/
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const path = require('path');

const ENGINE_DIR = path.join(__dirname, '../../lib/engine');
const PROVER_DIR = path.join(__dirname, '../../lib/prover');
const LIB_DIR = path.join(__dirname, '../../lib');
const UI_DIR = path.resolve(__dirname, '../../src/ui');

// ─── Shared helpers ─────────────────────────────────────────────────

/**
 * Collect all .js files recursively from a directory.
 */
function collectJSFiles(dir) {
  const files = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    if (entry.isDirectory()) {
      files.push(...collectJSFiles(path.join(dir, entry.name)));
    } else if (entry.name.endsWith('.js')) {
      files.push(path.join(dir, entry.name));
    }
  }
  return files;
}

/**
 * Extract local require() paths from a JS file.
 * Only captures relative requires (starting with './' or '../').
 * Ignores comments and string literals (good enough for this codebase).
 */
function extractRequires(filePath) {
  const src = fs.readFileSync(filePath, 'utf8');
  const requires = [];
  const re = /require\(\s*['"]([^'"]+)['"]\s*\)/g;
  let m;
  while ((m = re.exec(src)) !== null) {
    const target = m[1];
    if (target.startsWith('./') || target.startsWith('../')) {
      requires.push(target);
    }
  }
  return requires;
}

/**
 * Create a resolver that maps require paths to relative paths within a base directory.
 * Returns null if the resolved path falls outside the base directory.
 */
function makeResolver(baseDir) {
  return function(fromFile, requirePath) {
    const fromDir = path.dirname(fromFile);
    const resolved = path.resolve(fromDir, requirePath);
    let rel = path.relative(baseDir, resolved);
    if (!rel.endsWith('.js')) {
      if (fs.existsSync(resolved + '.js')) {
        rel = path.relative(baseDir, resolved + '.js');
      } else if (fs.existsSync(path.join(resolved, 'index.js'))) {
        rel = path.relative(baseDir, path.join(resolved, 'index.js'));
      }
    }
    if (rel.startsWith('..')) return null;
    return rel;
  };
}

/**
 * Generic layer violation scanner.
 * @param {string} baseDir - Root directory to scan
 * @param {Function} classify - (relPath) => layerName
 * @param {Object} layerOrder - { layerName: number } (higher = outer)
 * @param {Function} resolve - makeResolver(baseDir) result
 * @param {Object} [opts]
 * @param {string[]} [opts.skipLayers] - Layers to skip as source (e.g. ['root', 'util'])
 * @param {string[]} [opts.skipTargetLayers] - Target layers to ignore (e.g. ['util'])
 * @returns {string[]} violation descriptions
 */
function findLayerViolations(baseDir, classify, layerOrder, resolve, opts = {}) {
  const skipSource = new Set(opts.skipLayers || []);
  const skipTarget = new Set(opts.skipTargetLayers || []);
  const allFiles = collectJSFiles(baseDir);
  const violations = [];

  for (const filePath of allFiles) {
    const relPath = path.relative(baseDir, filePath);
    const sourceLayer = classify(relPath);
    if (skipSource.has(sourceLayer)) continue;

    const requires = extractRequires(filePath);
    for (const req of requires) {
      const targetRel = resolve(filePath, req);
      if (!targetRel) continue;

      const targetLayer = classify(targetRel);
      if (skipTarget.has(targetLayer)) continue;

      const srcOrder = layerOrder[sourceLayer];
      const tgtOrder = layerOrder[targetLayer];

      if (tgtOrder > srcOrder) {
        violations.push(
          `${relPath} (${sourceLayer}) \u2192 ${targetRel} (${targetLayer})`
        );
      }
    }
  }
  return violations;
}

// ─── Engine layer classification ────────────────────────────────────

function classifyEngineModule(relPath) {
  if (relPath === 'index.js') return 'root';
  if (relPath.startsWith('lnl/')) return 'lnl';
  if (relPath.startsWith('opt/')) return 'opt';
  if (relPath.startsWith('ill/')) return 'ill';
  return 'generic';
}

const ENGINE_LAYER_ORDER = {
  generic: 0,
  lnl: 1,
  opt: 2,
  ill: 3,
  root: 4,  // index.js can import anything
};

// ─── Prover layer classification ────────────────────────────────────

/**
 * Classify a prover module into its layer.
 * The 4 layered modules form the prover DAG; everything else is 'util'
 * (shared infrastructure below all layers: pt, context, state, bridge, etc.)
 */
function classifyProverModule(relPath) {
  if (relPath === 'kernel.js') return 'kernel';
  if (relPath === 'generic.js') return 'generic';
  if (relPath === 'focused.js') return 'focused';
  if (relPath.startsWith('strategy/')) return 'strategy';
  return 'util';
}

const PROVER_LAYER_ORDER = {
  util: -1,    // below all layers
  kernel: 0,
  generic: 1,
  focused: 2,
  strategy: 3,
};

// ─── Resolvers ──────────────────────────────────────────────────────

const resolveToEngine = makeResolver(ENGINE_DIR);
const resolveToProver = makeResolver(PROVER_DIR);

// ─── Tests ──────────────────────────────────────────────────────────

describe('engine layer DAG enforcement', () => {
  it('no inner layer imports from an outer layer', () => {
    const violations = findLayerViolations(
      ENGINE_DIR, classifyEngineModule, ENGINE_LAYER_ORDER, resolveToEngine,
      { skipLayers: ['root'] }
    );
    if (violations.length > 0) {
      assert.fail(
        `Engine layer DAG violations (inner layer imports outer layer):\n` +
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

describe('prover layer DAG enforcement', () => {
  it('no inner layer imports from an outer layer', () => {
    const violations = findLayerViolations(
      PROVER_DIR, classifyProverModule, PROVER_LAYER_ORDER, resolveToProver,
      { skipLayers: ['util'], skipTargetLayers: ['util'] }
    );
    if (violations.length > 0) {
      assert.fail(
        `Prover layer DAG violations (inner layer imports outer layer):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });
});

describe('global boundary enforcement', () => {
  it('lib/ must not import from src/ui/', () => {
    const allFiles = collectJSFiles(LIB_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const requires = extractRequires(filePath);
      for (const req of requires) {
        const resolved = path.resolve(path.dirname(filePath), req);
        if (resolved.startsWith(UI_DIR + path.sep) || resolved === UI_DIR) {
          violations.push(
            `${path.relative(LIB_DIR, filePath)} \u2192 ${req}`
          );
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `lib/ \u2192 src/ui/ boundary violations:\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });
});
