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

// ─── matchOpts field-access enforcement ──────────────────────────────
//
// Verifies each engine layer only accesses matchOpts fields it is allowed to.
// This complements the require() DAG: require() enforces module-level boundaries,
// this enforces field-level boundaries on the shared matchOpts callback bag.
//
// The allowed-field sets encode the dependency inversion contracts:
// - generic defines interface contracts (provePersistent, matchDynamicRule, etc.)
//   and consumes them — it doesn't need to know which layer implements them.
// - lnl consumes generic interfaces + its own context + opt fast-path callbacks.
// - opt consumes everything above + FFI context data.
//
// Field shapes come from match.js factory exports (single source of truth).
// Per-layer consumption extras are explicitly documented below.

const _match = require('../../lib/engine/match');
const { GENERIC_FIELDS, LNL_FIELDS, OPT_FIELDS, FFI_FIELDS } = _match;

// Generic layer access: generic fields (includes provePersistent — the interface
// generic consumes, implemented by outer layers) + interface callbacks it
// defined (provided by outer layers) + opt fast-path (intentional exception).
const GENERIC_ACCESS = new Set([
  ...GENERIC_FIELDS,
  // Interface callbacks defined in generic, implemented by lnl
  'matchDynamicRule', 'resolveEx', 'drainLolis', 'dynamicRuleTag',
  // Opt fast-path inline in hot loop (match.js:354-368) — intentional exception:
  // avoids function call overhead per compiled step in hottest loop
  'execPS', 'useCompiledSteps',
]);

// LNL layer access: generic's access + LNL-owned fields + opt callbacks it uses
// + ffiParsedModes (design debt: backward cache mode detection).
const LNL_ACCESS = new Set([
  ...GENERIC_ACCESS,
  ...LNL_FIELDS,
  // Opt callbacks consumed by lnl (lnl calls opt for compiled dispatch)
  'tryCCDispatch', 'execExStep',
  // Design debt: lnl reads FFI context for backward cache mode detection
  'ffiParsedModes',
]);

// Opt layer access: lnl's access + all FFI context data.
const OPT_ACCESS = new Set([
  ...LNL_ACCESS,
  ...OPT_FIELDS,
  ...FFI_FIELDS,
]);

const MATCHOPTS_FIELDS = {
  generic: GENERIC_ACCESS,
  lnl: LNL_ACCESS,
  opt: OPT_ACCESS,
};

/**
 * Extract matchOpts field accesses from a JS file.
 *
 * Captures three syntactic forms:
 *   1. matchOpts.FIELD              — direct property access
 *   2. matchOpts?.FIELD             — optional chaining
 *   3. { FIELD1, FIELD2 } = matchOpts  — destructuring (including renames)
 *
 * Aliasing (e.g. `const x = matchOpts; x.FIELD`) is not detected by regex
 * and is therefore prohibited by convention — enforced by the aliasing test.
 */
function extractMatchOptsFields(filePath) {
  const src = fs.readFileSync(filePath, 'utf8');
  const fields = new Set();

  // Direct access: matchOpts.FIELD or matchOpts?.FIELD
  const reDirect = /matchOpts[?]?\.\s*(\w+)/g;
  let m;
  while ((m = reDirect.exec(src)) !== null) {
    fields.add(m[1]);
  }

  // Destructuring: const { FIELD1, FIELD2: alias, ... } = matchOpts
  // The LHS is an object pattern; RHS is literal identifier matchOpts.
  const reDestructure = /\{\s*([^}]+?)\s*\}\s*=\s*matchOpts\b/g;
  while ((m = reDestructure.exec(src)) !== null) {
    const body = m[1];
    // Split on top-level commas; extract the key (before ':' for renames)
    for (const part of body.split(',')) {
      const key = part.trim().split(':')[0].trim();
      if (key && /^\w+$/.test(key)) fields.add(key);
    }
  }

  return fields;
}

/**
 * Detect illegal aliasing of matchOpts — any assignment where the RHS is the
 * literal `matchOpts` identifier (and not a property access on it) defeats
 * the field-access scanner. Callers must access fields directly.
 *
 * Allowed: matchOpts.x, matchOpts?.x, { x } = matchOpts, foo(matchOpts)
 * Banned: const x = matchOpts, let x = matchOpts, x = matchOpts (assignment)
 */
function detectMatchOptsAliases(filePath) {
  const src = fs.readFileSync(filePath, 'utf8');
  const aliases = [];
  // Match: (const|let|var|=) <identifier> = matchOpts   where RHS is bare matchOpts
  // The lookahead ensures matchOpts is not followed by `.`, `?.`, `,`, `)`, etc. used as arg.
  // Require assignment context: `= matchOpts` at end of RHS (followed by ; \n , } ) or EOF).
  const re = /(?:(?:const|let|var)\s+)?(\w+)\s*=\s*matchOpts\s*(?=[;\n,})]|$)/g;
  let m;
  while ((m = re.exec(src)) !== null) {
    // Skip: destructuring (handled separately) — that's `{ ... } = matchOpts`
    // The regex above doesn't match destructuring because `(\w+)` requires an identifier.
    aliases.push({ name: m[1], offset: m.index });
  }
  return aliases;
}

describe('matchOpts field-access enforcement', () => {
  it('engine layers only access allowed matchOpts fields', () => {
    const allFiles = collectJSFiles(ENGINE_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const relPath = path.relative(ENGINE_DIR, filePath);
      const layer = classifyEngineModule(relPath);

      // root (index.js) and ill/ can access any field — they're above all layers
      if (layer === 'root' || layer === 'ill') continue;

      const allowed = MATCHOPTS_FIELDS[layer];
      if (!allowed) continue;

      const accessed = extractMatchOptsFields(filePath);
      for (const field of accessed) {
        if (!allowed.has(field)) {
          violations.push(`${relPath} (${layer}) accesses matchOpts.${field}`);
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `matchOpts field-access violations (layer accesses disallowed field):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });

  it('matchOpts is never aliased (would defeat the field-access scanner)', () => {
    // The field-access scanner relies on `matchOpts.FIELD` or
    // `{ FIELD } = matchOpts` being the only ways fields are read.
    // Aliasing (`const opts = matchOpts; opts.FIELD`) bypasses detection.
    // Prohibit it to keep the boundary enforceable.
    const allFiles = collectJSFiles(ENGINE_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const relPath = path.relative(ENGINE_DIR, filePath);
      const aliases = detectMatchOptsAliases(filePath);
      for (const a of aliases) {
        violations.push(`${relPath}: \`${a.name} = matchOpts\` (use matchOpts.${a.name} or destructure instead)`);
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `matchOpts aliasing detected (bypasses field-access scanner):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });

  it('all matchOpts fields are covered by some factory (shape stability)', () => {
    // Every field referenced by any engine layer must come from one of the
    // protocol factories — otherwise it would be a ghost field not in the
    // frozen shape, causing runtime errors or IC polymorphism.
    const allFactoryFields = new Set([
      ..._match.GENERIC_FIELDS,
      ..._match.LNL_FIELDS,
      ..._match.OPT_FIELDS,
      ..._match.FFI_FIELDS,
    ]);

    const allFiles = collectJSFiles(ENGINE_DIR);
    const unknownFields = new Set();

    for (const filePath of allFiles) {
      const relPath = path.relative(ENGINE_DIR, filePath);
      const layer = classifyEngineModule(relPath);
      if (layer === 'root') continue;  // composition root
      const accessed = extractMatchOptsFields(filePath);
      for (const field of accessed) {
        if (!allFactoryFields.has(field)) {
          unknownFields.add(`${relPath}: matchOpts.${field}`);
        }
      }
    }

    if (unknownFields.size > 0) {
      assert.fail(
        `Fields accessed but not produced by any factory:\n` +
        [...unknownFields].map(v => `  ${v}`).join('\n')
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
