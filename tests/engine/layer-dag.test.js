/**
 * Architecture layer enforcement tests.
 *
 * Enforces three sets of layering rules by scanning require() calls:
 *
 * 1. Forward engine DAG:
 *      kernel/ <- generic core <- opt/ <- index.js
 *    Inner layers must NEVER import from outer layers. The only wiring
 *    point is the composition root (index.js), which sees all layers.
 *    (The former lnl/ layer lives in family/lnl/lib/ and reaches the
 *    engine only through cc.family — TODO_0086.)
 *
 * 2. Backward prover DAG:
 *      kernel.js <- generic.js <- focused.js <- strategy/
 *    Utility modules (pt, context, state, bridge, etc.) sit below
 *    all layers and can be imported by any layer.
 *
 * 3. Global boundaries:
 *      lib/ must not import from src/ui/
 *      lib/ must not import from calculus/ — calculus-bound machinery
 *      lives in calculus/<name>/{calculus-config.js,lib/} and reaches the
 *      generic engine ONLY through opts.calculusConfig (audit 2026-09-02:
 *      the former lib/engine/ill/ layer moved out; the engine holds no
 *      calculus default).
 *      lib/ must not import from family/ — structural-family machinery
 *      lives in family/<name>/{family-config.js,lib/} and reaches the
 *      engine ONLY through cc.family (TODO_0086).
 *      family/ must not import from calculus/ — a family is shared BY
 *      calculi, it may not depend on any one of them.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import path from 'path';
const ENGINE_DIR = path.join(import.meta.dirname, '../../lib/engine');
const PROVER_DIR = path.join(import.meta.dirname, '../../lib/prover');
const LIB_DIR = path.join(import.meta.dirname, '../../lib');
const UI_DIR = path.resolve(import.meta.dirname, '../../src/ui');
const FAMILY_DIR = path.resolve(import.meta.dirname, '../../family');

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
 * Extract local import/require paths from a JS file.
 * Captures relative imports (starting with './' or '../') from ESM
 * `import ... from '...'`, bare `import '...'`, dynamic `import('...')`,
 * and legacy `require('...')` calls.
 * Ignores comments and string literals (good enough for this codebase).
 */
function extractRequires(filePath) {
  const src = fs.readFileSync(filePath, 'utf8');
  const requires = [];
  const patterns = [
    /require\(\s*['"]([^'"]+)['"]\s*\)/g,
    /import\s+(?:[^'"`;]+?\s+from\s+)?['"]([^'"]+)['"]/g,
    /import\(\s*['"]([^'"]+)['"]\s*\)/g,
    // Re-export barrels are imports too (audit 2026-09-02: this pattern
    // previously evaded the scanner entirely).
    /export\s+(?:\{[^}]*\}|\*(?:\s+as\s+\w+)?)\s+from\s+['"]([^'"]+)['"]/g,
  ];
  for (const re of patterns) {
    let m;
    while ((m = re.exec(src)) !== null) {
      const target = m[1];
      if (target.startsWith('./') || target.startsWith('../')) {
        requires.push(target);
      }
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
  if (relPath.startsWith('timed/')) return 'timed';
  if (relPath.startsWith('opt/')) return 'opt';
  // optimizer.js IS the optimization-profile wiring (builds opt-layer
  // stacks; imported only by the composition root) — opt tier, so it may
  // import opt/ modules (RES_0143 M5).
  if (relPath === 'optimizer.js') return 'opt';
  // engine/theories/ no longer exists (RES_0143 L10): representation
  // READING (ratParts) moved to lib/kernel/rat-term.js; the ratlit
  // equational theory + registration moved beside binlit's to
  // calculus/till/lib/ratlit-theory.js; rat FFI implementations joined
  // calculus/ill/lib/ffi/.
  return 'generic';
}

const ENGINE_LAYER_ORDER = {
  generic: 0,
  timed: 1,   // scheduler layer above generic: may import generic only
  opt: 2,
  root: 3,  // index.js can import anything
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
// - the family layer (family/<name>/lib/) consumes generic interfaces + its
//   own context + opt fast-path callbacks.
// - opt consumes everything above + FFI context data.
//
// Field shapes come from match.js factory exports (single source of truth).
// Per-layer consumption extras are explicitly documented below.

import _match from '../../lib/engine/match.js';
const { GENERIC_FIELDS, FAMILY_FIELDS, OPT_FIELDS, FFI_FIELDS } = _match;

// Generic layer access: generic fields (includes provePersistent — the interface
// generic consumes, implemented by outer layers) + interface callbacks it
// defined (provided by outer layers) + opt fast-path (intentional exception).
const GENERIC_ACCESS = new Set([
  ...GENERIC_FIELDS,
  // Interface callbacks defined in generic, implemented by the family layer
  'matchDynamicRule', 'resolveEx', 'drainDynamicRules', 'dynamicRuleTag',
  // Opt fast-path inline in hot loop (match.js:354-368) — intentional exception:
  // avoids function call overhead per compiled step in hottest loop
  'execPS', 'useCompiledSteps',
  // Strategy A matcher fast path (RES_0143 F4): generic THREADS the
  // injected opt callback (matchOpts.deltaBypass) into matchLinear1 and
  // guards on its presence — the implementation lives in opt/, generic
  // holds only the null-checked call.
  'deltaBypass',
]);

// Family layer access: generic's access + family-owned fields + opt callbacks
// it uses + ffiParsedModes (design debt: backward cache mode detection).
const FAMILY_ACCESS = new Set([
  ...GENERIC_ACCESS,
  ...FAMILY_FIELDS,
  // Opt callbacks consumed by the family layer (compiled dispatch)
  'tryCCDispatch', 'execExStep',
  // Design debt: family reads FFI context for backward cache mode detection
  'ffiParsedModes',
]);

// Opt layer access: family's access + all FFI context data.
const OPT_ACCESS = new Set([
  ...FAMILY_ACCESS,
  ...OPT_FIELDS,
  ...FFI_FIELDS,
]);

const MATCHOPTS_FIELDS = {
  generic: GENERIC_ACCESS,
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

      // root (index.js) can access any field — it's above all layers
      if (layer === 'root') continue;

      const allowed = MATCHOPTS_FIELDS[layer];
      if (!allowed) continue;

      const accessed = extractMatchOptsFields(filePath);
      for (const field of accessed) {
        if (!allowed.has(field)) {
          violations.push(`${relPath} (${layer}) accesses matchOpts.${field}`);
        }
      }
    }

    // Family layer files (family/<name>/lib/) get the family access set.
    for (const filePath of collectJSFiles(FAMILY_DIR)) {
      const relPath = path.relative(FAMILY_DIR, filePath);
      const accessed = extractMatchOptsFields(filePath);
      for (const field of accessed) {
        if (!FAMILY_ACCESS.has(field)) {
          violations.push(`family/${relPath} (family) accesses matchOpts.${field}`);
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
    const allFiles = [...collectJSFiles(ENGINE_DIR), ...collectJSFiles(FAMILY_DIR)];
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
      ..._match.FAMILY_FIELDS,
      ..._match.OPT_FIELDS,
      ..._match.FFI_FIELDS,
    ]);

    const allFiles = [...collectJSFiles(ENGINE_DIR), ...collectJSFiles(FAMILY_DIR)];
    const unknownFields = new Set();

    for (const filePath of allFiles) {
      const relPath = path.relative(ENGINE_DIR, filePath);
      const layer = filePath.startsWith(FAMILY_DIR) ? 'family' : classifyEngineModule(relPath);
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

  it('lib/ must not import from calculus/ (engine holds no calculus default)', () => {
    // The inverse of the plug-in contract: calculus/<name>/ imports lib/
    // freely, but the generic core may never reach into a calculus \u2014 all
    // calculus-specific behavior arrives via opts.calculusConfig. This is
    // what makes the former lib/engine/ill/ smuggle structurally
    // impossible to reintroduce (audit 2026-09-02).
    const CALCULUS_DIR = path.resolve(import.meta.dirname, '../../calculus');
    const allFiles = collectJSFiles(LIB_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const requires = extractRequires(filePath);
      for (const req of requires) {
        const resolved = path.resolve(path.dirname(filePath), req);
        if (resolved.startsWith(CALCULUS_DIR + path.sep)) {
          violations.push(
            `${path.relative(LIB_DIR, filePath)} \u2192 ${req}`
          );
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `lib/ \u2192 calculus/ boundary violations (pass a calculusConfig instead):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });

  it('calculus/ cross-imports follow the declared ancestor DAG', () => {
    // A calculus may import lib/, family/, calculus/kit.js, itself, and its
    // DECLARED ANCESTORS (the @extends chain, more-primitive only) \u2014 never a
    // sibling or descendant. Adding an entry here is the explicit opt-in for a
    // new fork; a new calculus dir with no entry fails, forcing the declaration.
    const CALCULUS_DIR = path.resolve(import.meta.dirname, '../../calculus');
    const ANCESTORS = {
      ill: [],
      till: ['ill'],
      fill: ['ill'],
      rill: ['fill', 'ill'],
      gill: ['till', 'ill'],
      will: ['gill', 'till', 'ill'],
      sill: ['gill', 'till', 'ill'],
      sax: [],
    };
    const seg0 = (p) => path.relative(CALCULUS_DIR, p).split(path.sep)[0];
    // Every calculus directory (has a calculus-config.js) must be declared.
    const undeclared = fs.readdirSync(CALCULUS_DIR)
      .filter(d => fs.existsSync(path.join(CALCULUS_DIR, d, 'calculus-config.js')))
      .filter(d => !(d in ANCESTORS));
    assert.equal(undeclared.length, 0,
      `undeclared calculus dirs (add to the ancestor DAG): ${undeclared.join(', ')}`);

    const violations = [];
    for (const filePath of collectJSFiles(CALCULUS_DIR)) {
      const self = seg0(filePath);
      if (!(self in ANCESTORS)) continue;   // kit.js and non-calculus files
      const allowed = new Set([self, 'kit.js', ...ANCESTORS[self]]);
      for (const req of extractRequires(filePath)) {
        const resolved = path.resolve(path.dirname(filePath), req);
        if (!resolved.startsWith(CALCULUS_DIR + path.sep)) continue;  // lib/family/etc
        const target = seg0(resolved);
        if (!allowed.has(target)) {
          violations.push(`${path.relative(CALCULUS_DIR, filePath)} \u2192 ${req} (${self} may not import ${target})`);
        }
      }
    }
    if (violations.length > 0) {
      assert.fail('calculus/ cross-import DAG violations:\n' + violations.map(v => `  ${v}`).join('\n'));
    }
  });

  it('lib/ must not import from family/ (family arrives via cc.family)', () => {
    // Structural-family machinery (family/<name>/lib/) plugs into the
    // engine as DATA on the calculus config — the generic core may never
    // import it directly (TODO_0086).
    const allFiles = collectJSFiles(LIB_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const requires = extractRequires(filePath);
      for (const req of requires) {
        const resolved = path.resolve(path.dirname(filePath), req);
        if (resolved.startsWith(FAMILY_DIR + path.sep)) {
          violations.push(
            `${path.relative(LIB_DIR, filePath)} \u2192 ${req}`
          );
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `lib/ \u2192 family/ boundary violations (pass cc.family instead):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });

  it('lib/engine imports neither lib/timed nor lib/measure (composition root excepted)', () => {
    // The timed and measure layers sit ABOVE the engine (RES_0143 M1/M2):
    // they import engine code; the engine reaches them only at the
    // composition root (index.js) — anywhere else is an inverted layer.
    const ENGINE_DIR = path.join(LIB_DIR, 'engine');
    const violations = [];
    for (const filePath of collectJSFiles(ENGINE_DIR)) {
      const rel = path.relative(ENGINE_DIR, filePath);
      if (rel === 'index.js') continue; // composition root wires the layers
      for (const req of extractRequires(filePath)) {
        if (/\/(timed|measure)\//.test(req) || /^\.\.\/(timed|measure)\b/.test(req)) {
          violations.push(`engine/${rel} → ${req}`);
        }
      }
    }
    assert.deepStrictEqual(violations, [],
      'lib/engine must not import the timed/measure layers (they sit above it)');
  });

  it('lib/ and family/ use only string-literal dynamic imports (scanner evasion)', () => {
    // extractRequires can only see literal module paths. A dynamic import
    // with a variable or template-literal path would evade every boundary
    // test above — prohibited by convention (audit 2026-09-02: confirmed
    // evasion vector). Comments are stripped first (convert.js documents
    // the unrelated `#import(path)` .ill directive in comments).
    const allFiles = [...collectJSFiles(LIB_DIR), ...collectJSFiles(FAMILY_DIR)];
    const violations = [];
    for (const filePath of allFiles) {
      const src = fs.readFileSync(filePath, 'utf8')
        .replace(/\/\*[\s\S]*?\*\//g, '')
        .replace(/\/\/.*$/gm, '');
      if (/\bimport\(\s*(?!['"])/.test(src)) {
        violations.push(path.relative(LIB_DIR, filePath));
      }
    }
    assert.deepStrictEqual(violations, [],
      'non-literal dynamic import() in lib/ or family/ — boundary scans cannot see it');
  });

  it('connective-name fallback inventory is frozen (no new ILL-name defaults)', () => {
    // lib/ code may not grow new `|| '<connective>'` fallbacks: the
    // existing ones are acknowledged residue (compose's rule-hash builder,
    // role lookups documented in lib/engine/index.js) that never fire when
    // calculus.roles is populated by deriveRoles(). New instances are
    // smuggled ILL knowledge — thread the name from calculus.roles or the
    // config instead. Removing a fallback: update the count down here.
    const ALLOWED = {
      // engine/compose.js reached 0 (RES_0143 L7): rc fields are required,
      // loud throw on absence — the ratchet only shrinks.
      'engine/convert.js': 3,
      'measure/decimate.js': 3,
      'prover/check-term.js': 1,
      'prover/generic-term.js': 1,
      'prover/kernel.js': 2,
      'prover/timed/elaborate-collapse.js': 4,
      'prover/timed/elaborate-trace.js': 7,
      'prover/timed/fire-check.js': 6,
    };
    const RE = /\|\|\s*'(loli|bang|tensor|monad|with|oplus|one|zero|exists|forall)'/g;
    const counts = {};
    for (const filePath of [...collectJSFiles(LIB_DIR), ...collectJSFiles(FAMILY_DIR)]) {
      const src = fs.readFileSync(filePath, 'utf8');
      const n = (src.match(RE) || []).length;
      if (n > 0) counts[path.relative(LIB_DIR, filePath)] = n;
    }
    assert.deepStrictEqual(counts, ALLOWED,
      'connective-name fallback inventory drifted — new `|| \'<conn>\'` in lib/ ' +
      'is smuggled calculus knowledge (or a removed one needs the allowlist updated)');
  });

  it('connective-name equality inventory is frozen (no new `=== \'<conn>\'` guards)', () => {
    // The fallback lint above only sees `|| '<conn>'` — a semantically
    // load-bearing guard written as `tag === 'with'` was invisible to it
    // (audit item 5: coalesce/isDead hardcoded ILL's external-choice
    // name; a calculus naming it differently got silently wrong cohort
    // merging). This second ratchet freezes DIRECT equality comparisons
    // against connective names. The residue is acknowledged: category
    // comparisons (`@category === 'monad'` — meta-vocabulary, not a
    // connective tag), kernel walkers (ast.js — the rTensor coupling
    // family), and checker/renderer surfaces. New instances: thread the
    // tag from resolveConn / tcfg / calculus.roles instead. Shrink-only.
    const ALLOWED = {
      'calculus/builders.js': 1,           // @category === 'monad'
      'calculus/index.js': 1,              // @category === 'monad'
      'engine/convert.js': 3,
      'engine/formula-utils.js': 1,        // @category === 'monad' (resolveConn itself)
      'engine/type-check.js': 1,
      'kernel/ast.js': 3,                  // clause-head walker (rTensor family)
      'measure/ci.js': 4,
      'measure/decimate.js': 2,
      'parser/earley-grammar.js': 2,
      'prover/draw-check.js': 1,
      'prover/rule-interpreter.js': 1,
      'prover/timed/elaborate-collapse.js': 4,
      // rules2-parser.js reached 0 (TODO_0009 audit 2026-09-11): its binder scan
      // now reads Store.BINDER_TAGS instead of `=== 'exists' || === 'forall'`.
    };
    const RE = /[=!]==?\s*'(loli|bang|tensor|monad|with|oplus|one|zero|exists|forall)'/g;
    const counts = {};
    for (const filePath of [...collectJSFiles(LIB_DIR), ...collectJSFiles(FAMILY_DIR)]) {
      const src = fs.readFileSync(filePath, 'utf8');
      const n = (src.match(RE) || []).length;
      if (n > 0) counts[path.relative(LIB_DIR, filePath)] = n;
    }
    assert.deepStrictEqual(counts, ALLOWED,
      'connective-name equality inventory drifted — new `=== \'<conn>\'` in lib/ ' +
      'is smuggled calculus knowledge (or a removed one needs the allowlist updated)');
  });

  it('family/ must not import from calculus/ (a family is shared by calculi)', () => {
    const CALCULUS_DIR = path.resolve(import.meta.dirname, '../../calculus');
    const allFiles = collectJSFiles(FAMILY_DIR);
    const violations = [];

    for (const filePath of allFiles) {
      const requires = extractRequires(filePath);
      for (const req of requires) {
        const resolved = path.resolve(path.dirname(filePath), req);
        if (resolved.startsWith(CALCULUS_DIR + path.sep)) {
          violations.push(
            `${path.relative(FAMILY_DIR, filePath)} \u2192 ${req}`
          );
        }
      }
    }

    if (violations.length > 0) {
      assert.fail(
        `family/ \u2192 calculus/ boundary violations:\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });
});

describe('certificate-checker import fence (toolbox paper §6: the TCB surface)', () => {
  // The trusted checking code — the kernel, its rule interpreter, the
  // step checkers (@fire/@draw), and the SLD certificate checker — must
  // stay on the verification side of the data/engine boundary: a checker
  // that imports an engine oracle (mass solver, FFI, timed scheduler,
  // opt/) could silently trust what it is supposed to re-derive.
  //
  // DIRECT imports are fenced to lib/kernel/* and lib/prover/*, plus
  // exactly four NAMED engine-side modules imported for pure helpers —
  // deliberate definition-sharing so checker and engine cannot drift on
  // the same decomposition:
  //   engine/pattern-utils.js       (collectMetavars — pure AST util)
  //   measure/decimate.js           (splitBody/DECIMATE_PREDS — the SAME
  //                                  body-splitting definition the driver
  //                                  uses; sharing it is the anti-drift
  //                                  choice, and only pure decomposition
  //                                  is called)
  //   engine/type-check.js          (_parseSignature — declaration parse)
  // Anything else — engine/timed/, engine/opt/, engine ffi, family/,
  // calculus/ — is a loud failure here.
  const TCB_MODULES = [
    'prover/kernel.js',
    'prover/context.js',
    'prover/rule-interpreter.js',
    'prover/sld-check.js',
    'prover/draw-check.js',
    'prover/timed/fire-check.js',
    'prover/forward-check.js',
    'prover/gtc-check.js',
  ];
  // (ratlit-theory left this list — RES_0143 L10 moved the ratParts
  // codec into lib/kernel/rat-term.js, which checkers may import freely;
  // the exception set only shrinks.)
  const PURE_EXCEPTIONS = new Set([
    'engine/pattern-utils.js',
    'measure/decimate.js',
    'engine/type-check.js',
  ]);
  const resolveToLib = makeResolver(LIB_DIR);

  it('checker modules import only kernel/prover code plus the named pure exceptions', () => {
    const violations = [];
    for (const mod of TCB_MODULES) {
      const filePath = path.join(LIB_DIR, mod);
      assert.ok(fs.existsSync(filePath), `TCB module missing: ${mod} (update the fence list)`);
      for (const req of extractRequires(filePath)) {
        const rel = resolveToLib(filePath, req);
        if (rel === null) {
          violations.push(`${mod} imports outside lib/: ${req}`);
          continue;
        }
        const relUnix = rel.split(path.sep).join('/');
        const ok = relUnix.startsWith('kernel/') ||
          relUnix.startsWith('prover/') ||
          PURE_EXCEPTIONS.has(relUnix);
        if (!ok) violations.push(`${mod} -> ${relUnix}`);
      }
    }
    if (violations.length > 0) {
      assert.fail(
        `TCB import-fence violations (checker imports engine-side code):\n` +
        violations.map(v => `  ${v}`).join('\n')
      );
    }
  });
});
