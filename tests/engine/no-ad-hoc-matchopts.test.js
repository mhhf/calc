/**
 * Static code-scan tests (TODO_0209 rubric S5, S6).
 *
 * Enforces the "no ad-hoc matchOpts" invariant mechanically:
 *   - In production code (lib/engine/), matchOpts is built exclusively at the
 *     composition root (index.js) using the factories in match.js. No other
 *     file may construct a matchOpts-shaped object literal.
 *   - In tests (tests/engine/), matchOpts must be produced via the
 *     makeMatchOpts helper (tests/engine/_match-opts.js), not as a bare
 *     object literal — this preserves the frozen 20-field shape the engine
 *     relies on.
 *
 * The scan searches for specific field names that are UNIQUE to the matchOpts
 * record (i.e., do not appear in any other configuration object in the codebase):
 *   provePersistent, matchDynamicRule, dynamicRuleTag, optimizePreserved,
 *   backchainUseFFI, useCompiledSteps, ffiParsedModes, ffiMeta, ffiGet, ffiIsGround.
 *
 * False positives (true constructions of matchOpts) are confined to a small
 * allowlist. Anything outside the allowlist is a regression.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const path = require('path');

const REPO = path.resolve(__dirname, '..', '..');

/** Recursively collect .js files under a directory. */
function walkJs(dir) {
  const out = [];
  for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
    const full = path.join(dir, entry.name);
    if (entry.isDirectory()) out.push(...walkJs(full));
    else if (entry.isFile() && entry.name.endsWith('.js')) out.push(full);
  }
  return out;
}

/**
 * Keys that uniquely identify a matchOpts-shaped record. If an object literal
 * contains any of these, it's either a genuine matchOpts construction
 * (allowed only in the factory/composition root) or a bug.
 */
const UNIQUE_MATCHOPTS_KEYS = [
  'provePersistent', 'matchDynamicRule', 'dynamicRuleTag',
  'optimizePreserved', 'backchainUseFFI', 'useCompiledSteps',
  'ffiParsedModes', 'ffiMeta', 'ffiGet', 'ffiIsGround',
];

/** Build a single regex that matches any literal object beginning with one of the unique keys. */
const UNIQUE_OBJECT_LITERAL = new RegExp(
  String.raw`\{\s*(` + UNIQUE_MATCHOPTS_KEYS.join('|') + String.raw`)\s*:`
);

/** Names of functions that legitimately accept matchOpts-field literals as arguments. */
const FACTORY_NAMES = [
  'buildMatchOpts', 'makeMatchOpts',
  'buildGenericProtocol', 'buildLnlProtocol', 'buildOptProtocol', 'buildFfiProtocol',
  // Common short aliases used in tests
  'bmo', 'bgp', 'blp', 'bop', 'bfp',
];
const FACTORY_RE = new RegExp(String.raw`\b(` + FACTORY_NAMES.join('|') + String.raw`)\s*\(`, 'g');

/** Remove the argument list (balanced parens) of every factory call. */
function stripFactoryCalls(src) {
  let result = '';
  let pos = 0;
  let m;
  FACTORY_RE.lastIndex = 0;
  while ((m = FACTORY_RE.exec(src)) !== null) {
    // Emit source up to and including the opening paren of the factory call
    result += src.slice(pos, m.index + m[0].length);
    // Walk forward balancing parens to find the matching close
    let depth = 1;
    let i = m.index + m[0].length;
    while (i < src.length && depth > 0) {
      const c = src[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      i++;
    }
    // Skip the argument list; emit the close paren only.
    result += ')';
    pos = i;
    FACTORY_RE.lastIndex = pos;
  }
  result += src.slice(pos);
  return result;
}

/**
 * Pre-process source to isolate true ad-hoc matchOpts literals:
 *   - strip block + line comments (pattern-matches inside JSDoc are false positives)
 *   - strip destructuring patterns `const { ... } = ...` and `function f({ ... })`
 *     (these bind names, not object-literal values)
 *   - strip arguments of known factory calls (legitimate matchOpts construction)
 */
function stripNonLiterals(src) {
  src = src
    // Remove block comments
    .replace(/\/\*[\s\S]*?\*\//g, '')
    // Remove line comments
    .replace(/\/\/.*$/gm, '')
    // Remove destructuring patterns: `const { ... } = ...` and `function f({ ... })`
    .replace(/(?:const|let|var)\s*\{[^}]*\}\s*=/g, '')
    .replace(/function\s+\w*\s*\(\s*\{[^}]*\}\s*[,)]/g, 'function(')
    .replace(/\(\s*\{[^}]*\}\s*\)\s*=>/g, '() =>');
  // Factory calls are balanced-paren — must handle separately
  src = stripFactoryCalls(src);
  return src;
}

describe('no ad-hoc matchOpts (rubric S5, S6)', () => {
  describe('S5 — production code (lib/engine/)', () => {
    // Allowlist: files legitimately constructing matchOpts.
    const ALLOWED = new Set([
      path.join(REPO, 'lib/engine/match.js'),   // factories live here
      path.join(REPO, 'lib/engine/index.js'),   // composition root
    ]);

    const files = walkJs(path.join(REPO, 'lib/engine'));

    for (const file of files) {
      if (ALLOWED.has(file)) continue;
      const rel = path.relative(REPO, file);
      it(`${rel} has no bare matchOpts object literals`, () => {
        const stripped = stripNonLiterals(fs.readFileSync(file, 'utf8'));
        const m = stripped.match(UNIQUE_OBJECT_LITERAL);
        assert.equal(m, null,
          `${rel}: found ad-hoc matchOpts literal starting with '${m && m[1]}'. ` +
          `Use buildMatchOpts at the composition root (lib/engine/index.js) instead.`);
      });
    }
  });

  describe('S6 — test code (tests/engine/)', () => {
    // Allowlist: files that legitimately reference these keys.
    const ALLOWED = new Set([
      path.join(REPO, 'tests/engine/_match-opts.js'),         // the helper itself
      path.join(REPO, 'tests/engine/match-factories.test.js'),// tests the factories
      path.join(REPO, 'tests/engine/prover-contract.test.js'),// sparse use via makeMatchOpts
      path.join(REPO, 'tests/engine/no-ad-hoc-matchopts.test.js'), // this file
    ]);

    const files = walkJs(path.join(REPO, 'tests/engine'));

    for (const file of files) {
      if (ALLOWED.has(file)) continue;
      const rel = path.relative(REPO, file);
      it(`${rel} has no bare matchOpts object literals`, () => {
        const stripped = stripNonLiterals(fs.readFileSync(file, 'utf8'));
        const m = stripped.match(UNIQUE_OBJECT_LITERAL);
        assert.equal(m, null,
          `${rel}: found ad-hoc matchOpts literal starting with '${m && m[1]}'. ` +
          `Use makeMatchOpts from tests/engine/_match-opts.js instead.`);
      });
    }
  });
});
