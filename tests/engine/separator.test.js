/**
 * Tests for directive separator tokens: |- (turnstile) and => (fat arrow).
 * Turnstile = backward entailment, fat arrow = forward reachability.
 * Part of TODO_0143/TODO_0147 infrastructure.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { parseDecls, _findSep } = require('../../lib/parser/declarations');

let _exprParser;
beforeEach(() => {
  Store.clear();
  if (!_exprParser) {
    const convert = require('../../lib/engine/convert');
    _exprParser = convert.parseExpr;
  }
});

// ─── Unit: _findSep ────────────────────────────────────────────

describe('_findSep', () => {
  it('finds |- at top level', () => {
    const r = _findSep('A * B |- C');
    assert.equal(r.separator, '|-');
    assert.equal(r.splitIndex, 6);
  });

  it('finds => at top level', () => {
    const r = _findSep('A * B => C * D');
    assert.equal(r.separator, '=>');
    assert.equal(r.splitIndex, 6);
  });

  it('returns null when no separator', () => {
    assert.equal(_findSep('A * B * C'), null);
  });

  it('ignores | inside brackets (array cons)', () => {
    assert.equal(_findSep('[H | T]'), null);
  });

  it('ignores |- inside parens', () => {
    assert.equal(_findSep('(A |- B) -o C'), null);
  });

  it('ignores => inside braces', () => {
    assert.equal(_findSep('{ A => B }'), null);
  });

  it('ignores |- inside brackets', () => {
    assert.equal(_findSep('[A |- B]'), null);
  });

  it('finds first separator (|- before =>)', () => {
    const r = _findSep('A |- B => C');
    assert.equal(r.separator, '|-');
  });

  it('handles empty LHS', () => {
    const r = _findSep('|- goal');
    assert.equal(r.separator, '|-');
    assert.equal(r.splitIndex, 0);
  });

  it('handles nested parens before separator', () => {
    const r = _findSep('(A * B) |- C');
    assert.equal(r.separator, '|-');
    assert.equal(r.splitIndex, 8);
  });
});

// ─── Integration: parseDecls with separators ──────────────────────────

describe('Directive separator: turnstile (|-)', () => {
  it('#prove with |- produces lhsHash and rhsHash', () => {
    Store.clear();
    const src = '#prove storage K V |- mem_read M K V.';
    const decls = parseDecls(src, _exprParser);
    assert.equal(decls.length, 1);
    const d = decls[0];
    assert.equal(d.type, 'query');
    assert.equal(d.kind, 'prove');
    assert.equal(d.separator, '|-');
    assert.equal(d.bodyHash, null);
    assert.ok(d.lhsHash, 'lhsHash should be set');
    assert.ok(d.rhsHash, 'rhsHash should be set');
  });

  it('#prove with empty LHS (no context)', () => {
    Store.clear();
    const src = '#prove |- no_overlap 0 32 32 32.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.separator, '|-');
    assert.equal(d.lhsHash, null);
    assert.ok(d.rhsHash);
  });

  it('#prove with settings and |-', () => {
    Store.clear();
    const src = '#prove (rules: [bin]) |- inc 0 1.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.separator, '|-');
    assert.deepEqual(d.settings, { rules: ['bin'] });
    assert.equal(d.lhsHash, null);
    assert.ok(d.rhsHash);
  });

  it('#prove with eigenvars and |-', () => {
    Store.clear();
    const src = '#prove [V] storage K V |- mem_read M K V.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.separator, '|-');
    assert.deepEqual(d.eigenVars, ['V']);
    // Both sides should be forall-wrapped
    assert.equal(Store.tag(d.lhsHash), 'forall');
    assert.equal(Store.tag(d.rhsHash), 'forall');
  });
});

describe('Directive separator: fat arrow (=>)', () => {
  it('#test with => produces lhsHash and rhsHash', () => {
    Store.clear();
    const src = '#test pc 0 * gas 0xffff => stop.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.type, 'query');
    assert.equal(d.kind, 'test');
    assert.equal(d.separator, '=>');
    assert.equal(d.bodyHash, null);
    assert.ok(d.lhsHash);
    assert.ok(d.rhsHash);
  });

  it('#reachable with => and eigenvars', () => {
    Store.clear();
    const src = '#reachable [X] pc 0 * stack X => stop.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.separator, '=>');
    assert.deepEqual(d.eigenVars, ['X']);
    assert.equal(Store.tag(d.lhsHash), 'forall');
    assert.equal(Store.tag(d.rhsHash), 'forall');
  });

  it('#unreachable with =>', () => {
    Store.clear();
    const src = '#unreachable pc 0 * gas 0xffff => revert.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.separator, '=>');
    assert.ok(d.lhsHash);
    assert.ok(d.rhsHash);
  });
});

describe('Backward compatibility', () => {
  it('#symex without separator still works', () => {
    Store.clear();
    const src = '#symex pc 0 * gas 0xffff.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.equal(d.kind, 'symex');
    assert.ok(d.bodyHash);
    assert.equal(d.separator, undefined);
    assert.equal(d.lhsHash, undefined);
    assert.equal(d.rhsHash, undefined);
  });

  it('#symex with eigenvars still works', () => {
    Store.clear();
    const src = '#symex [X] pc 0 * stack X.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.ok(d.bodyHash);
    assert.equal(d.separator, undefined);
    assert.equal(Store.tag(d.bodyHash), 'forall');
  });

  it('array cons [H | T] is not mistaken for turnstile', () => {
    Store.clear();
    const src = '#symex bytecode [0x60 | Rest].';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.ok(d.bodyHash);
    assert.equal(d.separator, undefined);
  });

  it('|- inside parens is not a separator', () => {
    Store.clear();
    // Slightly contrived but tests nesting: a monad with | and - adjacent
    const src = '#prove (counter 1 * counter 2) -o { counter 3 }.';
    const decls = parseDecls(src, _exprParser);
    const d = decls[0];
    assert.ok(d.bodyHash);
    assert.equal(d.separator, undefined);
  });
});

// ─── Integration: convert.load with split queries ────────────────────────────

describe('convert.load: splitQueries integration', () => {
  it('split query flows through to load() result', () => {
    Store.clear();
    const fs = require('fs');
    const os = require('os');
    const pathMod = require('path');

    // Write a temporary .ill file with separator directives
    const tmpDir = fs.mkdtempSync(pathMod.join(os.tmpdir(), 'calc-sep-'));
    const tmpFile = pathMod.join(tmpDir, 'test_sep.ill');
    fs.writeFileSync(tmpFile, [
      'counter : type.',
      'inc : counter N -o { counter (i N) }.',
      '#prove |- counter e.',
      '#test counter e => counter (i e).',
    ].join('\n'));

    try {
      const convert = require('../../lib/engine/convert');
      const result = convert.load(tmpFile);
      // #prove with |- → splitQueries
      assert.ok(result.splitQueries.has('prove'), 'splitQueries should have prove');
      const prove = result.splitQueries.get('prove');
      assert.equal(prove.separator, '|-');
      assert.equal(prove.lhsHash, null); // empty LHS
      assert.ok(prove.rhsHash);

      // #test with => → splitQueries
      assert.ok(result.splitQueries.has('test'), 'splitQueries should have test');
      const test_ = result.splitQueries.get('test');
      assert.equal(test_.separator, '=>');
      assert.ok(test_.lhsHash);
      assert.ok(test_.rhsHash);

      // queries map should NOT have these
      assert.ok(!result.queries.has('prove'));
      assert.ok(!result.queries.has('test'));
    } finally {
      fs.rmSync(tmpDir, { recursive: true });
    }
  });
});
