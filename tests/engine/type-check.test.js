/**
 * Tests for sort checking (lib/engine/type-check.js)
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const {
  _parseSignature,
  sortTable,
  inferSort,
  _checkTerm,
  checkForwardRule,
  checkClause,
  checkAll,
} = require('../../lib/engine/type-check');

// ─── Helpers ────────────────────────────────────────────────────────────────

function atom(name) { return Store.put('atom', [name]); }
function freevar(name) { return Store.put('freevar', [name]); }
function arrow(a, b) { return Store.put('arrow', [a, b]); }
function type() { return Store.put('type', []); }
function binlit(n) { return Store.put('binlit', [n]); }
function tensor(a, b) { return Store.put('tensor', [a, b]); }

function pred(name, ...args) {
  Store.registerTag(name);
  return Store.put(name, args);
}

// ─── _parseSignature ────────────────────────────────────────────────────────

describe('_parseSignature', () => {
  beforeEach(() => Store.clear());

  it('parses nullary type (bin: type)', () => {
    const sig = _parseSignature(type());
    assert.deepEqual(sig, { argSorts: [], returnSort: 'type' });
  });

  it('parses nullary constructor (e: bin)', () => {
    const sig = _parseSignature(atom('bin'));
    assert.deepEqual(sig, { argSorts: [], returnSort: 'bin' });
  });

  it('parses unary arrow (i: bin -> bin)', () => {
    const sig = _parseSignature(arrow(atom('bin'), atom('bin')));
    assert.deepEqual(sig, { argSorts: ['bin'], returnSort: 'bin' });
  });

  it('parses ternary predicate (plus: bin -> bin -> bin -> type)', () => {
    const sig = _parseSignature(
      arrow(atom('bin'), arrow(atom('bin'), arrow(atom('bin'), type())))
    );
    assert.deepEqual(sig, { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' });
  });

  it('returns null for predicate application (axiom)', () => {
    const h = pred('plus', binlit(0n), binlit(0n), binlit(0n));
    assert.strictEqual(_parseSignature(h), null);
  });

  it('parses mixed sort arrows (f: bin -> nat -> type)', () => {
    const sig = _parseSignature(
      arrow(atom('bin'), arrow(atom('nat'), type()))
    );
    assert.deepEqual(sig, { argSorts: ['bin', 'nat'], returnSort: 'type' });
  });
});

// ─── sortTable ─────────────────────────────────────────────────────────

describe('sortTable', () => {
  beforeEach(() => Store.clear());

  it('builds table from type declarations', () => {
    const types = new Map([
      ['bin', type()],
      ['e', atom('bin')],
      ['i', arrow(atom('bin'), atom('bin'))],
      ['plus', arrow(atom('bin'), arrow(atom('bin'), arrow(atom('bin'), type())))],
    ]);
    const table = sortTable(types);
    assert.equal(table.size, 4);
    assert.deepEqual(table.get('bin'), { argSorts: [], returnSort: 'type' });
    assert.deepEqual(table.get('e'), { argSorts: [], returnSort: 'bin' });
    assert.deepEqual(table.get('i'), { argSorts: ['bin'], returnSort: 'bin' });
    assert.deepEqual(table.get('plus'), { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' });
  });

  it('filters out axioms', () => {
    const types = new Map([
      ['bin', type()],
      ['plus/z1', pred('plus', binlit(0n), binlit(0n), binlit(0n))],
    ]);
    const table = sortTable(types);
    assert.equal(table.size, 1);
    assert.ok(table.has('bin'));
    assert.ok(!table.has('plus/z1'));
  });

  it('handles empty input', () => {
    const table = sortTable(new Map());
    assert.equal(table.size, 0);
  });
});

// ─── inferSort ──────────────────────────────────────────────────────────────

describe('inferSort', () => {
  beforeEach(() => Store.clear());

  it('returns bin for binlit', () => {
    assert.equal(inferSort(binlit(42n), new Map(), new Map()), 'bin');
  });

  it('returns sort for atom in sortTable', () => {
    const st = new Map([['e', { argSorts: [], returnSort: 'bin' }]]);
    assert.equal(inferSort(atom('e'), st, new Map()), 'bin');
  });

  it('returns sort for predicate in sortTable', () => {
    const h = pred('plus', binlit(0n), binlit(0n), binlit(0n));
    const st = new Map([['plus', { argSorts: ['bin','bin','bin'], returnSort: 'type' }]]);
    assert.equal(inferSort(h, st, new Map()), 'type');
  });

  it('returns recorded sort for freevar', () => {
    const v = freevar('_M');
    const ms = new Map([[v, 'bin']]);
    assert.equal(inferSort(v, new Map(), ms), 'bin');
  });

  it('returns _ for connective', () => {
    const h = tensor(binlit(0n), binlit(1n));
    assert.equal(inferSort(h, new Map(), new Map()), '_');
  });
});

// ─── _checkTerm ─────────────────────────────────────────────────────────────

describe('_checkTerm', () => {
  beforeEach(() => Store.clear());

  it('accepts well-typed term', () => {
    const st = new Map([
      ['o', { argSorts: ['bin'], returnSort: 'bin' }],
      ['plus', { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' }],
    ]);
    const M = freevar('_M'), N = freevar('_N'), R = freevar('_R');
    const h = pred('plus', pred('o', M), pred('o', N), pred('o', R));
    const errors = [];
    _checkTerm(h, 'type', st, new Map(), errors, 'test');
    assert.deepEqual(errors, []);
  });

  it('detects arity error', () => {
    const st = new Map([
      ['plus', { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' }],
    ]);
    const h = pred('plus', binlit(0n), binlit(1n)); // 2 args, should be 3
    const errors = [];
    _checkTerm(h, 'type', st, new Map(), errors, 'test');
    assert.equal(errors.length, 1);
    assert.match(errors[0], /expects 3 args.*got 2/);
  });

  it('detects sort mismatch', () => {
    const st = new Map([
      ['plus', { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' }],
    ]);
    const h = pred('plus', binlit(0n), binlit(0n), binlit(0n));
    const errors = [];
    // Expect 'bin' but plus returns 'type'
    _checkTerm(h, 'bin', st, new Map(), errors, 'test');
    assert.equal(errors.length, 1);
    assert.match(errors[0], /expected sort 'bin', got 'type'/);
  });

  it('detects metavar sort inconsistency', () => {
    const st = new Map([
      ['f', { argSorts: ['bin'], returnSort: 'type' }],
      ['g', { argSorts: ['nat'], returnSort: 'type' }],
    ]);
    const M = freevar('_M');
    const errors = [];
    const ms = new Map();
    // f(M) → M : bin, then g(M) → M : nat (conflict!)
    _checkTerm(pred('f', M), 'type', st, ms, errors, 'test');
    _checkTerm(pred('g', M), 'type', st, ms, errors, 'test');
    assert.equal(errors.length, 1);
    assert.match(errors[0], /metavar _M used as 'bin' and 'nat'/);
  });

  it('skips predicates not in sort table', () => {
    const h = pred('unknown_pred', binlit(0n));
    const errors = [];
    _checkTerm(h, 'type', new Map(), new Map(), errors, 'test');
    assert.deepEqual(errors, []);
  });

  it('recurses into connective children', () => {
    const st = new Map([
      ['plus', { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' }],
    ]);
    // tensor(plus(e,e,e), plus(e,e)) — second plus has wrong arity
    const good = pred('plus', binlit(0n), binlit(0n), binlit(0n));
    const bad = pred('plus', binlit(0n), binlit(0n)); // 2 args
    const h = tensor(good, bad);
    const errors = [];
    _checkTerm(h, '_', st, new Map(), errors, 'test');
    assert.equal(errors.length, 1);
    assert.match(errors[0], /expects 3 args.*got 2/);
  });
});

// ─── checkForwardRule ───────────────────────────────────────────────────────

describe('checkForwardRule', () => {
  beforeEach(() => Store.clear());

  it('accepts well-typed forward rule', () => {
    const st = new Map([
      ['pc', { argSorts: ['bin'], returnSort: 'type' }],
      ['inc', { argSorts: ['bin', 'bin'], returnSort: 'type' }],
    ]);
    const Pc = freevar('_Pc'), Pc1 = freevar('_Pc1');
    const rule = {
      name: 'test/rule',
      antecedent: { linear: [pred('pc', Pc)], persistent: [pred('inc', Pc, Pc1)] },
      consequent: { linear: [pred('pc', Pc1)], persistent: [] },
    };
    const errors = checkForwardRule(rule, st);
    assert.deepEqual(errors, []);
  });

  it('detects arity error in forward rule', () => {
    const st = new Map([
      ['pc', { argSorts: ['bin'], returnSort: 'type' }],
    ]);
    const rule = {
      name: 'bad/rule',
      antecedent: { linear: [pred('pc', binlit(0n), binlit(1n))], persistent: [] },
      consequent: { linear: [], persistent: [] },
    };
    const errors = checkForwardRule(rule, st);
    assert.equal(errors.length, 1);
    assert.match(errors[0], /rule 'bad\/rule'/);
    assert.match(errors[0], /expects 1 args.*got 2/);
  });

  it('detects sort mismatch in forward rule consequent', () => {
    const st = new Map([
      ['pc', { argSorts: ['bin'], returnSort: 'type' }],
      ['ee', { argSorts: [], returnSort: 'nat' }],
    ]);
    // pc(ee) — ee has sort 'nat', but pc expects 'bin'
    const rule = {
      name: 'bad/sort',
      antecedent: { linear: [], persistent: [] },
      consequent: { linear: [pred('pc', atom('ee'))], persistent: [] },
    };
    const errors = checkForwardRule(rule, st);
    assert.ok(errors.length > 0);
    assert.match(errors[0], /expected sort 'bin', got 'nat'/);
  });
});

// ─── checkClause ────────────────────────────────────────────────────────────

describe('checkClause', () => {
  beforeEach(() => Store.clear());

  it('accepts well-typed clause', () => {
    const st = new Map([
      ['o', { argSorts: ['bin'], returnSort: 'bin' }],
      ['plus', { argSorts: ['bin', 'bin', 'bin'], returnSort: 'type' }],
    ]);
    const M = freevar('_M'), N = freevar('_N'), R = freevar('_R');
    const clause = {
      hash: pred('plus', pred('o', M), pred('o', N), pred('o', R)),
      premises: [pred('plus', M, N, R)],
    };
    const errors = checkClause('plus/s1', clause, st);
    assert.deepEqual(errors, []);
  });

  it('detects metavar inconsistency across head and premise', () => {
    const st = new Map([
      ['f', { argSorts: ['bin'], returnSort: 'type' }],
      ['g', { argSorts: ['nat'], returnSort: 'type' }],
    ]);
    const M = freevar('_M');
    const clause = {
      hash: pred('f', M),       // M : bin
      premises: [pred('g', M)], // M : nat — conflict!
    };
    const errors = checkClause('bad/clause', clause, st);
    assert.equal(errors.length, 1);
    assert.match(errors[0], /metavar _M used as 'bin' and 'nat'/);
  });
});

// ─── checkAll integration ───────────────────────────────────────────────────

describe('checkAll', () => {
  beforeEach(() => Store.clear());

  it('returns zero errors for well-typed program', () => {
    const types = new Map([
      ['bin', type()],
      ['e', atom('bin')],
      ['o', arrow(atom('bin'), atom('bin'))],
      ['plus', arrow(atom('bin'), arrow(atom('bin'), arrow(atom('bin'), type())))],
    ]);
    const M = freevar('_M'), N = freevar('_N'), R = freevar('_R');
    const rules = [{
      name: 'test/rule',
      antecedent: {
        linear: [pred('plus', pred('o', M), pred('o', N), pred('o', R))],
        persistent: [],
      },
      consequent: { linear: [], persistent: [] },
    }];
    const clauses = new Map();
    const result = checkAll(types, rules, clauses);
    assert.deepEqual(result.errors, []);
  });

  it('collects errors from rules and clauses', () => {
    const types = new Map([
      ['pc', arrow(atom('bin'), type())],
    ]);
    const rules = [{
      name: 'bad/rule',
      antecedent: { linear: [pred('pc', binlit(0n), binlit(1n))], persistent: [] },
      consequent: { linear: [], persistent: [] },
    }];
    const clauses = new Map();
    const result = checkAll(types, rules, clauses);
    assert.ok(result.errors.length > 0);
  });

  it('throws in strict mode', () => {
    const types = new Map([
      ['pc', arrow(atom('bin'), type())],
    ]);
    const rules = [{
      name: 'bad/rule',
      antecedent: { linear: [pred('pc', binlit(0n), binlit(1n))], persistent: [] },
      consequent: { linear: [], persistent: [] },
    }];
    assert.throws(
      () => checkAll(types, rules, new Map(), { strict: true }),
      /Sort checking failed/
    );
  });
});

// ─── Full ILL integration ───────────────────────────────────────────────────

describe('checkAll with real ILL', { timeout: 15000 }, () => {
  it('produces zero errors for multisig.ill', () => {
    const mde = require('../../lib/engine');
    Store.clear();
    const calc = mde.load('calculus/ill/programs/multisig.ill', { cache: false });
    const result = checkAll(calc.definitions, calc.forwardRules, calc.clauses);
    if (result.errors.length > 0) {
      console.error('Sort check errors:', result.errors.slice(0, 10));
    }
    assert.equal(result.errors.length, 0, `Expected 0 errors, got ${result.errors.length}: ${result.errors[0] || ''}`);
  });
});
