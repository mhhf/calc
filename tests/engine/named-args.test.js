/**
 * Tests for named predicate arguments (TODO 144)
 *
 * Pi-binder syntax: (name: sort) for naming argument positions.
 * Desugared to positional hashes — names never enter the engine.
 */
const { describe, it, before, after } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');
const Store = require('../../lib/kernel/store');
const mde = require('../../lib/engine');

// ─── Parser: named_arg production ────────────────────────────────────────────

describe('Named args — parser', () => {
  it('parses (name: sort) as named_arg sentinel', () => {
    const h = mde.parseExpr('(addr: bin)');
    assert.strictEqual(Store.tag(h), 'named_arg');
    const nameChild = Store.child(h, 0);
    const exprChild = Store.child(h, 1);
    assert.strictEqual(Store.tag(nameChild), 'atom');
    assert.strictEqual(Store.child(nameChild, 0), 'addr');
    assert.strictEqual(Store.tag(exprChild), 'atom');
    assert.strictEqual(Store.child(exprChild, 0), 'bin');
  });

  it('parses (name: complex_expr) with expression body', () => {
    const h = mde.parseExpr('(result: bin -> type)');
    assert.strictEqual(Store.tag(h), 'named_arg');
    const exprChild = Store.child(h, 1);
    assert.strictEqual(Store.tag(exprChild), 'arrow');
  });

  it('named_arg in arrow chain: (a: bin) -> type', () => {
    const h = mde.parseExpr('(a: bin) -> type');
    assert.strictEqual(Store.tag(h), 'arrow');
    const left = Store.child(h, 0);
    assert.strictEqual(Store.tag(left), 'named_arg');
  });

  it('named_arg in application: balance (address: A) (amount: B)', () => {
    const h = mde.parseExpr('balance (address: A) (amount: B)');
    // Finalized as predicate application with named_arg children
    assert.strictEqual(Store.tag(h), 'balance');
    const c0 = Store.child(h, 0);
    const c1 = Store.child(h, 1);
    assert.strictEqual(Store.tag(c0), 'named_arg');
    assert.strictEqual(Store.tag(c1), 'named_arg');
  });

  it('plain parens still work: (A)', () => {
    const h = mde.parseExpr('(A)');
    assert.strictEqual(Store.tag(h), 'metavar');
    assert.strictEqual(Store.child(h, 0), 'A');
  });

  it('plain parens with expression: (A * B)', () => {
    const h = mde.parseExpr('(A * B)');
    assert.strictEqual(Store.tag(h), 'tensor');
  });
});

// ─── stripNamedArgsFromArrowChain ────────────────────────────────────────────

describe('Named args — stripNamedArgsFromArrowChain', () => {
  const { stripNamedArgsFromArrowChain } = require('../../lib/engine/convert');

  it('strips named args from fully named arrow chain', () => {
    const h = mde.parseExpr('(a: bin) -> (b: bin) -> type');
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(h);

    // Clean hash should match plain arrow chain
    const plain = mde.parseExpr('bin -> bin -> type');
    assert.strictEqual(cleanHash, plain);
    assert.deepStrictEqual(argNames, ['a', 'b']);
  });

  it('strips from mixed named/unnamed chain', () => {
    const h = mde.parseExpr('bin -> (b: bin) -> type');
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(h);

    const plain = mde.parseExpr('bin -> bin -> type');
    assert.strictEqual(cleanHash, plain);
    assert.deepStrictEqual(argNames, [null, 'b']);
  });

  it('no-op for plain arrow chain (no named args)', () => {
    const h = mde.parseExpr('bin -> bin -> type');
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(h);

    assert.strictEqual(cleanHash, h);
    assert.deepStrictEqual(argNames, []);
  });

  it('handles single named arg', () => {
    const h = mde.parseExpr('(x: bin) -> type');
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(h);

    const plain = mde.parseExpr('bin -> type');
    assert.strictEqual(cleanHash, plain);
    assert.deepStrictEqual(argNames, ['x']);
  });

  it('non-arrow hash passes through unchanged', () => {
    const h = mde.parseExpr('bin');
    const { cleanHash, argNames } = stripNamedArgsFromArrowChain(h);
    assert.strictEqual(cleanHash, h);
    assert.deepStrictEqual(argNames, []);
  });
});

// ─── resolveNamedArgSentinels ────────────────────────────────────────────────

describe('Named args — resolveNamedArgSentinels', () => {
  const { resolveNamedArgSentinels } = require('../../lib/engine/convert');

  // Set up argNamesTable
  const argNamesTable = new Map();
  argNamesTable.set('balance', ['address', 'amount']);
  argNamesTable.set('storage', ['key', 'value']);

  it('resolves fully named call site to positional', () => {
    const named = mde.parseExpr('balance (address: A) (amount: B)');
    const clean = resolveNamedArgSentinels(named, argNamesTable);
    const positional = mde.parseExpr('balance A B');
    assert.strictEqual(clean, positional);
  });

  it('resolves reordered named args', () => {
    const named = mde.parseExpr('balance (amount: B) (address: A)');
    const clean = resolveNamedArgSentinels(named, argNamesTable);
    const positional = mde.parseExpr('balance A B');
    assert.strictEqual(clean, positional);
  });

  it('resolves mixed positional + named', () => {
    const named = mde.parseExpr('balance A (amount: B)');
    const clean = resolveNamedArgSentinels(named, argNamesTable);
    const positional = mde.parseExpr('balance A B');
    assert.strictEqual(clean, positional);
  });

  it('no-op for fully positional call', () => {
    const positional = mde.parseExpr('balance A B');
    const clean = resolveNamedArgSentinels(positional, argNamesTable);
    assert.strictEqual(clean, positional);
  });

  it('resolves inside connectives (loli, tensor)', () => {
    const named = mde.parseExpr('balance (address: A) (amount: B) * storage (key: K) (value: V)');
    const clean = resolveNamedArgSentinels(named, argNamesTable);
    const positional = mde.parseExpr('balance A B * storage K V');
    assert.strictEqual(clean, positional);
  });

  it('resolves inside forward rule body', () => {
    const named = mde.parseExpr('balance (address: A) (amount: B) -o { storage (key: K) (value: V) }');
    const clean = resolveNamedArgSentinels(named, argNamesTable);
    const positional = mde.parseExpr('balance A B -o { storage K V }');
    assert.strictEqual(clean, positional);
  });

  // ─── Error cases ──────────────────────────────────────────────────────

  it('error: unknown argument name', () => {
    const named = mde.parseExpr('balance (nonexistent: A) (amount: B)');
    assert.throws(
      () => resolveNamedArgSentinels(named, argNamesTable),
      /no argument 'nonexistent'.*known: address, amount/
    );
  });

  it('error: duplicate named argument', () => {
    const named = mde.parseExpr('balance (address: A) (address: B)');
    assert.throws(
      () => resolveNamedArgSentinels(named, argNamesTable),
      /Duplicate named argument 'address'/i
    );
  });

  it('error: named args for predicate with no named declarations', () => {
    const named = mde.parseExpr('foo (name: A)');
    assert.throws(
      () => resolveNamedArgSentinels(named, argNamesTable),
      /no named declarations/i
    );
  });

  it('error: positional after named', () => {
    const named = mde.parseExpr('balance (address: A) B');
    assert.throws(
      () => resolveNamedArgSentinels(named, argNamesTable),
      /positional.*after named/i
    );
  });

  it('error: missing arguments', () => {
    const named = mde.parseExpr('balance (address: A)');
    assert.throws(
      () => resolveNamedArgSentinels(named, argNamesTable),
      /missing.*amount/i
    );
  });
});

// ─── Two-pass loadFile integration ───────────────────────────────────────────

describe('Named args — loadFile integration', () => {
  const tmpDir = path.join(__dirname, '../../.tmp-test-named-args');

  before(() => {
    fs.mkdirSync(tmpDir, { recursive: true });
  });

  function writeAndLoad(source) {
    const filePath = path.join(tmpDir, `test-${Date.now()}-${Math.random().toString(36).slice(2)}.ill`);
    fs.writeFileSync(filePath, source);
    const convert = require('../../lib/engine/convert');
    return convert.load(filePath);
  }

  it('extracts argNamesTable from declarations', () => {
    const result = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
    `);
    assert(result.argNamesTable.has('balance'));
    assert.deepStrictEqual(result.argNamesTable.get('balance'), ['address', 'amount']);
  });

  it('definitions hash matches positional equivalent', () => {
    const named = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
    `);
    const positional = writeAndLoad(`
balance: bin -> bin -> type.
    `);
    assert.strictEqual(named.definitions.get('balance'), positional.definitions.get('balance'),
      'named and positional declarations should produce identical hashes');
  });

  it('named call sites in rules produce same hashes as positional', () => {
    const named = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
storage: (key: bin) -> (value: bin) -> type.
transfer: balance (address: Addr) (amount: Amt) -o { storage (key: Addr) (value: Amt) }.
    `);
    const positional = writeAndLoad(`
balance: bin -> bin -> type.
storage: bin -> bin -> type.
transfer: balance Addr Amt -o { storage Addr Amt }.
    `);
    const namedRule = named.forwardRules.find(r => r.name === 'transfer');
    const positionalRule = positional.forwardRules.find(r => r.name === 'transfer');
    assert.strictEqual(namedRule.hash, positionalRule.hash,
      'forward rules with named args should hash identically to positional');
  });

  it('named call sites in clauses produce same hashes as positional', () => {
    const named = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
check_balance: balance (address: Addr) (amount: Amt)
  <- balance Addr Amt.
    `);
    const positional = writeAndLoad(`
balance: bin -> bin -> type.
check_balance: balance Addr Amt
  <- balance Addr Amt.
    `);
    assert.strictEqual(
      named.clauses.get('check_balance').hash,
      positional.clauses.get('check_balance').hash
    );
  });

  it('reordered named args in rules produce same hashes', () => {
    const ordered = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
rule1: balance (address: A) (amount: B) -o { balance (address: A) (amount: B) }.
    `);
    const reordered = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
rule1: balance (amount: B) (address: A) -o { balance (amount: B) (address: A) }.
    `);
    assert.strictEqual(
      ordered.forwardRules[0].hash,
      reordered.forwardRules[0].hash,
      'reordered named args should resolve to same positional hash'
    );
  });

  it('mixed positional and named args work', () => {
    const mixed = writeAndLoad(`
balance: (address: bin) -> (amount: bin) -> type.
rule1: balance A (amount: B) -o { balance A (amount: B) }.
    `);
    const positional = writeAndLoad(`
balance: bin -> bin -> type.
rule1: balance A B -o { balance A B }.
    `);
    assert.strictEqual(
      mixed.forwardRules[0].hash,
      positional.forwardRules[0].hash
    );
  });

  it('argNamesTable empty when no named args used', () => {
    const result = writeAndLoad(`
balance: bin -> bin -> type.
    `);
    assert.strictEqual(result.argNamesTable.size, 0);
  });

  it('error: named call site for predicate with no named declarations', () => {
    assert.throws(
      () => writeAndLoad(`
foo: bin -> type.
rule1: foo (x: A) -o { foo A }.
      `),
      /no named declarations/i
    );
  });

  it('argNamesTable survives precompile/loadPrecompiled cycle', () => {
    const source = `
balance: (address: bin) -> (amount: bin) -> type.
storage: (key: bin) -> (value: bin) -> type.
    `;
    const srcPath = path.join(tmpDir, `test-precompile-${Date.now()}.ill`);
    const binPath = path.join(tmpDir, `test-precompile-${Date.now()}.bin`);
    fs.writeFileSync(srcPath, source);

    // Precompile
    Store.clear();
    const pre = mde.precompile(srcPath, binPath);
    assert.deepStrictEqual(pre.argNamesTable.get('balance'), ['address', 'amount']);

    // Load from precompiled
    const calc = mde.loadPrecompiled(binPath);
    assert.ok(calc.argNamesTable, 'argNamesTable should be restored from cache');
    assert.deepStrictEqual(calc.argNamesTable.get('balance'), ['address', 'amount']);
    assert.deepStrictEqual(calc.argNamesTable.get('storage'), ['key', 'value']);
  });

  // Cleanup
  after(() => {
    try { fs.rmSync(tmpDir, { recursive: true }); } catch {}
  });
});

// ─── Sort table integration ──────────────────────────────────────────────────

describe('Named args — sort table', () => {
  const { buildSortTable } = require('../../lib/engine/type-check');

  it('includes argNames in sort entries', () => {
    const argNamesTable = new Map();
    argNamesTable.set('balance', ['address', 'amount']);

    const binHash = Store.put('atom', ['bin']);
    const typeHash = Store.put('type', []);
    const balanceType = Store.put('arrow', [binHash, Store.put('arrow', [binHash, typeHash])]);

    const definitions = new Map();
    definitions.set('balance', balanceType);

    const table = buildSortTable(definitions, argNamesTable);
    const entry = table.get('balance');
    assert.ok(entry);
    assert.deepStrictEqual(entry.argSorts, ['bin', 'bin']);
    assert.strictEqual(entry.returnSort, 'type');
    assert.deepStrictEqual(entry.argNames, ['address', 'amount']);
  });

  it('sort entry has no argNames when not in argNamesTable', () => {
    const definitions = new Map();
    const binHash = Store.put('atom', ['bin']);
    const typeHash = Store.put('type', []);
    definitions.set('foo', Store.put('arrow', [binHash, typeHash]));

    const table = buildSortTable(definitions);
    const entry = table.get('foo');
    assert.ok(entry);
    assert.strictEqual(entry.argNames, undefined);
  });
});

// ─── show.js with argNamesTable ──────────────────────────────────────────────

describe('Named args — show', () => {
  const { show } = require('../../lib/engine/show');

  it('displays named arguments when argNamesTable provided', () => {
    const argNamesTable = new Map();
    argNamesTable.set('balance', ['address', 'amount']);

    const h = mde.parseExpr('balance 0x5 0xa');
    const withNames = show(h, argNamesTable);
    assert.ok(withNames.includes('address:'), `Expected 'address:' in '${withNames}'`);
    assert.ok(withNames.includes('amount:'), `Expected 'amount:' in '${withNames}'`);
  });

  it('displays without names when no argNamesTable', () => {
    const h = mde.parseExpr('balance 0x5 0xa');
    const plain = show(h);
    assert.ok(!plain.includes('address:'), 'Should not have arg names without table');
    assert.ok(plain.includes('balance('));
  });

  it('displays without names for predicates not in table', () => {
    const argNamesTable = new Map();
    argNamesTable.set('storage', ['key', 'value']);

    const h = mde.parseExpr('balance 0x5 0xa');
    const result = show(h, argNamesTable);
    assert.ok(!result.includes('key:'), 'Should not use storage names for balance');
  });
});

// ─── Type-check error messages with arg names ────────────────────────────────

describe('Named args — type-check errors', () => {
  const { _checkTerm, buildSortTable } = require('../../lib/engine/type-check');

  it('arity error includes arg names', () => {
    const argNamesTable = new Map();
    argNamesTable.set('balance', ['address', 'amount']);

    const binHash = Store.put('atom', ['bin']);
    const typeHash = Store.put('type', []);
    const balanceType = Store.put('arrow', [binHash, Store.put('arrow', [binHash, typeHash])]);
    const definitions = new Map();
    definitions.set('balance', balanceType);

    const sortTable = buildSortTable(definitions, argNamesTable);
    const errors = [];
    // balance used as nullary atom (0 args instead of 2)
    const h = Store.put('atom', ['balance']);
    _checkTerm(h, 'type', sortTable, new Map(), errors, 'test');
    assert.strictEqual(errors.length, 1);
    assert.ok(errors[0].includes('address: bin'), `Expected 'address: bin' in '${errors[0]}'`);
    assert.ok(errors[0].includes('amount: bin'), `Expected 'amount: bin' in '${errors[0]}'`);
  });
});
