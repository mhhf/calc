/**
 * Tests for @def abbreviation macros — TODO_0150
 *
 * @def is extralogical parse-time expansion (Twelf %abbrev model).
 * Produces identical content-addressed hashes to writing things out longhand.
 */
const { describe, it } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const Store = require('../../lib/kernel/store');
const { extractMacros, expandMacros } = require('../../lib/parser/macros');
const { parseExpr, desugarPreserved } = require('../../lib/engine/convert');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, flattenAntecedent } = require('../../lib/engine/compile');
const mde = require('../../lib/engine');

const ILL_RC = resolveConnectives(ILL_CONNECTIVES);

describe('@def abbreviation macros', { timeout: 10000 }, () => {

  // ── Extraction ──────────────────────────────────────────────────────────

  describe('extractMacros', () => {
    it('extracts a simple macro', () => {
      const source = '@def foo(X, Y) := bar X * baz Y.\nsome_rule: bar A * baz B -o { qux }.';
      const { macroTable, cleanSource } = extractMacros(source);
      assert.strictEqual(macroTable.size, 1);
      assert(macroTable.has('foo'));
      assert.deepStrictEqual(macroTable.get('foo').params, ['X', 'Y']);
      assert.strictEqual(macroTable.get('foo').body, 'bar X * baz Y');
      // @def should be blanked
      assert(!cleanSource.includes('@def'));
      // Rest preserved
      assert(cleanSource.includes('some_rule'));
    });

    it('extracts multiple macros', () => {
      const source = '@def a(X) := foo X.\n@def b(X, Y) := bar X * baz Y.\n';
      const { macroTable } = extractMacros(source);
      assert.strictEqual(macroTable.size, 2);
      assert(macroTable.has('a'));
      assert(macroTable.has('b'));
    });

    it('handles paren-aware body terminator', () => {
      const source = '@def dispatch(BC, PC, OP, PC2) := !arr_get BC PC OP * !inc PC PC2.\n';
      const { macroTable } = extractMacros(source);
      assert.strictEqual(macroTable.get('dispatch').body, '!arr_get BC PC OP * !inc PC PC2');
    });

    it('handles braces in macro body', () => {
      const source = '@def foo(X) := { bar X }.\n';
      const { macroTable } = extractMacros(source);
      assert.strictEqual(macroTable.get('foo').body, '{ bar X }');
    });

    it('preserves line structure when blanking', () => {
      const source = '@def foo(X) := bar X.\nsecond_line.';
      const { cleanSource } = extractMacros(source);
      const lines = cleanSource.split('\n');
      assert.strictEqual(lines.length, 2);
      assert.strictEqual(lines[1], 'second_line.');
    });

    it('rejects duplicate macro names', () => {
      const source = '@def foo(X) := bar X.\n@def foo(Y) := baz Y.\n';
      assert.throws(() => extractMacros(source), /duplicate/);
    });

    it('rejects nullary macros', () => {
      const source = '@def foo() := bar.\n';
      assert.throws(() => extractMacros(source), /at least one parameter/);
    });

    it('rejects lowercase params', () => {
      const source = '@def foo(x) := bar x.\n';
      assert.throws(() => extractMacros(source), /must start with uppercase/);
    });

    it('rejects missing :=', () => {
      const source = '@def foo(X) bar X.\n';
      assert.throws(() => extractMacros(source), /:=/);
    });

    it('rejects unterminated body', () => {
      const source = '@def foo(X) := bar X';
      assert.throws(() => extractMacros(source), /unterminated/);
    });

    it('returns empty table when no macros', () => {
      const source = 'rule: foo * bar -o { baz }.';
      const { macroTable, cleanSource } = extractMacros(source);
      assert.strictEqual(macroTable.size, 0);
      assert.strictEqual(cleanSource, source);
    });
  });

  // ── Expansion ───────────────────────────────────────────────────────────

  describe('expandMacros', () => {
    it('expands a simple macro call', () => {
      const table = new Map([['foo', { params: ['X', 'Y'], body: 'bar X * baz Y' }]]);
      const result = expandMacros('foo(A, B) * qux', table);
      assert.strictEqual(result, 'bar A * baz B * qux');
    });

    it('expands nested parens in args', () => {
      const table = new Map([['foo', { params: ['X'], body: 'bar X' }]]);
      const result = expandMacros('foo(f(A, B))', table);
      assert.strictEqual(result, 'bar f(A, B)');
    });

    it('respects word boundaries', () => {
      const table = new Map([['pc', { params: ['X'], body: 'counter X' }]]);
      // "vpc" should NOT match "pc" macro
      const result = expandMacros('vpc(A) * pc(B)', table);
      assert.strictEqual(result, 'vpc(A) * counter B');
    });

    it('checks arity', () => {
      const table = new Map([['foo', { params: ['X', 'Y'], body: 'bar X * baz Y' }]]);
      assert.throws(() => expandMacros('foo(A)', table), /expects 2.*got 1/);
    });

    it('expands nested macros', () => {
      const table = new Map([
        ['inner', { params: ['X'], body: 'leaf X' }],
        ['outer', { params: ['X'], body: 'inner(X) * extra' }],
      ]);
      const result = expandMacros('outer(A)', table);
      assert.strictEqual(result, 'leaf A * extra');
    });

    it('detects expansion cycles', () => {
      const table = new Map([
        ['a', { params: ['X'], body: 'b(X)' }],
        ['b', { params: ['X'], body: 'a(X)' }],
      ]);
      assert.throws(() => expandMacros('a(Z)', table), /cycle/i);
    });

    it('rejects $macro( with hard error', () => {
      const table = new Map([['foo', { params: ['X'], body: 'bar X' }]]);
      assert.throws(
        () => expandMacros('$foo(A) * baz', table),
        /\$ \(preserved\) cannot prefix macro/
      );
    });

    it('does not trigger $macro error when $ preceded by word char', () => {
      const table = new Map([['foo', { params: ['X'], body: 'bar X' }]]);
      // "a$foo(" — $ preceded by word char 'a', so $macro detection skips it.
      // But foo( still matches as a macro call ($ is not a word boundary char).
      const result = expandMacros('a$foo(A)', table);
      assert.strictEqual(result, 'a$bar A');
    });

    it('handles multiple calls in one text', () => {
      const table = new Map([['m', { params: ['X'], body: 'wrapped X' }]]);
      const result = expandMacros('m(A) * m(B)', table);
      assert.strictEqual(result, 'wrapped A * wrapped B');
    });

    it('substitutes params with word boundaries', () => {
      const table = new Map([['foo', { params: ['X'], body: 'barX * X' }]]);
      // "X" in "barX" should NOT be substituted; standalone "X" should
      const result = expandMacros('foo(val)', table);
      assert.strictEqual(result, 'barX * val');
    });
  });

  // ── Content-addressed hash identity ─────────────────────────────────────

  describe('hash identity', () => {
    it('macro expansion produces same hash as longhand', () => {
      const longhand = parseExpr('bytecode BC * pc PC * gas GAS');
      const table = new Map([
        ['evm_ctx', { params: ['BC', 'PC', 'GAS'], body: 'bytecode BC * pc PC * gas GAS' }]
      ]);
      const expanded = expandMacros('evm_ctx(BC, PC, GAS)', table);
      const macroHash = parseExpr(expanded);
      assert.strictEqual(macroHash, longhand,
        'macro expansion should produce identical content-addressed hash');
    });

    it('nested macro produces same hash as longhand', () => {
      const longhand = parseExpr('!arr_get BC PC OP * !inc PC PC2');
      const table = new Map([
        ['dispatch', { params: ['BC', 'PC', 'OP', 'PC2'], body: '!arr_get BC PC OP * !inc PC PC2' }]
      ]);
      const expanded = expandMacros('dispatch(BC, PC, OP, PC2)', table);
      const macroHash = parseExpr(expanded);
      assert.strictEqual(macroHash, longhand);
    });

    it('macro with complex args produces correct hash', () => {
      const longhand = parseExpr('foo (bar A B) * baz C');
      const table = new Map([
        ['m', { params: ['X', 'Y'], body: 'foo X * baz Y' }]
      ]);
      const expanded = expandMacros('m((bar A B), C)', table);
      const macroHash = parseExpr(expanded);
      assert.strictEqual(macroHash, longhand);
    });
  });

  // ── Macro + preserved sugar ($) ─────────────────────────────────────────

  describe('interaction with $preserved', () => {
    it('$ on atoms inside macro body works correctly', () => {
      // User defines macro with $ inside the body:
      const table = new Map([
        ['evm_pre', { params: ['BC', 'PC', 'GAS'],
          body: '$bytecode BC * pc PC * gas GAS' }]
      ]);
      const expanded = expandMacros('evm_pre(BC, PC, GAS) -o { pc PC2 }', table);
      // Should expand to: $bytecode BC * pc PC * gas GAS -o { pc PC2 }
      assert(expanded.includes('$bytecode BC'));
      // Parse and desugar
      const parsed = parseExpr(expanded);
      const desugared = desugarPreserved(parsed);
      // bytecode should appear in both ante and conseq
      const ante = Store.child(desugared, 0);
      const conseq = Store.child(desugared, 1);
      const anteFlat = flattenAntecedent(ante, ILL_RC);
      const anteTags = anteFlat.linear.map(h => Store.tag(h));
      assert(anteTags.includes('bytecode'), 'antecedent should have bytecode');
      const body = Store.child(conseq, 0);
      const conseqFlat = flattenAntecedent(body, ILL_RC);
      const conseqTags = conseqFlat.linear.map(h => Store.tag(h));
      assert(conseqTags.includes('bytecode'), 'consequent should have bytecode (injected by $)');
    });
  });

  // ── Macro + named args (TODO_0144) ──────────────────────────────────────

  describe('interaction with named args', () => {
    it('named arg syntax inside macro body is preserved through expansion', () => {
      // Macros expand at text level, named args resolve after parsing
      const table = new Map([
        ['ctx', { params: ['X'], body: 'pred(name: X)' }]
      ]);
      const expanded = expandMacros('ctx(val)', table);
      assert.strictEqual(expanded, 'pred(name: val)');
    });
  });

  // ── Integration: loadFile ───────────────────────────────────────────────

  describe('loadFile integration', { timeout: 15000 }, () => {
    it('loads .ill file with @def and produces correct rules', () => {
      // Write a temp .ill file with macros
      const fs = require('fs');
      const tmpDir = require('os').tmpdir();
      const tmpFile = path.join(tmpDir, `calc-macro-test-${Date.now()}.ill`);

      fs.writeFileSync(tmpFile, `
@def ctx(PC, GAS) := pc PC * gas GAS.

step: ctx(PC, GAS) * !inc PC PC' -o { ctx(PC', GAS) }.
`);

      try {
        const calc = mde.load(tmpFile, { cache: false });
        // Should have one forward rule
        assert.strictEqual(calc.forwardRules.length, 1);
        const rule = calc.forwardRules[0];
        assert.strictEqual(rule.name, 'step');

        // compiled rules have antecedent: { linear: [...], persistent: [...] }
        const anteTags = rule.antecedent.linear.map(h => Store.tag(h));
        assert(anteTags.includes('pc'), 'antecedent should have pc');
        assert(anteTags.includes('gas'), 'antecedent should have gas');
      } finally {
        fs.unlinkSync(tmpFile);
      }
    });

    it('macros from #imported files are visible', () => {
      const fs = require('fs');
      const tmpDir = require('os').tmpdir();
      const libFile = path.join(tmpDir, `calc-macro-lib-${Date.now()}.ill`);
      const mainFile = path.join(tmpDir, `calc-macro-main-${Date.now()}.ill`);

      fs.writeFileSync(libFile, '@def ctx(PC) := pc PC.\n');
      fs.writeFileSync(mainFile, `#import(${libFile})\nstep: ctx(PC) * !inc PC PC' -o { ctx(PC') }.\n`);

      try {
        const calc = mde.load(mainFile, { cache: false });
        assert.strictEqual(calc.forwardRules.length, 1);
        const anteTags = calc.forwardRules[0].antecedent.linear.map(h => Store.tag(h));
        assert(anteTags.includes('pc'), 'imported macro should expand correctly');
      } finally {
        fs.unlinkSync(libFile);
        fs.unlinkSync(mainFile);
      }
    });
  });
});
