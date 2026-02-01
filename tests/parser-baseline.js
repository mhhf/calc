/**
 * Parser Baseline Tests
 *
 * Captures current parsing behavior to ensure the DSL refactor doesn't break anything.
 * Tests parser output structure, not just that parsing succeeds.
 */

const { describe, it } = require('node:test');
const assert = require('node:assert');
const calc = require('../ll.json');
const calcParser = require('../lib/parser.js');
const Calc = require('../lib/calc.js');

const { parser } = calcParser(calc);

// Helper to get AST info
function astInfo(node) {
  if (typeof node === 'string') {
    return { type: 'string', value: node };
  }
  const rule = Calc.db.rules[node.id];
  return {
    ruleName: rule.ruleName,
    ctxName: rule.ctxName,
    children: node.vals.map(v => typeof v === 'string' ? v : astInfo(v))
  };
}

describe('Parser Baseline', function() {

  describe('Atom Parsing', function() {

    it('should parse simple atom', function() {
      const node = parser.parse('-- : P |- -- : P');
      const info = astInfo(node);

      assert.strictEqual(info.ruleName, 'Sequent');
      assert.strictEqual(info.children.length, 2);
      // Left side: Structure_Term_Formula containing P
      assert.strictEqual(info.children[0].ruleName, 'Structure_Term_Formula');
    });

    it('should parse atom with freevar', function() {
      const node = parser.parse('-- : A?X |- -- : A?X');
      const left = node.vals[0].vals[1]; // Formula
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_Atprop');
      // Inner should be Atprop_Freevar (accessed via vals[0])
      const atprop = left.vals[0];
      assert.ok(atprop, 'Should have inner atprop');
      // atprop is an object with id
      const atpropRule = Calc.db.rules[atprop.id];
      assert.strictEqual(atpropRule.ruleName, 'Atprop_Freevar');
    });

    it('should parse parametric atom', function() {
      const node = parser.parse('-- : foo(T?X, T?Y) |- -- : bar');
      const left = node.vals[0].vals[1];
      const leftAtprop = left.vals[0];
      const rule = Calc.db.rules[leftAtprop.id];
      assert.strictEqual(rule.ruleName, 'Atprop_Parametric');
    });

  });

  describe('Connective Parsing', function() {

    it('should parse tensor (*)', function() {
      const node = parser.parse('-- : A * B |- -- : C');
      const left = node.vals[0].vals[1]; // Formula
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_Tensor');
    });

    it('should parse loli (-o)', function() {
      const node = parser.parse('-- : A -o B |- -- : C');
      const left = node.vals[0].vals[1];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
    });

    it('should parse with (&)', function() {
      const node = parser.parse('-- : A & B |- -- : C');
      const left = node.vals[0].vals[1];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_With');
    });

    it('should parse bang (!)', function() {
      const node = parser.parse('-- : ! A |- -- : B');
      const left = node.vals[0].vals[1];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_Bang');
    });

    it('should parse nested connectives', function() {
      const node = parser.parse('-- : (A * B) -o C |- -- : D');
      const left = node.vals[0].vals[1];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
      // Left child should be tensor
      const tensorRule = Calc.db.rules[left.vals[0].id];
      assert.strictEqual(tensorRule.ruleName, 'Formula_Tensor');
    });

  });

  describe('Structure Parsing', function() {

    it('should parse neutral (I)', function() {
      const node = parser.parse('I |- -- : A');
      const left = node.vals[0];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Structure_Neutral');
    });

    it('should parse comma', function() {
      const node = parser.parse('-- : A, -- : B |- -- : C');
      const left = node.vals[0];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Structure_Comma');
    });

    it('should parse structure variable', function() {
      const node = parser.parse('?X, -- : A |- -- : B');
      const left = node.vals[0];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Structure_Comma');
      // First child should be structure freevar
      const freevarRule = Calc.db.rules[left.vals[0].id];
      assert.strictEqual(freevarRule.ruleName, 'Structure_Freevar');
    });

  });

  describe('Precedence', function() {

    it('should parse * with higher precedence than -o', function() {
      // A * B -o C should parse as (A * B) -o C
      const node = parser.parse('-- : A * B -o C |- -- : D');
      const formula = node.vals[0].vals[1];
      const rule = Calc.db.rules[formula.id];
      // Outer should be loli
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
      // Inner left should be tensor
      const leftChild = formula.vals[0];
      const leftRule = Calc.db.rules[leftChild.id];
      assert.strictEqual(leftRule.ruleName, 'Formula_Tensor');
    });

    it('should parse & with higher precedence than -o', function() {
      // A & B -o C should parse as (A & B) -o C
      const node = parser.parse('-- : A & B -o C |- -- : D');
      const formula = node.vals[0].vals[1];
      const rule = Calc.db.rules[formula.id];
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
      const leftChild = formula.vals[0];
      const leftRule = Calc.db.rules[leftChild.id];
      assert.strictEqual(leftRule.ruleName, 'Formula_With');
    });

    it('should respect explicit parentheses', function() {
      // A -o (B * C) - loli should be outer
      const node = parser.parse('-- : A -o (B * C) |- -- : D');
      const formula = node.vals[0].vals[1];
      const rule = Calc.db.rules[formula.id];
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
      // vals[0] = left child (A), vals[1] = right child (B * C)
      const rightChild = formula.vals[1];
      const rightRule = Calc.db.rules[rightChild.id];
      assert.strictEqual(rightRule.ruleName, 'Formula_Tensor');
    });

  });

  describe('Terms', function() {

    it('should parse term any (--)', function() {
      const node = parser.parse('-- : A |- -- : A');
      const left = node.vals[0];
      const rule = Calc.db.rules[left.id];
      assert.strictEqual(rule.ruleName, 'Structure_Term_Formula');
      // First val should be term_any
      const term = left.vals[0];
      const termRule = Calc.db.rules[term.id];
      assert.strictEqual(termRule.ruleName, 'Term_Any');
    });

    it('should parse term variable', function() {
      const node = parser.parse('T?X : A |- -- : A');
      const left = node.vals[0];
      const term = left.vals[0];
      const termRule = Calc.db.rules[term.id];
      assert.strictEqual(termRule.ruleName, 'Term_Freevar');
    });

    it('should parse term concatenate', function() {
      const node = parser.parse('T?X . T?Y : A |- -- : A');
      const left = node.vals[0];
      const term = left.vals[0];
      const termRule = Calc.db.rules[term.id];
      assert.strictEqual(termRule.ruleName, 'Term_Concatenate');
    });

    it('should parse term pair', function() {
      const node = parser.parse('< T?X , T?Y > : A |- -- : A');
      const left = node.vals[0];
      const term = left.vals[0];
      const termRule = Calc.db.rules[term.id];
      assert.strictEqual(termRule.ruleName, 'Term_Pair');
    });

  });

  describe('Complex Formulas', function() {

    it('should parse currying example', function() {
      const node = parser.parse('-- : (A * B) -o C |- -- : A -o (B -o C)');
      assert.ok(node);
      const leftFormula = node.vals[0].vals[1];
      const rightFormula = node.vals[1].vals[1];
      // Left: (A * B) -o C - outer is loli
      assert.strictEqual(Calc.db.rules[leftFormula.id].ruleName, 'Formula_Loli');
      // Right: A -o (B -o C) - outer is loli
      assert.strictEqual(Calc.db.rules[rightFormula.id].ruleName, 'Formula_Loli');
    });

    it('should parse distribution example', function() {
      const node = parser.parse('-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)');
      assert.ok(node);
    });

  });

});
