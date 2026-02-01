/**
 * Calc.db Baseline Tests
 *
 * Captures the structure of Calc.db as produced from ll.json.
 * Used to verify DSL refactor generates equivalent structure.
 */

const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert');

// Reset Calc state for clean tests
function resetCalcModule() {
  // Clear require cache
  delete require.cache[require.resolve('../lib/calc.js')];
  const Calc = require('../lib/calc.js');
  Calc.initialized = false;
  Calc.rule_index = 0;
  Calc.db = { rules: {}, toIds: {} };
  return Calc;
}

describe('Calc.db Structure', function() {

  describe('Initialization', function() {

    it('should initialize from ll.json', function() {
      const Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);

      assert.strictEqual(Calc.initialized, true);
      assert.ok(Object.keys(Calc.db.rules).length > 0);
      assert.ok(Object.keys(Calc.db.toIds).length > 0);
    });

    it('should create integer IDs for all rules', function() {
      const Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);

      // All rule keys should be numeric
      for (const key of Object.keys(Calc.db.rules)) {
        assert.ok(!isNaN(parseInt(key)), `Key ${key} should be numeric`);
      }
    });

  });

  describe('Connective Rules', function() {

    let Calc;

    beforeEach(function() {
      Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);
    });

    it('should have Formula_Tensor with correct metadata', function() {
      const id = Calc.db.toIds.Formula?.Formula_Tensor;
      assert.ok(id !== undefined, 'Formula_Tensor should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Formula_Tensor');
      assert.strictEqual(rule.ctxName, 'Formula');
      assert.ok(rule.ascii, 'Should have ascii format');
      assert.ok(rule.latex, 'Should have latex format');
      assert.strictEqual(rule.polarity, 'positive', 'Tensor should be positive');
    });

    it('should have Formula_Loli with correct metadata', function() {
      const id = Calc.db.toIds.Formula?.Formula_Loli;
      assert.ok(id !== undefined, 'Formula_Loli should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Formula_Loli');
      assert.strictEqual(rule.polarity, 'negative', 'Loli should be negative');
    });

    it('should have Formula_With with correct metadata', function() {
      const id = Calc.db.toIds.Formula?.Formula_With;
      assert.ok(id !== undefined, 'Formula_With should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Formula_With');
      assert.strictEqual(rule.polarity, 'negative', 'With should be negative');
    });

    it('should have Formula_Bang with correct metadata', function() {
      const id = Calc.db.toIds.Formula?.Formula_Bang;
      assert.ok(id !== undefined, 'Formula_Bang should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Formula_Bang');
      assert.strictEqual(rule.polarity, 'positive', 'Bang should be positive');
    });

  });

  describe('Structure Rules', function() {

    let Calc;

    beforeEach(function() {
      Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);
    });

    it('should have Structure_Comma', function() {
      const id = Calc.db.toIds.Structure?.Structure_Comma;
      assert.ok(id !== undefined, 'Structure_Comma should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Structure_Comma');
      assert.strictEqual(rule.ctxName, 'Structure');
    });

    it('should have Structure_Neutral', function() {
      const id = Calc.db.toIds.Structure?.Structure_Neutral;
      assert.ok(id !== undefined, 'Structure_Neutral should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Structure_Neutral');
    });

    it('should have Structure_Term_Formula', function() {
      const id = Calc.db.toIds.Structure?.Structure_Term_Formula;
      assert.ok(id !== undefined, 'Structure_Term_Formula should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.isTermType, true, 'Should be marked as term type');
    });

  });

  describe('Term Rules', function() {

    let Calc;

    beforeEach(function() {
      Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);
    });

    it('should have Term_Any', function() {
      const id = Calc.db.toIds.Term?.Term_Any;
      assert.ok(id !== undefined, 'Term_Any should exist');

      const rule = Calc.db.rules[id];
      assert.strictEqual(rule.ruleName, 'Term_Any');
      assert.ok(rule.ascii, 'Should have ascii format');
    });

    it('should have Term_Freevar', function() {
      const id = Calc.db.toIds.Term?.Term_Freevar;
      assert.ok(id !== undefined, 'Term_Freevar should exist');
    });

    it('should have Term_Concatenate', function() {
      const id = Calc.db.toIds.Term?.Term_Concatenate;
      assert.ok(id !== undefined, 'Term_Concatenate should exist');
    });

    it('should have Term_Pair', function() {
      const id = Calc.db.toIds.Term?.Term_Pair;
      assert.ok(id !== undefined, 'Term_Pair should exist');
    });

  });

  describe('Context Mappings', function() {

    let Calc;

    beforeEach(function() {
      Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);
    });

    it('should have toIds mapping for all contexts', function() {
      const expectedContexts = ['Atprop', 'Formula', 'Structure', 'Term', 'Sequent'];

      for (const ctx of expectedContexts) {
        assert.ok(Calc.db.toIds[ctx], `Should have toIds for ${ctx}`);
        assert.ok(Object.keys(Calc.db.toIds[ctx]).length > 0, `${ctx} should have rules`);
      }
    });

    it('should have bidirectional ID mapping', function() {
      // For each toIds entry, verify we can look up the rule
      for (const ctx of Object.keys(Calc.db.toIds)) {
        for (const ruleName of Object.keys(Calc.db.toIds[ctx])) {
          const id = Calc.db.toIds[ctx][ruleName];
          const rule = Calc.db.rules[id];
          assert.ok(rule, `Rule ${ctx}.${ruleName} (id=${id}) should exist in rules`);
          assert.strictEqual(rule.ruleName, ruleName);
          assert.strictEqual(rule.ctxName, ctx);
        }
      }
    });

  });

  describe('Format Properties', function() {

    let Calc;

    beforeEach(function() {
      Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);
    });

    it('should have ascii format for connectives', function() {
      const connectives = ['Formula_Tensor', 'Formula_Loli', 'Formula_With', 'Formula_Bang'];

      for (const name of connectives) {
        const id = Calc.db.toIds.Formula[name];
        const rule = Calc.db.rules[id];
        assert.ok(rule.ascii, `${name} should have ascii format`);
      }
    });

    it('should have latex format for connectives', function() {
      const connectives = ['Formula_Tensor', 'Formula_Loli', 'Formula_With', 'Formula_Bang'];

      for (const name of connectives) {
        const id = Calc.db.toIds.Formula[name];
        const rule = Calc.db.rules[id];
        assert.ok(rule.latex, `${name} should have latex format`);
      }
    });

    it('should have precedence for binary connectives', function() {
      const binaryConnectives = ['Formula_Tensor', 'Formula_Loli', 'Formula_With'];

      for (const name of binaryConnectives) {
        const id = Calc.db.toIds.Formula[name];
        const rule = Calc.db.rules[id];
        assert.ok(rule.precedence, `${name} should have precedence`);
        assert.ok(Array.isArray(rule.precedence), 'Precedence should be array');
      }
    });

  });

  describe('Rule Count Snapshot', function() {

    it('should have expected approximate rule count', function() {
      const Calc = resetCalcModule();
      const calc = require('../ll.json');
      Calc.init(calc);

      const ruleCount = Object.keys(Calc.db.rules).length;
      // ll.json currently has 28 rules after simplification
      assert.ok(ruleCount >= 25, `Expected at least 25 rules, got ${ruleCount}`);
      assert.ok(ruleCount <= 50, `Expected at most 50 rules, got ${ruleCount}`);
    });

  });

});
