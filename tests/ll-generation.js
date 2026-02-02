/**
 * ll.json Generation Tests
 *
 * Tests for generating ll.json from .calc and .rules files.
 */

const { test, describe, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');

const generator = require('../lib/celf/generator');
const tsParser = require('../lib/celf/ts-parser');

describe('ll.json generator', () => {

  before(async () => {
    await tsParser.init();
  });

  test('generates ll.json with correct structure', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules',
      { calcName: 'LinearLogic' }
    );

    assert.ok(llJson.calc_name);
    assert.ok(llJson.calc_structure);
    assert.ok(llJson.calc_structure_rules_meta);
    assert.ok(llJson.calc_structure_rules);
    assert.ok(llJson.rules);
  });

  test('extracts binary operators from connectives', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    const binOps = llJson.calc_structure.Formula_Bin_Op;
    assert.ok(binOps);

    // Check tensor
    assert.ok(binOps.Formula_Tensor);
    assert.strictEqual(binOps.Formula_Tensor.ascii, '*');

    // Check loli
    assert.ok(binOps.Formula_Loli);
    assert.strictEqual(binOps.Formula_Loli.ascii, '-o');

    // Check with
    assert.ok(binOps.Formula_With);
    assert.strictEqual(binOps.Formula_With.ascii, '&');
  });

  test('generates rule categories correctly', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    // Axioms (0 premises) go to RuleZer
    assert.ok(llJson.calc_structure_rules.RuleZer.Id);

    // Unary rules (1 premise) go to RuleU
    assert.ok(llJson.calc_structure_rules.RuleU.Tensor_L);
    assert.ok(llJson.calc_structure_rules.RuleU.Loli_R);

    // Binary rules (2 premises) go to RuleBin
    assert.ok(llJson.calc_structure_rules.RuleBin.Tensor_R);
    assert.ok(llJson.calc_structure_rules.RuleBin.With_R);
  });

  test('generates Tensor_L rule correctly', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    const tensorL = llJson.rules.RuleU.Tensor_L;
    assert.ok(tensorL);
    assert.strictEqual(tensorL.length, 2);

    // Conclusion
    assert.ok(tensorL[0].includes('?X'));
    assert.ok(tensorL[0].includes('F?A * F?B'));
    assert.ok(tensorL[0].includes('F?C'));

    // Premise
    assert.ok(tensorL[1].includes('F?A'));
    assert.ok(tensorL[1].includes('F?B'));
  });

  test('generates Loli_R rule correctly', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    const loliR = llJson.rules.RuleU.Loli_R;
    assert.ok(loliR);
    assert.strictEqual(loliR.length, 2);

    // Conclusion: ?X |- -- : F?A -o F?B
    assert.strictEqual(loliR[0], '?X |- -- : F?A -o F?B');

    // Premise: ?X, -- : F?A |- -- : F?B
    assert.strictEqual(loliR[1], '?X, -- : F?A |- -- : F?B');
  });

  test('generates binary rules with two premises', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    const tensorR = llJson.rules.RuleBin.Tensor_R;
    assert.ok(tensorR);
    assert.strictEqual(tensorR.length, 3);  // conclusion + 2 premises

    const withR = llJson.rules.RuleBin.With_R;
    assert.ok(withR);
    assert.strictEqual(withR.length, 3);
  });

  test('uses @pretty annotation for rule labels', async () => {
    const llJson = await generator.generate(
      './calculus/linear-logic.calc',
      './calculus/linear-logic.rules'
    );

    // tensor_l has @pretty "⊗L"
    const tensorL = llJson.calc_structure_rules.RuleU.Tensor_L;
    assert.ok(tensorL.ascii.includes('⊗') || tensorL.ascii.includes('L'));
  });
});

describe('generator helpers', () => {

  before(async () => {
    await tsParser.init();
  });

  test('extractConnectives finds annotated declarations', async () => {
    const result = await tsParser.parseFile('./calculus/linear-logic.calc');
    const connectives = generator.extractConnectives(result.ast);

    assert.ok(connectives.tensor);
    assert.strictEqual(connectives.tensor.arity, 2);
    assert.strictEqual(connectives.tensor.ascii, '_ * _');
    assert.strictEqual(connectives.tensor.polarity, 'positive');
  });

  test('extractRules finds clause declarations', async () => {
    const result = await tsParser.parseFile('./calculus/linear-logic.rules');
    const rules = generator.extractRules(result.ast);

    assert.ok(rules.tensor_l);
    assert.strictEqual(rules.tensor_l.numPremises, 1);
    assert.strictEqual(rules.tensor_l.pretty, '⊗L');
    assert.strictEqual(rules.tensor_l.invertible, true);
  });

  test('getAnnotation extracts values correctly', async () => {
    const result = await tsParser.parse(`
      foo: type
        @ascii "test"
        @prec 60 left
        @shallow true.
    `);
    const decl = result.ast.declarations[0];

    assert.strictEqual(generator.getAnnotation(decl.annotations, 'ascii'), 'test');

    const prec = generator.getAnnotation(decl.annotations, 'prec');
    assert.strictEqual(prec.precedence, 60);
    assert.strictEqual(prec.associativity, 'left');

    assert.strictEqual(generator.getAnnotation(decl.annotations, 'shallow'), true);
    assert.strictEqual(generator.getAnnotation(decl.annotations, 'nonexistent'), null);
  });
});

describe('pattern generation', () => {

  before(async () => {
    await tsParser.init();
  });

  test('termToPattern handles variables', async () => {
    const result = await tsParser.parse('foo: bar A B.');
    const decl = result.ast.declarations[0];

    // The term should contain variable applications
    const pattern = generator.termToPattern(decl.head);
    assert.ok(pattern.includes('F?A') || pattern.includes('A'));
    assert.ok(pattern.includes('F?B') || pattern.includes('B'));
  });

  test('termToPattern handles seq correctly', async () => {
    // Parse a simple sequent pattern
    const result = await tsParser.parse('test: deriv (seq G A).');
    const decl = result.ast.declarations[0];

    const pattern = generator.termToPattern(decl.head);
    // Should produce something like "?X |- -- : F?A"
    assert.ok(pattern.includes('|-'), `Pattern should contain turnstile: ${pattern}`);
  });
});
