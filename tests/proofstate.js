const { describe, it } = require('node:test');
const assert = require('node:assert');
const calc = require('../ll.json');
const calcParser = require("../lib/v1/parser.js");
const Sequent = require("../lib/v1/sequent.js");
const Proofstate = require("../lib/v1/proofstate.js");
const Ruleset = require("../lib/v1/ruleset.js");
const PT = require("../lib/v1/pt.js");
const parser = calcParser(calc).parser;
const {rules, bwd, getRule} = Ruleset.init();

const toPT = function (str) {
  let ast = parser.parse(str)
  let seq = Sequent.fromTree(ast);
  let pt = new PT({conclusion: seq});
  return pt;
}

// Helper to run proof search on a formula string
const proveFormula = function (formulaStr) {
  const Calc = require("../lib/v1/calc.js");
  let node = parser.parse(formulaStr);
  let seq = Sequent.fromTree(node);
  let pt = new PT({ conclusion: seq });
  let atoms = Sequent.getAtoms(seq, {rules: Calc.db.rules});

  let result = Proofstate.auto(pt, {
    positive: atoms,
    negative: [],
    debug: false,
    mode: 'proof',
    rules,
    bwd,
    getRule,
    calc
  });

  return { result, pt, seq };
}

describe("Proofstate", function () {

  // Focus is now tracked externally (via ProofSearchState), not in sequent syntax
  // The old blur test used focus bracket syntax which is removed
  it("should track focus state externally", function () {
    const { ProofSearchState } = require('../lib/v1/prover.js');
    let state = new ProofSearchState();

    assert.strictEqual(state.isFocused(), false);
    assert.strictEqual(state.phase, 'inversion');

    state.focus('R', null);
    assert.strictEqual(state.isFocused(), true);
    assert.strictEqual(state.focusPosition, 'R');

    state.blur();
    assert.strictEqual(state.isFocused(), false);
    assert.strictEqual(state.phase, 'inversion');
  });

  // Proof search tests - these verify that focusing and polarity work correctly
  // If these fail, check that:
  // 1. mode: 'proof' is passed to Proofstate.auto (enables forward chaining)
  // 2. Right-focusing for positive atoms is enabled in proofstate.js
  // 3. getInvertableRule skips atomic formulas (atoms use Id, not inversion)

  describe("Proof Search", function () {

    it("should prove identity: Q |- Q", function () {
      let { result } = proveFormula("-- : Q |- -- : Q");
      assert.strictEqual(result.success, true);
    });

    it("should prove modus ponens: P, P -o Q |- Q", function () {
      let { result } = proveFormula("-- : P, -- : P -o Q |- -- : Q");
      assert.strictEqual(result.success, true);
    });

    it("should prove tensor identity: P * Q |- P * Q", function () {
      let { result } = proveFormula("-- : P * Q |- -- : P * Q");
      assert.strictEqual(result.success, true);
    });

    it("should prove tensor commutativity: P * Q |- Q * P", function () {
      let { result } = proveFormula("-- : P * Q |- -- : Q * P");
      assert.strictEqual(result.success, true);
    });

    it("should prove with elimination (left): A & B |- A", function () {
      let { result } = proveFormula("-- : A & B |- -- : A");
      assert.strictEqual(result.success, true);
    });

    it("should prove with elimination (right): A & B |- B", function () {
      let { result } = proveFormula("-- : A & B |- -- : B");
      assert.strictEqual(result.success, true);
    });

    it("should prove with introduction: A |- A & A", function () {
      let { result } = proveFormula("-- : A |- -- : A & A");
      assert.strictEqual(result.success, true);
    });

    it("should prove distribution: P -o (R & Q) |- (P -o Q) & (P -o R)", function () {
      let { result } = proveFormula("-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)");
      assert.strictEqual(result.success, true);
    });

    it("should prove currying: (A * B) -o C |- A -o (B -o C)", function () {
      let { result } = proveFormula("-- : (A * B) -o C |- -- : A -o (B -o C)");
      assert.strictEqual(result.success, true);
    });

    it("should prove uncurrying: A -o (B -o C) |- (A * B) -o C", function () {
      let { result } = proveFormula("-- : A -o (B -o C) |- -- : (A * B) -o C");
      assert.strictEqual(result.success, true);
    });

  });

})
