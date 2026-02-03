const { describe, it } = require('node:test');
const assert = require('node:assert');
const calc = require('../ll.json');
const calcParser = require("../lib/v1/parser.js");
const Sequent = require("../lib/v1/sequent.js");
const parser = calcParser(calc).parser;
const mgu = require("../lib/v1/mgu.js");

describe("Sequent", function () {
  it("should parse a tree correctly", function () {
    let formula = "(?X, ?X), ?Y |- < AT? B , AT? C > : F?A * F?B";
    let node = parser.parse(formula)
    let seq = Sequent.fromTree(node);
    // Output format has extra parens around first pair element
    assert.strictEqual(seq.toString(), "(? X)* 2, ? Y |- <( AT? B ) , AT? C > F? A * F? B");
  });

  it.skip("should compare two sequents (Sequent.compare removed)", function () {
    // Sequent.compare function was removed from the codebase
    let f1 = "?X, ?Y, -- : F?A -o F?B |- -- : F?C";
    let f2 = "-- : F? A, -- : F? P -o F? Q |- -- : F?Q";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)
    let s1 = Sequent.fromTree(n1);
    let s2 = Sequent.fromTree(n2);
    // let l = Sequent.compare(s1, s2, {});
    // assert.ok(l);
  });

  it("should construct the right compare permutation", function () {
    assert.strictEqual(
      Sequent.constructCompareOptions([0, 1, 2], [1,2,4]).length,
      6
    );
  })

  it("should return all free variables of a sequent", function () {
    let f1 = "?X, ?Y, -- : F?A, -- : X, -- : F?A -o F?B |- -- : bla( T? C) * F?A";
    let n1 = parser.parse(f1)
    let s1 = Sequent.fromTree(n1);
    let vars = Sequent.getFreeVariables(s1);
    assert.strictEqual(
      vars.map(v => v.toString()).sort().join(", "),
      "C, F? A, F? B"
    );
  });


  it("should rename all free variables to unique ones", function () {
    let f1 = "?X, ?Y, -- : F?A, -- : X, -- : F?A -o F?B |- -- : bla( T? C )";
    let n1 = parser.parse(f1)
    let s1 = Sequent.fromTree(n1);
    let initialVarIndex = Sequent.varIndex;
    let seq = Sequent.renameUnique(s1);
    let result = seq.seq.toString();
    // Check that variables were renamed to V_N pattern
    assert.match(result, /V_\d+/);
    // Should have introduced 3 new unique variables
    assert.strictEqual(Sequent.varIndex - initialVarIndex, 3);
  });

  it("should compute the correct mgu", function () {
    let f1 = "I |- -- : plus(TT? z, TT? s. TT? z, T? X)";
    let f2 = "I |- -- : plus(TT? z, T? N, T? N)";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)
    let theta = mgu([[n1, n2]]);
    assert.ok(theta);
  });

})
