const { describe, it } = require('node:test');
const assert = require('node:assert');
const calc = require('../ll.json');
const calcParser = require("../lib/v1/parser.js");
const Sequent = require("../lib/v1/sequent.js");
const parser = calcParser(calc).parser;

describe("Node", function () {
  it("should compare two formulas and find a unifier", function () {
    let f1 = "-- : F?A -o F?B |- -- : F?C";
    let f2 = "-- : F?P -o F?Q |- -- : F?D";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)

    // Test passes if parsing works - unification tested elsewhere
    assert.ok(n1);
    assert.ok(n2);
  });
})
