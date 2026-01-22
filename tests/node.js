const should = require('chai').should()
const calc = require('../ll.json');
const calcParser = require("../lib/parser.js");
const Sequent = require("../lib/sequent.js");
const parser = calcParser(calc).parser;
// TODO - rewrite to mgu
// const compare = require('../lib/compare.js');


describe("Node", function () {
  it("should compare two formulas and find a unifier", function () {
    let f1 = "-- : F?A -o F?B |- -- : F?C";
    let f2 = "-- : F?P -o F?Q |- -- : F?D";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)

    // let u = compare(n1, n2);
    // (!!u).should.be.true;
  });
})
