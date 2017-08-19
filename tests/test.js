const should = require('chai').should()
const calc = require('../ll.json');
const calcParser = require("../lib/parser.js");
const Sequent = require("../lib/sequent.js");
const parser = calcParser(calc).parser;

describe("Sequent", function () {
  it("should parse a tree correctly", function () {
    let formula = "(?X, ?X), ?Y |- < AT? B , AT? C > : F?A xx F?B";
    let node = parser.parse(formula)
    let seq = Sequent.fromTree(node);
    seq.toString().should.equal("(? X)* 2, (? Y)* 1 |- <( AT? B ) , AT? C > : F? A xx F? B");
  });

  it("should compare two sequents", function () {
    let f1 = "?X, ?Y, * : F?A -o F?B |- * : F?C";
    let f2 = "* : F? A, * : F? P -o F? Q |- * : F?Q";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)
    let s1 = Sequent.fromTree(n1);
    let s2 = Sequent.fromTree(n2);
    let l = Sequent.compare(s1, s2, {
      // debug: true
    });
    l.should.be.ok;
  });

  it("should construct the right compare permutation", function () {
    Sequent.constructCompareOptions([0, 1, 2], [1,2,4])
    .length
    .should.equal(6);
  })
})
