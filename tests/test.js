const should = require('chai').should()
const calc = require('../ll.json');
const calcParser = require("../lib/parser.js");
const Sequent = require("../lib/sequent.js");
const parser = calcParser(calc).parser;
const mgu = require("../lib/mgu.js");

describe("Sequent", function () {
  it("should parse a tree correctly", function () {
    let formula = "(?X, ?X), ?Y |- < AT? B , AT? C > : F?A xx F?B";
    let node = parser.parse(formula)
    let seq = Sequent.fromTree(node);
    seq.toString().should.equal("(? X)* 2, ? Y |- <( AT? B ) , AT? C > : F? A xx F? B");
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

  it("should return all free variables of a sequent", function () {
    let f1 = "?X, ?Y, -- : F?A, -- : X, -- : F?A -o F?B |- -- : bla( T? C) * F?A";
    let n1 = parser.parse(f1)
    let s1 = Sequent.fromTree(n1);
    let vars = Sequent.getFreeVariables(s1);
    vars.map(v => v.toString()).sort().join(", ")
    .should.eq("C, F? A, F? B")
  });


  it("should rename all free variables to unique ones", function () {
    let f1 = "?X, ?Y, -- : F?A, -- : X, -- : F?A -o F?B |- -- : bla( T? C )";
    let n1 = parser.parse(f1)
    let s1 = Sequent.fromTree(n1);
    let seq = Sequent.renameUnique(s1);
    seq.seq.toString()
    .should.eq(" ? X, ? Y, F? V_2, X, F? V_2 -o F? V_1 |- bla ( V_0 )")
    Sequent.varIndex.should.eq(3)
  });

  it.only("should compute the correct mgu", function () {
    let f1 = "I |- -- : plus(TT? z, TT? s. TT? z, T? X)";
    let f2 = "I |- -- : plus(TT? z, T? N, T? N)";
    let n1 = parser.parse(f1)
    let n2 = parser.parse(f2)
    let theta = mgu([[n1, n2]]);
    theta.should.be.ok;
  });


})


