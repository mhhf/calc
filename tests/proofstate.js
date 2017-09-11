const should = require('chai').should()
const calc = require('../ll.json');
const calcParser = require("../lib/parser.js");
const Sequent = require("../lib/sequent.js");
const Proofstate = require("../lib/proofstate.js");
const PT = require("../lib/pt.js");
const parser = calcParser(calc).parser;

const toPT = function (str) {
  let ast = parser.parse(str)
  let seq = Sequent.fromTree(ast);
  let pt = new PT({conclusion: seq});
  return pt;
}

describe("Proofstate", function () {

  it("should blurR", function () {
    let pt = toPT("F? P |- * : [ F?Q ]");
    Proofstate.blurR(pt);
    Object.keys(pt.delta_in).length.should.eq(1);
    pt.premisses.length.should.eq(1);
    Object.keys(pt.premisses[0].conclusion.linear_ctx).length.should.eq(0)
  });

})
