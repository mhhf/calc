const PT = require("../v1/pt.js");
const Proofstate = require("../v1/proofstate.js");
const helper = require("../v1/helper.js");
const Sequent = require("../v1/sequent.js");




// TODO - better name
const run_chain = function ({
  seq,
  atoms,
  negative,
  rules,
  bwd,
  getRule,
  calc
}) {
  // console.log(`chain: ${seq}`);
  let pt = new PT({
    conclusion: seq
  })

  let isProovable = Proofstate.auto(pt, {
    positive: atoms,
    negative,
    debug: true,
    // debug_type: "live",
    rules,
    bwd,
    getRule,
    calc
    // , mode: "proof"
  });

  let str = helper.formatCleanTree(isProovable.debug, "technique")
  console.log(`DEBUG:\n${str}`);

  const chain = function (pt) {
    // if the end is reached, maybe i have to check wether focus is blurred, otherwise fail
    if(pt.premisses.length === 0) return pt.conclusion;
    let isReducable = pt.premisses.reduceRight((a,c) => a + (c.proven ? 0 : 1), 0) === 1;
    if(!isReducable) return false;
    return chain(pt.premisses.find(ptp => !ptp.proven));
  }

  return chain(pt);
}


const saturate = function ({seq, atoms, negative, rules, bwd, getRule, calc}) {
  let seq_ = run_chain({seq, atoms, negative, rules, bwd, getRule, calc});

  // let focusingSteps = 0;
  let success = true;
  while(success) {
    success = false;
    // focusingSteps ++;

    for(var i = 0; i < Object.keys(seq_.persistent_ctx).length; i++) {
      let id = Object.keys(seq_.persistent_ctx)[i];
      seq__ = Sequent.copy(seq_);
      seq__.linear_ctx[id] = {val: seq_.persistent_ctx[id], num: 1};
      seq__ = run_chain({seq: seq__, atoms, negative, rules, bwd, getRule, calc})
      if(seq__) {
        // console.log(`res : ${seq__}`);
        seq_ = seq__;
        success = true;
        break;
      }
    }
  }
  return seq_;
}

module.exports = {
  chain: run_chain,
  saturate
}
