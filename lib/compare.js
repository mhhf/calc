// TODO - this may be hacky implemented
//        unification and substitution
//        currently only the substitution is returned
//        but maybe at some point unification is necessery
var clc = require('cli-color');
const substitute = require("./substitute.js");

const propagate = function (theta, new_theta) {
  new_theta.forEach(([k, v]) => {
    theta = theta.map(([k_, v_]) => [k_, substitute(v_.copy(), k, v)])
  })
  return theta.concat(new_theta);
}

const isFreevar = str => /\_Freevar$/.test(str)

const compare = function(n1, n2, o = {}) {
  let result = false;

  // 1.      constructs are equal
  // 1.1     compare children
  if(n1.ruleConstructor == n2.ruleConstructor
    // (n1.ruleConstructor === "Structure_Term_Formula"
    // && n2.ruleConstructor === "Structure_Focused_Term_Formula")
    // ||
    // (n2.ruleConstructor === "Structure_Term_Formula"
    // && n1.ruleConstructor === "Structure_Focused_Term_Formula")
  ) {
    if(o.debug) console.log(`${clc.green("matching ")}\n  ${n1.toString()}\n  ${n2.toString()}`);

    if(isFreevar(n1.ruleConstructor)) {
      if( n1.vals[0] === n2.vals[0] ) {
        // TODO - this should not occur, since mgu is only used for fresh rules with disjunct variables
        throw new Error(`this should not occur, since mgu is only used for fresh rules with disjunct variables`);
        return [];
      } else {
        return [[n1, n2]]
      }
    } else {
      result = n1.vals
      .map((v1, i) => {
        let v2 = n2.vals[i];
        if(typeof v1 === "string") {
          // throw new Error("shouldn't be here");
          return v1 === v2 ? [] : false
        } else {
          return compare(v1, v2, o);
        }
      })
      .reduceRight((a, r) =>
        a
        && Array.isArray(a)
        && Array.isArray(r)
        // TODO - propagate
        && propagate(a, r)         , [])
    }


  } else {
    let isSameType = n1.ruleName === n2.ruleName;
    let isFreevar = node => node.ruleConstructor.match(/\_Freevar$/)
    if(isSameType && isFreevar(n1)) {
      if(o.debug) console.log(clc.yellow("substitution found: ") + n1.toString()+ " -> " +n2.toString());
      result = [[n1, n2]];
    } else if(isSameType && isFreevar(n2)) {
      if(o.debug) console.log(clc.yellow("substitution found: ") + n2.toString()+ " -> " +n1.toString());
      result = [[n2, n1]];
    }
  }

  return result;

}

module.exports = compare;
