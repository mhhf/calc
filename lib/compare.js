// TODO - this may be hacky implemented
//        unification and substitution
//        currently only the substitution is returned
//        but maybe at some point unification is necessery
var clc = require('cli-color');

const compare = function(n1, n2) {
  let result = false;

  // 1.      constructs are equal
  // 1.1     compare children

  if(n1.ruleConstructor == n2.ruleConstructor) {
    // console.log(clc.green("matching ") + n1.ruleConstructor);

    result = n1.vals
      .filter(v => typeof v === "object")
      .map((v1, i) => {
      let v2 = n2.vals[i];
      return compare(v1, v2);
    })
    .reduceRight((a, r) => a && Array.isArray(a) && Array.isArray(r) && a.concat(r), [])

  } else {
    // console.log(clc.yellow("not matching: ") + n1.ruleConstructor + " " +n2.ruleConstructor);
    let isSameType = n1.ruleName === n2.ruleName;
    let isFreevar = node => node.ruleConstructor.match(/\_Freevar$/)
    if(isSameType && isFreevar(n1)) {
      // console.log(clc.yellow("n1"));
      result = [[n1, n2]];
    } else if(isSameType && isFreevar(n2)) {
      // console.log(clc.yellow("n2"));
      result = [[n2, n1]];
    }
  }

  return result;

}

module.exports = compare;
