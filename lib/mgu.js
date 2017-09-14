// TODO - ocurrence check
const isFreevar = str => /\_Freevar$/.test(str)
const subs = require("./substitute.js");
const Calc = require("./calc.js");

const propagate = function (theta, new_theta) {
  new_theta.forEach(([k, v]) => {
    theta = theta.map(([k_, v_]) => [k_, subs(v_.copy(), k, v)])
  })
  return theta.concat(new_theta);
}

const mgu = function (G) {
  let rules = Calc.db.rules;
  var theta = [];
  while (G.length > 0) {
    let job = G.pop();
    let t0 = job[0];
    let t1 = job[1];
    let isEqType = t0.id == t1.id;
    let isVarL = typeof t0 !== "string" && isFreevar(rules[t0.id].ruleName)
    let isVarR = typeof t1 !== "string" && isFreevar(rules[t1.id].ruleName)
    let isEq = t0.toString() === t1.toString();
    let isString = typeof t0 === "string" || typeof t1 === "string"

    // console.log(`unifying ${t0} =?= ${t1}`);
    // console.log(`isEqType: ${isEqType} -- ${t0.id} ${t1.id}`);
    if(isEq) {
      // do notighg
    } else if(isVarL && isVarR) {
      // console.log(`  ?? doublevar`);
      G = [[t0, t1]].concat(G);
    } else if(isVarL) {
      // console.log(`  eleminate`);
      theta = propagate(theta, [[t0, t1]])
      G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))
    } else if(isVarR) {
      // console.log(`  swap`);
      G.push([t1, t0]);
    } else if(isEqType && !isString) {
      // console.log(`  decompose`);
      t0.vals
      .forEach((v, i) => {
        G.push([v, t1.vals[i]]);
      })
    } else {
      // console.log(`  fail`);
      return false;
    }
    // console.log(`  G: \n${G.map(task => `    ${task}`).join("\n")}`);
  }
  return theta;
}

module.exports = mgu;
