// TODO - ocurrence check
const isFreevar = str => /\_Freevar$/.test(str)
const subs = require("./substitute.js");

const mgu = function (G) {
  const theta = [];
  while (G.length > 0) {
    let job = G.pop();
    let t0 = job[0];
    let t1 = job[1];
    let isEqType = t0.ruleConstructor == t1.ruleConstructor;
    let isVarL = isFreevar(t0.ruleConstructor)
    let isVarR = isFreevar(t1.ruleConstructor)
    let isEq = t0.toString() === t1.toString();

    // console.log(`unifying ${t0} =?= ${t1}`);
    if(isEq) {
      // do notighg
    } else if(isVarL && isVarR) {
      // console.log(`  ?? doublevar`);
      G = [[t0, t1]].concat(G);
    } else if(isVarL) {
      // console.log(`  eleminate`);
      theta.push([t0, t1])
      G = G.map(([l, r]) => ([subs(l, t0, t1), subs(r, t0, t1)]))
    } else if(isVarR) {
      // console.log(`  swap`);
      G.push([t1, t0]);
    } else if(isEqType) {
      // console.log(`  decompose`);
      t0.vals.forEach((v, i) => {
        G.push([v, t1.vals[i]]);
      })
    } else {
      // console.log(`  fail`);
      // console.log(t0, t1);
      return false;
    }
    // console.log(`  G: \n${G.map(task => `    ${task}`).join("\n")}`);
  }
  return theta;
}

module.exports = mgu;
