const Calc = require("./calc.js");
const isFreevar = str => /\_Freevar$/.test(str)

class Ressource {

}

Ressource.getFreeVariables = function (r) {
  let type = Calc.db.rules[r.id];
  if(isFreevar(type.ruleName) && type.ruleName !== "Structure_Freevar") {
    return [r];
  } else {
    return r.vals
      .filter(v => typeof v !== "string")
      .map(Ressource.getFreeVariables)
      .reduceRight((a, r_) => a.concat(r_), [])
    || []
  }
}

module.exports = Ressource;
