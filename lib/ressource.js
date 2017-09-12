const isFreevar = str => /\_Freevar$/.test(str)

class Ressource {

}

Ressource.getFreeVariables = function (r) {
  if(isFreevar(r.ruleConstructor) && r.ruleConstructor !== "Structure_Freevar") {
    return [r];
  } else {
    return typeof r !== "string" && r.vals
      .map(Ressource.getFreeVariables)
      .reduceRight((a, r_) => a.concat(r_), [])
    || []
  }
}

module.exports = Ressource;
