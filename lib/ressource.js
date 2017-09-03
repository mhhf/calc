class Ressource {

}

Ressource.getFreeVariables = function (r) {
  if(r.ruleConstructor === "Formula_Freevar") {
    return [r];
  } else {
    return typeof r !== "string" && r.vals
      .map(Ressource.getFreeVariables)
      .reduceRight((a, r_) => a.concat(r_), [])
    || []
  }
}

module.exports = Ressource;
