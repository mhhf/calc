// CALC abstraction
//
class Calc {}

Calc.rule_index = 0;
Calc.db = {
  rules: {},
  toIds: {}
};
Calc.initialized = false;
Calc.eachStructureRule = function (calc, f) {
  Object.keys(calc.calc_structure)
  .forEach(ctxName => {
    let ctx = calc.calc_structure[ctxName];
    Object.keys(ctx)
    .forEach(ruleName => {
      let rule = ctx[ruleName];
      f({
        ctxName,
        ctx,
        ruleName,
        rule
      })
    })
  })
}

Calc.init = function (calc) {
  if(Calc.initialized) return false;
  Calc.initialized = true;
  let num_ctxs = Object.keys(calc.calc_structure).length;
  Object.keys(calc.calc_structure)
  .forEach((ctxName, ctx_id) => {
    let ctx = calc.calc_structure[ctxName];
    Object.keys(ctx)
    .forEach(ruleName => {
      let rule = ctx[ruleName];
      let id = Calc.rule_index ++;
      if(!(ctxName in Calc.db.toIds)) Calc.db.toIds[ctxName] = {}
      Calc.db.toIds[ctxName][ruleName] = id;
      Calc.db.rules[id] = Object.assign({}, rule, {
        ctxName,
        ruleName
      });
    })
  })
}

module.exports = Calc;
