// CALC abstraction
//
// const calc = require("../ll.json");
class Calc {}

const FORMAT_PORPS = [
  "isabelle",
  "isabelle_se",
  "ascii",
  "latex",
  "latex_se"
];


function constructDepOrder(calc) {
  let depGraph = {};
  let keys = Object.keys(calc)
    .forEach(ctxName => {
    let ctx = calc[ctxName];
    let deps = {};
      Object.keys(ctx)
      .forEach(ruleName => {
      let rule = ctx[ruleName];
      if("type" in rule) (Array.isArray(rule.type) ? rule.type : [])
          .forEach(t => deps[t] = true)
    })
    depGraph[ctxName] = Object.keys(deps);
  });
  let depGraphStr = JSON.stringify(depGraph, false, 2);
  let depOrder = [];
  let got = true;
  let rmKey = key => Object.keys(depGraph)
    .forEach(k => {
      let i = depGraph[k].indexOf(key);
      if(i > -1) {
        depGraph[k].splice(i, 1);
      }
    })
  // rm mutual
  Object.keys(depGraph)
  .forEach(key => {
    let i = depGraph[key].indexOf(key);
    if(i > -1) {
      depGraph[key].splice(i, 1)
    }
  })
  rmKey("string");
  while (got) {
    got = false;
    let rmEl = Object.keys(depGraph)
    .find(e => depGraph[e].length == 0)
    if(rmEl) {
      got = true;
      depOrder.push(rmEl);
      delete depGraph[rmEl];
      rmKey(rmEl);
    }
  }
  return depOrder;
}

const simplifyCalc = function (calc) {

  var calc_ = {};

  let calc_structure = constructDepOrder(calc.calc_structure);

  // TODO - assumption: one rule can only have ONE reducable context
  // 1.
  let reducable_ctxs = [];
  calc_structure
  .forEach(ctxName => {
    let ctx = calc.calc_structure[ctxName];
    let has_only_reducable_rules = Object.keys(ctx)
    .map(ruleName => (ctx[ruleName].type || []).length === 0)
    .reduceRight((a, t) => a && t, true);
    if(has_only_reducable_rules) {
      // if(DEBUG) console.log(clc.green(`CONTEXT ${ctxName} IS REDUCABLE`));
      reducable_ctxs.push(ctxName);
    }
  })
  // 2.
  calc_structure
  .forEach(ctxName => {
    if(reducable_ctxs.indexOf(ctxName) > -1) return null;
    let ctx = calc.calc_structure[ctxName];
    let ctx_ = {};
    Object.keys(ctx).forEach(ruleName => {
      let rule = ctx[ruleName];
      let types = Array.isArray(rule.type)
        ? rule.type
        : (rule.type
          ? [rule.type]
          : [])
      let reducable_ctx = reducable_ctxs
        .map(reducable_ctx_name => types.indexOf(reducable_ctx_name) > -1 ? reducable_ctx_name : false)
        .reduceRight((a, t) => a || t, false);

      // 2.1
      if(reducable_ctx) {
        // if(DEBUG)
        //   console.log(`RULE ${ctxName}.${ruleName} has reducable ctx "${reducable_ctx}"`);
        // 2.1.1    remove (NR) from (NC)
        let position = types.indexOf(reducable_ctx);
        let types_ = types.slice(0, position).concat(types.slice(position + 1))
        var precedence_;
        if("precedence" in rule) {
          precedence_ = rule.precedence.slice(0, position).concat(rule.precedence.slice(position + 1))
        }
        // 2.1.2    for each constructor (RR) in (CC)
        Object.keys(calc.calc_structure[reducable_ctx])
        .forEach(tmpRuleName => {
          let rule_ = {};
          let tmpRule = calc.calc_structure[reducable_ctx][tmpRuleName];
          const genSyntax = function (key) {
            return (types.map(
              t => (reducable_ctxs.indexOf(t) > -1)
                ? ` ${tmpRule[key] || ""} `
                : " _ ").join(""))
                .replace(/\s+/g, " ").trim()
          }
          FORMAT_PORPS
            .filter(type => rule[type] || tmpRule[type])
            .forEach(type => rule_[type] = genSyntax(type));
          rule_.type = types_;
          if("precedence" in rule) {
            rule_.precedence = precedence_;
          }

          rule_ = Object.assign({}, rule, rule_);

          // if parent rule should be ignored in shallow embedding
          // and child rule not
          // new rule should be NOT shallow
          if(
            "shallow" in rule
            && !rule.shallow
            && (!("shallow" in tmpRule)
              || tmpRule.shallow)
          ) {
            delete rule_.shallow;
          }

          // if(DEBUG) {
          //   console.log(clc.green(`\n\nHERE I SHOULD DO SOMETHING`));
          //   console.log(clc.red(position));
          //   console.log(JSON.stringify(rule,false,2));
          //   console.log(JSON.stringify(tmpRule, false, 2));
          //   console.log("---");
          //   console.log(`Rule_: ${JSON.stringify(rule_, false, 2)}`);
          //   console.log("\n");
          // }
          // TODO - update precedence
          // TODO - what if i want to specify mixfix notation?
          ctx_[tmpRuleName] = rule_;
        })
      } else {
        ctx_[ruleName] = rule;
      }

    })
    calc_[ctxName] = ctx_;
  })

  Object.assign(calc, {"calc_structure": calc_});

  return calc;
}

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

const analyzeProperties = function (calc, ctxName, ruleName, o) {
  let polMap = calc.calc_structure_rules_meta.polarity;

  if(ctxName === "Formula" && typeof polMap[ruleName] === "string") {
    o.polarity = polMap[ruleName];
  }
  if(ruleName === "Structure_Term_Formula"
    || ruleName === "Structure_Focused_Term_Formula") {
    o.isTermType = true;
  }
}

Calc.init = function (calc) {
  console.log("THIS SHOULD BE CALLED JUST ONE TIME");

  if(Calc.initialized) return false;
  Calc.initialized = true;
  calc = simplifyCalc(calc);
  Calc.calc = calc;
  let num_ctxs = Object.keys(calc.calc_structure).length;
  Object.keys(calc.calc_structure)
  .forEach((ctxName, ctx_id) => {
    let ctx = calc.calc_structure[ctxName];
    Object.keys(ctx)
    .forEach(ruleName => {
      let o = {
        ctxName,
        ruleName
      };
      let rule = ctx[ruleName];
      let id = Calc.rule_index ++;
      analyzeProperties(calc, ctxName, ruleName, o);
      if(!(ctxName in Calc.db.toIds)) Calc.db.toIds[ctxName] = {}
      Calc.db.toIds[ctxName][ruleName] = id;
      Calc.db.rules[id] = Object.assign({}, rule, o);
    })
  })
}

module.exports = Calc;
