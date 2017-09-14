const Calc = require("./calc.js");

const sub = function (node, key, val) {

  if(typeof node === "string") return node;
  let type = Calc.db.rules[node.id];

  // ignore bounded variables
  if (
    type.ruleName === "Formula_Forall"
    && node.vals[0].vals[0] == key.vals[0]
  ) {
    return node;
  }

  let isSameConstructor = node.id === key.id;
  if(isSameConstructor && node.vals[0] === key.vals[0]) {
    return val.copy();
  } else {
    node.vals = node.vals
    .map(v => {
      if(typeof v !== "object") return v;
      return sub(v, key, val);
    })
    return node;
  }

}


module.exports = sub;
