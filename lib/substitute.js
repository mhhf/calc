const sub = function (node, key, val) {

  // ignore bounded variables
  if (
    node.ruleConstructor === "Formula_Forall"
    && node.vals[0].vals[0] == key.vals[0]
  ) {
    return node;
  }

  let isSameConstructor = node.ruleConstructor === key.ruleConstructor;
  if(isSameConstructor && node.vals[0] === key.vals[0]) {
    return val;
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
