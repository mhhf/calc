// TODO - rename to antecedents and succedents
const keccak = require('keccakjs')
const compare = require('./compare.js');
const calc = require('../ll.json');
const substitute = require('./substitute.js');
var clc = require('cli-color');

const sha3 = str => {
  var hash = new keccak("256") // uses 512 bits by default
  hash.update(str)
  return hash.digest('hex') // hex output
}

class Sequent {
  // this.premisses is a multiset ->
  //   object mapping from id's to an object containing
  //      {
  //        num: - number of entities of this type,
  //        val: - the actual "value" - node
  //      }

  constructor(params) {
    this.premisses = params && params.premisses || {};
    this.conclusion = params && params.conclusion || {};
    this.focus = null;
  }

  substitute(theta) {
    let premisses_ = {};
    let conclusion_ = this.conclusion;
    theta.forEach(([k, v]) => {
      conclusion_ = substitute(conclusion_, k, v)
    })
    Object.keys(this.premisses)
    .forEach(id => {
      let val = this.premisses[id].val;
      let num = this.premisses[id].num;
      theta.forEach(([k, v]) => {
        val = substitute(val, k, v);
      })
      premisses_[id] = {
        val,
        num
      }
    });
    return new Sequent({
      premisses: premisses_,
      conclusion: conclusion_,
      focus: this.focus
    })
  }

  toString(o) {
    let prStr = Object
    .keys(this.premisses)
    .map(id => this.premisses[id])
    .map(n => {
      let ret = n.val.toString(o);
      if(n == this.focus) {
        switch(o.style) {
          default:
          ret = `[${ret}]`;
        }
      }
      if(n.num > 1) {
        ret = `(${ret})* ${n.num}`
      }
      if("highlight" in o && o.highlight.indexOf(n.val) > -1) {
        ret = clc.bold(ret);
      }
      return ret;
    })
    .join(", ")
    return `${prStr} |- ${this.conclusion.toString(o)}`
  }

  ffocus(id) {
    this.focus = this.premisses[id];
  }

  getFocusingCandidates() {
    let candidates = Object.keys(this.premisses)
    .map(id => {
      let p = this.premisses[id].val;
      let pol = calc.calc_structure_rules_meta.polarity;
      let type = p.vals[1].ruleConstructor;
      return (type in pol && pol[type] === "negative" && id)
    })
    .filter(c => !!c)
    return candidates;
  }
}


// EL LIST x EL LIST => (EL x EL) LIST LIST
// TODO - better naming
Sequent.constructCompareOptions = function (r1, r2) {
  if(r1.length === 0 || r2.length === 0) return [];
  let a = r1[0];
  return r2.map((b, j) => {
    let r1_ = r1.slice(1)
    let r2_ = r2.slice(0,j).concat(r2.slice(j+1));
    let ret = Sequent.constructCompareOptions(r1_, r2_)
    let ret_;
    if(ret.length > 0) {
      ret_ = ret.map(r => r.concat([[a, b]]));
    } else {
      ret_ = ret.concat([[[a, b]]]);
    }
    return ret_;
  })
  .reduceRight((a,r) => a.concat(r), [])
}


// TODO - clean up this mess
// TODO - multiset bullshit
Sequent.compare = function (s1, s2, o = {}) {

  if(o.debug) {
    console.log(`comparing:\n  ${s1.toString()}\n  ${s2.toString()}\n`);
  }

  let c1 = s1.conclusion;
  let c2 = s2.conclusion;
  let conclusion_comparesion = compare(c1,c2);
  if(!conclusion_comparesion) return false;


  // TODO - optimize this hard!
  // 1. match premisses
  // 1.1 remove structure variables from premisses, since there are subject to ressource management
  // 2. match conclusion
  let p1 = Object.keys(s1.premisses).map(k => s1.premisses[k]);
  let p2 = Object.keys(s2.premisses).map(k => s2.premisses[k]);
  // p1.forEach(resource => {
  //   console.log(resource.val);
  // })
  p1 = p1.filter(ressource => ressource.val.ruleConstructor !== "Structure_Freevar")
  p2 = p2.filter(ressource => ressource.val.ruleConstructor !== "Structure_Freevar")
  if(o.debug) {
    let p = p1.map(p => p.val.toString()).join("\n  ");
    console.log(`premisses: \n  ${p}\n`);
  }

  // TODO - maybe speed those things up with an prefix trie implementation of a multiset

  let options = Sequent.constructCompareOptions(p1, p2);
  if(o.debug) {
    options.forEach((option, i) => {
      let c = option.map(([x, y]) => `${x.val.toString()}  <> ${y.val.toString()}\n    ${compare(x.val, y.val)}`);
      console.log(`option ${i}:\n${c.join("\n")}`);
    })
  }

  let comparesons = options.map((option, i) => {
    return option
    .map(([x, y]) => compare(x.val, y.val))
    .reduceRight((a, c) => {
      if(a && c) {
        if(c.length == 0) { // no change in substitution
          return a;
        } else {
          // TODO - test  this
          let isConflict = c.reduceRight( (ac, [k, v]) => {
            // let k_in_a = a.reduceRight((pos, cc) => pos || cc[0].toString() == k.toString(), false)
            let a_k = a.find(cc => cc[0].toString() == k.toString())
              return ac && (a_k) && (a_k[1].toString() == v.toString())
            }, true)
          if(isConflict) {
            return false;
          } else {
            c.forEach(([k, v]) => {a = a.concat([[k, v]])})
            return a;
          }
        }
      } else { // fail to unify this option
        return false;
      }
    }, conclusion_comparesion)
  })

  let simpleRenaming = comparesons
  .find(obj => Object.keys(obj)
    .map(key => obj[key].ruleConstructor == "Formula_Freevar")
    .reduceRight((a, c) => a && c, true))

  if(o.debug) {
    console.log("\n"+comparesons.map((o, i) => `option ${i}:${o == simpleRenaming ? clc.green(" simple") : ""}\n${
      Object.keys(o).map(k => `${k}  ->  ${o[k].toString()}`).join("\n")
    }`).join("\n\n"));
  }

  return simpleRenaming || (0 in comparesons && comparesons[0]);
}

Sequent.fromTree = function (seq) {
  var premisses = {};

  const tree2multiset = (struct) => {
    if(struct.ruleConstructor === "Structure_Comma") {
      tree2multiset(struct.vals[0]);
      tree2multiset(struct.vals[1]);
    } else {
      let id = sha3(struct.toString())
      if(id in premisses) {
        premisses[id].num ++;
      } else {
        premisses[id] = {
          val: struct,
          num: 1
        }
      }
    }
  }

  tree2multiset(seq.vals[0]);
  var conclusion = seq.vals[1];

  return new Sequent({
    premisses,
    conclusion
  });
}

module.exports = Sequent;
