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
  // this.antecedent is a multiset ->
  //   object mapping from id's to an object containing
  //      {
  //        num: - number of entities of this type,
  //        val: - the actual "value" - node
  //      }

  constructor(params) {
    this.antecedent = params && params.antecedent || {};
    this.succedent  = params && params.succedent || {};
    this.ffocus();
    this.potentialRessources = params && params.potentialRessources || {};
    // this.focus = null; // node
    // this.focusPosition = null; // "R" | "L";
  }

  substitute(theta) {
    let antecedent_ = {};
    let succedent_ = this.succedent;
    theta.forEach(([k, v]) => {
      succedent_ = substitute(succedent_, k, v)
    })
    Object.keys(this.antecedent)
    .forEach(id => {
      let val = this.antecedent[id].val;
      let num = this.antecedent[id].num;
      theta.forEach(([k, v]) => {
        val = substitute(val, k, v);
      })
      antecedent_[id] = {
        val,
        num
      }
    });
    return new Sequent({
      antecedent: antecedent_,
      succedent: succedent_,
      focus: this.focus
    })
  }

  toString(o = {}) {
    let prStr = Object
    .keys(this.antecedent)
    .map(id => this.antecedent[id])
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
    return `${prStr} |- ${this.succedent.toString(o)}`
  }

  ffocus() {
    // this.focus = this.antecedent[id];
    let focus = Object.keys(this.antecedent)
    .map(id => this.antecedent[id].val)
    .find(r => {
      return r.ruleConstructor === "Structure_Focused_Term_Formula"
    });
    if(focus) this.focusPosition = "L";

    if(!focus && this.succedent.ruleConstructor === "Structure_Focused_Term_Formula") {
      focus = this.succedent;
      this.focusPosition = "R";
    }
    this.focus = focus;
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

  let c1 = s1.succedent;
  let c2 = s2.succedent;
  let succedent_comparesion = compare(c1,c2);
  if(!succedent_comparesion) return false;


  // TODO - optimize this hard!
  // 1. match antecedent
  // 1.1 remove structure variables from antecedent, since there are subject to ressource management
  // 2. match succedent
  let p1 = Object.keys(s1.antecedent).map(k => s1.antecedent[k]);
  let p2 = Object.keys(s2.antecedent).map(k => s2.antecedent[k]);
  // p1.forEach(resource => {
  //   console.log(resource.val);
  // })
  p1 = p1.filter(ressource => ressource.val.ruleConstructor !== "Structure_Freevar")
  p2 = p2.filter(ressource => ressource.val.ruleConstructor !== "Structure_Freevar")
  if(o.debug) {
    let p = p1.map(p => p.val.toString()).join("\n  ");
    console.log(`antecedent: \n  ${p}\n`);
  }

  // TODO - maybe speed those things up with an prefix trie implementation of a multiset

  let options = Sequent.constructCompareOptions(p1, p2);
  if(o.debug) {
    options.forEach((option, i) => {
      let c = option.map(([x, y]) => `${x.val.toString()}  <> ${y.val.toString()}\n    ${compare(x.val, y.val)}`);
      console.log(`option ${i}:\n${c.join("\n")}`);
    })
  }
  if(options.length == 0) options = [[]];

  let comparesons = options
    .map((option, i) => {
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
    }, succedent_comparesion)
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
  var antecedent = {};

  const tree2multiset = (struct) => {
    if(struct.ruleConstructor === "Structure_Comma") {
      tree2multiset(struct.vals[0]);
      tree2multiset(struct.vals[1]);
    } else {
      let id = sha3(struct.toString())
      if(id in antecedent) {
        antecedent[id].num ++;
      } else {
        antecedent[id] = {
          val: struct,
          num: 1
        }
      }
    }
  }

  tree2multiset(seq.vals[0]);
  var succedent = seq.vals[1];

  return new Sequent({
    antecedent,
    succedent
  });
}

module.exports = Sequent;
