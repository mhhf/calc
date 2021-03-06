// TODO - rename to antecedents and succedents
// TODO - optimize rename unique - get the lowest var index and go from here, no need to touch the local index
const keccak = require('keccakjs')
const compare = require('./compare.js');
const mgu = require('./mgu.js');
const calc = require('../ll.json');
const substitute = require('./substitute.js');
const Calc = require('./calc.js');
var clc = require('cli-color');
const Res = require('./ressource.js');

const sha3 = str => {
  var hash = new keccak("256") // uses 512 bits by default
  hash.update(str)
  return hash.digest('hex') // hex output
}

class Sequent {
  // this.linear_ctx is a multiset ->
  //   object mapping from id's to an object containing
  //      {
  //        num: - number of entities of this type,
  //        val: - the actual "value" - node
  //      }
  // this.persistent_ctx is a set ->
  //   object mapping from id's to the ressource values

  constructor(params) {
    this.persistent_ctx = params && params.persistent_ctx || {};
    this.linear_ctx = params && params.linear_ctx || {};
    this.succedent  = params && params.succedent || {};
    this.ffocus();
    // this.potentialRessources = params && params.potentialRessources || {};
    // this.focus = null; // node
    // this.focusPosition = null; // "R" | "L";
  }

  substitute(theta) {
    let linear_ctx_ = {};
    let persistent_ctx_ = {};
    let succedent_ = this.succedent;
    theta.forEach(([k, v]) => {
      succedent_ = substitute(succedent_, k, v)
    })

    Object.keys(this.linear_ctx)
    .forEach(id => {
      let val = this.linear_ctx[id].val;
      let num = this.linear_ctx[id].num;
      theta.forEach(([k, v]) => {
        val = substitute(val, k, v);
      })
      linear_ctx_[id] = {
        val,
        num
      }
    });

    Object.keys(this.persistent_ctx)
    .forEach(id => {
      let val = this.persistent_ctx[id];
      theta.forEach(([k, v]) => {
        val = substitute(val, k, v);
      })
      persistent_ctx_[id] = val;
    });

    return new Sequent({
      persistent_ctx: persistent_ctx_,
      linear_ctx: linear_ctx_,
      succedent: succedent_,
      focus: this.focus
    })
  }

  toString(o = {}) {
    let extensive = false;
    if(o.style === "ascii_extensive") {
      extensive = true;
      o.style = "ascii";
    }
    let prStr = Object
    .keys(this.linear_ctx)
    .map(id => this.linear_ctx[id])
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
      if("highlight" in o && (o.highlight || []).indexOf(n.val) > -1) {
        ret = clc.bold(ret);
      }
      return ret;
    })
    .join(extensive ? "\n" : ", ")

    let gammaStr = Object.keys(this.persistent_ctx)
    .map(id => this.persistent_ctx[id])
    .map(n => {
      return n.toString();
    })
    .join(extensive ? "\n - " : ", ")

    let vdash = "|-";
    if(o.style === "latex") vdash = "\\vdash";
    if(extensive) {
      return `Rules:\n - ${gammaStr}\n\nContext:\n ${prStr}`
    } else {
      return `${gammaStr? gammaStr + ";" : ""}${prStr === "" ? "I" : prStr} ${vdash} ${this.succedent.toString(o)}`
    }
  }

  // todo - refactor everything to focusID
  // TODO - rename it to updateFocus()
  ffocus() {
    // this.focus = this.linear_ctx[id];
    let focusId = Object.keys(this.linear_ctx)
    .find(id => {
      return this.linear_ctx[id].val.isFocus()
    });

    let focus = Object.keys(this.linear_ctx)
    .map(id => this.linear_ctx[id].val)
    .find(r => r.isFocus());
    if(focus) this.focusPosition = "L";

    if(!focus && this.succedent.isFocus()) {
      focus = this.succedent;
      this.focusPosition = "R";
    }
    this.focus = focus;
    this.focusId = focusId;
  }

}

Sequent.varIndex = 0;

Sequent.renameUniqueArray = function (seqs) {
  let vars = seqs
    .map(seq => Sequent.getFreeVariables(seq))
    .reduceRight((a, r) => a.concat(r), [])
    .reduceRight((a, v) => {
      let varNames = a.map(v => v.toString())
      if( varNames.indexOf(v.toString()) > -1 ) {
        return a;
      } else {
        return a.concat([v]);
      }
    }, [])

  let theta = vars
  .map(v => {
    let to = v.copy();
    to.vals[0] = `V_${Sequent.varIndex++}`
    return [v, to]
  })

  let seqs_ = seqs
    .map(seq => Sequent.copy(seq))
    .map(seq => {seq.substitute(theta); return seq;})

  return {
    seqs: seqs_,
    theta
  };

}

Sequent.renameUnique = function (seq) {
  let vars = Sequent.getFreeVariables(seq);

  let theta = vars
  .map(v => {
    let to = v.copy();
    to.vals[0] = `V_${Sequent.varIndex++}`
    return [v, to]
  })

  let seq_ = Sequent.copy(seq);

  seq_.substitute(theta);

  return {
    seq: seq_,
    theta
  };
}

// TODO - make the result unique
Sequent.getFreeVariables = function (seq) {

  let linear_vars = Object.keys(seq.linear_ctx)
  .map(id => {
    let r = seq.linear_ctx[id].val;
    return Res.getFreeVariables(r);
  })
  .reduceRight((a, r) => a.concat(r), []);
  let persistent_vars = Object.keys(seq.persistent_ctx)
  .map(id => {
    let r = seq.persistent_ctx[id];
    return Res.getFreeVariables(r);
  })
  .reduceRight((a, r) => a.concat(r), []);
  let succedent_vars = Res.getFreeVariables(seq.succedent);

  // Reduce to one array and unique after variable names
  let vars = linear_vars
  .concat(persistent_vars)
  .concat(succedent_vars)
  .reduceRight((a, r) => {
    let varNames = a.map(v => v.toString())
    if( varNames.indexOf(r.toString()) > -1 ) {
      return a;
    } else {
      return a.concat([r]);
    }
  }, [])

  return vars;
}

Sequent.copy = function (seq) {
  // copy linear_ctx
  let linear_ctx = {};
  Object.keys(seq.linear_ctx)
  .forEach(id => {
    let r = seq.linear_ctx[id];
    linear_ctx[id] = {num: r.num, val: r.val.copy()};
  });
  let persistent_ctx = {};
  Object.keys(seq.persistent_ctx)
  .forEach(id => {
    persistent_ctx[id] = seq.persistent_ctx[id].copy()
  });
  // copy succedent
  let succedent = seq.succedent.copy();
  return new Sequent({
    persistent_ctx,
    linear_ctx,
    succedent
  });
}

Sequent.remove_structural_variables = function (seq) {
  let linear_ctx_ = {}
  Object.keys(seq.linear_ctx)
  .forEach(id => {
    let r = seq.linear_ctx[id];
    let type = Calc.db.rules[r.val.id];
    if(type.ruleName !== "Structure_Freevar"
    && type.ruleName !== "Structure_Neutral"
    ) {
      linear_ctx_[id] = r;
    }
  })
  seq.linear_ctx = linear_ctx_;
}

Sequent.isStable = function (seq, o) {
  Object.keys(seq.linear_ctx)
  .forEach(id => {
    let r = seq.linear_ctx[id];

  })
}

Sequent.add_to_linear_ctx = function (seq, ast, num = 1) {
  let id = sha3(ast.toString())
  if(id in seq.linear_ctx) {
    seq.linear_ctx[id].num += num;
  } else {
    seq.linear_ctx[id] = {num: num, val: ast}
  }
}

Sequent.add_to_antecedent_bulk = function (seq, delta) {
  Object.keys(delta)
  .forEach(id => {
    let r = delta[id]
    Sequent.add_to_linear_ctx(seq, r.val, r.num);
  })
}

Sequent.remove_from_antecedent = function (seq, delta) {
  let linear_ctx_ = {};
  Object.keys(seq.linear_ctx)
  .forEach(id => {
    let r1 = seq.linear_ctx[id];
    let r2 = delta[id];
    if(r2 && r1.num < r2.num) {
      linear_ctx_ = false;
    } else if(linear_ctx_ && r2 && r1.num > r2.num) {
      linear_ctx_[id] = {num: r1.num - r2.num, val: r1.val}
    } else if(linear_ctx_ && !r2) {
      linear_ctx_[id] = r1;
    }
  })
  if(linear_ctx_) {
    seq.linear_ctx = linear_ctx_;
  }
  return linear_ctx_;
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

// TODO - remove id from antecedent if available
// put new unfocused thing under new id
Sequent.blur = function (seq) {
  if(seq.focusPosition === "R") {
    seq.focus.doUnfocus();
  } else if(seq.focusPosition === "L") {
    seq.focus.doUnfocus();
  }
}


Sequent.fromTree = function (seq) {
  var linear_ctx = {};

  const tree2multiset = (struct) => {
    let type = Calc.db.rules[struct.id];
    if(type.ruleName === "Structure_Comma") {
      tree2multiset(struct.vals[0]);
      tree2multiset(struct.vals[1]);
    } else {
      if(type.ruleName === "Structure_Neutral")
        return null;
      let id = sha3(struct.toString())
      if(id in linear_ctx) {
        linear_ctx[id].num ++;
      } else {
        linear_ctx[id] = {
          val: struct,
          num: 1
        }
      }
    }
  }

  tree2multiset(seq.vals[0]);
  var succedent = seq.vals[1];

  return new Sequent({
    linear_ctx,
    succedent
  });
}

// TODO - ugly - refactor
Sequent.getAtoms = function (seq, o) {

  const atomic = ["Formula_Freevar", "Formula_Atprop"]

  const getAtoms = function (n) {
    if(typeof n === "string") return [[n]];
    let type = o.rules[n.id];

    // TODO - export this to node.isAtomic()
    if((type.ctxName === "Formula")
      && atomic.indexOf(type.ruleName) > -1
    ) {
      if(n.ruleName === "Formula_Freevar") {
        return [[n.toString(), n]];
      } else {
        return [[n.vals[0].vals[0], n]];
      }
    } else if(n.ruleName === "Formula_Forall") {
      return getAtoms(n.vals[2]);
      // .map(getAtoms)
      // .reduceRight((a,e) => a.concat(e), []);
    } else {
      return n.vals
        .map(getAtoms)
        .reduceRight((a,e) => a.concat(e), []);
    }
  }

  let atoms = Object.keys(seq.linear_ctx)
    .map(id => seq.linear_ctx[id].val)
    .map(getAtoms)
    .reduceRight((a, e) => a.concat(e), []);

  atoms = atoms.concat(getAtoms(seq.succedent))

  // unique
  let aa = {};
  atoms.forEach(a => aa[a[0]] = true)

  return Object.keys(aa);
}


module.exports = Sequent;
