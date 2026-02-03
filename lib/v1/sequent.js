/**
 * Sequent - Multi-context sequent representation
 *
 * Supports both legacy 2-context (linear + persistent) and
 * new multi-context (LNL: cartesian + linear) sequent styles.
 *
 * Context modes:
 *   - linear: No contraction, no weakening (resources used exactly once)
 *   - cartesian: Contraction + weakening (intuitionistic, reusable)
 *
 * Storage format:
 *   contexts = {
 *     linear: { [hash]: { num, val, hash } },
 *     cartesian: { [hash]: { num, val, hash } }
 *   }
 */

const { profiler } = require("./profiler.js");
const { getStore } = require("./store.js");
const { internNode } = require("./intern.js");
const { hashCombine } = require('../hash');

/**
 * Compute content-addressed hash for a node
 */
function computeHash(ast) {
  profiler.count('sequent.hash.content');
  return internNode(ast).hash;
}

const calc = require('../../ll.json');
const substitute = require('./substitute.js');
const Calc = require('./calc.js');
var clc = require('cli-color');
const Res = require('./ressource.js');

/**
 * Context mode definitions
 * Each mode specifies structural rules allowed
 */
const CONTEXT_MODES = {
  linear: {
    contraction: false,
    weakening: false,
    description: 'Linear context - resources used exactly once'
  },
  cartesian: {
    contraction: true,
    weakening: true,
    description: 'Cartesian context - intuitionistic with contraction and weakening'
  },
  // Alias for backwards compat
  persistent: {
    contraction: true,
    weakening: true,
    description: 'Persistent context (alias for cartesian)'
  }
};

class Sequent {
  /**
   * Create a sequent
   *
   * @param {Object} params - Sequent parameters
   * @param {Object} [params.contexts] - New-style: { linear: {...}, cartesian: {...} }
   * @param {Object} [params.linear_ctx] - Legacy: linear context multiset
   * @param {Object} [params.persistent_ctx] - Legacy: persistent context set
   * @param {*} params.succedent - Succedent formula
   */
  constructor(params) {
    // Support both new and legacy APIs
    if (params && params.contexts) {
      // New-style: explicit contexts map
      this.contexts = {};
      for (const [mode, ctx] of Object.entries(params.contexts)) {
        this.contexts[mode] = ctx || {};
      }
    } else {
      // Legacy-style: linear_ctx + persistent_ctx
      this.contexts = {
        linear: params && params.linear_ctx || {},
        cartesian: params && params.persistent_ctx || {}
      };
    }

    this.succedent = params && params.succedent || {};
    this._hash = null; // Cached sequent hash
  }

  /**
   * Get linear context (backwards compat)
   */
  get linear_ctx() {
    return this.contexts.linear || {};
  }

  set linear_ctx(val) {
    this.contexts.linear = val;
    this._hash = null;
  }

  /**
   * Get persistent/cartesian context (backwards compat)
   */
  get persistent_ctx() {
    return this.contexts.cartesian || {};
  }

  set persistent_ctx(val) {
    this.contexts.cartesian = val;
    this._hash = null;
  }

  /**
   * Get content-addressed hash of this sequent
   * Enables O(1) equality
   */
  getHash() {
    if (this._hash !== null) {
      return this._hash;
    }

    profiler.count('sequent.getHash');

    // Collect hashes from all contexts
    const allHashes = [];

    for (const [mode, ctx] of Object.entries(this.contexts)) {
      const modeHashes = Object.values(ctx)
        .map(entry => entry.hash || computeHash(entry.val))
        .sort((a, b) => a < b ? -1 : 1);
      allHashes.push(...modeHashes);
    }

    const succedentHash = computeHash(this.succedent);

    this._hash = hashCombine(...allHashes, succedentHash);

    return this._hash;
  }

  /**
   * O(1) equality check via hash comparison
   */
  equals(other) {
    if (!(other instanceof Sequent)) return false;
    return this.getHash() === other.getHash();
  }

  /**
   * Apply substitution to all formulas
   */
  substitute(theta) {
    profiler.count('sequent.substitute');

    let succedent_ = this.succedent;
    theta.forEach(([k, v]) => {
      succedent_ = substitute(succedent_, k, v);
    });

    const newContexts = {};

    for (const [mode, ctx] of Object.entries(this.contexts)) {
      const newCtx = {};

      Object.keys(ctx).forEach(id => {
        let val = ctx[id].val;
        let num = ctx[id].num;

        theta.forEach(([k, v]) => {
          val = substitute(val, k, v);
        });

        // Recompute hash after substitution
        const hash = computeHash(val);
        const newId = hash.toString();

        // Handle case where substitution might change the key
        if (newId in newCtx) {
          newCtx[newId].num += num;
        } else {
          newCtx[newId] = { val, num, hash };
        }
      });

      newContexts[mode] = newCtx;
    }

    return new Sequent({
      contexts: newContexts,
      succedent: succedent_
    });
  }

  /**
   * Get list of context modes in this sequent
   */
  getContextModes() {
    return Object.keys(this.contexts);
  }

  /**
   * Check if sequent has multiple contexts (LNL style)
   */
  isMultiContext() {
    const modes = this.getContextModes();
    return modes.length > 1 &&
           modes.some(m => Object.keys(this.contexts[m]).length > 0 || m === 'cartesian');
  }

  /**
   * Render sequent as string
   */
  toString(o = {}) {
    let extensive = false;
    if (o.style === "ascii_extensive") {
      extensive = true;
      o.style = "ascii";
    }

    // Render linear context
    let linearStr = Object.keys(this.contexts.linear || {})
      .map(id => this.contexts.linear[id])
      .map(n => {
        let ret = n.val.toString(o);
        if (n.num > 1) {
          ret = `(${ret})* ${n.num}`;
        }
        if ("highlight" in o && (o.highlight || []).indexOf(n.val) > -1) {
          ret = clc.bold(ret);
        }
        return ret;
      })
      .join(extensive ? "\n" : ", ");

    // Render cartesian context
    let cartesianStr = Object.keys(this.contexts.cartesian || {})
      .map(id => this.contexts.cartesian[id])
      .map(n => {
        // Cartesian entries might be direct values (legacy) or {val, num} objects
        const val = n.val || n;
        return val.toString ? val.toString(o) : String(val);
      })
      .join(extensive ? "\n - " : ", ");

    let vdash = "|-";
    if (o.style === "latex") vdash = "\\vdash";

    if (extensive) {
      return `Rules:\n - ${cartesianStr}\n\nContext:\n ${linearStr}`;
    } else {
      // LNL style: Γ ; Δ ⊢ A
      const linearPart = linearStr === "" ? "I" : linearStr;
      if (cartesianStr) {
        return `${cartesianStr} ; ${linearPart} ${vdash} ${this.succedent.toString(o)}`;
      } else {
        return `${linearPart} ${vdash} ${this.succedent.toString(o)}`;
      }
    }
  }
}

// =============================================================================
// Static methods
// =============================================================================

Sequent.varIndex = 0;

/**
 * Get mode properties for a context
 */
Sequent.getContextMode = function(seq, mode) {
  if (!seq.contexts || !seq.contexts[mode]) return null;
  return CONTEXT_MODES[mode] || null;
};

/**
 * Add formula to a specific context by mode
 */
Sequent.addToContext = function(seq, mode, ast, num = 1) {
  profiler.count('sequent.addToContext');

  if (!seq.contexts[mode]) {
    seq.contexts[mode] = {};
  }

  const hash = computeHash(ast);
  const id = hash.toString();

  if (id in seq.contexts[mode]) {
    seq.contexts[mode][id].num += num;
  } else {
    seq.contexts[mode][id] = { num, val: ast, hash };
  }

  seq._hash = null;
};

/**
 * Rename variables to unique names across array of sequents
 */
Sequent.renameUniqueArray = function(seqs) {
  let vars = seqs
    .map(seq => Sequent.getFreeVariables(seq))
    .reduceRight((a, r) => a.concat(r), [])
    .reduceRight((a, v) => {
      let varNames = a.map(v => v.toString());
      if (varNames.indexOf(v.toString()) > -1) {
        return a;
      } else {
        return a.concat([v]);
      }
    }, []);

  let theta = vars.map(v => {
    let to = v.copy();
    to.vals[0] = `V_${Sequent.varIndex++}`;
    return [v, to];
  });

  let seqs_ = seqs
    .map(seq => Sequent.copy(seq))
    .map(seq => { seq.substitute(theta); return seq; });

  return { seqs: seqs_, theta };
};

/**
 * Rename variables to unique names in single sequent
 */
Sequent.renameUnique = function(seq) {
  let vars = Sequent.getFreeVariables(seq);

  let theta = vars.map(v => {
    let to = v.copy();
    to.vals[0] = `V_${Sequent.varIndex++}`;
    return [v, to];
  });

  let seq_ = Sequent.copy(seq);
  seq_.substitute(theta);

  return { seq: seq_, theta };
};

/**
 * Get all free variables in sequent
 */
Sequent.getFreeVariables = function(seq) {
  let allVars = [];

  // Collect from all contexts
  for (const [mode, ctx] of Object.entries(seq.contexts)) {
    const ctxVars = Object.keys(ctx)
      .map(id => {
        const entry = ctx[id];
        const val = entry.val || entry;
        return Res.getFreeVariables(val);
      })
      .reduceRight((a, r) => a.concat(r), []);
    allVars = allVars.concat(ctxVars);
  }

  // Collect from succedent
  let succedent_vars = Res.getFreeVariables(seq.succedent);
  allVars = allVars.concat(succedent_vars);

  // Unique by variable name
  return allVars.reduceRight((a, r) => {
    let varNames = a.map(v => v.toString());
    if (varNames.indexOf(r.toString()) > -1) {
      return a;
    } else {
      return a.concat([r]);
    }
  }, []);
};

/**
 * Deep copy a sequent
 */
Sequent.copy = function(seq) {
  profiler.count('sequent.copy');
  const endTime = profiler.time('sequent.copy');

  const newContexts = {};

  for (const [mode, ctx] of Object.entries(seq.contexts)) {
    newContexts[mode] = {};
    Object.keys(ctx).forEach(id => {
      const entry = ctx[id];
      if (entry.val) {
        // Multiset entry
        newContexts[mode][id] = {
          num: entry.num,
          val: entry.val.copy(),
          hash: entry.hash
        };
      } else if (entry.copy) {
        // Direct value (legacy persistent_ctx style)
        newContexts[mode][id] = entry.copy();
      } else {
        newContexts[mode][id] = entry;
      }
    });
  }

  let succedent = seq.succedent.copy();
  endTime();

  return new Sequent({
    contexts: newContexts,
    succedent
  });
};

/**
 * Remove structural variables from linear context
 */
Sequent.remove_structural_variables = function(seq) {
  const linear = seq.contexts.linear || {};
  let linear_ctx_ = {};

  Object.keys(linear).forEach(id => {
    let r = linear[id];
    let type = Calc.db.rules[r.val.id];
    if (type.ruleName !== "Structure_Freevar" &&
        type.ruleName !== "Structure_Neutral") {
      linear_ctx_[id] = r;
    }
  });

  seq.contexts.linear = linear_ctx_;
};

Sequent.isStable = function(seq, o) {
  // TODO: implement stability check
};

/**
 * Add to linear context (backwards compat)
 */
Sequent.add_to_linear_ctx = function(seq, ast, num = 1) {
  Sequent.addToContext(seq, 'linear', ast, num);
};

/**
 * Add multiple entries to linear context
 */
Sequent.add_to_antecedent_bulk = function(seq, delta) {
  Object.keys(delta).forEach(id => {
    let r = delta[id];
    Sequent.add_to_linear_ctx(seq, r.val, r.num);
  });
};

/**
 * Remove entries from linear context
 */
Sequent.remove_from_antecedent = function(seq, delta) {
  const linear = seq.contexts.linear || {};
  let linear_ctx_ = {};

  Object.keys(linear).forEach(id => {
    let r1 = linear[id];
    let r2 = delta[id];
    if (r2 && r1.num < r2.num) {
      linear_ctx_ = false;
    } else if (linear_ctx_ && r2 && r1.num > r2.num) {
      linear_ctx_[id] = { num: r1.num - r2.num, val: r1.val };
    } else if (linear_ctx_ && !r2) {
      linear_ctx_[id] = r1;
    }
  });

  if (linear_ctx_) {
    seq.contexts.linear = linear_ctx_;
  }
  return linear_ctx_;
};

/**
 * Construct comparison options (for unification)
 */
Sequent.constructCompareOptions = function(r1, r2) {
  if (r1.length === 0 || r2.length === 0) return [];
  let a = r1[0];
  return r2.map((b, j) => {
    let r1_ = r1.slice(1);
    let r2_ = r2.slice(0, j).concat(r2.slice(j + 1));
    let ret = Sequent.constructCompareOptions(r1_, r2_);
    let ret_;
    if (ret.length > 0) {
      ret_ = ret.map(r => r.concat([[a, b]]));
    } else {
      ret_ = ret.concat([[[a, b]]]);
    }
    return ret_;
  }).reduceRight((a, r) => a.concat(r), []);
};

/**
 * Convert parsed tree to sequent
 *
 * Supports both 2-arg (Δ ⊢ A) and 3-arg (Γ ; Δ ⊢ A) sequents
 */
Sequent.fromTree = function(seq) {
  const numArgs = seq.vals.length;

  // Determine sequent arity from parsed tree
  if (numArgs === 3) {
    // LNL 3-arg sequent: seq(cart_ctx, lin_ctx, formula)
    return Sequent.fromTreeLNL(seq);
  } else {
    // Standard 2-arg sequent: seq(ctx, formula)
    return Sequent.fromTreeSimple(seq);
  }
};

/**
 * Convert 2-arg sequent tree (Δ ⊢ A)
 */
Sequent.fromTreeSimple = function(seq) {
  const linear_ctx = {};

  const tree2multiset = (struct) => {
    let type = Calc.db.rules[struct.id];
    if (type.ruleName === "Structure_Comma") {
      tree2multiset(struct.vals[0]);
      tree2multiset(struct.vals[1]);
    } else {
      if (type.ruleName === "Structure_Neutral") return null;

      const hash = computeHash(struct);
      const id = hash.toString();

      if (id in linear_ctx) {
        linear_ctx[id].num++;
      } else {
        linear_ctx[id] = { val: struct, num: 1, hash };
      }
    }
  };

  tree2multiset(seq.vals[0]);
  const succedent = seq.vals[1];

  return new Sequent({
    contexts: { linear: linear_ctx, cartesian: {} },
    succedent
  });
};

/**
 * Convert 3-arg LNL sequent tree (Γ ; Δ ⊢ A)
 */
Sequent.fromTreeLNL = function(seq) {
  const cartesian_ctx = {};
  const linear_ctx = {};

  // Helper to convert structure tree to multiset
  const tree2multiset = (struct, target, commaRule, neutralRule) => {
    if (!struct || !struct.id) return;
    let type = Calc.db.rules[struct.id];
    if (!type) return;

    // Check for comma (context concatenation)
    if (type.ruleName === commaRule ||
        type.ruleName === "Structure_Comma" ||
        type.ruleName.includes("Comma")) {
      tree2multiset(struct.vals[0], target, commaRule, neutralRule);
      tree2multiset(struct.vals[1], target, commaRule, neutralRule);
    } else if (type.ruleName === neutralRule ||
               type.ruleName === "Structure_Neutral" ||
               type.ruleName.includes("Neutral") ||
               type.ruleName.includes("Empty")) {
      // Skip neutral/empty elements
      return;
    } else {
      const hash = computeHash(struct);
      const id = hash.toString();

      if (id in target) {
        target[id].num++;
      } else {
        target[id] = { val: struct, num: 1, hash };
      }
    }
  };

  // Parse cartesian context (Γ) - vals[0]
  tree2multiset(seq.vals[0], cartesian_ctx, "Cart_Structure_Comma", "Cart_Structure_Neutral");

  // Parse linear context (Δ) - vals[1]
  tree2multiset(seq.vals[1], linear_ctx, "Structure_Comma", "Structure_Neutral");

  // Succedent (A) - vals[2]
  const succedent = seq.vals[2];

  return new Sequent({
    contexts: { cartesian: cartesian_ctx, linear: linear_ctx },
    succedent
  });
};

/**
 * Get atomic formulas from sequent
 */
Sequent.getAtoms = function(seq, o) {
  const atomic = ["Formula_Freevar", "Formula_Atprop"];

  const getAtoms = function(n) {
    if (typeof n === "string") return [[n]];
    if (!n || !n.id) return [];
    let type = o.rules[n.id];
    if (!type) return [];

    if ((type.ctxName === "Formula") && atomic.indexOf(type.ruleName) > -1) {
      if (type.ruleName === "Formula_Freevar") {
        return [[n.toString(), n]];
      } else {
        if (n.vals && n.vals[0] && n.vals[0].vals) {
          return [[n.vals[0].vals[0], n]];
        }
        return [[n.toString(), n]];
      }
    } else if (type.ruleName === "Formula_Forall") {
      return getAtoms(n.vals[2]);
    } else {
      return (n.vals || [])
        .map(getAtoms)
        .reduceRight((a, e) => a.concat(e), []);
    }
  };

  // Collect from all contexts
  let atoms = [];
  for (const ctx of Object.values(seq.contexts)) {
    const ctxAtoms = Object.keys(ctx)
      .map(id => ctx[id].val)
      .map(getAtoms)
      .reduceRight((a, e) => a.concat(e), []);
    atoms = atoms.concat(ctxAtoms);
  }

  atoms = atoms.concat(getAtoms(seq.succedent));

  // Unique
  let aa = {};
  atoms.forEach(a => aa[a[0]] = true);

  return Object.keys(aa);
};

// Export hash utility
Sequent.computeHash = computeHash;

// Export context modes for external use
Sequent.CONTEXT_MODES = CONTEXT_MODES;

module.exports = Sequent;
