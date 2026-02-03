/**
 * TreeSequent - Generic tree-based sequent representation
 *
 * This is the Level 1 (theory-compliant) representation where:
 *   - Antecedent and succedent are TREES (not multisets)
 *   - Display postulates operate on tree structure
 *   - No optimizations (faithful to display calculus)
 *
 * Structure: antecedent ⊢ succedent
 *   - antecedent: A tree structure (connectives like comma, empty, struct, etc.)
 *   - succedent: A formula or tree structure
 *
 * For LNL family: antecedent = (cart_structure, structure)
 *   - Γ ; Δ ⊢ A where Γ is cart_structure, Δ is structure
 *
 * Display Postulates:
 *   - Exchange: comma(X, Y) ⊣⊢ comma(Y, X)
 *   - Associativity: comma(comma(X, Y), Z) ⊣⊢ comma(X, comma(Y, Z))
 *   - Unit: comma(empty, X) ⊣⊢ X ⊣⊢ comma(X, empty)
 *   - Contraction (cartesian): Γ, X, X → Γ, X
 *   - Weakening (cartesian): Γ → Γ, X
 */

const { profiler } = require("./profiler.js");
const { internNode } = require("./intern.js");
const { hashCombine } = require('../hash');

/**
 * Compute content-addressed hash for a node
 */
function computeHash(ast) {
  if (!ast) return 0n;
  profiler.count('tree-sequent.hash');
  return internNode(ast).hash;
}

/**
 * TreeSequent class - generic tree-based sequent
 *
 * Unlike the optimized Sequent class, this preserves full tree structure.
 */
class TreeSequent {
  /**
   * Create a tree sequent
   *
   * @param {Object} params - Sequent parameters
   * @param {*} params.antecedent - Antecedent structure (tree)
   * @param {*} params.succedent - Succedent formula/structure
   * @param {Object} [params.meta] - Optional metadata (family, roles, etc.)
   */
  constructor(params = {}) {
    this.antecedent = params.antecedent || null;
    this.succedent = params.succedent || null;
    this.meta = params.meta || {};
    this._hash = null;
  }

  /**
   * Get content-addressed hash for this sequent
   */
  getHash() {
    if (this._hash !== null) {
      return this._hash;
    }

    profiler.count('tree-sequent.getHash');

    const antHash = computeHash(this.antecedent);
    const succHash = computeHash(this.succedent);

    this._hash = hashCombine(antHash, succHash);
    return this._hash;
  }

  /**
   * O(1) equality check via hash
   */
  equals(other) {
    if (!(other instanceof TreeSequent)) return false;
    return this.getHash() === other.getHash();
  }

  /**
   * Deep copy
   */
  copy() {
    profiler.count('tree-sequent.copy');

    return new TreeSequent({
      antecedent: this.antecedent?.copy?.() || this.antecedent,
      succedent: this.succedent?.copy?.() || this.succedent,
      meta: { ...this.meta }
    });
  }

  /**
   * Render as string
   */
  toString(o = {}) {
    const vdash = o.style === "latex" ? "\\vdash" : "|-";
    const antStr = this.antecedent?.toString?.(o) || "I";
    const succStr = this.succedent?.toString?.(o) || "_";
    return `${antStr} ${vdash} ${succStr}`;
  }
}

// =============================================================================
// LNL-specific TreeSequent (3-arg: Γ ; Δ ⊢ A)
// =============================================================================

/**
 * LNLTreeSequent - Tree sequent for LNL family
 *
 * Specialized for the LNL 3-arg sequent structure:
 *   Γ (cart_structure) ; Δ (structure) ⊢ A (formula)
 */
class LNLTreeSequent extends TreeSequent {
  /**
   * Create an LNL tree sequent
   *
   * @param {Object} params
   * @param {*} params.cartesian - Cartesian context (Γ)
   * @param {*} params.linear - Linear context (Δ)
   * @param {*} params.succedent - Succedent formula (A)
   */
  constructor(params = {}) {
    super({
      antecedent: null, // Computed from cartesian + linear
      succedent: params.succedent,
      meta: params.meta
    });

    this.cartesian = params.cartesian || null;
    this.linear = params.linear || null;
  }

  /**
   * Get hash (includes both contexts)
   */
  getHash() {
    if (this._hash !== null) {
      return this._hash;
    }

    profiler.count('lnl-tree-sequent.getHash');

    const cartHash = computeHash(this.cartesian);
    const linHash = computeHash(this.linear);
    const succHash = computeHash(this.succedent);

    this._hash = hashCombine(cartHash, linHash, succHash);
    return this._hash;
  }

  /**
   * Deep copy
   */
  copy() {
    profiler.count('lnl-tree-sequent.copy');

    return new LNLTreeSequent({
      cartesian: this.cartesian?.copy?.() || this.cartesian,
      linear: this.linear?.copy?.() || this.linear,
      succedent: this.succedent?.copy?.() || this.succedent,
      meta: { ...this.meta }
    });
  }

  /**
   * Render as LNL-style string: Γ ; Δ ⊢ A
   */
  toString(o = {}) {
    const vdash = o.style === "latex" ? "\\vdash" : "|-";
    const semi = o.style === "latex" ? ";" : ";";

    const cartStr = this.cartesian?.toString?.(o) || "·";
    const linStr = this.linear?.toString?.(o) || "I";
    const succStr = this.succedent?.toString?.(o) || "_";

    if (cartStr === "·" || cartStr === "cart_empty") {
      return `${linStr} ${vdash} ${succStr}`;
    }
    return `${cartStr} ${semi} ${linStr} ${vdash} ${succStr}`;
  }
}

// =============================================================================
// Factory functions
// =============================================================================

/**
 * Create TreeSequent from parsed tree
 *
 * @param {Object} tree - Parsed sequent tree
 * @param {Object} calc - Calculus database (for rule lookup)
 * @returns {TreeSequent|LNLTreeSequent}
 */
TreeSequent.fromTree = function(tree, calc) {
  if (!tree || !tree.vals) {
    return new TreeSequent({ antecedent: null, succedent: null });
  }

  const numArgs = tree.vals.length;

  if (numArgs === 3) {
    // LNL 3-arg: seq(cart_ctx, lin_ctx, formula)
    return new LNLTreeSequent({
      cartesian: tree.vals[0],
      linear: tree.vals[1],
      succedent: tree.vals[2]
    });
  } else if (numArgs === 2) {
    // Standard 2-arg: seq(ctx, formula)
    return new TreeSequent({
      antecedent: tree.vals[0],
      succedent: tree.vals[1]
    });
  } else {
    throw new Error(`Unknown sequent arity: ${numArgs}`);
  }
};

/**
 * Apply a structural rule (display postulate) to a tree sequent
 *
 * @param {TreeSequent} seq - Input sequent
 * @param {string} rule - Rule name (e.g., 'exchange', 'assoc_l', 'assoc_r')
 * @param {Array} path - Path to the substructure to transform
 * @returns {TreeSequent} - Transformed sequent
 */
TreeSequent.applyStructural = function(seq, rule, path) {
  // TODO: Implement structural rule application
  // This requires:
  // 1. Navigate to path in antecedent
  // 2. Apply transformation based on rule
  // 3. Return new sequent
  throw new Error('TreeSequent.applyStructural not yet implemented');
};

/**
 * Check if a formula is "displayed" (isolated on one side)
 *
 * In display calculus, a formula Z is displayed if:
 *   - The sequent is equivalent to Z ⊢ Y' (Z on left, alone)
 *   - Or the sequent is equivalent to X' ⊢ Z (Z on right, alone)
 *
 * @param {TreeSequent} seq - The sequent
 * @param {*} formula - The formula to check
 * @returns {boolean}
 */
TreeSequent.isDisplayed = function(seq, formula) {
  // For basic check: is formula exactly the antecedent or succedent?
  const antHash = computeHash(seq.antecedent);
  const succHash = computeHash(seq.succedent);
  const targetHash = computeHash(formula);

  return antHash === targetHash || succHash === targetHash;
};

// =============================================================================
// Exports
// =============================================================================

module.exports = {
  TreeSequent,
  LNLTreeSequent,
  computeHash
};
