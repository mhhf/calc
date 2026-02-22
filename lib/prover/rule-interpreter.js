/**
 * Generic Rule Interpreter
 *
 * Reads rule.descriptor (flat JSON) from calculus.rules and produces
 * spec objects for the prover. Each spec has: makePremises, copyContext,
 * and optionally requiresEmptyDelta, contextSplit.
 *
 * Data computation (computeRuleSpecMeta) is separated from function
 * creation (buildRuleSpecsFromMeta) so metadata can be precomputed
 * at build time into ill.json.
 *
 * No TermApp walking — all AST analysis happens in rules/analyze.js
 * at load time.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { debruijnSubst } = require('../kernel/substitute');
const { freshEvar, freshMetavar } = require('../kernel/fresh');

/**
 * Determine the spec key for a rule.
 * Standard rules: name as-is (tensor_r, with_l1, ...).
 * Non-standard names: use connective_side (promotion → bang_r, dereliction → bang_l).
 * Structural rules: keep name (copy).
 */
function specKey(rule, d) {
  if (rule.name === 'id') return null;
  if (!d.connective) return rule.name; // structural (copy)

  const expected = `${d.connective}_${d.side}`;
  const base = expected.replace(/_[lr]$/, '') + '_';
  if (rule.name === expected || rule.name.startsWith(base)) return rule.name;
  return expected; // promotion → bang_r, dereliction → bang_l
}

/**
 * Build a makePremises function from a descriptor.
 */
function buildMakePremises(d) {
  return (formula, seq, idx) => {
    const ch = Array.from({ length: d.arity }, (_, i) => Store.child(formula, i));

    // Binder opening for quantifier rules
    if (d.binding) {
      if (d.binding === 'eigenvariable') {
        // ∃L, ∀R: open with fresh eigenvariable
        ch[0] = debruijnSubst(ch[0], 0n, freshEvar());
      } else if (d.binding === 'metavar') {
        // ∃R, ∀L: open with fresh metavar (unification will find witness)
        const mv = freshMetavar();
        ch[0] = debruijnSubst(ch[0], 0n, mv);
      }
    }

    const cart = Seq.getContext(seq, 'cartesian');

    return d.premises.map(p => {
      const lin = (p.linear || []).map(i => ch[i]);
      const xCart = (p.cartesian || []).map(i => ch[i]);
      const succ = p.succedent != null ? ch[p.succedent] : seq.succedent;
      return Seq.fromArrays(lin, xCart.length ? [...cart, ...xCart] : cart, succ);
    });
  };
}

/**
 * Compute rule spec metadata (pure data, serializable).
 * Extracts specKey, copyContext, requiresEmptyDelta, contextSplit, alternatives
 * from rule descriptors without creating makePremises functions.
 *
 * @param {Object} rules - calculus.rules (name → rule)
 * @returns {{ specData: Object, alternatives: Object }}
 */
function computeRuleSpecMeta(rules) {
  const specData = {};
  const alternatives = {};

  for (const [name, rule] of Object.entries(rules)) {
    if (name === 'id') continue;

    const d = rule.descriptor;
    const key = specKey(rule, d);
    if (!key) continue;

    const data = { ruleName: name, copyContext: d.copyContext };
    if (d.emptyLinear && rule.numPremises > 0) data.requiresEmptyDelta = true;
    if (d.contextSplit) data.contextSplit = true;
    if (d.binding) data.binding = d.binding;

    // Handle key collisions (dereliction and absorption both map to bang_l)
    if (specData[key]) {
      specData[name] = data;
      if (!alternatives[key]) alternatives[key] = [];
      alternatives[key].push(name);
    } else {
      specData[key] = data;
    }
  }

  // Add suffixed variants to alternatives (with_l → [with_l1, with_l2])
  for (const key of Object.keys(specData)) {
    const match = key.match(/^(.+_[lr])(\d+)$/);
    if (match) {
      const base = match[1];
      if (!alternatives[base]) alternatives[base] = [];
      if (!alternatives[base].includes(key)) alternatives[base].push(key);
    }
  }

  return { specData, alternatives };
}

/**
 * Build rule specs from precomputed metadata + rules (for makePremises).
 * @param {{ specData: Object, alternatives: Object }} meta - from computeRuleSpecMeta
 * @param {Object} rules - calculus.rules (needed for makePremises construction)
 * @returns {{ specs: Object, alternatives: Object }}
 */
function buildRuleSpecsFromMeta(meta, rules) {
  const specs = {};

  for (const [key, data] of Object.entries(meta.specData)) {
    const rule = rules[data.ruleName];
    const spec = { copyContext: data.copyContext };
    if (data.requiresEmptyDelta) spec.requiresEmptyDelta = true;
    if (data.contextSplit) spec.contextSplit = true;

    if (rule.numPremises === 0) {
      spec.makePremises = () => [];
    } else if (rule.structural) {
      spec.makePremises = (formula, seq) => {
        const cart = Seq.getContext(seq, 'cartesian');
        const linear = Seq.getContext(seq, 'linear');
        return [Seq.fromArrays([...linear, formula], cart, seq.succedent)];
      };
    } else {
      spec.makePremises = buildMakePremises(rule.descriptor);
    }

    specs[key] = spec;
  }

  return { specs, alternatives: meta.alternatives };
}

/**
 * Build rule specs from calculus rules (convenience: compute meta + build).
 * @returns {{ specs: Object, alternatives: Object }}
 */
function buildRuleSpecs(calculus) {
  const meta = computeRuleSpecMeta(calculus.rules);
  return buildRuleSpecsFromMeta(meta, calculus.rules);
}

module.exports = { buildRuleSpecs, computeRuleSpecMeta, buildRuleSpecsFromMeta };
