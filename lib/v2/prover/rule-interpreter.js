/**
 * Generic Rule Interpreter
 *
 * Reads rule.descriptor (flat JSON) from calculus.rules and produces
 * spec objects for the prover. Each spec has: makePremises, copyContext,
 * and optionally requiresEmptyDelta, contextSplit.
 *
 * No TermApp walking — all AST analysis happens in rules/analyze.js
 * at load time.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');

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
 * Build rule specs from calculus rules (reads rule.descriptor).
 * @returns {{ specs: Object, alternatives: Object }}
 */
function buildRuleSpecs(calculus) {
  const specs = {};
  const alternatives = {};

  for (const [name, rule] of Object.entries(calculus.rules)) {
    if (name === 'id') continue;

    const d = rule.descriptor;
    const key = specKey(rule, d);
    if (!key) continue;

    const spec = {
      copyContext: d.copyContext,
    };

    if (d.emptyLinear && rule.numPremises > 0) spec.requiresEmptyDelta = true;
    if (d.contextSplit) spec.contextSplit = true;

    // makePremises
    if (rule.numPremises === 0) {
      spec.makePremises = () => [];
    } else if (rule.structural) {
      spec.makePremises = (formula, seq) => {
        const cart = Seq.getContext(seq, 'cartesian');
        const linear = Seq.getContext(seq, 'linear');
        return [Seq.fromArrays([...linear, formula], cart, seq.succedent)];
      };
    } else {
      spec.makePremises = buildMakePremises(d);
    }

    // Handle key collisions (dereliction and absorption both map to bang_l)
    if (specs[key]) {
      specs[name] = spec;
      if (!alternatives[key]) alternatives[key] = [];
      alternatives[key].push(name);
    } else {
      specs[key] = spec;
    }
  }

  // Add suffixed variants to alternatives (with_l → [with_l1, with_l2])
  for (const key of Object.keys(specs)) {
    const match = key.match(/^(.+_[lr])(\d+)$/);
    if (match) {
      const base = match[1];
      if (!alternatives[base]) alternatives[base] = [];
      if (!alternatives[base].includes(key)) alternatives[base].push(key);
    }
  }

  return { specs, alternatives };
}

module.exports = { buildRuleSpecs };
