/**
 * Generic Rule Interpreter
 *
 * Reads rule.descriptor (flat JSON) from calculus.rules and produces
 * spec objects for the prover. Each spec has: makePremises, copyContext,
 * and optionally requiresEmptyDelta, contextSplit.
 *
 * Data computation (specMeta) is separated from function
 * creation (specsFromMeta) so metadata can be precomputed
 * at build time into ill.json.
 *
 * No TermApp walking — all AST analysis happens in rules/rules2-parser.js
 * at load time.
 */

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';
import { apply, debruijnSubst } from '../kernel/substitute.js';
import { unify } from '../kernel/unify.js';
import { freshEvar, freshMetavar } from '../kernel/fresh.js';
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
 * Compute premises from a descriptor, formula, and sequent.
 * Defunctionalized: single function dispatching on descriptor shape,
 * replacing per-rule closures. Zig-portable: translates to a switch.
 *
 * Three descriptor types:
 *   'zero'       — zero-premise rules (zero_l, one_r): return []
 *   'structural' — copy rule: promote formula into linear context
 *   'standard'   — all connective rules: read arity/binding/premises from descriptor
 *
 * Called as spec.makePremises(formula, seq, index) where `this` is the spec.
 * The spec carries `this._premiseType` and `this._descriptor`.
 */
function interpretPremises(formula, seq, _index) {
  const type = this._premiseType;

  // Template rules (TODO_0265 Phase 6b, D1): match the principal pattern
  // (and for left rules the conclusion-succedent pattern) by one-way
  // unification — pattern metavars bind, sequent content is rigid — then
  // evaluate @grade side conditions through the grade-algebra record and
  // instantiate premise patterns by substitution. Returns null when the
  // pattern or a side condition fails (the rule is simply inapplicable);
  // zero-premise template rules still go through the full check, so a
  // guard like `K = 0` is enforced in search AND kernel verification.
  if (type === 'template') {
    const t = this._template;
    let theta = unify(t.principal, formula);
    if (!theta) return null;
    if (t.succedent != null) {
      const th2 = unify(apply(t.succedent, theta), seq.succedent);
      if (!th2) return null;
      theta = theta.concat(th2);
    }
    if (t.steps.length) {
      const g = this._grades;
      if (!g) return null;
      const tmap = new Map(theta.map(e => [e[0], e[1]]));
      const resolve = (o) => (o.g !== undefined ? o.g : tmap.get(o.v));
      for (const s of t.steps) {
        const a = resolve(s.a), b = resolve(s.b);
        // non-numeric grades (ω/0 labels, unresolved metavars) fail
        // guards — they are matched structurally, never arithmetically
        if (a === undefined || b === undefined || !g.isStamp(a) || !g.isStamp(b)) return null;
        if (s.kind === 'def') {
          const r = s.op === '+' ? g.effect.compose(a, b) : g.effect.sub(a, b);
          // grades are ℚ≥0 in v1 — `-` is a monus (negative ⇒ inapplicable)
          if (g.availability.cmp(r, g.effect.unit()) < 0) return null;
          theta.push([s.out, r]);
          tmap.set(s.out, r);
        } else {
          const c = g.availability.cmp(a, b);
          const ok = s.op === '=' ? c === 0 : s.op === '<' ? c < 0 :
            s.op === '>' ? c > 0 : s.op === '<=' ? c <= 0 : c >= 0;
          if (!ok) return null;
        }
      }
    }
    const cart = Seq.getContext(seq, 'cartesian');
    return t.premises.map(p => {
      const lin = p.linear.map(h => apply(h, theta));
      const xCart = p.cartesian.map(h => apply(h, theta));
      const succ = p.succedent != null ? apply(p.succedent, theta) : seq.succedent;
      return Seq.fromArrays(lin, xCart.length ? [...cart, ...xCart] : cart, succ);
    });
  }

  // Zero-premise: zero_l (discard context), one_r (require empty)
  if (type === 'zero') return [];

  // Structural: copy from cartesian into linear
  if (type === 'structural') {
    const cart = Seq.getContext(seq, 'cartesian');
    const linear = Seq.getContext(seq, 'linear');
    return [Seq.fromArrays([...linear, formula], cart, seq.succedent)];
  }

  // Standard connective rules: dispatch on descriptor data
  const d = this._descriptor;
  const ch = Array.from({ length: d.arity }, (_, i) => Store.child(formula, i));

  // Binder opening for quantifier rules
  if (d.binding) {
    if (d.binding === 'eigenvariable') {
      // ∃L, ∀R: open with fresh eigenvariable
      ch[0] = debruijnSubst(ch[0], 0n, freshEvar());
    } else if (d.binding === 'metavar') {
      // ∃R, ∀L: open with fresh metavar (unification will find witness)
      ch[0] = debruijnSubst(ch[0], 0n, freshMetavar());
    }
  }

  const cart = Seq.getContext(seq, 'cartesian');

  return d.premises.map(p => {
    const lin = (p.linear || []).map(i => ch[i]);
    const xCart = (p.cartesian || []).map(i => ch[i]);
    const succ = p.succedent != null ? ch[p.succedent] : seq.succedent;
    return Seq.fromArrays(lin, xCart.length ? [...cart, ...xCart] : cart, succ);
  });
}

/**
 * Compute rule spec metadata (pure data, serializable).
 * Extracts specKey, copyContext, requiresEmptyDelta, contextSplit, alternatives
 * from rule descriptors without creating makePremises functions.
 *
 * @param {Object} rules - calculus.rules (name → rule)
 * @returns {{ specData: Object, alternatives: Object }}
 */
function specMeta(rules) {
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
    // Zero-premise left rules that don't require empty linear discard remaining context
    // (e.g., zero_l: the entire linear context is discarded). Template
    // axioms (retiming at_l) consume ONLY their principal — never discard.
    if (rule.numPremises === 0 && d.side === 'l' && !d.emptyLinear && !d.template) data.discardsContext = true;
    if (d.modeShift) data.modeShift = true;
    if (d.requiresSuccedentTag) data.requiresSuccedentTag = d.requiresSuccedentTag;

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
 * @param {{ specData: Object, alternatives: Object }} meta - from specMeta
 * @param {Object} rules - calculus.rules (needed for makePremises construction)
 * @param {Object} [grades] - grade-algebra record (template-rule side conditions)
 * @returns {{ specs: Object, alternatives: Object }}
 */
function specsFromMeta(meta, rules, grades = null) {
  const specs = {};

  for (const [key, data] of Object.entries(meta.specData)) {
    const rule = rules[data.ruleName];
    const spec = { copyContext: data.copyContext };
    if (data.requiresEmptyDelta) spec.requiresEmptyDelta = true;
    if (data.contextSplit) spec.contextSplit = true;
    if (data.discardsContext) spec.discardsContext = true;
    if (data.modeShift) spec.modeShift = true;
    if (data.requiresSuccedentTag) spec.requiresSuccedentTag = data.requiresSuccedentTag;

    // Defunctionalized: all specs share interpretPremises, dispatch on _premiseType.
    // No per-rule closures — Zig-portable (single function + descriptor data).
    spec.makePremises = interpretPremises;
    if (rule.descriptor.template) {
      // Template rules dispatch on template even with zero premises — the
      // pattern/guard check must run in search AND kernel verification.
      spec._premiseType = 'template';
      spec._template = rule.descriptor.template;
      spec._grades = grades;
    } else if (rule.numPremises === 0) {
      spec._premiseType = 'zero';
    } else if (rule.structural) {
      spec._premiseType = 'structural';
    } else {
      spec._premiseType = 'standard';
      spec._descriptor = rule.descriptor;
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
  const meta = specMeta(calculus.rules);
  return specsFromMeta(meta, calculus.rules, calculus.grades);
}

/** Use precomputed meta if available, otherwise compute from scratch. */
function initRuleSpecs(calculus) {
  return calculus.ruleSpecMeta
    ? specsFromMeta(calculus.ruleSpecMeta, calculus.rules, calculus.grades)
    : buildRuleSpecs(calculus);
}

export { buildRuleSpecs, specMeta, initRuleSpecs };
export default { buildRuleSpecs, specMeta, initRuleSpecs };
