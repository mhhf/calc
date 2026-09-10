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
import { collectMetavars } from '../engine/pattern-utils.js';
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
  // discharge THEORY PREMISES through the calculus's theory engine
  // (TODO_0273: `<- !qsub F E H` etc., derived over the arithmetic theory;
  // output variables are bound by the derivation) and instantiate premise
  // patterns by substitution. Returns null when the pattern or a theory
  // goal fails (the rule is simply inapplicable); zero-premise template
  // rules still go through the full check, so a goal like `!eq K 0` is
  // enforced in search AND kernel verification.
  if (type === 'template') {
    const t = this._template;
    let theta = unify(t.principal, formula);
    if (!theta) return null;
    if (t.succedent != null) {
      const th2 = unify(apply(t.succedent, theta), seq.succedent);
      if (!th2) return null;
      theta = theta.concat(th2);
    }
    if (this._theoryGoals) {
      const th = this._theory;
      if (!th) return null;
      for (const tg of this._theoryGoals) {
        const m = tg.args.length;
        const argv = new Array(m);
        for (let i = 0; i < m; i++) {
          const a = tg.args[i];
          if (a.v === undefined) {
            if (a.t !== undefined) {
              const inst = apply(a.t, theta);
              // compound inputs must be ground — mirrors the bare-var
              // rigidity fence below (TODO_0274 item 2)
              const rem = new Set();
              collectMetavars(inst, rem);
              if (rem.size) return null;
              argv[i] = inst;
            } else {
              argv[i] = a.g;
            }
            continue;
          }
          let val;
          for (let k = theta.length - 1; k >= 0; k--) {
            if (theta[k][0] === a.v) { val = theta[k][1]; break; }
          }
          // input vars must be resolved by the sequent match to something
          // rigid; only a declared OUTPUT var may stay free (bound by the
          // derivation) — mirrors the old non-numeric-grade fence
          if (val === undefined) {
            if (!a.out) return null;
            argv[i] = a.v;
          } else if (!a.out && Store.tag(val) === 'metavar') {
            return null;
          } else {
            argv[i] = val;
          }
        }
        const sub = th.prove(Store.put(tg.tag, argv));
        if (sub == null) return null;
        for (const b of sub) theta.push(b);
      }
    }
    // Template binder opening (TODO_0298): a template rule with @binding
    // rebinds the binder-body var to the OPENED body before premises are
    // instantiated. eigenvariable → fresh evar (∃-L); metavar → fresh
    // metavar (∃-R search); witness → the variable named in the rule,
    // resolved from the principal match (∃_ρ-R: the drawn token's member).
    if (this._bindingMode) {
      const look = (v) => {
        for (let k = theta.length - 1; k >= 0; k--) {
          if (theta[k][0] === v) return theta[k][1];
        }
        return undefined;
      };
      let witness;
      if (this._bindingMode === 'eigenvariable') witness = freshEvar();
      else if (this._bindingMode === 'metavar') witness = freshMetavar();
      else witness = look(t.witnessVar);
      const body = look(t.bodyVar);
      if (witness === undefined || body === undefined) return null;
      const opened = debruijnSubst(body, 0n, witness);
      theta = theta.map(b => (b[0] === t.bodyVar ? [t.bodyVar, opened] : b));
    }

    const cs = this._ctxStruct || Seq.DEFAULT_CONTEXT_STRUCTURE;
    // No copy source (single-zone families, TODO_0309): a premise that
    // ASKS for cartesian formulas is inapplicable; otherwise the
    // copy-source column simply doesn't exist on premise sequents.
    const cart = cs.copySource ? Seq.getContext(seq, cs.copySource) : null;
    const premises = [];
    for (const p of t.premises) {
      const lin = p.linear.map(h => apply(h, theta));
      const xCart = p.cartesian.map(h => apply(h, theta));
      if (xCart.length && !cs.copySource) return null;
      const succ = p.succedent != null ? apply(p.succedent, theta) : seq.succedent;
      // Premise consumable columns carry ONLY premise formulas (wrapper-
      // routed, TODO_0285) — the surrounding context arrives via delta
      // threading (generic.addDelta), so no conclusion-context spread.
      const cols = Seq.routeContexts(cs, lin);
      if (cs.copySource) cols[cs.copySource] = xCart.length ? [...cart, ...xCart] : cart;
      premises.push(Seq.seq(cols, succ));
    }
    // Companion consumption (TODO_0309): exact axioms return the
    // instantiated companion formulas for the caller to remove from the
    // pool — the extended { premises, consume } contract.
    if (t.companions) {
      return { premises, consume: t.companions.map(h => apply(h, theta)) };
    }
    return premises;
  }

  // Zero-premise: zero_l (discard context), one_r (require empty)
  if (type === 'zero') return [];

  // Explicit cut (TODO_0309): premises depend on a cut formula the
  // descriptor cannot supply — the search instantiates it from the
  // subformula closure (focused.js), the kernel from the recorded
  // premise. Uninterpretable here, so generic dispatch skips it.
  if (type === 'cut') return null;

  // Structural: copy from the copy-source zone into the copied formula's
  // own consumable zone (wrapper-routed); all other columns pass through
  // unchanged (TODO_0285).
  if (type === 'structural') {
    const cs = this._ctxStruct || Seq.DEFAULT_CONTEXT_STRUCTURE;
    const zone = Seq.routeZone(cs, formula);
    return [Seq.seq({
      ...seq.contexts,
      [zone]: [...Seq.getContext(seq, zone), formula],
    }, seq.succedent)];
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
    } else if (d.binding === 'unfold') {
      // μ/ν unfold (TODO_0009): open the body with the WHOLE principal
      // formula (σX.F) as the witness → F[σX.F/X]. Deterministic: no fresh
      // variable, so the kernel re-derives the premise hash-identically and
      // the step is fully verified (verifyTree's binding-degradation path
      // is never taken because the exact-match subtractIntro succeeds).
      ch[0] = debruijnSubst(ch[0], 0n, formula);
    }
  }

  const cs = this._ctxStruct || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const cart = cs.copySource ? Seq.getContext(seq, cs.copySource) : null;

  const out = [];
  for (const p of d.premises) {
    const lin = (p.linear || []).map(i => ch[i]);
    const xCart = (p.cartesian || []).map(i => ch[i]);
    if (xCart.length && !cs.copySource) return null;
    const succ = p.succedent != null ? ch[p.succedent] : seq.succedent;
    // Wrapper-routed premise columns; context arrives via delta threading
    // (see the template-premise site above). TODO_0285.
    const cols = Seq.routeContexts(cs, lin);
    if (cs.copySource) cols[cs.copySource] = xCart.length ? [...cart, ...xCart] : cart;
    out.push(Seq.seq(cols, succ));
  }
  return out;
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
    if (d.affine) data.affine = true;
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
 * @param {Object} [theory] - theory engine ({ prove }) discharging template
 *   theory premises (TODO_0273); ILL-style calculi pass none
 * @returns {{ specs: Object, alternatives: Object }}
 */
function specsFromMeta(meta, rules, theory = null, ctxStruct = null) {
  const specs = {};

  // Compile a template's theory goals into per-argument recipes so apply
  // time needs no term walk (TODO_0273): each argument is a ground hash
  // ({ g }), a bare variable ({ v, out }) resolved against theta, or — for
  // compound arguments — a substitution template ({ t }).
  const compileTheoryGoals = (goals) => goals.map(({ goal, outs }) => {
    const n = Store.arity(goal);
    const args = new Array(n);
    for (let i = 0; i < n; i++) {
      const c = Store.child(goal, i);
      if (!Store.isTermChild(c)) { args[i] = { g: c }; continue; }
      if (Store.tag(c) === 'metavar') {
        args[i] = { v: c, out: outs.includes(c) };
      } else {
        const mvs = new Set();
        collectMetavars(c, mvs);
        args[i] = mvs.size ? { t: c } : { g: c };
      }
    }
    return { tag: Store.tag(goal), args };
  });

  for (const [key, data] of Object.entries(meta.specData)) {
    const rule = rules[data.ruleName];
    const spec = { copyContext: data.copyContext };
    if (data.requiresEmptyDelta) spec.requiresEmptyDelta = true;
    if (data.contextSplit) spec.contextSplit = true;
    if (data.discardsContext) spec.discardsContext = true;
    if (data.modeShift) spec.modeShift = true;
    if (data.affine) spec.affine = true;
    if (data.requiresSuccedentTag) spec.requiresSuccedentTag = data.requiresSuccedentTag;

    // Defunctionalized: all specs share interpretPremises, dispatch on _premiseType.
    // No per-rule closures — Zig-portable (single function + descriptor data).
    spec.makePremises = interpretPremises;
    // Zone names for premise construction (TODO_0086): bound per spec so
    // interpretPremises (this-dispatched) needs no extra argument.
    if (ctxStruct) spec._ctxStruct = ctxStruct;
    if (rule.descriptor.template) {
      // Template rules dispatch on template even with zero premises — the
      // pattern/theory-goal check must run in search AND kernel verification.
      spec._premiseType = 'template';
      spec._template = rule.descriptor.template;
      spec._theory = theory;
      // Template binder opening (TODO_0298): eigenvariable/metavar/witness
      if (rule.descriptor.binding) spec._bindingMode = rule.descriptor.binding;
      const goals = rule.descriptor.template.theoryGoals;
      spec._theoryGoals = goals && goals.length ? compileTheoryGoals(goals) : null;
    } else if (rule.descriptor.cut) {
      // Explicit cut (TODO_0309): dispatched by the search's cut choices
      // and the kernel's cut case, never by generic premise computation.
      spec._premiseType = 'cut';
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
  return specsFromMeta(meta, calculus.rules, calculus.theory, calculus.contextStructure || null);
}

/** Use precomputed meta if available, otherwise compute from scratch. */
function initRuleSpecs(calculus) {
  return calculus.ruleSpecMeta
    ? specsFromMeta(calculus.ruleSpecMeta, calculus.rules, calculus.theory, calculus.contextStructure || null)
    : buildRuleSpecs(calculus);
}

export { buildRuleSpecs, specMeta, initRuleSpecs };
export default { buildRuleSpecs, specMeta, initRuleSpecs };
