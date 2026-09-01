/**
 * L1 Kernel - Proof Verification
 *
 * Given a proof tree, verifies that each step is valid.
 * This is the trusted core: if verifyTree says "valid" with no
 * `unverified` entries, the proof is correct regardless of which strategy
 * built it.
 *
 * Does NOT search for proofs - only checks them.
 *
 * Two levels (round-15 F1):
 *   verifyStep — SHAPE ONLY: one rule application checked against its
 *     recomputed premises (subset comparison, no resource accounting).
 *   verifyTree — the full checker: rule shapes PLUS linear resource
 *     accounting. It re-threads the prover's lazy delta discipline —
 *     each recorded premise context must be the rule-introduced formulas
 *     plus a sub-multiset of the still-unconsumed pool; leftovers flow
 *     through siblings and the ROOT leftover must be empty. Both lazy
 *     (prover-recorded) and exact (hand-split) trees are accepted.
 *
 * Steps the kernel cannot re-derive are ACCEPTED but reported in
 * `unverified` (deduplicated reasons):
 *   'modeSwitch' — a bridge step (forward-engine execution); the settle/
 *     exec run is trusted, not re-checked. Callers claiming full
 *     verification must assert `valid && !unverified`.
 *   'binding'    — a quantifier step whose fresh eigenvariable cannot be
 *     re-generated hash-identically; premise contexts are matched up to
 *     unification, degraded to count checks when that fails.
 */

import { initRuleSpecs } from './rule-interpreter.js';
import Seq from '../kernel/sequent.js';
import Store from '../kernel/store.js';
import { unify } from '../kernel/unify.js';
import { isAtomic } from '../kernel/ast.js';
import Context from './context.js';
/**
 * Create a kernel verifier for a calculus
 * @param {Object} calculus - Loaded calculus with rules, polarity, etc.
 * @returns {{ verifyStep, verifyTree }}
 */
function createKernel(calculus) {
  const { specs, alternatives } = initRuleSpecs(calculus);
  const stepCheckers = calculus.stepCheckers || null;
  const ctxStruct = calculus.contextStructure || {
    zones: ['linear', 'cartesian'],
    copySource: 'cartesian',
    copyTarget: 'linear',
  };

  /**
   * Verify a single proof step — SHAPE ONLY.
   *
   * Single-step verification: the rule's recomputed premises must be
   * present in the recorded ones (subset). Resource tracking (all linear
   * formulas consumed exactly once) is verifyTree's job — a step checked
   * here in isolation can still leak context (e.g. id with leftovers).
   *
   * @param {Object} conclusion - The sequent being proved
   * @param {string} ruleName - Name of rule applied
   * @param {Object[]} premises - Child sequents (proof tree conclusions)
   * @returns {{ valid: boolean, error?: string }}
   */
  function verifyStep(conclusion, ruleName, premises, state, opts = {}) {
    // Identity axiom — check all context zones for a matching formula
    if (ruleName === 'id' || ruleName === 'id_+' || ruleName === 'id_-') {
      if (premises.length !== 0) {
        return { valid: false, error: `Identity expects 0 premises, got ${premises.length}` };
      }
      for (const zone of ctxStruct.zones) {
        const ctx = Seq.getContext(conclusion, zone);
        for (const h of ctx) {
          if (unify(h, conclusion.succedent)) return { valid: true };
        }
      }
      return { valid: false, error: 'Identity: no matching formula in context' };
    }

    // Copy from copySource to copyTarget
    if (ruleName === 'copy') {
      if (premises.length !== 1) {
        return { valid: false, error: `Copy expects 1 premise, got ${premises.length}` };
      }
      const source = Seq.getContext(conclusion, ctxStruct.copySource);
      if (source.length === 0) {
        return { valid: false, error: `Copy: no ${ctxStruct.copySource} context` };
      }
      // Premise should have an extra formula in copyTarget copied from copySource
      const premiseTarget = Seq.getContext(premises[0], ctxStruct.copyTarget);
      const conclusionTarget = Seq.getContext(conclusion, ctxStruct.copyTarget);
      if (premiseTarget.length !== conclusionTarget.length + 1) {
        return { valid: false, error: 'Copy: premise should have one more formula in target' };
      }
      const extra = premiseTarget.filter(h => !conclusionTarget.includes(h));
      if (extra.length === 0) {
        // Duplicate formula matching conclusion — the extra copy must come from
        // copySource (which can duplicate freely). Trust the structural match.
        return { valid: true };
      }
      const inSource = extra.some(h => source.includes(h));
      if (!inSource) {
        return { valid: false, error: `Copy: extra formula not from ${ctxStruct.copySource} context` };
      }
      return { valid: true };
    }

    // Mode switch — the computation right rule is where backward meets
    // forward. Dispatched via the modeShift descriptor flag (not the rule
    // name): monad_r in ILL, `<tag>_r` for any calculus's computation
    // connective, whose tag comes from the roles record.
    // Two verification levels depending on execution profile:
    //   termVerified=true ('guided' or 'full' with terms):
    //     rightFocus + rightFocusTerm succeeded → state.monadicTerm contains proof term.
    //     Returns evidence for check-term.js to recurse into (guided) or inspect (full).
    //   termVerified=false (default 'full' without terms):
    //     Returns unverified:'modeSwitch' — structural check only.
    //     The forward engine + rightFocus is trusted at this level.
    // Calculus-declared step checkers (P1 slot routing, TODO_0294): the
    // calculus binds rule names to custom checkers via
    // `calculus.stepCheckers` — the kernel knows nothing about their
    // content (the timed @fire checker lives in lib/prover/timed/).
    // Data-level here; resource threading is verifyTree's job.
    const custom = stepCheckers && stepCheckers[ruleName];
    if (custom) {
      const r = custom.step(conclusion, state, { calculus, program: opts.program || null });
      if (r.error) return { valid: false, error: `${ruleName}: ${r.error}` };
      return { valid: true };
    }

    const spec = specs[ruleName];
    if (spec && spec.modeShift) {
      const compTag = calculus.roles?.computation?.tag || 'monad';
      if (!conclusion.succedent || !Store.isTerm(conclusion.succedent) ||
          Store.tag(conclusion.succedent) !== compTag) {
        return { valid: false, error: `${ruleName}: succedent is not monadic` };
      }
      if (state && state.termVerified) {
        return { valid: true, evidence: state.monadicTerm || null };
      }
      return { valid: true, unverified: 'modeSwitch', evidence: null };
    }

    if (!spec) {
      return { valid: false, error: `Unknown rule: ${ruleName}` };
    }

    // Find the principal formula and apply the rule
    const linear = Seq.getContext(conclusion, 'linear');
    const succedent = conclusion.succedent;

    // Determine position from rule name
    const side = ruleName.endsWith('_r') || ruleName.match(/_r\d+$/) ? 'R' : 'L';

    // Check the rule against one principal-formula candidate: recompute the
    // expected premises and compare with the recorded ones.
    // For context-splitting rules, the actual premises may have delta
    // distributed — we check that succedents match and that produced
    // formulas are present.
    const checkWith = (formula, index) => {
      if (!formula || isAtomic(formula)) {
        return { valid: false, error: `Rule ${ruleName}: principal formula is atomic` };
      }

      const expectedPremises = spec.makePremises(formula, conclusion, index);
      if (!expectedPremises) {
        return { valid: false, error: `Rule ${ruleName}: makePremises returned null` };
      }

      if (expectedPremises.length !== premises.length) {
        return { valid: false, error: `Rule ${ruleName}: expected ${expectedPremises.length} premises, got ${premises.length}` };
      }

      for (let i = 0; i < expectedPremises.length; i++) {
        const expected = expectedPremises[i];
        const actual = premises[i];

        // Succedent must match
        if (expected.succedent !== actual.succedent) {
          return { valid: false, error: `Rule ${ruleName}: premise ${i} succedent mismatch` };
        }

        // Expected linear formulas must be present in actual
        const expectedLinear = Seq.getContext(expected, 'linear');
        const actualLinear = Seq.getContext(actual, 'linear');
        for (const h of expectedLinear) {
          if (!actualLinear.includes(h)) {
            return { valid: false, error: `Rule ${ruleName}: premise ${i} missing expected formula` };
          }
        }
      }

      return { valid: true };
    };

    if (side === 'R') {
      return checkWith(succedent, -1);
    }

    // Left rule: any context formula with the rule's connective tag is a
    // candidate — the step is valid if SOME candidate reproduces the
    // recorded premises (the tag alone can be ambiguous: two bang formulas,
    // dereliction vs absorption keyed under one connective, ...).
    const connMatch = ruleName.match(/^(.+)_l\d?$/);
    const connective = connMatch ? connMatch[1] : null;

    let firstFailure = null;
    for (let i = 0; i < linear.length; i++) {
      if (Store.tag(linear[i]) !== connective) continue;
      const r = checkWith(linear[i], i);
      if (r.valid) return r;
      if (!firstFailure) firstFailure = r;
    }
    return firstFailure ||
      { valid: false, error: `Rule ${ruleName}: no matching formula in context` };
  }

  /**
   * Verify an entire proof tree (recursive) WITH linear resource
   * accounting (round-15 F1).
   *
   * Discipline: walk(node) returns the LEFTOVER multiset — the part of the
   * node's recorded linear context its subtree did not consume — or null
   * on error. The prover records contexts lazily (a premise carries the
   * rule-introduced formulas PLUS the not-yet-consumed pool; leftovers
   * flow to the next sibling), so per-step multiset equality is
   * impossible; instead each premise context is decomposed as
   * intro ⊎ D with D a sub-multiset of the current pool, and the pool
   * threads pool' = (pool − D) ⊎ walk(child). Exact (hand-split) trees
   * are the D = exact-split special case. The ROOT leftover must be empty
   * — this is what rejects forged proofs like `a ⊗ b ⊢ a`.
   *
   * @param {Object} tree - ProofTree node
   * @returns {{ valid: boolean, errors: string[], unverified?: string[] }}
   *   `unverified` lists reasons ('modeSwitch', 'binding') for steps that
   *   were accepted without full re-derivation — see the header comment.
   */
  function verifyTree(tree, opts = {}) {
    const errors = [];
    const unverified = new Set();
    const idRules = new Set(['id', 'id_+', 'id_-']);

    // Remove the intro formulas from a recorded premise context.
    // Exact hash first; unify fallback (metavar witnesses from binding
    // rules). Returns the remaining multiset (= the delta the premise
    // carried) or null if an intro formula is missing.
    const subtractIntro = (ctx, intro) => {
      let rest = ctx;
      for (const e of intro) {
        if (Context.has(rest, e)) { rest = Context.remove(rest, e); continue; }
        let matched = null;
        for (const c of Context.toArray(rest)) {
          if (unify(e, c)) { matched = c; break; }
        }
        if (matched === null) return null;
        rest = Context.remove(rest, matched);
      }
      return rest;
    };

    // Try to verify one (principal candidate, spec) at this node, given
    // the precomputed child leftovers. Returns { leftover } or { error }.
    // Pure — pushes nothing, so the candidate loop can backtrack.
    const tryCandidate = (node, spec, formula, index, ctxL, side, childLeftovers) => {
      const seq = node.conclusion;
      const expected = spec.makePremises(formula, seq, index);
      if (!expected) {
        return { error: `Rule ${node.rule}: makePremises returned null` };
      }
      if (expected.length !== node.premises.length) {
        return { error: `Rule ${node.rule}: expected ${expected.length} premises, got ${node.premises.length}` };
      }

      let pool = side === 'L' ? Context.remove(ctxL, formula) : ctxL;
      if (pool === null) return { error: `Rule ${node.rule}: principal not in context` };
      if (spec.requiresEmptyDelta && !Context.isEmpty(pool)) {
        return { error: `Rule ${node.rule}: context must be empty (promotion-style rule)` };
      }
      if (spec.discardsContext) {
        // zero_l-style: consumes the principal and discards the rest
        return { leftover: Context.empty() };
      }
      if (expected.length === 0) {
        // zero-premise: left consumes only its principal (template axioms
        // like at_l), right consumes nothing — leftover threads on
        return { leftover: pool };
      }

      // Standard binding rules AND template eigenvariable rules (TODO_0298:
      // superpose_l) generate fresh variables the kernel cannot reproduce
      // hash-identically; witness-mode templates re-derive deterministically
      // and get no such degradation.
      const isBinding = !!spec._descriptor?.binding ||
        spec._bindingMode === 'eigenvariable' || spec._bindingMode === 'metavar';
      const branchInfo = [];                 // copyContext: [D, L] per child
      for (let i = 0; i < expected.length; i++) {
        const child = node.premises[i];
        const exp = expected[i];
        const succOk = exp.succedent === child.conclusion.succedent ||
          !!unify(exp.succedent, child.conclusion.succedent);
        if (!succOk) return { error: `Rule ${node.rule}: premise ${i} succedent mismatch` };

        const ci = Context.fromArray(Seq.getContext(child.conclusion, 'linear'));
        const intro = Seq.getContext(exp, 'linear');
        let di = subtractIntro(ci, intro);
        if (di === null) {
          if (!isBinding) return { error: `Rule ${node.rule}: premise ${i} missing expected formula` };
          // fresh eigenvariables cannot be re-generated hash-identically:
          // degrade to a count check (|ctx| ≥ |intro|) and take the pool
          // intersection as the carried delta
          if (Context.size(ci) < intro.length) {
            return { error: `Rule ${node.rule}: premise ${i} context too small` };
          }
          const notInCi = Context.subtract(pool, ci);
          di = notInCi === null ? pool : Context.subtract(pool, notInCi);
          unverified.add('binding');
        }
        if (!Context.contains(pool, di)) {
          return { error: `Rule ${node.rule}: premise ${i} carries formulas not in the available context` };
        }
        const li = childLeftovers[i];
        if (spec.copyContext) branchInfo.push([di, li]);
        else pool = Context.merge(Context.subtract(pool, di), li);
      }

      if (spec.copyContext) {
        // Additive: every branch sees the SAME delta and must leave the
        // SAME leftover (the with_r soundness condition, kernel-side)
        const [d0, l0] = branchInfo[0];
        for (let i = 1; i < branchInfo.length; i++) {
          if (!Context.eq(branchInfo[i][0], d0)) {
            return { error: `Rule ${node.rule}: additive branches carry different contexts` };
          }
          if (!Context.eq(branchInfo[i][1], l0)) {
            return { error: `Rule ${node.rule}: additive branches consume different resources` };
          }
        }
        pool = Context.merge(Context.subtract(pool, d0), l0);
      }
      return { leftover: pool };
    };

    // walk returns the leftover multiset, or null (error already pushed)
    function walk(node) {
      if (!node.rule) {
        errors.push('Unproven goal found');
        return null;
      }
      const seq = node.conclusion;
      const linearArr = Seq.getContext(seq, 'linear');
      const ctxL = Context.fromArray(linearArr);
      const rule = node.rule;

      // Identity: consumes exactly one linear formula (or none, when the
      // match lives in a reusable zone)
      if (idRules.has(rule)) {
        if (node.premises.length !== 0) {
          errors.push(`At rule ${rule}: Identity expects 0 premises, got ${node.premises.length}`);
          return null;
        }
        if (Context.has(ctxL, seq.succedent)) return Context.remove(ctxL, seq.succedent);
        for (const h of linearArr) {
          if (unify(h, seq.succedent)) return Context.remove(ctxL, h);
        }
        for (const zone of ctxStruct.zones) {
          if (zone === 'linear') continue;
          for (const h of Seq.getContext(seq, zone)) {
            if (unify(h, seq.succedent)) return ctxL;   // reusable: no linear consumption
          }
        }
        errors.push(`At rule ${rule}: Identity: no matching formula in context`);
        return null;
      }

      // Recurse FIRST — child verification is independent of which
      // principal candidate the step check settles on
      const childLeftovers = node.premises.map(walk);
      if (childLeftovers.some(l => l === null)) return null;

      // Calculus-declared step checkers (P1 slot routing, TODO_0294):
      // full re-derivation with resource threading — never enters
      // `unverified`; the kernel only routes the binding
      const custom = stepCheckers && stepCheckers[rule];
      if (custom) {
        const r = custom.tree(node, childLeftovers, { calculus, program: opts.program || null });
        if (r.error) { errors.push(`At rule ${rule}: ${r.error}`); return null; }
        return r.leftover;
      }

      const spec = specs[rule];
      if (!spec) {
        errors.push(`At rule ${rule}: Unknown rule: ${rule}`);
        return null;
      }

      // Mode switch: structural check only — the forward run is trusted
      // and flagged; the bridge consumed the entire linear context
      if (spec.modeShift) {
        const compTag = calculus.roles?.computation?.tag || 'monad';
        if (!seq.succedent || !Store.isTerm(seq.succedent) ||
            Store.tag(seq.succedent) !== compTag) {
          errors.push(`At rule ${rule}: succedent is not monadic`);
          return null;
        }
        if (!(node.state && node.state.termVerified)) unverified.add('modeSwitch');
        return Context.empty();
      }

      // Copy: premise context = conclusion linear ⊎ one copySource formula
      if (rule === 'copy') {
        if (node.premises.length !== 1) {
          errors.push(`At rule copy: Copy expects 1 premise, got ${node.premises.length}`);
          return null;
        }
        const source = Seq.getContext(seq, ctxStruct.copySource);
        if (source.length === 0) {
          errors.push(`At rule copy: no ${ctxStruct.copySource} context`);
          return null;
        }
        const ci = Context.fromArray(Seq.getContext(node.premises[0].conclusion, ctxStruct.copyTarget));
        for (const c of source) {
          if (!Context.eq(ci, Context.add(ctxL, c))) continue;
          // leftover of an unconsumed copy is weakenable (it came from the
          // reusable zone) — drop up to one occurrence
          const l0 = childLeftovers[0];
          return Context.has(l0, c) ? Context.remove(l0, c) : l0;
        }
        errors.push('At rule copy: premise context is not conclusion + one copied formula');
        return null;
      }

      // Generic rules: find the principal, thread the pool
      const side = rule.endsWith('_r') || /_r\d+$/.test(rule) ? 'R' : 'L';
      let firstError = null;
      if (side === 'R') {
        const r = tryCandidate(node, spec, seq.succedent, -1, ctxL, 'R', childLeftovers);
        if (r.leftover !== undefined) return r.leftover;
        firstError = r.error;
      } else {
        const connMatch = rule.match(/^(.+)_l\d?$/);
        const connective = connMatch ? connMatch[1] : null;
        const tried = new Set();
        for (let i = 0; i < linearArr.length; i++) {
          const h = linearArr[i];
          if (tried.has(h) || Store.tag(h) !== connective) continue;
          tried.add(h);
          const r = tryCandidate(node, spec, h, i, ctxL, 'L', childLeftovers);
          if (r.leftover !== undefined) return r.leftover;
          if (!firstError) firstError = r.error;
        }
      }
      errors.push(`At rule ${rule}: ${firstError || 'no matching formula in context'}`);
      return null;
    }

    const leftover = walk(tree);
    if (leftover !== null && !Context.isEmpty(leftover)) {
      errors.push(`Root: ${Context.size(leftover)} linear resource(s) unconsumed`);
    }
    const result = { valid: errors.length === 0, errors };
    if (unverified.size > 0) result.unverified = [...unverified].sort();
    return result;
  }

  return { verifyStep, verifyTree };
}

export { createKernel };
export default { createKernel };
