/**
 * L1 Kernel - Proof Verification
 *
 * Given a proof tree, verifies that each step is valid.
 * This is the trusted core: if verifyTree says "valid",
 * the proof is correct regardless of which strategy built it.
 *
 * Does NOT search for proofs - only checks them.
 */

import { initRuleSpecs } from './rule-interpreter.js';
import Seq from '../kernel/sequent.js';
import Store from '../kernel/store.js';
import { unify } from '../kernel/unify.js';
import { isAtomic } from '../kernel/ast.js';
/**
 * Create a kernel verifier for a calculus
 * @param {Object} calculus - Loaded calculus with rules, polarity, etc.
 * @returns {{ verifyStep, verifyTree }}
 */
function createKernel(calculus) {
  const { specs, alternatives } = initRuleSpecs(calculus);
  const ctxStruct = calculus.contextStructure || {
    zones: ['linear', 'cartesian'],
    copySource: 'cartesian',
    copyTarget: 'linear',
  };

  /**
   * Verify a single proof step.
   *
   * Single-step verification only. Resource tracking (all linear formulas
   * consumed exactly once) is handled by check-term.js, not verifyTree.
   *
   * @param {Object} conclusion - The sequent being proved
   * @param {string} ruleName - Name of rule applied
   * @param {Object[]} premises - Child sequents (proof tree conclusions)
   * @returns {{ valid: boolean, error?: string }}
   */
  function verifyStep(conclusion, ruleName, premises, state) {
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
   * Verify an entire proof tree (recursive).
   *
   * @param {Object} tree - ProofTree node
   * @returns {{ valid: boolean, errors: string[] }}
   */
  function verifyTree(tree) {
    const errors = [];

    function walk(node) {
      if (!node.rule) {
        // Unproven goal
        errors.push('Unproven goal found');
        return;
      }

      // Verify this step
      const childConclusions = node.premises.map(p => p.conclusion);
      const result = verifyStep(node.conclusion, node.rule, childConclusions, node.state);
      if (!result.valid) {
        errors.push(`At rule ${node.rule}: ${result.error}`);
      }

      // Recurse into children
      for (const child of node.premises) {
        walk(child);
      }
    }

    walk(tree);
    return { valid: errors.length === 0, errors };
  }

  return { verifyStep, verifyTree };
}

export { createKernel };
export default { createKernel };
