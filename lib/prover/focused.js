/**
 * L3 Focused Prover (Andreoli's focusing discipline)
 *
 * Imports generic search primitives from L2 (generic.js).
 * Contains ONLY focusing-specific logic:
 * - findInvertible: find formula with invertible rule
 * - chooseFocus: choose formula to focus on
 * - prove: focused proof search with inversion/focus/blur phases
 */

import { ProofTree, leaf } from './pt.js';
import { FocusedProofState, inversion, focus } from './state.js';
import Context from './context.js';
import Seq from '../kernel/sequent.js';
import Store from '../kernel/store.js';
import { unify } from '../kernel/unify.js';
import { isAtomic } from '../kernel/ast.js';
import { createGenericProver } from './generic.js';
import bridge from './bridge.js';
import { MetaCtx } from './meta-ctx.js';
import { checkCyclicProof } from './gtc-check.js';
/**
 * Create a focused prover for a calculus
 * @param {Object} calculus - Loaded calculus with polarity, rules, etc.
 */
function createProver(calculus) {
  // Zone names from the calculus's declared structure (TODO_0086):
  // CZ = consumable zone, SZ = copy-source zone (reusable).
  const ctxStruct = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const SZ = ctxStruct.copySource;
  const generic = createGenericProver(calculus);

  // Re-export L2 helpers for backward compatibility
  const { connective, isPositive, isNegative, ruleName, ruleIsInvertible,
          tryIdentity, applyRule, childDelta, addDelta, pool } = generic;

  // =========================================================================
  // L3: Focusing-specific logic
  // =========================================================================

  /**
   * Find invertible formula (returns { position, index, formula } or null)
   */
  const findInvertible = (seq) => {
    // Check succedent (right)
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = Store.tag(seq.succedent);
      if (ruleIsInvertible(tag, 'r')) {
        return { position: 'R', index: -1, formula: seq.succedent };
      }
    }

    // Check consumable zones (left) — union pool, TODO_0285
    const linear = pool(seq);
    for (let i = 0; i < linear.length; i++) {
      const h = linear[i];
      if (!isAtomic(h)) {
        const tag = Store.tag(h);
        if (ruleIsInvertible(tag, 'l')) {
          return { position: 'L', index: i, formula: h };
        }
      }
    }

    return null;
  };

  /**
   * Choose focus targets. Left formulas whose tag has an @affine
   * weakening rule additionally get a LAST-RESORT affine choice
   * (affine: true): the affine rule is excluded from the normal focus
   * alternatives and tried only after every ordinary choice fails —
   * weakening must never preempt a consumer (a greedy ghost would steal
   * a token a later sibling needs, and committed premise search never
   * revisits; TODO_0298).
   */
  const chooseFocus = (seq, affine = null) => {
    const choices = [];

    // Right focus: positive, or non-invertible negative
    if (seq.succedent && !isAtomic(seq.succedent)) {
      const tag = Store.tag(seq.succedent);
      if (isPositive(tag) || !ruleIsInvertible(tag, 'r')) {
        choices.push({ position: 'R', formula: seq.succedent });
      }
    } else if (seq.succedent && isAtomic(seq.succedent)) {
      choices.push({ position: 'R', formula: seq.succedent });
    }

    // Left focus: negative, or non-invertible positive (union pool)
    const linear = pool(seq);
    for (let i = 0; i < linear.length; i++) {
      const h = linear[i];
      if (!isAtomic(h)) {
        const tag = Store.tag(h);
        if (isNegative(tag) || !ruleIsInvertible(tag, 'l')) {
          choices.push({
            position: 'L',
            index: i,
            hash: h,
            formula: h
          });
        }
      }
    }

    choices.reverse();

    // Last-resort affine choices (appended after every normal choice)
    if (affine) {
      for (let i = 0; i < linear.length; i++) {
        const h = linear[i];
        if (!isAtomic(h) && affine.has(Store.tag(h))) {
          choices.push({ position: 'L', index: i, hash: h, formula: h, affine: true });
        }
      }
    }

    return choices;
  };

  /**
   * Affine boundary discharge (TODO_0298, THY_0027 §3h/§5): a calculus
   * may declare a pure-weakening rule `@affine` (will's ghost on drawn
   * tokens). Committed premise search cannot decide token consumption
   * locally — a branch cannot know whether a later sibling needs the
   * token — so tokens thread lazily and are discharged by INSERTING the
   * affine rule exactly at the two places where leftovers die:
   *   - the proof root (globally-unused tokens), and
   *   - additive (copyContext) branch balancing — "a branch that draws
   *     less discharges the surplus by ghost".
   * The insertion rewrites the recorded lazy conclusions (stripToken
   * removes the carried occurrence below the inserted node), so the
   * kernel verifies the repaired tree with no special cases.
   *
   * Memoized per rules object: the map depends only on the (fixed) rule
   * table, and recomputing it per prove() call dominated µs-scale proofs
   * (measured 83% of the identity benchmark, audit 2026-09-02).
   */
  const _affineCache = new WeakMap();
  const affineRules = (ruleSpecs) => {
    let map = _affineCache.get(ruleSpecs);
    if (map !== undefined) return map;
    map = null;
    for (const [name, spec] of Object.entries(ruleSpecs)) {
      if (!spec.affine) continue;
      const m = name.match(/^(.+)_l\d*$/);
      if (!m) continue;
      if (!map) map = new Map();
      map.set(m[1], name);
    }
    _affineCache.set(ruleSpecs, map);
    return map;
  };

  // Multiset intersection of two sorted contexts (min counts).
  const intersectDelta = (a, b) => {
    const out = [];
    let i = 0, j = 0;
    while (i < a.length && j < b.length) {
      if (a[i] === b[j]) { out.push(a[i]); i++; j++; }
      else if (a[i] < b[j]) i++;
      else j++;
    }
    return Context.fromArray(out);
  };

  const stripToken = (tree, token) => {
    // Route to the token's consumable zone (the wrapper tag decides the
    // column; spread preserves all other columns — TODO_0285).
    const zone = Seq.routeZone(ctxStruct, token);
    const lin = Seq.getContext(tree.conclusion, zone);
    const i = lin.indexOf(token);
    if (i < 0) return tree;
    const conclusion = Seq.seq({
      ...tree.conclusion.contexts,
      [zone]: [...lin.slice(0, i), ...lin.slice(i + 1)],
    }, tree.conclusion.succedent);
    return new ProofTree({
      conclusion,
      premises: tree.premises.map(p => stripToken(p, token)),
      rule: tree.rule,
      proven: tree.proven,
      state: tree.state,
    });
  };

  const dischargeAffine = (tree, delta, affine) => {
    if (!affine) return null;
    let out = tree;
    for (const token of Context.toArray(delta)) {
      const rName = affine.get(Store.tag(token));
      if (!rName) return null;
      out = new ProofTree({
        conclusion: out.conclusion,
        premises: [stripToken(out, token)],
        rule: rName,
        proven: true,
        state: null,
      });
    }
    return out;
  };

  /**
   * Apply a rule and recurse into premises.
   *
   * mc (MetaCtx) is passed explicitly because applyAndRecurse is defined at the
   * createProver level (not inside prove()), so it can't access mc via closure.
   * search() accesses mc via closure from prove().
   *
   * The conclusion sequent is resolved via mc.resolveSeq only when mc.hasBindings()
   * is true — this guard avoids the O(contexts × term_size) cost for the common
   * case of ground proofs (no metavars).
   */
  const applyAndRecurse = (seq, rName, spec, position, index, state, searchFn, depth, delta, opts, mc, affine) => {
    // Mode switch: monad_r bypasses standard premise computation
    if (spec.modeShift) {
      const engineCalc = opts?.engineCalc || null;
      const switchResult = bridge.modeSwitch(seq, engineCalc, opts, rName, calculus);
      if (!switchResult) return null;
      return {
        proofTree: switchResult.proofNode,
        delta_out: Context.empty()
      };
    }

    const result = applyRule(seq, position, index, spec);
    if (!result?.success) return null;

    const childResults = [];
    let currentDelta = result.delta_remaining;
    let allSuccess = true;

    for (const premise of result.premises) {
      const cDelta = childDelta(premise, currentDelta);
      const premiseWithDelta = addDelta(premise, currentDelta, spec.copyContext);
      const childResult = searchFn(premiseWithDelta, inversion(), depth + 1, cDelta);

      if (!childResult) {
        allSuccess = false;
        break;
      }

      childResults.push(childResult);
      if (!spec.copyContext) {
        currentDelta = childResult.delta_out;
      }
    }

    if (!allSuccess) return null;

    let finalDelta;
    if (spec.discardsContext) {
      // zero_l and similar: discard all remaining linear resources
      finalDelta = Context.empty();
    } else if (spec.copyContext && childResults.length > 0) {
      // Additive rules copy the context to every branch — soundness
      // requires every branch to consume the SAME multiset, i.e. all
      // leftover deltas agree (otherwise `a, b |- (a * b) & a` would be
      // provable by silently discarding b in the second branch).
      // Committed premise search means a branch is not re-derived with a
      // different consumption when the leftovers disagree — sound, with a
      // known completeness corner. EXCEPTION (TODO_0298): when the
      // branches differ only by @affine-dischargeable leftovers (drawn
      // tokens), the lighter branches are ghost-balanced in place —
      // THY_0027 §3h, additive lockstep by sharing plus ghost.
      finalDelta = childResults[0].delta_out;
      let balanced = null;
      for (let i = 1; i < childResults.length; i++) {
        if (!Context.eq(childResults[i].delta_out, finalDelta)) {
          if (!affine) return null;
          balanced = true;
          finalDelta = intersectDelta(finalDelta, childResults[i].delta_out);
        }
      }
      if (balanced) {
        for (const cr of childResults) {
          const surplus = Context.subtract(cr.delta_out, finalDelta);
          if (Context.isEmpty(surplus)) continue;
          const wrapped = dischargeAffine(cr.proofTree, surplus, affine);
          if (!wrapped) return null;
          cr.proofTree = wrapped;
          cr.delta_out = finalDelta;
        }
      }
    } else {
      finalDelta = currentDelta;
    }

    return {
      proofTree: new ProofTree({
        conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
        premises: childResults.map(r => r.proofTree),
        rule: rName,
        proven: true,
        state: state.copy()
      }),
      delta_out: finalDelta
    };
  };

  /**
   * Cut-formula candidates (TODO_0309): the PROPER subformula closure of
   * the sequent, minus pool members (cutting on a present formula only
   * shuffles it) and the succedent itself (a cut concluding the goal
   * from the goal loops). Formula-ness is decided by the calculus table:
   * a connective with declared polarity, or an atom — grade slots and
   * other non-formula subterms never qualify. The SAX subformula
   * property (FSCD 2020 Thm. 7) is what makes this candidate set
   * complete for snip search.
   */
  const cutCandidates = (pool0, succ) => {
    const excluded = new Set(pool0);
    if (succ != null) excluded.add(succ);
    const out = new Set();
    const walk = (h) => {
      if (!Store.isTerm(h)) return;
      const a = Store.arity(h);
      for (let i = 0; i < a; i++) {
        const c = Store.child(h, i);
        if (!Store.isTermChild(c)) continue;
        const ct = Store.tag(c);
        const isFormula = ct === 'atom' || calculus.polarity?.[ct] !== undefined;
        if (isFormula && !excluded.has(c)) out.add(c);
        walk(c);
      }
    };
    for (const h of pool0) walk(h);
    if (succ != null) walk(succ);
    return out;
  };

  /**
   * Apply the explicit cut rule with cut formula X — the no-principal
   * analogue of applyAndRecurse: premise 1 derives X from a share of the
   * pool, premise 2 consumes X to derive the succedent; delta threads
   * producer → consumer exactly as in a context-splitting rule.
   */
  const applyCut = (seq, X, state, searchFn, depth, mc) => {
    const premises = [
      Seq.seq(Seq.routeContexts(ctxStruct, []), X),
      Seq.seq(Seq.routeContexts(ctxStruct, [X]), seq.succedent),
    ];
    const childResults = [];
    let currentDelta = Context.fromArray(pool(seq));
    for (const premise of premises) {
      const cDelta = childDelta(premise, currentDelta);
      const premiseWithDelta = addDelta(premise, currentDelta);
      const childResult = searchFn(premiseWithDelta, inversion(), depth + 1, cDelta);
      if (!childResult) return null;
      childResults.push(childResult);
      currentDelta = childResult.delta_out;
    }
    return {
      proofTree: new ProofTree({
        conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
        premises: childResults.map(r => r.proofTree),
        rule: 'cut',
        proven: true,
        state: state.copy(),
      }),
      delta_out: currentDelta,
    };
  };

  // ==========================================================================
  // Exhaustive (backtracking) variant — opt-in via opts.exhaustive.
  //
  // The committed search above returns the FIRST locally-successful result at
  // every choice point (`if (result) return result`). That is fast and sound,
  // but incomplete for the additive don't-know nondeterminism under a linear
  // resource constraint: choosing `with_l1` can succeed locally while leaving a
  // leftover that only fails the emptiness check at the root — by which point
  // every choice has committed and `with_l2` is never tried (THY_0042 §4, the
  // `a & I ⊢ I` / weakening `!a ⊢ I` corner). The documented committed-choice
  // corner at applyAndRecurse's copyContext branch is the same phenomenon.
  //
  // The fix is genuine backtracking via a success continuation `sk`: every
  // candidate result is offered to `sk`, which either accepts it (returns a
  // final answer) or rejects it (returns null) — driving the enclosing choice
  // loop to its next alternative. At the root, `sk` requires an empty linear
  // pool, so that global constraint now flows back into `with_l1`/`with_l2`.
  //
  // This is a SEPARATE driver: the committed path (searchCore/applyAndRecurse)
  // is left untouched, so the ILL/EVM proof path is byte-identical and pays
  // nothing. Soundness is unchanged — the returned tree is still kernel- and
  // GTC-verified post-hoc; `sk` only reorders which proofs the search finds.
  // The K helpers below mirror applyAndRecurse/applyCut in continuation form.
  // ==========================================================================

  const applyAndRecurseK = (seq, rName, spec, position, index, state, searchFn, depth, delta, opts, mc, affine, sk) => {
    if (spec.modeShift) {
      const engineCalc = opts?.engineCalc || null;
      const switchResult = bridge.modeSwitch(seq, engineCalc, opts, rName, calculus);
      if (!switchResult) return null;
      return sk({ proofTree: switchResult.proofNode, delta_out: Context.empty() });
    }

    const result = applyRule(seq, position, index, spec);
    if (!result?.success) return null;
    const premises = result.premises;

    // Assemble the finished node from all child results and offer it to sk.
    const finish = (childResults, currentDelta) => {
      let finalDelta;
      let finalChildren = childResults;
      if (spec.discardsContext) {
        finalDelta = Context.empty();
      } else if (spec.copyContext && childResults.length > 0) {
        // Additive: every branch must consume the same multiset; @affine
        // leftovers may be ghost-balanced (THY_0027 §3h). Clone before any
        // balancing mutation so a rejected path never leaks into a retry.
        finalDelta = childResults[0].delta_out;
        let balanced = false;
        for (let i = 1; i < childResults.length; i++) {
          if (!Context.eq(childResults[i].delta_out, finalDelta)) {
            if (!affine) return null;
            balanced = true;
            finalDelta = intersectDelta(finalDelta, childResults[i].delta_out);
          }
        }
        if (balanced) {
          finalChildren = childResults.map(cr => ({ ...cr }));
          for (const cr of finalChildren) {
            const surplus = Context.subtract(cr.delta_out, finalDelta);
            if (Context.isEmpty(surplus)) continue;
            const wrapped = dischargeAffine(cr.proofTree, surplus, affine);
            if (!wrapped) return null;
            cr.proofTree = wrapped;
            cr.delta_out = finalDelta;
          }
        }
      } else {
        finalDelta = currentDelta;
      }
      return sk({
        proofTree: new ProofTree({
          conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
          premises: finalChildren.map(r => r.proofTree),
          rule: rName,
          proven: true,
          state: state.copy(),
        }),
        delta_out: finalDelta,
      });
    };

    // Thread premises left-to-right; each premise is searched with a
    // continuation that carries the leftover to the next premise. On a reject
    // deep down, searchFn backtracks INTO an earlier premise's own choices.
    const go = (i, currentDelta, acc) => {
      if (i === premises.length) return finish(acc, currentDelta);
      const premise = premises[i];
      const cDelta = childDelta(premise, currentDelta);
      const premiseWithDelta = addDelta(premise, currentDelta, spec.copyContext);
      return searchFn(premiseWithDelta, inversion(), depth + 1, cDelta, (childResult) => {
        const nextDelta = spec.copyContext ? currentDelta : childResult.delta_out;
        return go(i + 1, nextDelta, [...acc, childResult]);
      });
    };
    return go(0, result.delta_remaining, []);
  };

  const applyCutK = (seq, X, state, searchFn, depth, mc, sk) => {
    const premises = [
      Seq.seq(Seq.routeContexts(ctxStruct, []), X),
      Seq.seq(Seq.routeContexts(ctxStruct, [X]), seq.succedent),
    ];
    const go = (i, currentDelta, acc) => {
      if (i === premises.length) {
        return sk({
          proofTree: new ProofTree({
            conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
            premises: acc.map(r => r.proofTree),
            rule: 'cut',
            proven: true,
            state: state.copy(),
          }),
          delta_out: currentDelta,
        });
      }
      const premise = premises[i];
      const cDelta = childDelta(premise, currentDelta);
      const premiseWithDelta = addDelta(premise, currentDelta);
      return searchFn(premiseWithDelta, inversion(), depth + 1, cDelta, (childResult) =>
        go(i + 1, childResult.delta_out, [...acc, childResult]));
    };
    return go(0, Context.fromArray(pool(seq)), []);
  };

  /**
   * Main proof search (focused discipline)
   */
  const prove = (seq, opts = {}) => {
    const ruleSpecs = opts.rules || {};
    const ruleAlternatives = opts.alternatives || {};
    const maxDepth = opts.maxDepth || 100;
    const mc = new MetaCtx();
    // @affine boundary discharge (null for calculi without such rules —
    // zero behavioral delta)
    const affine = affineRules(ruleSpecs);
    // Explicit-cut search (TODO_0309): active only when the calculus
    // declares a cut rule. cutSeen is the path-scoped loop guard — each
    // sequent hash opens at most one cut layer per search path.
    const cutSpec = ruleSpecs.cut && ruleSpecs.cut._premiseType === 'cut'
      ? ruleSpecs.cut : null;
    const cutSeen = cutSpec ? new Set() : null;

    // Proof search follows Andreoli's focusing discipline:
    //   Pre-focusing:  try axioms (identity, copy)
    //   Inversion:     eagerly apply invertible rules (Phase 1)
    //   Focus:         choose a formula to focus on (Phase 2)
    //   Decomposition: apply non-invertible rule to focused formula (Phase 3)
    //   Blur:          when focused formula becomes invertible, return to inversion
    //
    // mc.save()/restore() wraps every choice point (focus loop, rule alternatives).
    // Inversion has no save/restore: if it fails, the failure propagates to the
    // caller's save/restore. Single-path, no branching within inversion.

    const searchCore = (seq, state, depth, delta) => {
      if (depth > maxDepth) return null;

      // Axiom: identity (A ⊢ A) — not part of focusing, checked first
      const idResult = tryIdentity(seq, 'R', -1);
      if (idResult?.success && Context.isEmpty(idResult.delta_out)) {
        mc.absorbTheta(idResult.theta);
        return {
          proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, 'id'),
          delta_out: idResult.delta_out
        };
      }

      // Axiom: copy from the copy-source zone — structural rule, pre-focusing
      const cart = Seq.getContext(seq, SZ);
      if (cart.length > 0 && Context.isEmpty(delta) && ruleSpecs.copy) {
        for (let i = 0; i < cart.length; i++) {
          const cartFormula = cart[i];
          const theta = unify(cartFormula, seq.succedent);
          if (theta) {
            const mark = mc.save();
            const newLinear = [cartFormula];
            // Copy targets the copied formula's own zone (wrapper-routed);
            // other consumable columns are empty here (delta is empty —
            // everything consumable is already consumed). TODO_0285.
            const premise = Seq.seq({
              ...Seq.routeContexts(ctxStruct, newLinear),
              [SZ]: cart,
            }, seq.succedent);
            const premiseDelta = Context.fromArray(newLinear);

            const childResult = search(premise, inversion(), depth + 1, premiseDelta);
            if (childResult) {
              return {
                proofTree: new ProofTree({
                  conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
                  premises: [childResult.proofTree],
                  rule: 'copy',
                  proven: true,
                  state: state.copy()
                }),
                delta_out: Context.empty()
              };
            }
            mc.restore(mark);
          }
        }
      }

      // Focusing Phase 1 — Inversion: apply invertible rules eagerly
      const inv = findInvertible(seq);
      if (inv) {
        const rName = ruleName(inv.formula, inv.position === 'R' ? 'r' : 'l');
        const spec = ruleSpecs[rName];

        if (spec) {
          const mark = mc.save();
          const result = applyAndRecurse(seq, rName, spec, inv.position, inv.index, state, search, depth, delta, opts, mc, affine);
          if (result) return result;
          mc.restore(mark);
        }
      }

      // Focusing Phase 2 — Focus: choose formula to enter focused phase
      if (state.isInversion()) {
        const choices = chooseFocus(seq, affine);

        for (const choice of choices) {
          const mark = mc.save();
          const newState = focus(choice.position, choice.hash);
          if (choice.affine) newState.affineOnly = true;
          const result = search(seq, newState, depth + 1, delta);
          if (result) return result;
          mc.restore(mark);
        }

        // Cut/snip choices (TODO_0309) — LAST resort, after every
        // ordinary focus choice failed: try each proper subformula as a
        // cut formula. Snip-bounded search is the SAX completeness
        // discipline (cut-free-with-snips, FSCD Thm. 5-7); the path
        // guard keeps a sequent from re-cutting inside its own cut.
        if (cutSpec && depth < maxDepth) {
          const key = Seq.hash(seq);
          if (!cutSeen.has(key)) {
            cutSeen.add(key);
            try {
              for (const X of cutCandidates(pool(seq), seq.succedent)) {
                const mark = mc.save();
                const result = applyCut(seq, X, state, search, depth, mc);
                if (result) return result;
                mc.restore(mark);
              }
            } finally {
              cutSeen.delete(key);
            }
          }
        }
      }

      // Focusing Phase 3 — Decomposition: apply non-invertible rule to focused formula
      if (state.isFocused()) {
        const linear = pool(seq);
        let focusFormula, focusIdx;

        if (state.position === 'R') {
          focusFormula = seq.succedent;
          focusIdx = -1;
        } else {
          focusIdx = linear.findIndex(h => h === state.focusHash);
          if (focusIdx < 0) return null;
          focusFormula = linear[focusIdx];
        }

        // Try identity for atoms
        if (isAtomic(focusFormula)) {
          const idResult = tryIdentity(seq, state.position, focusIdx);
          if (idResult) {
            mc.absorbTheta(idResult.theta);
            return {
              proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, state.position === 'R' ? 'id_+' : 'id_-'),
              delta_out: idResult.delta_out
            };
          }
          return null;
        }

        // Check blur condition
        const side = state.position === 'R' ? 'r' : 'l';
        const tag = Store.tag(focusFormula);
        const shouldBlur = ruleIsInvertible(tag, side);

        if (shouldBlur) {
          return search(seq, inversion(), depth, delta);
        }

        // Apply focused rule
        const rName = ruleName(focusFormula, state.position === 'R' ? 'r' : 'l');

        const ruleNames = [];
        if (ruleSpecs[rName]) ruleNames.push(rName);
        if (ruleAlternatives[rName]) {
          for (const alt of ruleAlternatives[rName]) ruleNames.push(alt);
        }

        // SYNTHETIC-ATOM identity (TODO_0300 1(ii)): a predicate-headed
        // formula with no rule on the focused side (drawn/superpose on the
        // right, ordinary predicates) is an atom at search level — its only
        // focused step is the general id, which must return leftovers like
        // the atomic id above. Without this, a synthetic atom is provable
        // by id only when it consumes the WHOLE context (the pre-focus id),
        // so e.g. `p c, a ⊢ p c ⊗ a` was refuted while `a, p c ⊢ a ⊗ p c`
        // proved — and drawn tokens could never partition through ⊗ (the
        // multiplicative mass-splitting leg of THY_0029).
        if (!ruleNames.some((n) => ruleSpecs[n])) {
          const idResult = tryIdentity(seq, state.position, focusIdx);
          if (idResult) {
            mc.absorbTheta(idResult.theta);
            return {
              proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, state.position === 'R' ? 'id_+' : 'id_-'),
              delta_out: idResult.delta_out
            };
          }
          return null;
        }

        for (const tryName of ruleNames) {
          const mark = mc.save();
          const trySpec = ruleSpecs[tryName];
          if (!trySpec) continue;
          // @affine rules run only under a last-resort affine focus;
          // ordinary focus skips them (see chooseFocus)
          if (state.affineOnly ? !trySpec.affine : trySpec.affine) continue;

          const result = applyAndRecurse(seq, tryName, trySpec, state.position, focusIdx, state, search, depth, delta, opts, mc, affine);
          if (result) return result;
          mc.restore(mark);
        }
      }

      return null;
    };

    // Exhaustive (continuation-threaded) mirror of searchCore. Every candidate
    // result is offered to `sk`; a rejection (null) unwinds to the nearest
    // choice loop, which tries its next alternative — so the root emptiness
    // constraint drives backtracking into with_l1/with_l2. mc bindings absorbed
    // at a terminal success are restored if sk rejects, so a rejected path
    // leaves no metavar residue. Structure follows searchCore line-for-line;
    // `searchK` (below) adds the shared loop-detection / cyclic-bud wrapper.
    const searchCoreK = (seq, state, depth, delta, sk) => {
      if (depth > maxDepth) return null;

      // Axiom: identity (A ⊢ A)
      const idResult = tryIdentity(seq, 'R', -1);
      if (idResult?.success && Context.isEmpty(idResult.delta_out)) {
        const mk = mc.save();
        mc.absorbTheta(idResult.theta);
        const acc = sk({
          proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, 'id'),
          delta_out: idResult.delta_out,
        });
        if (acc) return acc;
        mc.restore(mk);   // sk rejected — fall through to other strategies
      }

      // Axiom: copy from the copy-source zone
      const cart = Seq.getContext(seq, SZ);
      if (cart.length > 0 && Context.isEmpty(delta) && ruleSpecs.copy) {
        for (let i = 0; i < cart.length; i++) {
          const cartFormula = cart[i];
          const theta = unify(cartFormula, seq.succedent);
          if (theta) {
            const mark = mc.save();
            const newLinear = [cartFormula];
            const premise = Seq.seq({
              ...Seq.routeContexts(ctxStruct, newLinear),
              [SZ]: cart,
            }, seq.succedent);
            const premiseDelta = Context.fromArray(newLinear);
            const acc = searchK(premise, inversion(), depth + 1, premiseDelta, (childResult) =>
              sk({
                proofTree: new ProofTree({
                  conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
                  premises: [childResult.proofTree],
                  rule: 'copy',
                  proven: true,
                  state: state.copy(),
                }),
                delta_out: Context.empty(),
              }));
            if (acc) return acc;
            mc.restore(mark);
          }
        }
      }

      // Focusing Phase 1 — Inversion
      const inv = findInvertible(seq);
      if (inv) {
        const rName = ruleName(inv.formula, inv.position === 'R' ? 'r' : 'l');
        const spec = ruleSpecs[rName];
        if (spec) {
          const mark = mc.save();
          const acc = applyAndRecurseK(seq, rName, spec, inv.position, inv.index, state, searchK, depth, delta, opts, mc, affine, sk);
          if (acc) return acc;
          mc.restore(mark);
        }
      }

      // Focusing Phase 2 — Focus
      if (state.isInversion()) {
        const choices = chooseFocus(seq, affine);
        for (const choice of choices) {
          const mark = mc.save();
          const newState = focus(choice.position, choice.hash);
          if (choice.affine) newState.affineOnly = true;
          const acc = searchK(seq, newState, depth + 1, delta, sk);
          if (acc) return acc;
          mc.restore(mark);
        }

        if (cutSpec && depth < maxDepth) {
          const key = Seq.hash(seq);
          if (!cutSeen.has(key)) {
            cutSeen.add(key);
            try {
              for (const X of cutCandidates(pool(seq), seq.succedent)) {
                const mark = mc.save();
                const acc = applyCutK(seq, X, state, searchK, depth, mc, sk);
                if (acc) return acc;
                mc.restore(mark);
              }
            } finally {
              cutSeen.delete(key);
            }
          }
        }
      }

      // Focusing Phase 3 — Decomposition
      if (state.isFocused()) {
        const linear = pool(seq);
        let focusFormula, focusIdx;
        if (state.position === 'R') {
          focusFormula = seq.succedent;
          focusIdx = -1;
        } else {
          focusIdx = linear.findIndex(h => h === state.focusHash);
          if (focusIdx < 0) return null;
          focusFormula = linear[focusIdx];
        }

        const emitLeaf = () => {
          const idr = tryIdentity(seq, state.position, focusIdx);
          if (!idr) return null;
          const mk = mc.save();
          mc.absorbTheta(idr.theta);
          const acc = sk({
            proofTree: leaf(mc.hasBindings() ? mc.resolveSeq(seq) : seq, state.position === 'R' ? 'id_+' : 'id_-'),
            delta_out: idr.delta_out,
          });
          if (acc) return acc;
          mc.restore(mk);
          return null;
        };

        // Identity for atoms
        if (isAtomic(focusFormula)) return emitLeaf();

        // Blur
        const side = state.position === 'R' ? 'r' : 'l';
        const tag = Store.tag(focusFormula);
        if (ruleIsInvertible(tag, side)) {
          return searchK(seq, inversion(), depth, delta, sk);
        }

        const rName = ruleName(focusFormula, state.position === 'R' ? 'r' : 'l');
        const ruleNames = [];
        if (ruleSpecs[rName]) ruleNames.push(rName);
        if (ruleAlternatives[rName]) {
          for (const alt of ruleAlternatives[rName]) ruleNames.push(alt);
        }

        // Synthetic-atom identity (TODO_0300 1(ii))
        if (!ruleNames.some((n) => ruleSpecs[n])) return emitLeaf();

        for (const tryName of ruleNames) {
          const mark = mc.save();
          const trySpec = ruleSpecs[tryName];
          if (!trySpec) continue;
          if (state.affineOnly ? !trySpec.affine : trySpec.affine) continue;
          const acc = applyAndRecurseK(seq, tryName, trySpec, state.position, focusIdx, state, searchK, depth, delta, opts, mc, affine, sk);
          if (acc) return acc;
          mc.restore(mark);
        }
      }

      return null;
    };

    // Path loop detection (TODO_0009 rung 3, Inc-2; opt-in `opts.detectLoops`).
    // A sequent that recurs identically at INVERSION entry on its own DFS path
    // is an infinite (fixpoint) unfolding with no finite proof descending
    // through it → fail fast. Conservative: this is the μ inductive "fail on
    // loop" half, and it also refuses ν-loops for now — Inc-4's cyclic proofs
    // reinstate guarded ν back-edges as SUCCESS, certified by the TCB GTC
    // checker. Sound (failing never accepts a false proof) and completeness-
    // preserving for FINITE proofs (an identical inversion sequent yields no
    // proof its ancestor occurrence did not already have — the rung-1 tabling
    // argument). Keyed at inversion entry ONLY: the focus/blur phase dance
    // revisits the same seq without applying a rule and must not self-trigger.
    // Seq.hash captures the whole sequent; at rule-application boundaries the
    // threaded delta is already folded into the premise columns (addDelta), so
    // the key is exact. Path-scoped Set (add on enter, delete on unwind).
    // Cyclic proofs (TODO_0009 rung 3, Inc-4; opt-in `opts.cyclicProofs`)
    // reinstate a recurring ν-succedent sequent as a coinductive back-edge
    // (a `nu_cycle` bud leaf closing to its companion) instead of failing —
    // the untrusted search's guess, certified post-hoc by the TCB GTC checker
    // (checkCyclicProof below). cyclicProofs implies the path Set.
    const cyclicProofs = !!opts.cyclicProofs;
    const gfpTag = calculus.roles && calculus.roles.gfp ? Store.TAG[calculus.roles.gfp] : undefined;
    // Exhaustive search MUST bound ν-unfolding: without loop detection it
    // backtracks over every unfolding to maxDepth (exponential on coinductive
    // or unprovable goals). detectLoops is the sound μ-inductive default and
    // does not block any finite proof, so exhaustive implies it.
    const seenOnPath = (opts.detectLoops || cyclicProofs || opts.exhaustive) ? new Set() : null;
    const search = seenOnPath
      ? (seq, state, depth, delta) => {
          if (!state.isInversion()) return searchCore(seq, state, depth, delta);
          const key = Seq.hash(seq);
          if (seenOnPath.has(key)) {
            // Coinductive back-edge: a ν-succedent sequent recurring on its own
            // path is a candidate cyclic (co)proof. Emit a bud leaf closing to
            // the companion (the ancestor with this same hash — context
            // conservation is automatic under full-hash keying). The GTC check
            // after the search certifies it (progress through νR). Any other
            // recurrence (μ / non-fixpoint) fails — the sound inductive default.
            if (cyclicProofs && gfpTag !== undefined && Store.tagId(seq.succedent) === gfpTag) {
              return {
                proofTree: new ProofTree({
                  conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
                  rule: 'nu_cycle', proven: true, premises: [],
                }),
                delta_out: Context.empty(),
              };
            }
            return null;
          }
          seenOnPath.add(key);
          try { return searchCore(seq, state, depth, delta); }
          finally { seenOnPath.delete(key); }
        }
      : searchCore;

    // Exhaustive loop-detection / cyclic-bud wrapper (mirrors `search`, sk-threaded).
    // CPS SCOPING (audit 2026-09-11): `key` names THIS sequent — an ancestor of
    // its own subtree but NOT of a sibling premise. Because sibling premises are
    // searched INSIDE this node's continuation (`sk`) while these frames are still
    // live, a naive add/try/finally-delete would leave `key` visible during the
    // sibling's search, so two identical-hash additive branches (e.g. `○a & ○a`,
    // any `A & A`) would make the second branch spuriously self-detect a loop and
    // fail — a completeness bug. So the continuation must see `key` REMOVED before
    // it runs (the sibling is not a descendant), and RE-ADDED on backtrack so a
    // genuine cycle inside this node's own subtree is still caught. seenOnPath
    // thereby holds exactly the current proof-path ancestors at every point.
    const searchK = seenOnPath
      ? (seq, state, depth, delta, sk) => {
          if (!state.isInversion()) return searchCoreK(seq, state, depth, delta, sk);
          const key = Seq.hash(seq);
          if (seenOnPath.has(key)) {
            if (cyclicProofs && gfpTag !== undefined && Store.tagId(seq.succedent) === gfpTag) {
              return sk({
                proofTree: new ProofTree({
                  conclusion: mc.hasBindings() ? mc.resolveSeq(seq) : seq,
                  rule: 'nu_cycle', proven: true, premises: [],
                }),
                delta_out: Context.empty(),
              });
            }
            return null;
          }
          seenOnPath.add(key);
          // Leaving this subtree (into a sibling / the parent continuation) drops
          // `key`; backtracking into it restores it.
          const skScoped = (result) => {
            seenOnPath.delete(key);
            try { return sk(result); }
            finally { seenOnPath.add(key); }
          };
          try { return searchCoreK(seq, state, depth, delta, skScoped); }
          finally { seenOnPath.delete(key); }
        }
      : searchCoreK;

    const initialDelta = Context.fromArray(pool(seq));
    let result;
    if (opts.exhaustive) {
      // Success continuation for the ROOT goal: a complete proof is acceptable
      // only when it consumes the whole linear pool (after any @affine root
      // discharge). This is the global constraint that committed search checks
      // too late; threading it as `sk` lets it drive additive backtracking.
      const rootSk = (r) => {
        let out = r;
        if (affine && !Context.isEmpty(out.delta_out)) {
          const wrapped = dischargeAffine(out.proofTree, out.delta_out, affine);
          if (wrapped) out = { proofTree: wrapped, delta_out: Context.empty() };
        }
        return Context.isEmpty(out.delta_out) ? out : null;
      };
      result = searchK(seq, inversion(), 0, initialDelta, rootSk);
    } else {
      result = search(seq, inversion(), 0, initialDelta);
    }

    // Root boundary discharge: globally-unused @affine leftovers (drawn
    // tokens) are consumed by inserting the affine rule at the root —
    // THY_0027 §5's stripping lemma read backwards (ghosts permute to
    // the root, so the root is where the search may add them).
    if (result && affine && !Context.isEmpty(result.delta_out)) {
      const wrapped = dischargeAffine(result.proofTree, result.delta_out, affine);
      if (wrapped) {
        result.proofTree = wrapped;
        result.delta_out = Context.empty();
      }
    }

    if (result && Context.isEmpty(result.delta_out)) {
      let tree = result.proofTree;
      // Resolve any remaining unground sequents (sibling subtrees
      // constructed before a metavar was bound by a later sibling)
      if (mc.hasBindings()) {
        tree = mc.resolveTree(tree);
      }
      // Cyclic-proof soundness gate (Inc-4): every nu_cycle back-edge must
      // satisfy the global trace condition — the untrusted search's guesses
      // are certified here by the TCB checker over the fully-resolved tree.
      if (cyclicProofs) {
        const gtc = checkCyclicProof(tree, {
          roles: calculus.roles,
          contextStructure: calculus.contextStructure,
          canonicalize: calculus.canonicalize,
        });
        if (!gtc.valid) return { success: false, proofTree: null, gtcErrors: gtc.errors };
      }
      return { success: true, proofTree: tree };
    }

    return { success: false, proofTree: null };
  };

  return { prove, findInvertible, chooseFocus, tryIdentity, connective, ruleName, ruleIsInvertible };
}

export { createProver };
export default { createProver };
