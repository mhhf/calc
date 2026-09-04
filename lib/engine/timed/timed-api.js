/**
 * Timed scheduler API construction (TODO_0265 Phase 4) — extracted
 * verbatim from _buildCalc (index.js; audit 2026-09-02 readability
 * split, zero semantic change).
 *
 * A calculus with a grade algebra (cc.grades: availability order + effect
 * monoid over stamps) gets settle/nextActivation/settleExplore and the
 * read-only views. ILL declares no grades slot → no timed API; the timed
 * matcher OWNS window/count/delay evaluation, so these rules never reach
 * forward.run's untimed intake (its guard stays loud).
 */

'use strict';

import Store from '../../kernel/store.js';
import forward from '../forward.js';
import backward from '../backchain.js';
import timed from './timed.js';
import { lintProductivity, lintChainCollapse, lintHypothesisS, lintWholeBind } from './timed-lint.js';
import { certifyContention } from './certify.js';
import game from './timed-game.js';
import views from './timed-views.js';

/**
 * @param {Object} deps — locals threaded from the composition root:
 *   cc, compiledRules, compileOpts (resolved _compileOpts(cc)),
 *   calcContext, rc (resolved connectives), filterRules, buildMatchOpts,
 *   clauses, definitions, backwardOpts
 * @returns {Object|null} the timed API record, or null (no cc.grades)
 */
function buildTimedApi({ cc, compiledRules, compileOpts, calcContext, rc,
  filterRules, buildMatchOpts, clauses, definitions, backwardOpts }) {
  if (!cc.grades) return null;

  const _tcfg = timed.buildTimedConfig(cc);
  // D16 productivity lint (Phase 5): conservative load-time WARNING on
  // zero-delay rule cycles (static Zeno check; maxSteps stays the
  // runtime backstop). Findings also ride on the API as `timedLint`.
  const _lint = lintProductivity(compiledRules.filter(r => !r.hasGrade0), _tcfg);
  for (const f of _lint) {
    console.warn(f.kind === 'self-cycle'
      ? `timed lint (D16): rule '${f.rule}' re-produces everything it consumes at zero delay — a Zeno self-cycle unless windows/guards break it`
      : `timed lint (D16): zero-delay rule cycle ${f.via} (rules: ${f.rules.join(', ')}) — Zeno unless resources deplete`);
  }
  // C1 chain-collapse advisory (same load-time channel as D16, advisory
  // tone) — gated on a productivity-clean rule set so Zeno cycles are
  // fixed before vocabulary advice is offered. Rides the API as
  // `timedAdvice`; collapsing stays the author's call.
  const _runtimeRules = compiledRules.filter(r => !r.hasGrade0);
  const _advice = [
    ...(_lint.length ? [] : lintChainCollapse(_runtimeRules, _tcfg)),
    ...lintHypothesisS(_runtimeRules, _tcfg, { ...rc, lintExempt: cc.lintExempt }),
    ...lintWholeBind(_runtimeRules, _tcfg),
  ];
  for (const f of _advice) {
    if (f.kind === 'chain-collapse') {
      console.warn(`timed lint (C1): '${f.pred}' is an unconditional chain intermediate — produced by ${f.producers.join(', ')}, consumed only by '${f.consumer}' with no other premise, window, or observer; consider collapsing the pair into one rule (delays add)`);
    } else if (f.kind === 'persistent-conclusion') {
      console.warn(`timed lint (C2): rule '${f.rule}' concludes persistent '${f.pred}' (${f.via}) — learned knowledge can backdate enablement (Hypothesis S, settle-optimality §1.3); external-choice menus are exempt`);
    } else if (f.kind === 'whole-bind-arrivals') {
      console.warn(`timed lint (C3): rule '${f.rule}' whole-binds '${f.pred}' while ${f.producers.join(', ')} produce(s) it — !_W chases every arrival and can starve under a deterministic chooser (PP2 §3b); prefer a counted take`);
    }
  }
  // Possessed rules (Phase 6c): compile a loli FACT on demand — a rule
  // and a loli are the same formula shape, so this is literally the rule
  // compiler (its content-addressed cache makes repeats free). Fences:
  // ground only (v1), no $-sugar leftovers, no unweighted multi-alt.
  const _compileLoli = (h) => {
    const r = forward.compileRule({
      name: 'loli:' + h, hash: h,
      antecedent: Store.child(h, 0), consequent: Store.child(h, 1),
    }, compileOpts);
    if (r.metavarCount > 0) {
      throw new Error('timed loli facts must be ground (v1) — variable-binding possessed rules are a 6b extension');
    }
    for (const p of (r.antecedent.linear || [])) {
      if (Store.tag(p) === 'preserved') {
        throw new Error('$-sugar inside a possessed rule: write the resource on both sides explicitly');
      }
    }
    if (r.consequentAlts && r.consequentAlts.length > 1 && !r.weighted) {
      throw new Error('unweighted additive-choice consequents in a possessed rule — use woplus');
    }
    return r;
  };
  const _timedOpts = (T, execOpts) => ({
    ...execOpts,
    horizon: _tcfg.parseStamp(T),
    timedConfig: _tcfg,
    calc: calcContext,
    compileLoli: _compileLoli,
    matchOpts: execOpts.matchOpts || buildMatchOpts(execOpts),
  });
  return {
    settle: (state, T, execOpts = {}) =>
      timed.settle(state, filterRules(execOpts), _timedOpts(T, execOpts)),
    // T2-applicability certifier (TODO_0293 (a), settle-optimality §11):
    // structural conflict-freedom first, else the monotone-relaxation
    // pairwise independence check — never runs settle
    certifyContention: (state, T, execOpts = {}) =>
      certifyContention(
        { prove: (g) => backward.prove(g, clauses, definitions, backwardOpts) },
        filterRules(execOpts), _tcfg, state, _tcfg.parseStamp(T), execOpts),
    // Bounded catch-up slices (TODO_0278 A2): same contract as settle,
    // plus chunk (slice width, parsed like a horizon) and onChunk.
    settleChunked: (state, T, execOpts = {}) =>
      timed.settleChunked(state, filterRules(execOpts), {
        ..._timedOpts(T, execOpts),
        // A chunk is an EXTENT (slice width), not a threshold: algebras
        // whose parseStamp widens thresholds to a down-set (product
        // stamps: scalar horizon → (T, ∞), TODO_0285) supply parseExtent
        // for widths; scalar algebras need no distinction.
        ...(execOpts.chunk !== undefined
          ? { chunk: (_tcfg.parseExtent || _tcfg.parseStamp)(execOpts.chunk) }
          : {}),
      }),
    settleExplore: (state, T, execOpts = {}) =>
      timed.settleExplore(state, filterRules(execOpts), _timedOpts(T, execOpts)),
    // Pareto-minimal completions over the join-derived partial order
    // (TODO_0285 P6a) — degenerates to the least completion for total
    // (scalar) stamp orders.
    settleFrontier: (state, T, execOpts = {}) =>
      timed.settleFrontier(state, filterRules(execOpts), _timedOpts(T, execOpts)),
    nextActivation: (state, execOpts = {}) =>
      timed.nextActivation(state, filterRules(execOpts), {
        timedConfig: _tcfg, calc: calcContext,
        matchOpts: execOpts.matchOpts || buildMatchOpts(execOpts),
      }),
    observable: (state, T) => views.observable(state, _tcfg.parseStamp(T), _tcfg),
    pending: (state, T) => views.pending(state, _tcfg.parseStamp(T), _tcfg),
    inFlight: (events, T) => views.inFlight(events, _tcfg.parseStamp(T), _tcfg),
    // with-projection: the host collapses an offered menu (external
    // choice); now-marked alternatives are strict — refused unless
    // fireable at the decision time (rules in scope for that check)
    choose: (state, factHash, index, chOpts = {}) =>
      game.withProject(state, factHash, index, {
        ...chOpts, timedConfig: _tcfg, roles: rc,
        rules: filterRules(chOpts), calc: calcContext,
        compileLoli: _compileLoli,
        matchOpts: chOpts.matchOpts || buildMatchOpts(chOpts),
      }),
    // per-alternative availability at horizon T (UI greying — pure query)
    menuStatus: (state, factHash, T, execOpts = {}) =>
      game.menuStatus(state, factHash, filterRules(execOpts),
        { ..._timedOpts(T, execOpts), roles: rc }),
    timedLint: _lint,
    timedAdvice: _advice,
    // the timed-config record (grades/parseStamp/units) — public: the
    // bridge and debug tooling read it (round-15 F7; was _timedConfig)
    timedConfig: _tcfg,
  };
}

export { buildTimedApi };
export default { buildTimedApi };
