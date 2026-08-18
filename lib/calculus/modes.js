/**
 * Mode Theory — monad rules for backward ↔ forward mode switch.
 *
 * monad_r: {A}R — invertible (negative polarity), zero premises.
 *   Triggers mode switch: transfers ALL linear resources to forward engine.
 *
 * monad_l: {A}L — not invertible, one premise.
 *   Sticky: only fires when succedent is monadic.
 *
 * Parameterized by the computation role record { tag, bodyIdx, gradeIdx }
 * (TODO_0265 Phase 2): rule names, descriptor connective/arity, the sticky
 * succedent tag, and the premise child index all derive from it. Default is
 * ILL's unary monad — rules named monad_r/monad_l, bit-identical to before.
 * A graded (2-ary) computation yields `<tag>_r`/`<tag>_l` with the body
 * premise at bodyIdx; the grade child rides along opaquely (grade algebra
 * composition lands with calculusConfig.grades, Phase 3).
 */

const ILL_COMPUTATION = { tag: 'monad', bodyIdx: 0, gradeIdx: null };

function monadRules(computation = ILL_COMPUTATION) {
  const { tag, bodyIdx, gradeIdx } = computation;
  const arity = gradeIdx === null ? 1 : 2;
  return {
    [`${tag}_r`]: {
      name: `${tag}_r`,
      descriptor: {
        connective: tag, side: 'r', arity,
        copyContext: false, emptyLinear: false, contextSplit: false,
        contextFlow: 'axiom', modeShift: true,
        premises: []
      },
      invertible: true, pretty: '{_}R', structural: false,
      bridge: null, numPremises: 0
    },
    [`${tag}_l`]: {
      name: `${tag}_l`,
      descriptor: {
        connective: tag, side: 'l', arity,
        copyContext: false, emptyLinear: false, contextSplit: false,
        contextFlow: 'preserved',
        requiresSuccedentTag: tag,
        premises: [{ linear: [bodyIdx] }]
      },
      invertible: false, pretty: '{_}L', structural: false,
      bridge: null, numPremises: 1
    }
  };
}

export { monadRules };
export default { monadRules };
