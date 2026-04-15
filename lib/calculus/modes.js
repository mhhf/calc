/**
 * Mode Theory — monad rules for backward ↔ forward mode switch.
 *
 * monad_r: {A}R — invertible (negative polarity), zero premises.
 *   Triggers mode switch: transfers ALL linear resources to forward engine.
 *
 * monad_l: {A}L — not invertible, one premise.
 *   Sticky: only fires when succedent is monadic.
 */

function monadRules() {
  return {
    monad_r: {
      name: 'monad_r',
      descriptor: {
        connective: 'monad', side: 'r', arity: 1,
        copyContext: false, emptyLinear: false, contextSplit: false,
        contextFlow: 'axiom', modeShift: true,
        premises: []
      },
      invertible: true, pretty: '{_}R', structural: false,
      bridge: null, numPremises: 0
    },
    monad_l: {
      name: 'monad_l',
      descriptor: {
        connective: 'monad', side: 'l', arity: 1,
        copyContext: false, emptyLinear: false, contextSplit: false,
        contextFlow: 'preserved',
        requiresSuccedentTag: 'monad',
        premises: [{ linear: [0] }]
      },
      invertible: false, pretty: '{_}L', structural: false,
      bridge: null, numPremises: 1
    }
  };
}

module.exports = { monadRules };
