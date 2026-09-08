/**
 * Measure-layer API attachment (RES_0143 M2 — the buildTimedApi
 * pattern): the decimation driver (calc.collapse / collapseView /
 * collapseDraw, TODO_0297 P2) and the CI-criterion certifier
 * (calc.certifyCI, TODO_0302 M5) attach onto the calc API here.
 *
 * Presence-gated on the timed API (settle) + a sort system — running
 * collapse is the D4 opt-in (plain settle leaves suspended ∃-facts
 * inert). Returns null when the gate fails; the composition root
 * spreads the result. The engine imports this module only at the
 * composition root — the measure layer sits ABOVE lib/engine (it
 * imports engine code, never the reverse).
 */

import decimate from './decimate.js';
import ci from './ci.js';

function buildCollapseApi(api, cc, sortSystem) {
  if (!api.settle || !sortSystem) return null;
  const stampTag = cc.stampTag || 'at';
  return {
    collapse: (state, o = {}) =>
      decimate.collapse(api, state, { stampTag, ...o }),
    // stepwise face (the shell's collapse mode): the caller threads
    // session = { state, waveMap, skolemSet } across view/draw calls
    collapseView: (session, o = {}) =>
      decimate.collapseView(api, session, { stampTag, ...o }),
    collapseDraw: (session, wave, o = {}) =>
      decimate.collapseDraw(api, session, wave, o),
    // certifyCI (THY_0031 §4): decide the separation criterion on the
    // computable cover — soundness-only; `separated` certifies
    // X ⊥ Y | Z, a refusal carries a witness walk and never asserts
    // dependence.
    certifyCI: (query = {}) =>
      ci.certifyCI(api, { stampTag, ...query }),
  };
}

export { buildCollapseApi };
export default { buildCollapseApi };
