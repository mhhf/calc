/**
 * Compiled Existential Chain — partial evaluation of proof search.
 *
 * For functional predicates (mode +...+-), existential resolution ≡
 * sequential function composition. This module compiles the goal sequence
 * into direct slot-to-slot dataflow: read theta → call FFI → write theta.
 *
 * Per-step semantics: each compiled step is tried first. On success, the
 * goal is resolved without subApplyIdx, state lookup, or tryFFIDirect.
 * On failure, the caller falls back to provePersistent for that goal only.
 *
 * Theory basis: for deterministic predicates, ∃x.P(inputs, x) reduces to
 * x := f(inputs). The compilation is partial evaluation of SLD resolution
 * over a known goal sequence with known modes.
 */

const Store = require('../../kernel/store');
const { getPredicateHead } = require('../../kernel/ast');
const ffiRegistry = require('../ill/ffi');

const _ffiMeta = ffiRegistry.defaultMeta;
const _ffiParsedModes = ffiRegistry.parsedModes;

// Reusable args buffer (max arity 5, same as ffi.js)
const _args = [0, 0, 0, 0, 0];

/**
 * Compile the existential goal chain for a rule.
 * Returns an array parallel to the ordered goals, with null entries for
 * goals that can't be compiled (no FFI handler).
 *
 * @param {Object} rule - Compiled forward rule with existentialSlots/existentialGoals
 * @returns {Array|null} Array of {handler, argSlot, argMeta, inputMask, arity}|null
 */
function compileExistentialChain(rule) {
  if (!rule.existentialSlots || rule.existentialSlots.length === 0) return null;
  if (!rule.existentialGoals) return null;

  const slots = rule.metavarSlots;

  // Collect goals in consequent-persistent order (mirrors resolveExistentials)
  const goalSet = new Set();
  for (const slot of rule.existentialSlots) {
    const sg = rule.existentialGoals[slot];
    if (sg) for (const g of sg) goalSet.add(g);
  }
  const persistentPats = rule.consequent.persistent || [];
  const orderedGoals = [];
  for (const p of persistentPats) {
    if (goalSet.has(p)) orderedGoals.push(p);
  }
  if (orderedGoals.length === 0) return null;

  // Cache ordered goals on rule (avoids Set+Array allocation per resolve call)
  rule._existentialGoalOrder = orderedGoals;

  let anyCompiled = false;
  const chain = new Array(orderedGoals.length);

  for (let gi = 0; gi < orderedGoals.length; gi++) {
    const goal = orderedGoals[gi];
    chain[gi] = null;

    const pred = getPredicateHead(goal);
    if (!pred) continue;

    const meta = _ffiMeta[pred];
    if (!meta || !meta.ffi) continue;

    const handler = ffiRegistry.get(meta.ffi);
    if (!handler) continue;

    const modes = _ffiParsedModes[pred];
    const arity = Store.arity(goal);
    if (arity !== modes.length) continue;

    // Map each arg to a slot index or literal.
    const argSlot = new Int32Array(arity);
    const argMeta = new Uint32Array(arity);
    let inputMask = 0;
    let valid = true;

    for (let i = 0; i < arity; i++) {
      const child = Store.child(goal, i);
      const slot = slots[child];

      if (slot !== undefined) {
        argSlot[i] = slot;
        argMeta[i] = child;
        if (modes[i] === '+') inputMask |= (1 << i);
      } else if (modes[i] !== '-') {
        argSlot[i] = -1;
        argMeta[i] = child;
      } else {
        valid = false;
        break;
      }
    }

    if (valid) {
      chain[gi] = { handler, argSlot, argMeta, inputMask, arity };
      anyCompiled = true;
    }
  }

  return anyCompiled ? chain : null;
}

/**
 * Try a single compiled existential step.
 * Returns true if FFI succeeded and outputs were written to theta.
 *
 * @param {Object} step - Compiled step spec
 * @param {Array} theta - Metavar bindings (mutated on success)
 * @param {Object} slots - Hash → slot index mapping (for chain deref)
 * @returns {boolean}
 */
function executeCompiledStep(step, theta, slots) {
  for (let j = 0; j < step.arity; j++) {
    const s = step.argSlot[j];
    if (s < 0) {
      _args[j] = step.argMeta[j];
    } else {
      let val = theta[s];
      if (val !== undefined) {
        // Deref metavar chain (fused rules: A→B→concrete)
        let cs;
        while ((cs = slots[val]) !== undefined && theta[cs] !== undefined) {
          val = theta[cs];
        }
        _args[j] = val;
      } else {
        _args[j] = step.argMeta[j];
        if (step.inputMask & (1 << j)) return false;
      }
    }
  }

  const result = step.handler(_args);
  if (!result || !result.success) return false;

  const ft = result.theta;
  for (let k = 0; k < ft.length; k++) {
    const outSlot = slots[ft[k][0]];
    if (outSlot !== undefined) theta[outSlot] = ft[k][1];
  }
  return true;
}

module.exports = { compileExistentialChain, executeCompiledStep };
