/**
 * Flat ZK Witness Generator — converts rewriting certificates to STARK traces.
 *
 * Companion to witness.js (tree-based). Takes a flat rewriting trace
 * (from buildRewriteTrace) and produces per-chip trace rows for the flat
 * verification path: FlatInitChip + FlatStepChip + FlatFinalChip + GammaRomAir.
 *
 * The flat path uses only 2 buses (CONTEXT_BUS + GAMMA_BUS) vs 5 for tree.
 * No OBLIG_BUS, no FORMULA_BUS, no DISCARD_BUS. Verification model:
 *   - Resource consistency: CONTEXT_BUS balance (sound)
 *   - Rule membership: GAMMA_BUS lookup (sound with committed gamma)
 *   - Rule application: NOT verified in circuit (JS checkRewriteTrace
 *     does full verification; ZK tensor decomposition is Phase 3 enhancement)
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');

/** Max arities — must match Rust FlatStepChip constants. */
const MAX_CONSUMED = 6;
const MAX_PRODUCED = 6;

/**
 * Build a right-associated tensor tree from ground hashes.
 * [f1, f2, f3] → tensor(f1, tensor(f2, f3))
 * [f1] → f1
 * [] → one
 */
function buildRightTensor(hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

/**
 * Generate a flat ZK witness from a rewriting trace.
 *
 * @param {Array} trace - Flat certificate (from buildRewriteTrace)
 * @param {Object} sequent - The sequent being proved (Store hashes)
 * @param {Object} [opts] - Options (unused for now, reserved for future params)
 * @returns {{ format: string, chips: Object, gamma_rom: number[][] }}
 */
function generateFlatWitness(trace, sequent, opts = {}) {
  const gammaEntries = new Map(); // hash → lookup count

  function addGammaLookup(hash) {
    gammaEntries.set(hash, (gammaEntries.get(hash) || 0) + 1);
  }

  // --- FlatInitChip rows: introduce initial linear context ---
  const linear = Seq.getContext(sequent, 'linear');
  const flatInit = linear.map(h => [1, h]);

  // --- FlatStepChip rows: one per forward step ---
  // Layout: [active, is_loli, ground_loli,
  //          consumed_0..5, consumed_active_0..5,
  //          produced_0..5, produced_active_0..5]
  const flatStep = [];
  const delta = new Map();
  for (const h of linear) delta.set(h, (delta.get(h) || 0) + 1);

  for (const step of trace) {
    const isLoli = step.ruleHash == null;
    let groundLoli = 0;

    if (!isLoli) {
      // Compiled rule: construct ground loli for gamma lookup.
      // ground_loli = loli(tensor(consumed), monad(tensor(produced)))
      const groundAnt = buildRightTensor(step.consumed);
      const groundCons = buildRightTensor(step.produced);
      const groundMonad = Store.put('monad', [groundCons]);
      groundLoli = Store.put('loli', [groundAnt, groundMonad]);
      addGammaLookup(groundLoli);
    }

    // Build row
    const row = [1, isLoli ? 1 : 0, groundLoli];

    // Consumed slots (padded to MAX_CONSUMED)
    for (let i = 0; i < MAX_CONSUMED; i++) {
      row.push(i < step.consumed.length ? step.consumed[i] : 0);
    }
    for (let i = 0; i < MAX_CONSUMED; i++) {
      row.push(i < step.consumed.length ? 1 : 0);
    }

    // Produced slots (padded to MAX_PRODUCED)
    for (let i = 0; i < MAX_PRODUCED; i++) {
      row.push(i < step.produced.length ? step.produced[i] : 0);
    }
    for (let i = 0; i < MAX_PRODUCED; i++) {
      row.push(i < step.produced.length ? 1 : 0);
    }

    flatStep.push(row);

    // Update delta
    for (const h of step.consumed) {
      const c = delta.get(h);
      if (c === 1) delta.delete(h);
      else delta.set(h, c - 1);
    }
    for (const h of step.produced) {
      delta.set(h, (delta.get(h) || 0) + 1);
    }
  }

  // --- FlatFinalChip rows: consume remaining linear context ---
  const flatFinal = [];
  for (const [h, cnt] of delta) {
    for (let i = 0; i < cnt; i++) {
      flatFinal.push([1, h]);
    }
  }

  // --- Gamma ROM ---
  const gamma_rom = [];
  for (const [hash, count] of gammaEntries) {
    gamma_rom.push([hash, 1, count]);
  }

  return {
    format: 'flat',
    chips: {
      flat_init: flatInit,
      flat_step: flatStep,
      flat_final: flatFinal,
    },
    gamma_rom,
  };
}

module.exports = { generateFlatWitness, MAX_CONSUMED, MAX_PRODUCED };
