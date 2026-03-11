/**
 * Flat ZK Witness Generator — converts rewriting certificates to STARK traces.
 *
 * Companion to witness.js (tree-based). Takes a flat rewriting trace
 * (from buildRewriteTrace) and produces per-chip trace rows for the flat
 * verification path: FlatInitChip + FlatStepChip + FlatFinalChip +
 * FormulaRomAir + GammaRomAir.
 *
 * Phase 3b: Full adversarial soundness via FORMULA_BUS tensor spine
 * verification. Uses 3 buses (CONTEXT_BUS + GAMMA_BUS + FORMULA_BUS).
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { buildRightTensor } = require('../kernel/ast');

/** Max arities — must match Rust FlatStepChip constants. */
const MAX_CONSUMED = 6;
const MAX_PRODUCED = 6;

/**
 * Build right-associated tensor spine intermediates.
 * For [h0, h1, h2]: tensor(h0, tensor(h1, h2))
 *   intermediates = [tensor(h1, h2)] (padded to MAX-2 with 0)
 * For [h0, h1]: tensor(h0, h1)
 *   intermediates = [h1] (padded)
 * For [h0] or []: no intermediates needed
 *
 * @param {number[]} hashes - Fact hashes
 * @param {number} maxSlots - MAX_CONSUMED or MAX_PRODUCED
 * @returns {number[]} Array of maxSlots-2 intermediate hashes (0 = unused)
 */
function buildSpineIntermediates(hashes, maxSlots) {
  const result = new Array(maxSlots - 2).fill(0);
  if (hashes.length <= 1) return result;

  // Right-associated: tensor(h[0], tensor(h[1], tensor(h[2], ...)))
  // Intermediates are the right children at each level.
  // i1 = tensor(h[1], tensor(h[2], ...)) for count >= 3
  // For count == 2: i1 = h[1]
  for (let i = 1; i < hashes.length - 1; i++) {
    // intermediate[i-1] = tensor tree of hashes[i..]
    const remaining = hashes.slice(i);
    result[i - 1] = buildRightTensor(remaining);
  }
  // Last intermediate (when count >= 2): just the last hash
  if (hashes.length >= 2) {
    result[hashes.length - 2] = hashes[hashes.length - 1];
  }
  return result;
}

/**
 * Generate a flat ZK witness from a rewriting trace.
 *
 * @param {Array} trace - Flat certificate (from buildRewriteTrace)
 * @param {Object} sequent - The sequent being proved (Store hashes)
 * @param {Object} [opts] - Options
 * @param {Object} [opts.calculus] - Loaded calculus (for deriveZkTags)
 * @returns {{ format: string, chips: Object, formula_rom: number[][], gamma_rom: number[][], tags: Object, constants: Object }}
 */
function generateFlatWitness(trace, sequent, opts = {}) {
  const gammaEntries = new Map(); // hash → lookup count
  const formulaLookups = new Map(); // hash → { tag, c0, c1, count }

  function addGammaLookup(hash) {
    gammaEntries.set(hash, (gammaEntries.get(hash) || 0) + 1);
  }

  function addFormulaLookup(hash) {
    if (!Store.isTerm(hash)) return;
    const tag = Store.tag(hash);
    const zkTag = zkTags[tag];
    if (zkTag == null) return;
    const arity = Store.arity(hash);
    const c0 = arity >= 1 ? Store.child(hash, 0) : 0;
    const c1 = arity >= 2 ? Store.child(hash, 1) : 0;
    const existing = formulaLookups.get(hash);
    if (existing) {
      existing.count++;
    } else {
      formulaLookups.set(hash, { tag: zkTag, c0, c1, count: 1 });
    }
  }

  // Derive ZK tags (needed for formula ROM)
  let zkTags;
  if (opts.tags) {
    zkTags = opts.tags;
  } else if (opts.calculus) {
    const { deriveZkTags } = require('./witness');
    zkTags = deriveZkTags(opts.calculus);
  } else {
    // Fallback: minimal tags for tensor/loli/monad/one
    zkTags = {};
  }

  const oneHash = Store.put('one', []);

  // --- FlatInitChip rows: introduce initial linear context ---
  const linear = Seq.getContext(sequent, 'linear');
  const flatInit = linear.map(h => [1, h]);

  // --- FlatStepChip rows: one per forward step ---
  const flatStep = [];
  const delta = new Map();
  for (const h of linear) delta.set(h, (delta.get(h) || 0) + 1);

  for (const step of trace) {
    const isLoli = step.ruleHash == null;

    // Loli/trigger separation: for loli matches, separate the loli hash
    // from the consumed array. The loli is consumed via CONTEXT_BUS.receive
    // on ground_loli; consumed slots hold only trigger facts.
    let consumed = step.consumed;
    let groundLoli = 0;

    if (isLoli) {
      groundLoli = step.loliHash;
      // Remove first occurrence of loliHash from consumed
      consumed = [...step.consumed];
      const loliIdx = consumed.indexOf(step.loliHash);
      if (loliIdx >= 0) consumed.splice(loliIdx, 1);
    }

    if (!isLoli) {
      // Compiled rule: construct ground loli for gamma lookup.
      const groundAnt = buildRightTensor(consumed);
      const groundCons = buildRightTensor(step.produced);
      const groundMonad = Store.put('monad', [groundCons]);
      groundLoli = Store.put('loli', [groundAnt, groundMonad]);
      addGammaLookup(groundLoli);
    }

    // Compute spine columns.
    // For loli matches: use the original loli's Store decomposition for
    // ant_hash/monad_hash/cons_hash (the original antecedent may contain
    // metavariables, so it won't match the ground trigger tensor).
    // For compiled rules: compute from consumed/produced triggers.
    let antHash, consHash, monadHash;
    let antSpine, consSpine;

    if (isLoli) {
      // Original loli decomposition from Store
      antHash = Store.child(groundLoli, 0);   // original antecedent
      monadHash = Store.child(groundLoli, 1); // original monad
      consHash = Store.child(monadHash, 0);   // original consequent body
      antSpine = new Array(MAX_CONSUMED - 2).fill(0);
      consSpine = new Array(MAX_PRODUCED - 2).fill(0);
    } else {
      antHash = consumed.length === 0 ? oneHash : buildRightTensor(consumed);
      consHash = step.produced.length === 0 ? oneHash : buildRightTensor(step.produced);
      monadHash = Store.put('monad', [consHash]);
      antSpine = buildSpineIntermediates(consumed, MAX_CONSUMED);
      consSpine = buildSpineIntermediates(step.produced, MAX_PRODUCED);
    }

    // Add formula ROM entries for spine verification
    addFormulaLookup(groundLoli); // loli(ant_hash, monad_hash)
    addFormulaLookup(monadHash);  // monad(cons_hash)
    // Tensor spine intermediates (compiled rules only — loli matches skip spine)
    if (!isLoli && consumed.length >= 2) {
      addFormulaLookup(antHash); // tensor(c0, ant_i1)
      for (let i = 0; i < antSpine.length; i++) {
        if (antSpine[i] !== 0 && consumed.length >= i + 3) {
          addFormulaLookup(antSpine[i]);
        }
      }
    }
    if (!isLoli && step.produced.length >= 2) {
      addFormulaLookup(consHash); // tensor(p0, cons_i1)
      for (let i = 0; i < consSpine.length; i++) {
        if (consSpine[i] !== 0 && step.produced.length >= i + 3) {
          addFormulaLookup(consSpine[i]);
        }
      }
    }

    // Build row (width 39)
    const compiled = isLoli ? 0 : 1;
    const row = [1, isLoli ? 1 : 0, groundLoli];

    // Consumed slots (trigger facts only)
    for (let i = 0; i < MAX_CONSUMED; i++) {
      row.push(i < consumed.length ? consumed[i] : 0);
    }
    for (let i = 0; i < MAX_CONSUMED; i++) {
      row.push(i < consumed.length ? 1 : 0);
    }

    // Produced slots
    for (let i = 0; i < MAX_PRODUCED; i++) {
      row.push(i < step.produced.length ? step.produced[i] : 0);
    }
    for (let i = 0; i < MAX_PRODUCED; i++) {
      row.push(i < step.produced.length ? 1 : 0);
    }

    // Spine columns
    row.push(antHash);
    for (let i = 0; i < MAX_CONSUMED - 2; i++) {
      row.push(antSpine[i]);
    }
    row.push(consHash);
    for (let i = 0; i < MAX_PRODUCED - 2; i++) {
      row.push(consSpine[i]);
    }
    row.push(monadHash);
    row.push(compiled);  // auxiliary: active * (1 - is_loli)

    flatStep.push(row);

    // Update delta (using original consumed for correct resource accounting)
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

  // --- Formula ROM ---
  const formula_rom = [];
  for (const [hash, info] of formulaLookups) {
    formula_rom.push([hash, info.tag, info.c0, info.c1, 1, info.count]);
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
    formula_rom,
    gamma_rom,
    tags: zkTags,
    constants: { one_hash: oneHash },
  };
}

module.exports = { generateFlatWitness, MAX_CONSUMED, MAX_PRODUCED };
