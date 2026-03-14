/**
 * Flat ZK Witness Generator — converts rewriting certificates to STARK traces.
 *
 * Companion to witness.js (tree-based). Takes a flat rewriting trace
 * (from buildRewriteTrace) and produces per-chip trace rows for the flat
 * verification path: FlatInitChip + FlatStepChip + FlatFinalChip +
 * FormulaRomAir + GammaRomAir.
 *
 * Phase 3b: Full adversarial soundness via FORMULA_BUS tensor spine
 * verification + SUBST_TREE_BUS body demands with preprocessed canonical
 * body form. Uses 5 buses (CONTEXT + GAMMA + FORMULA + SUBST_TREE + FREEVAR).
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { buildRightTensor } = require('../kernel/ast');

/** Max arities — must match Rust FlatStepChip constants. */
const MAX_CONSUMED = 6;
const MAX_PRODUCED = 6;

/**
 * Flatten a tensor tree into its non-tensor leaves (left-to-right DFS).
 * tensor(tensor(A, B), C) → [A, B, C]
 * tensor(A, tensor(B, C)) → [A, B, C]
 * single_fact → [single_fact]
 */
function flattenTensor(hash) {
  if (!Store.isTerm(hash) || Store.tag(hash) !== 'tensor') return [hash];
  const left = Store.rawChild(hash, 0);
  const right = Store.rawChild(hash, 1);
  return [...flattenTensor(left), ...flattenTensor(right)];
}

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
 * @returns {{ format: string, chips: Object, formula_rom: number[][], gamma_rom: number[][], freevar_rom: number[][], tags: Object, constants: Object }}
 */
function generateFlatWitness(trace, sequent, opts = {}) {
  const gammaEntries = new Map(); // hash → lookup count
  const formulaLookups = new Map(); // hash → { tag, c0, c1, count }
  const substRows = [];            // SubstChip rows (width 15)
  const freevarRomEntries = new Map(); // "substId:freevarHash" → { substId, freevarHash, groundValue, lookups }
  let substIdCtr = 1;

  function addGammaLookup(hash) {
    gammaEntries.set(hash, (gammaEntries.get(hash) || 0) + 1);
  }

  function addFormulaLookup(hash) {
    if (!Store.isTerm(hash)) return;
    const tag = Store.tag(hash);
    let zkTag = zkTags[tag];
    // Dynamic ZK tag assignment for tags not in the calculus definition
    // (e.g., predicate/atom tags encountered during SubstChip tree walks)
    if (zkTag == null) {
      if (!tag) return;
      const maxTag = Object.values(zkTags).reduce((a, b) => Math.max(a, b), 0);
      zkTag = maxTag + 1;
      zkTags[tag] = zkTag;
    }
    const arity = Store.arity(hash);
    const c0 = arity >= 1 ? Store.rawChild(hash, 0) : 0;
    const c1 = arity >= 2 ? Store.rawChild(hash, 1) : 0;
    const existing = formulaLookups.get(hash);
    if (existing) {
      existing.count++;
    } else {
      formulaLookups.set(hash, { tag: zkTag, c0, c1, count: 1 });
    }
  }

  function addFreevarLookup(substId, freevarHash, groundValue) {
    const key = `${substId}:${freevarHash}`;
    const existing = freevarRomEntries.get(key);
    if (existing) {
      existing.lookups++;
    } else {
      freevarRomEntries.set(key, { substId, freevarHash, groundValue, lookups: 1 });
    }
  }

  /**
   * Emit SubstChip rows for a pattern→ground tree walk.
   * Non-root entry: receives from SUBST_TREE_BUS.
   * Verifies structural matching + freevar consistency.
   *
   * Handles three row types:
   * - Internal (same tag): decompose both sides, recurse into children
   * - Freevar leaf: verify freevar consistency via FREEVAR_BUS
   * - Unwrap leaf: tag mismatch where new.c0 == old (wrapper node)
   */
  function emitSubstTree(oldHash, newHash, substId) {
    if (oldHash === newHash) return; // Identical hashes — no row needed

    const oldTag = Store.tag(oldHash);

    if (oldTag === 'freevar') {
      // Freevar leaf: verify old is freevar, check consistency via FREEVAR_BUS
      addFormulaLookup(oldHash); // FORMULA_BUS demand for old (freevar decomposition)
      addFreevarLookup(substId, oldHash, newHash);
      const c0_old = Store.rawChild(oldHash, 0);
      const zkTag = zkTags[oldTag] || 0;
      substRows.push([1, oldHash, newHash, 0, 1, substId, zkTag,
        typeof c0_old === 'number' ? c0_old : 0, 0, 0, 0, 0, 0, 0, 0, 0]);
      return;
    }

    const newTag = Store.isTerm(newHash) ? Store.tag(newHash) : null;
    if (newTag !== oldTag) {
      // Tag mismatch — check if new wraps old (e.g., bang(old) or loli(old, ...))
      if (Store.isTerm(newHash) && Store.rawChild(newHash, 0) === oldHash) {
        // Unwrap leaf: new.c0 == old. Decompose new side only via FORMULA_BUS.
        // Do NOT add old hash to formula ROM — unwrap rows don't demand it.
        addFormulaLookup(newHash);
        const newZkTag = zkTags[newTag] || 0;
        const c0_new = Store.rawChild(newHash, 0) || 0;
        const c1_new = Store.rawChild(newHash, 1) || 0;
        // is_unwrap=1, is_internal=0, non_root_int=0
        substRows.push([1, oldHash, newHash, 0, 0, substId, newZkTag,
          0, 0, c0_new, c1_new, 0, 0, 0, 0, 1]);
      }
      // else: genuine structural mismatch with no wrapper relationship — skip
      return;
    }

    // Internal node: decompose both sides, verify same tag
    addFormulaLookup(oldHash); // FORMULA_BUS demand for old (same-tag decomposition)
    addFormulaLookup(newHash);
    const zkTag = zkTags[oldTag] || 0;
    const c0_old = Store.rawChild(oldHash, 0) || 0;
    const c1_old = Store.rawChild(oldHash, 1) || 0;
    const c0_new = Store.rawChild(newHash, 0) || 0;
    const c1_new = Store.rawChild(newHash, 1) || 0;
    const c0_eq = (c0_old === c0_new) ? 1 : 0;
    const c1_eq = (c1_old === c1_new) ? 1 : 0;
    // Non-root: is_root=0, is_internal=1, non_root_int=1, is_unwrap=0
    substRows.push([1, oldHash, newHash, 0, 0, substId, zkTag,
      c0_old, c1_old, c0_new, c1_new, c0_eq, c1_eq, 1, 1, 0]);

    // Recurse for differing children (non-root verifies both c0 and c1)
    if (!c0_eq) emitSubstTree(c0_old, c0_new, substId);
    if (!c1_eq) emitSubstTree(c1_old, c1_new, substId);
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
  // opts.initialLinear overrides sequent extraction (used by chunked witness)
  const linear = opts.initialLinear || Seq.getContext(sequent, 'linear');
  const flatInit = linear.map(h => [1, h]);

  // --- FlatStepChip rows: one per forward step ---
  const flatStep = [];
  const flatStepPrep = [];  // preprocessed: canon_cons per step
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
    let groundAnt = 0, groundCons = 0, substId = 0;
    let canonCons = 0;

    // ground_cons = right-associated tensor of produced facts (ALL steps).
    // Verified by the cons spine FORMULA_BUS lookups.
    groundCons = step.produced.length === 0 ? oneHash : buildRightTensor(step.produced);
    consSpine = buildSpineIntermediates(step.produced, MAX_PRODUCED);

    if (isLoli) {
      // Original loli decomposition from Store (pattern, may have freevars)
      antHash = Store.child(groundLoli, 0);   // original antecedent pattern
      monadHash = Store.child(groundLoli, 1); // original monad
      consHash = Store.child(monadHash, 0);   // original consequent body pattern
      // Ground tensor of consumed (for antecedent spine verification)
      groundAnt = consumed.length === 0 ? oneHash : buildRightTensor(consumed);
      antSpine = buildSpineIntermediates(consumed, MAX_CONSUMED);
      // Canonical body: right-associate the body pattern's tensor tree.
      // Since tensor is associative, this preserves the leaf multiset.
      // Preprocessed (committed at keygen) — adversary cannot modify.
      const bodyLeaves = flattenTensor(consHash);
      canonCons = bodyLeaves.length === 0 ? oneHash : buildRightTensor(bodyLeaves);
    } else {
      antHash = consumed.length === 0 ? oneHash : buildRightTensor(consumed);
      consHash = groundCons; // compiled: cons_hash = ground_cons (both right-associated)
      monadHash = Store.put('monad', [consHash]);
      antSpine = buildSpineIntermediates(consumed, MAX_CONSUMED);
    }

    // Add formula ROM entries for spine verification
    addFormulaLookup(groundLoli); // loli(ant_hash, monad_hash)
    addFormulaLookup(monadHash);  // monad(cons_hash)

    // Loli antecedent spine: ground_ant tensor decomposition
    if (isLoli && consumed.length >= 2) {
      addFormulaLookup(groundAnt);
      for (let i = 0; i < antSpine.length; i++) {
        if (antSpine[i] !== 0 && consumed.length >= i + 3) {
          addFormulaLookup(antSpine[i]);
        }
      }
    }
    // Compiled antecedent spine: ant_hash tensor decomposition
    if (!isLoli && consumed.length >= 2) {
      addFormulaLookup(antHash);
      for (let i = 0; i < antSpine.length; i++) {
        if (antSpine[i] !== 0 && consumed.length >= i + 3) {
          addFormulaLookup(antSpine[i]);
        }
      }
    }
    // Consequent spine: ground_cons tensor decomposition (ALL steps)
    if (step.produced.length >= 2) {
      addFormulaLookup(groundCons);
      for (let i = 0; i < consSpine.length; i++) {
        if (consSpine[i] !== 0 && step.produced.length >= i + 3) {
          addFormulaLookup(consSpine[i]);
        }
      }
    }

    // Emit SubstChip tree walk rows for loli matching verification
    if (isLoli) {
      substId = substIdCtr++;
      // Antecedent: verify ant_hash (pattern) → ground_ant (ground tensor)
      emitSubstTree(antHash, groundAnt, substId);
      // Body: single demand for canon_cons → ground_cons.
      // canon_cons is the right-associated canonical form of consHash.
      // ground_cons is the right-associated tensor of produced facts.
      // Both have matching structure, so SubstChip walks successfully.
      emitSubstTree(canonCons, groundCons, substId);
    }

    // Build row (width 42)
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
    row.push(compiled);    // auxiliary: active * (1 - is_loli)
    row.push(groundAnt);   // ground antecedent tensor (loli only)
    row.push(groundCons);  // ground consequent tensor (all steps)
    row.push(substId);     // substitution instance ID (loli only)

    flatStep.push(row);
    flatStepPrep.push(canonCons);  // preprocessed: canonical body hash

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

  // --- Freevar ROM ---
  const freevar_rom = [];
  for (const entry of freevarRomEntries.values()) {
    freevar_rom.push([entry.substId, entry.freevarHash, entry.groundValue, 1, entry.lookups]);
  }

  // Build chips object
  const chips = {
    flat_init: flatInit,
    flat_step: flatStep,
    flat_final: flatFinal,
  };
  if (substRows.length > 0) chips.subst = substRows;

  return {
    format: 'flat',
    chips,
    flat_step_prep: flatStepPrep,  // preprocessed: canon_cons per step
    formula_rom,
    gamma_rom,
    freevar_rom,
    tags: zkTags,
    constants: { one_hash: oneHash },
  };
}

/**
 * Generate chunked flat ZK witnesses from a rewriting trace.
 *
 * Splits a long trace into chunks of at most maxRowsPerChunk steps,
 * producing an array of FlatWitnessJson objects with context continuity:
 * chunk[i].flat_final context == chunk[i+1].flat_init context.
 *
 * @param {Array} trace - Flat certificate (from buildRewriteTrace)
 * @param {Object} sequent - The sequent being proved (Store hashes)
 * @param {Object} [opts] - Options (same as generateFlatWitness)
 * @param {number} [opts.maxRowsPerChunk] - Max flat_step rows per chunk (default: 2^20)
 * @returns {Object[]} Array of FlatWitnessJson objects
 */
function generateChunkedFlatWitness(trace, sequent, opts = {}) {
  const maxRows = opts.maxRowsPerChunk || (1 << 20);

  if (trace.length <= maxRows) {
    return [generateFlatWitness(trace, sequent, opts)];
  }

  // Derive initial linear context from sequent
  const linear = Seq.getContext(sequent, 'linear');
  let currentLinear = [...linear];
  const chunks = [];

  for (let start = 0; start < trace.length; start += maxRows) {
    const end = Math.min(start + maxRows, trace.length);
    const segment = trace.slice(start, end);

    const chunk = generateFlatWitness(segment, sequent, {
      ...opts,
      initialLinear: currentLinear,
    });
    chunks.push(chunk);

    // Next chunk's init = this chunk's final context
    currentLinear = chunk.chips.flat_final.map(row => row[1]);
  }

  return chunks;
}

module.exports = { generateFlatWitness, generateChunkedFlatWitness, MAX_CONSUMED, MAX_PRODUCED };
