/**
 * Rule Analysis — classify linear patterns as preserved, consumed, produced, or delta.
 *
 * Preserved: identical pattern hash on both sides of -o (skip consume/produce).
 * Consumed: antecedent-only pattern (removed from state).
 * Produced: consequent-only pattern (added to state).
 * Delta: same predicate head on both sides, different arguments (in-place update).
 *
 * Handles N:M multi-match via hash counting: min(n, m) preserved,
 * extra ante → consumed, extra conseq → produced, then delta pairing.
 */

const Store = require('../kernel/store');
const { getPredicateHead: getPredHead } = require('../kernel/ast');

/**
 * Analyze a compiled rule's linear patterns (v1: preserved detection).
 *
 * @param {Object} compiledRule - Output of forward.compileRule()
 * @returns {{ preserved: number[], consumed: number[], produced: number[] }}
 */
function analyzeRule(compiledRule) {
  const anteLinear = compiledRule.antecedent.linear || [];
  const conseqLinear = compiledRule.consequent.linear || [];

  // Count occurrences of each hash on each side
  const anteCount = new Map();
  for (const h of anteLinear) {
    anteCount.set(h, (anteCount.get(h) || 0) + 1);
  }

  const conseqCount = new Map();
  for (const h of conseqLinear) {
    conseqCount.set(h, (conseqCount.get(h) || 0) + 1);
  }

  const preserved = [];
  const consumed = [];
  const produced = [];

  // Process all unique hashes from both sides
  const allHashes = new Set([...anteCount.keys(), ...conseqCount.keys()]);
  for (const h of allHashes) {
    const ac = anteCount.get(h) || 0;
    const cc = conseqCount.get(h) || 0;
    const p = Math.min(ac, cc);

    for (let i = 0; i < p; i++) preserved.push(h);
    for (let i = 0; i < ac - p; i++) consumed.push(h);
    for (let i = 0; i < cc - p; i++) produced.push(h);
  }

  return { preserved, consumed, produced };
}

/**
 * Find which child positions differ between two same-pred patterns.
 * @param {number} anteHash
 * @param {number} conseqHash
 * @returns {number[]} indices where children differ
 */
function findChangedPositions(anteHash, conseqHash) {
  const a = Store.arity(anteHash);
  const changed = [];
  for (let i = 0; i < a; i++) {
    if (Store.child(anteHash, i) !== Store.child(conseqHash, i)) {
      changed.push(i);
    }
  }
  return changed;
}

/**
 * Analyze a compiled rule with delta detection (v2).
 *
 * Builds on v1: after identifying preserved patterns (identical hashes),
 * groups remaining consumed/produced by predicate head and pairs them
 * as deltas (same pred, different args).
 *
 * @param {Object} compiledRule - Output of forward.compileRule()
 * @returns {{
 *   preserved: number[],
 *   consumed: number[],
 *   produced: number[],
 *   deltas: Array<{ pred: string, anteHash: number, conseqHash: number, changedPositions: number[] }>
 * }}
 */
function analyzeDeltas(compiledRule) {
  const v1 = analyzeRule(compiledRule);

  // Group consumed and produced by predicate head
  const consumedByPred = new Map();
  for (const h of v1.consumed) {
    const pred = getPredHead(h);
    if (!pred) continue;
    if (!consumedByPred.has(pred)) consumedByPred.set(pred, []);
    consumedByPred.get(pred).push(h);
  }

  const producedByPred = new Map();
  for (const h of v1.produced) {
    const pred = getPredHead(h);
    if (!pred) continue;
    if (!producedByPred.has(pred)) producedByPred.set(pred, []);
    producedByPred.get(pred).push(h);
  }

  const deltas = [];

  // For each pred that appears in both consumed and produced, pair them
  for (const [pred, cList] of consumedByPred) {
    const pList = producedByPred.get(pred);
    if (!pList || pList.length === 0) continue;

    const pairs = Math.min(cList.length, pList.length);
    for (let i = 0; i < pairs; i++) {
      const anteHash = cList[i];
      const conseqHash = pList[i];
      const changedPositions = findChangedPositions(anteHash, conseqHash);

      deltas.push({ pred, anteHash, conseqHash, changedPositions });
    }
  }

  // Build remaining consumed/produced (excluding paired entries)
  const remainingConsumed = [];
  const remainingProduced = [];

  // Rebuild by iterating pred groups and skipping paired indices
  for (const [pred, cList] of consumedByPred) {
    const pList = producedByPred.get(pred);
    const pairs = pList ? Math.min(cList.length, pList.length) : 0;
    for (let i = pairs; i < cList.length; i++) {
      remainingConsumed.push(cList[i]);
    }
  }
  // Add consumed with no pred head (shouldn't happen, but be safe)
  for (const h of v1.consumed) {
    if (getPredHead(h) === null) remainingConsumed.push(h);
  }

  for (const [pred, pList] of producedByPred) {
    const cList = consumedByPred.get(pred);
    const pairs = cList ? Math.min(cList.length, pList.length) : 0;
    for (let i = pairs; i < pList.length; i++) {
      remainingProduced.push(pList[i]);
    }
  }
  for (const h of v1.produced) {
    if (getPredHead(h) === null) remainingProduced.push(h);
  }

  return {
    preserved: v1.preserved,
    consumed: remainingConsumed,
    produced: remainingProduced,
    deltas
  };
}

/**
 * Compute buffer size limits from rule structure.
 * Used to pre-size flat buffers for match worklist and theta.
 *
 * @param {Object} compiledRule - Output of forward.compileRule()
 * @returns {{ maxWorklist: number, maxTheta: number, linearCount: number, persistentCount: number }}
 */
function analyzeBufferLimits(compiledRule) {
  const linearPats = compiledRule.antecedent.linear || [];
  const persistentPats = compiledRule.antecedent.persistent || [];
  const linearCount = linearPats.length;
  const persistentCount = persistentPats.length;

  // Max worklist depth: sum of pattern tree depths across all linear patterns.
  // Each match(pattern, fact) decomposes through arity levels.
  let maxWorklist = 0;
  for (const p of linearPats) {
    maxWorklist += patternDepthSum(p);
  }

  // Max theta entries: count of distinct metavars across all patterns
  const allVars = new Set();
  for (const p of linearPats) collectMetavars(p, allVars);
  for (const p of persistentPats) collectMetavars(p, allVars);
  // Also count metavars in consequent (for substitution buffer sizing)
  const conseqLinear = compiledRule.consequent.linear || [];
  const conseqPersistent = compiledRule.consequent.persistent || [];
  for (const p of conseqLinear) collectMetavars(p, allVars);
  for (const p of conseqPersistent) collectMetavars(p, allVars);
  const maxTheta = allVars.size;

  return { maxWorklist, maxTheta, linearCount, persistentCount };
}

/**
 * Sum of all node counts in a pattern tree (upper bound on worklist entries).
 */
function patternDepthSum(h) {
  const t = Store.tag(h);
  if (!t) return 1;
  if (t === 'freevar' || t === 'atom') return 1;
  const a = Store.arity(h);
  let sum = 1;
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) sum += patternDepthSum(c);
  }
  return sum;
}

/**
 * Collect all metavar hashes from a pattern into a Set.
 */
function collectMetavars(h, out) {
  const t = Store.tag(h);
  if (!t) return;
  if (t === 'freevar') {
    const name = Store.child(h, 0);
    if (typeof name === 'string' && name.startsWith('_')) out.add(h);
    return;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) collectMetavars(c, out);
  }
}

/**
 * Compute cross-rule maximum buffer limits.
 * @param {Object[]} compiledRules - Array of compiled rules with .limits
 * @returns {{ maxWorklist: number, maxTheta: number }}
 */
function computeGlobalLimits(compiledRules) {
  let maxWorklist = 0;
  let maxTheta = 0;
  for (const r of compiledRules) {
    if (r.limits) {
      if (r.limits.maxWorklist > maxWorklist) maxWorklist = r.limits.maxWorklist;
      if (r.limits.maxTheta > maxTheta) maxTheta = r.limits.maxTheta;
    }
  }
  return { maxWorklist, maxTheta };
}

/**
 * Check if a pattern child is a metavar (freevar starting with _).
 * @param {number} h - Child hash
 * @returns {boolean}
 */
function isMetavarChild(h) {
  return Store.tag(h) === 'freevar' &&
    typeof Store.child(h, 0) === 'string' && Store.child(h, 0).startsWith('_');
}

/**
 * Compute per-position pattern roles for antecedent.linear.
 *
 * Each position gets: preserved, delta, or consumed.
 * Delta entries include precomputed metadata for bypass matching:
 * - bindings: [{pos, slot}] for direct child → theta binding
 * - flat: true if all children are metavars or ground (bypass safe)
 *
 * @param {number[]} anteLinear - Antecedent linear patterns
 * @param {Object} analysis - Output of analyzeDeltas()
 * @param {Object} slots - metavarSlots from compileRule
 * @returns {Array<{type: string, ...}>}
 */
function computePatternRoles(anteLinear, analysis, slots) {
  // Count remaining preserved/delta instances per hash
  const preservedLeft = {};
  for (const h of analysis.preserved) preservedLeft[h] = (preservedLeft[h] || 0) + 1;

  // Queue delta entries by anteHash for ordered assignment
  const deltaQueue = {};
  for (let di = 0; di < analysis.deltas.length; di++) {
    const d = analysis.deltas[di];
    if (!deltaQueue[d.anteHash]) deltaQueue[d.anteHash] = [];
    deltaQueue[d.anteHash].push(di);
  }
  const deltaUsed = {};

  const roles = [];
  for (let i = 0; i < anteLinear.length; i++) {
    const h = anteLinear[i];
    if (preservedLeft[h] > 0) {
      preservedLeft[h]--;
      roles.push({ type: 'preserved' });
    } else if (deltaQueue[h] && (deltaUsed[h] || 0) < deltaQueue[h].length) {
      const di = deltaQueue[h][deltaUsed[h] || 0];
      deltaUsed[h] = (deltaUsed[h] || 0) + 1;
      const delta = analysis.deltas[di];

      // Precompute bindings and ground checks for delta bypass
      const a = Store.arity(h);
      const bindings = [];
      const groundChecks = [];
      let flat = true;
      for (let j = 0; j < a; j++) {
        const c = Store.child(h, j);
        if (Store.isTermChild(c)) {
          if (isMetavarChild(c)) {
            bindings.push({ pos: j, slot: slots[c] });
          } else if (isGround(c)) {
            groundChecks.push({ pos: j, value: c });
          } else {
            flat = false; // compound non-ground child → can't bypass
          }
        } else {
          // Non-term child (string, bigint) — treated as literal to verify
          groundChecks.push({ pos: j, value: c });
        }
      }
      roles.push({ type: 'delta', deltaIdx: di, bindings, groundChecks, flat });
    } else {
      roles.push({ type: 'consumed' });
    }
  }
  return roles;
}

/**
 * Check if term is ground (no metavars). Used for delta bypass safety check.
 */
function isGround(h) {
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'freevar') return !Store.child(h, 0)?.startsWith('_');
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && !isGround(c)) return false;
  }
  return true;
}

/**
 * Precompute "compiled substitution" recipe for a consequent pattern.
 *
 * For flat patterns (children are metavars or literals), the recipe
 * allows Store.put(tag, [theta[s0], theta[s1], ...]) — no recursive traversal.
 *
 * @param {number} pattern - Consequent pattern hash
 * @param {Object} slots - metavarSlots from compileRule
 * @returns {{ tag: string, sources: Array, compiled: boolean } | null}
 */
function compileSubstitution(pattern, slots) {
  const tag = Store.tag(pattern);
  if (!tag) return null;
  if (tag === 'atom' || tag === 'freevar') {
    // Atom or freevar: check if it's a slotted metavar
    if (tag === 'freevar' && slots[pattern] !== undefined) {
      return { tag: null, slot: slots[pattern], compiled: true, isSlot: true };
    }
    return null; // literal, no sub needed
  }

  const a = Store.arity(pattern);
  const sources = [];
  let allResolved = true;

  for (let i = 0; i < a; i++) {
    const c = Store.child(pattern, i);
    if (!Store.isTermChild(c)) {
      // Non-term child (string, bigint) — literal
      sources.push({ type: 'literal', value: c });
    } else if (isMetavarChild(c) && slots[c] !== undefined) {
      sources.push({ type: 'slot', slot: slots[c] });
    } else if (isGround(c)) {
      sources.push({ type: 'literal', value: c });
    } else {
      allResolved = false;
      break;
    }
  }

  if (!allResolved) return null; // compound pattern, fall back to applyIndexed
  return { tag, sources, compiled: true, isSlot: false };
}

module.exports = {
  analyzeRule, analyzeDeltas, analyzeBufferLimits, computeGlobalLimits,
  computePatternRoles, compileSubstitution
};
