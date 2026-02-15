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

const Store = require('../../kernel/store');
const { NON_PRED_TAGS } = require('../../kernel/ast');

/**
 * Get the predicate head of a formula. O(1).
 * @param {number} h - Hash of formula
 * @returns {string|null}
 */
function getPredHead(h) {
  const t = Store.tag(h);
  if (!t) return null;
  if (!NON_PRED_TAGS.has(t)) return t;
  if (t === 'atom') return Store.child(h, 0);
  return null;
}

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

module.exports = { analyzeRule, analyzeDeltas, analyzeBufferLimits, computeGlobalLimits };
