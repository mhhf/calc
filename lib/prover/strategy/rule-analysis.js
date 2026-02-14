/**
 * Rule Analysis — classify linear patterns as preserved, consumed, or produced.
 *
 * Preserved: identical pattern hash on both sides of -o (skip consume/produce).
 * Consumed: antecedent-only pattern (removed from state).
 * Produced: consequent-only pattern (added to state).
 *
 * Handles N:M multi-match via hash counting: min(n, m) preserved,
 * extra ante → consumed, extra conseq → produced.
 */

/**
 * Analyze a compiled rule's linear patterns.
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

module.exports = { analyzeRule };
