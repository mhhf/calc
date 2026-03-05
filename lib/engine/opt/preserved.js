/**
 * Preserved optimization — skip re-producing unchanged facts.
 *
 * When a rule's antecedent and consequent share linear patterns
 * (preserved facts), we skip consuming and re-producing them.
 * This avoids Store lookups and FactSet mutations for unchanged facts.
 */

/**
 * Build a skip-count map for preserved patterns.
 * Returns null if no preserved patterns.
 */
function buildPreservedSkip(preserved) {
  if (!preserved || preserved.length === 0) return null;
  const skipCount = {};
  for (const h of preserved) skipCount[h] = (skipCount[h] || 0) + 1;
  return skipCount;
}

/**
 * Filter linear patterns by removing preserved (re-produced) facts.
 * Used by explore multi-alt branches where compiled recipes aren't available.
 */
function filterPreserved(linearPats, preserved) {
  const skipCount = buildPreservedSkip(preserved);
  if (!skipCount) return linearPats;
  const skipUsed = {};
  const out = [];
  for (const p of linearPats) {
    if (skipCount[p] > 0 && (skipUsed[p] || 0) < skipCount[p]) {
      skipUsed[p] = (skipUsed[p] || 0) + 1;
      continue;
    }
    out.push(p);
  }
  return out;
}

module.exports = {
  buildPreservedSkip,
  filterPreserved,
};
