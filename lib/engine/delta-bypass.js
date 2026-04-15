/**
 * Delta bypass optimization for pattern matching.
 *
 * Strategy A: Direct child extraction for flat delta patterns.
 * Skips unification overhead for patterns where all bindings can be
 * resolved by positional child access on the content-addressed Store.
 */

const Store = require('../kernel/store');

// Reusable buffer for tracking slots written by delta bypass
const _deltaWritten = new Array(8);

/**
 * Try to match a flat delta pattern via direct child extraction.
 * Returns true if matched (theta/consumed mutated), false if no match.
 *
 * @param {number} pattern - Pattern hash
 * @param {number} origPos - Original position in antecedent linear list
 * @param {Object} rule - Compiled rule
 * @param {Object} state - FactSet-based State object
 * @param {Array} theta - Substitution bindings
 * @param {Map} consumed - Consumed fact counts
 * @param {Map} reserved - Reserved fact counts
 * @param {boolean} isPreserved - Whether pattern is preserved
 * @param {number} tagIdx - Pre-computed tag index for pattern
 */
function deltaBypass(pattern, origPos, rule, state, theta,
                          consumed, reserved, isPreserved, tagIdx) {
  const role = rule.patternRoles[origPos];
  if (!role || role.type !== 'delta' || !role.flat || isPreserved) return false;

  const meta = rule.linearMeta[pattern];
  const pred = meta.pred;
  const bindings = role.bindings;
  const gc = role.groundChecks;
  const candidates = tagIdx >= 0 ? state.linear.group(tagIdx) : state.groupForPred(pred);

  for (let ci = 0; ci < candidates.length; ci++) {
    const h = candidates[ci];
    const hTag = tagIdx >= 0 ? tagIdx : Store.tagId(h);
    const available = state.linear.count(hTag, h) - (consumed.get(h) || 0) - (reserved.get(h) || 0);
    if (available <= 0) continue;

    if (gc.length > 0) {
      let gcOk = true;
      for (let gi = 0; gi < gc.length; gi++) {
        if (Store.child(h, gc[gi].pos) !== gc[gi].value) { gcOk = false; break; }
      }
      if (!gcOk) continue;
    }

    let writtenCount = 0;
    let bindOk = true;
    for (let bi = 0; bi < bindings.length; bi++) {
      const val = Store.child(h, bindings[bi].pos);
      const slot = bindings[bi].slot;
      const existing = theta[slot];
      if (existing !== undefined) {
        if (existing !== val) { bindOk = false; break; }
      } else {
        theta[slot] = val;
        _deltaWritten[writtenCount++] = slot;
      }
    }

    if (bindOk) {
      consumed.set(h, (consumed.get(h) || 0) + 1);
      return true;
    }

    for (let wi = 0; wi < writtenCount; wi++) theta[_deltaWritten[wi]] = undefined;
  }

  return false;
}

module.exports = { deltaBypass };
