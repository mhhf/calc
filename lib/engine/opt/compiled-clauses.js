/**
 * Compiled clause dispatch for zero-subgoal backward clauses.
 *
 * Layer: Optimization (Tier 1 of compiled clause pipeline)
 *
 * Compiles zero-subgoal backward clauses into direct dispatch tables,
 * indexed by predicate head + first argument (WAM-style first-argument
 * indexing). For predicates with known modes (input/output positions),
 * provides fast persistent goal resolution without backchainer overhead.
 *
 * Pipeline position:
 *   FFI → State → **Compiled Clause** → Backward Cache → Full Clause
 *
 * Sound: the clause IS the proof for zero-subgoal clauses.
 * Complete for zero-subgoal clauses with known modes.
 * Falls through (returns null) for: no match, no modes, unresolvable goals.
 *
 * Theory compliance: partial evaluation (first Futamura projection) of
 * backward chainer specialized to zero-subgoal clause set. Equational
 * theory support (binlit ↔ i/o/e) via rewrite-on-mismatch.
 */

const Store = require('../../kernel/store');
const { isPredTag, getPredicateHead } = require('../../kernel/ast');

const _TAG_METAVAR = Store.TAG.metavar;

// Reusable local theta buffer for clause metavars.
// Safe: persistent proving pipeline is not reentrant.
const _MAX_LOCAL = 64;
const _localTheta = new Array(_MAX_LOCAL);

/**
 * First-argument head for index lookup.
 * Mirrors backchain.js getFirstArgHead — binlit → i/o/e mapping.
 */
function _firstArgHead(goal) {
  const arity = Store.arity(goal);
  if (arity === 0) return null;
  const a = Store.child(goal, 0);
  if (!Store.isTerm(a)) return null;
  const t = Store.tag(a);
  if (t === 'atom') return Store.child(a, 0);
  if (t === 'freevar' || t === 'metavar') return '_';
  if (isPredTag(t)) return t;
  if (t === 'binlit') {
    const v = Store.child(a, 0);
    if (v === 0n) return 'e';
    return (v & 1n) === 1n ? 'i' : 'o';
  }
  return null;
}

// ── Input Matching ──────────────────────────────────────────────────

/**
 * Match clause arg against goal arg at an INPUT position.
 * Clause metavars bind in localTheta[localSlots[hash]].
 * Equational theories applied on tag mismatch (binlit ↔ i/o/e).
 */
function _matchInput(ch, gh, localTheta, localSlots, theories) {
  if (ch === gh) return true;

  // Clause-side metavar
  if (Store.isTerm(ch) && Store.tagId(ch) === _TAG_METAVAR) {
    const s = localSlots[ch];
    if (s !== undefined) {
      if (localTheta[s] !== undefined) {
        return localTheta[s] === gh ||
               _matchInput(localTheta[s], gh, localTheta, localSlots, theories);
      }
      localTheta[s] = gh;
      return true;
    }
  }

  if (!Store.isTerm(ch) || !Store.isTerm(gh)) return false;

  const ct = Store.tagId(ch), gt = Store.tagId(gh);
  if (ct !== gt) {
    if (theories) {
      const th = theories[gt];
      if (th) {
        const rw = th.rewrite(gt, gh, ct, Store.arity(ch));
        if (rw !== null) return _matchInput(ch, rw, localTheta, localSlots, theories);
      }
    }
    return false;
  }

  const ca = Store.arity(ch);
  if (ca !== Store.arity(gh)) return false;
  for (let i = 0; i < ca; i++) {
    if (!_matchInput(Store.child(ch, i), Store.child(gh, i),
                     localTheta, localSlots, theories)) return false;
  }
  return true;
}

// ── Output Reconstruction ───────────────────────────────────────────

/**
 * Build output value from clause arg with resolved local metavars.
 */
function _buildOutput(ch, localTheta, localSlots) {
  if (Store.isTerm(ch) && Store.tagId(ch) === _TAG_METAVAR) {
    const s = localSlots[ch];
    return (s !== undefined && localTheta[s] !== undefined) ? localTheta[s] : ch;
  }
  if (!Store.isTerm(ch)) return ch;
  const a = Store.arity(ch);
  if (a === 0) return ch;
  let changed = false;
  const nc = new Array(a);
  for (let i = 0; i < a; i++) {
    const c = Store.child(ch, i);
    nc[i] = (typeof c === 'number' && Store.isTerm(c))
      ? _buildOutput(c, localTheta, localSlots) : c;
    if (nc[i] !== c) changed = true;
  }
  return changed ? Store.put(Store.tag(ch), nc) : ch;
}

// ── Build ───────────────────────────────────────────────────────────

/**
 * Build compiled clause dispatch table from backward chaining index.
 * Extracts zero-subgoal clauses, indexed by predHead → firstArgHead.
 *
 * @param {Object} backchainIndex - from backchain.buildIndex()
 * @returns {Object} dispatch: { predHead: { firstArg: [compiled, ...] } }
 */
function buildClauseDispatch(backchainIndex) {
  const dispatch = {};

  function add(index) {
    for (const pred in index) {
      for (const fa in index[pred]) {
        for (const [, compiled] of index[pred][fa]) {
          if (compiled.premises && compiled.premises.length !== 0) continue;
          if (!dispatch[pred]) dispatch[pred] = {};
          if (!dispatch[pred][fa]) dispatch[pred][fa] = [];
          dispatch[pred][fa].push(compiled);
        }
      }
    }
  }

  add(backchainIndex.clauses);
  add(backchainIndex.types);
  return dispatch;
}

// ── Dispatch ────────────────────────────────────────────────────────

/**
 * Try to prove a persistent goal via compiled clause dispatch.
 * Mode-driven: matches input positions, computes outputs.
 *
 * @param {Object} dispatch - from buildClauseDispatch()
 * @param {number} goal - instantiated goal hash
 * @param {Object} slots - forward-rule metavar hash → slot index
 * @param {Array} theta - forward-rule metavar bindings (mutated on success)
 * @param {Function|null} canonicalize - normalize output (i/o/e → binlit)
 * @param {Array|null} theories - equational theory lookup by tagId
 * @param {Object|null} parsedModes - { predName: ['+','-',...] }
 * @returns {true|null} true = proved, null = fall through
 */
function tryCompiledClause(dispatch, goal, slots, theta, canonicalize, theories, parsedModes) {
  const head = getPredicateHead(goal);
  if (!head) return null;

  const byFA = dispatch[head];
  if (!byFA) return null;

  const modes = parsedModes && parsedModes[head];
  if (!modes) return null;

  const arity = Store.arity(goal);
  if (arity !== modes.length) return null;

  // Gather candidates via first-argument indexing
  const fa = _firstArgHead(goal) || '_';
  let cands;
  if (fa !== '_') {
    const exact = byFA[fa], wild = byFA['_'];
    if (!exact && !wild) return null;
    cands = exact && wild ? exact.concat(wild) : (exact || wild);
  } else {
    cands = [];
    for (const k in byFA) {
      const b = byFA[k];
      if (Array.isArray(b)) for (let i = 0; i < b.length; i++) cands.push(b[i]);
    }
  }
  if (!cands || cands.length === 0) return null;

  for (let ci = 0; ci < cands.length; ci++) {
    const compiled = cands[ci];
    if (Store.arity(compiled.hash) !== arity) continue;
    if (compiled.metavarCount > _MAX_LOCAL) continue;

    // Reset local theta
    for (let j = 0; j < compiled.metavarCount; j++) _localTheta[j] = undefined;

    // Phase 1: match input positions
    let ok = true;
    for (let i = 0; i < arity; i++) {
      if (modes[i] !== '+') continue;
      if (!_matchInput(Store.child(compiled.hash, i), Store.child(goal, i),
                       _localTheta, compiled.localSlots, theories)) {
        ok = false; break;
      }
    }
    if (!ok) continue;

    // Phase 2: compute + bind output positions
    for (let i = 0; i < arity; i++) {
      if (modes[i] !== '-') continue;
      const out = _buildOutput(Store.child(compiled.hash, i), _localTheta, compiled.localSlots);
      const val = canonicalize ? canonicalize(out) : out;
      const ga = Store.child(goal, i);

      if (Store.isTerm(ga) && Store.tagId(ga) === _TAG_METAVAR) {
        const s = slots[ga];
        if (s !== undefined) {
          if (theta[s] !== undefined) {
            if (theta[s] !== val) { ok = false; break; }
          } else {
            theta[s] = val;
          }
        }
      } else if (ga !== val) {
        ok = false; break;
      }
    }
    if (!ok) continue;

    return true;
  }

  return null;
}

module.exports = { buildClauseDispatch, tryCompiledClause };
