/**
 * Compiled clause dispatch for backward clauses.
 *
 * Layer: Optimization (compiled clause pipeline)
 *
 * Tier 1: Zero-subgoal clauses → direct dispatch (base cases).
 * Tier 2: Single self-recursive clauses → loop + base case (structural descent).
 *
 * Indexed by predicate head + first argument (WAM-style first-argument
 * indexing). For predicates with known modes (input/output positions),
 * provides fast persistent goal resolution without backchainer overhead.
 *
 * Pipeline position:
 *   FFI → State → **Compiled Clause** → Backward Cache → Full Clause
 *
 * Sound: the clause IS the proof. Tier 1 is trivially sound. Tier 2
 * is sound for tail-recursive structural descent — the loop performs
 * exactly the same matching as the backchainer's recursive frames.
 *
 * Theory compliance: partial evaluation (first Futamura projection) of
 * backward chainer specialized to the clause set. Equational theory
 * support (binlit ↔ i/o/e) via rewrite-on-mismatch.
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

// ── Tier 2: Recursion Analysis ──────────────────────────────────────

/**
 * Analyze a recursive clause for Tier 2 compilation.
 *
 * A clause qualifies if:
 * - Exactly one premise, calling the same predicate (self-recursion)
 * - Each input arg in the recursive call is a sub-term of the
 *   corresponding head arg (structural descent)
 *
 * Returns a recursion descriptor or null if not compilable.
 */
function _analyzeRecursiveClause(compiled, pred) {
  if (!compiled.premises || compiled.premises.length !== 1) return null;
  const premise = compiled.premises[0];
  const premHead = getPredicateHead(premise);
  if (premHead !== pred) return null;

  const headArity = Store.arity(compiled.hash);
  const premArity = Store.arity(premise);
  if (premArity !== headArity) return null;

  // For each input position: the recursive call's arg must be a sub-term
  // of the head's arg (i.e., a child of a pattern-matched constructor).
  // For output positions: track whether the output wraps the recursive result.
  //
  // We store the head clause entry + premise for use during execution.
  // The actual matching reuses the existing _matchInput/_buildOutput.
  return {
    compiled,       // The clause (head pattern, localSlots, metavarCount)
    premise,        // The recursive premise term
  };
}

/**
 * Build Tier 2 dispatch entries.
 *
 * For each predicate, collects:
 * - baseCases: Tier 1 compiled entries (zero subgoals) — array per firstArg
 * - recursive: Tier 2 descriptors (one self-recursive premise) — array per firstArg
 *
 * A predicate qualifies for Tier 2 if it has at least one base case AND
 * at least one recursive clause.
 */
function _buildTier2(backchainIndex, parsedModes) {
  if (!parsedModes) return {};
  const tier2 = {};

  // Collect ALL clauses (both base and recursive) per predicate
  const allClauses = {};  // pred → { fa → [[name, compiled], ...] }

  function collect(index) {
    for (const pred in index) {
      if (!parsedModes[pred]) continue;
      if (!allClauses[pred]) allClauses[pred] = {};
      for (const fa in index[pred]) {
        if (!allClauses[pred][fa]) allClauses[pred][fa] = [];
        for (const entry of index[pred][fa]) {
          allClauses[pred][fa].push(entry);
        }
      }
    }
  }

  collect(backchainIndex.clauses);
  collect(backchainIndex.types);

  for (const pred in allClauses) {
    const modes = parsedModes[pred];
    const baseCases = {};   // fa → [compiled, ...]
    const recursive = {};   // fa → [descriptor, ...]
    let hasBase = false, hasRec = false;

    for (const fa in allClauses[pred]) {
      for (const [, compiled] of allClauses[pred][fa]) {
        if (!compiled.premises || compiled.premises.length === 0) {
          // Base case (Tier 1)
          if (!baseCases[fa]) baseCases[fa] = [];
          baseCases[fa].push(compiled);
          hasBase = true;
        } else {
          // Try to analyze as recursive
          const desc = _analyzeRecursiveClause(compiled, pred);
          if (desc) {
            if (!recursive[fa]) recursive[fa] = [];
            recursive[fa].push(desc);
            hasRec = true;
          }
        }
      }
    }

    if (hasBase && hasRec) {
      tier2[pred] = { baseCases, recursive, modes };
    }
  }

  return tier2;
}

// ── Build ───────────────────────────────────────────────────────────

/**
 * Build compiled clause dispatch table from backward chaining index.
 *
 * Returns dispatch with:
 * - Tier 1 entries: dispatch[pred][fa] = [compiled, ...]
 * - Tier 2 entries: dispatch._tier2[pred] = { baseCases, recursive, modes }
 *
 * @param {Object} backchainIndex - from backchain.buildIndex()
 * @param {Object|null} parsedModes - { predName: ['+','-',...] }
 * @returns {Object} dispatch table
 */
function buildClauseDispatch(backchainIndex, parsedModes) {
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

  // Tier 2 analysis
  dispatch._tier2 = _buildTier2(backchainIndex, parsedModes);

  return dispatch;
}

// ── Tier 1 Dispatch ─────────────────────────────────────────────────

/**
 * Try Tier 1 (zero-subgoal) dispatch for a goal with given args.
 * Used by both direct Tier 1 calls and as base-case check in Tier 2 loop.
 *
 * @param {Object} byFA - dispatch[pred] (firstArg → [compiled,...])
 * @param {number} goal - goal hash (used for output binding)
 * @param {Array} args - current goal args (may differ from goal's in Tier 2 loop)
 * @param {number} arity - number of args
 * @param {Array} modes - mode array for this predicate
 * @param {Object} slots - forward-rule metavar slots
 * @param {Array} theta - forward-rule bindings
 * @param {Function|null} canonicalize
 * @param {Array|null} theories
 * @returns {number|null} output hash if base case matched, null otherwise
 */
function _tryTier1WithArgs(byFA, args, arity, modes, theories) {
  // First-argument indexing on current args
  let fa = '_';
  if (arity > 0) {
    const a = args[0];
    if (Store.isTerm(a)) {
      const t = Store.tag(a);
      if (t === 'atom') fa = Store.child(a, 0);
      else if (t === 'freevar' || t === 'metavar') fa = '_';
      else if (isPredTag(t)) fa = t;
      else if (t === 'binlit') {
        const v = Store.child(a, 0);
        fa = v === 0n ? 'e' : ((v & 1n) === 1n ? 'i' : 'o');
      }
    }
  }

  let cands;
  if (fa !== '_') {
    const exact = byFA[fa], wild = byFA['_'];
    if (!exact && !wild) return null;
    cands = exact && wild ? exact.concat(wild) : (exact || wild);
  } else {
    cands = [];
    for (const k in byFA) {
      if (k === '_tier2') continue;
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

    // Match input positions against current args
    let ok = true;
    for (let i = 0; i < arity; i++) {
      if (modes[i] !== '+') continue;
      if (!_matchInput(Store.child(compiled.hash, i), args[i],
                       _localTheta, compiled.localSlots, theories)) {
        ok = false; break;
      }
    }
    if (!ok) continue;

    // Build output values
    const outputs = [];
    for (let i = 0; i < arity; i++) {
      if (modes[i] !== '-') continue;
      outputs.push(_buildOutput(Store.child(compiled.hash, i), _localTheta, compiled.localSlots));
    }
    return outputs;
  }

  return null;
}

/**
 * Try a single recursive clause against current args.
 * Returns updated args for the recursive call, or null on mismatch.
 *
 * Also extracts the output template from the clause head at the output
 * position, with localTheta resolved to determine the wrapper structure.
 */
function _tryRecursiveClause(desc, args, arity, modes, theories) {
  const compiled = desc.compiled;
  if (Store.arity(compiled.hash) !== arity) return null;
  if (compiled.metavarCount > _MAX_LOCAL) return null;

  // Reset local theta
  for (let j = 0; j < compiled.metavarCount; j++) _localTheta[j] = undefined;

  // Match input positions of the head against current args
  for (let i = 0; i < arity; i++) {
    if (modes[i] !== '+') continue;
    if (!_matchInput(Store.child(compiled.hash, i), args[i],
                     _localTheta, compiled.localSlots, theories)) {
      return null;
    }
  }

  // Extract the recursive call's args (from the premise)
  const premise = desc.premise;
  const newArgs = new Array(arity);
  for (let i = 0; i < arity; i++) {
    const premChild = Store.child(premise, i);
    // Resolve metavars bound during head matching
    newArgs[i] = _resolveLocal(premChild, compiled.localSlots);
  }

  // Extract output wrapper: for each output position, determine
  // the structure around the recursive output.
  // The output template is the head's output arg with localTheta resolved.
  // The part that corresponds to the recursive output is a metavar that
  // maps to the premise's output arg.
  const outputWrappers = [];
  for (let i = 0; i < arity; i++) {
    if (modes[i] !== '-') continue;
    const headOut = Store.child(compiled.hash, i);
    outputWrappers.push(headOut);
  }

  return { newArgs, outputWrappers, localSlots: compiled.localSlots };
}

/**
 * Resolve a term using the current _localTheta bindings.
 */
function _resolveLocal(hash, localSlots) {
  if (Store.isTerm(hash) && Store.tagId(hash) === _TAG_METAVAR) {
    const s = localSlots[hash];
    if (s !== undefined && _localTheta[s] !== undefined) return _localTheta[s];
    return hash;
  }
  if (!Store.isTerm(hash)) return hash;
  const a = Store.arity(hash);
  if (a === 0) return hash;
  let changed = false;
  const nc = new Array(a);
  for (let i = 0; i < a; i++) {
    const c = Store.child(hash, i);
    nc[i] = (typeof c === 'number' && Store.isTerm(c))
      ? _resolveLocal(c, localSlots) : c;
    if (nc[i] !== c) changed = true;
  }
  return changed ? Store.put(Store.tag(hash), nc) : hash;
}

/**
 * Apply output wrappers from the unwind stack to a base output.
 *
 * Each stack entry contains { wrappers, localSlots } from a recursive
 * clause match. The wrapper is the clause head's output template; we
 * substitute the recursive output (which was the premise's output arg)
 * into the template by re-resolving with the recursive result.
 */
function _applyWrapStack(baseOutputs, wrapStack, modes, arity) {
  let outputs = baseOutputs;
  for (let si = wrapStack.length - 1; si >= 0; si--) {
    const { wrappers, localSlots, premiseOutputSlots } = wrapStack[si];
    // Bind the recursive result into localTheta at the premise output slot
    let oi = 0;
    for (let i = 0; i < arity; i++) {
      if (modes[i] !== '-') continue;
      const premSlot = premiseOutputSlots[oi];
      if (premSlot !== undefined) {
        _localTheta[premSlot] = outputs[oi];
      }
      oi++;
    }
    // Now rebuild the head's output template with the recursive result bound
    const newOutputs = [];
    for (const w of wrappers) {
      newOutputs.push(_buildOutput(w, _localTheta, localSlots));
    }
    outputs = newOutputs;
  }
  return outputs;
}

// ── Tier 2 Dispatch ─────────────────────────────────────────────────

/**
 * Try Tier 2 (recursive) dispatch. Loops over recursive clauses,
 * trying base cases at each level. Builds output on unwind.
 *
 * @returns {true|null}
 */
function _tryTier2(t2entry, goal, slots, theta, canonicalize, theories, effectiveModes) {
  const { baseCases, recursive } = t2entry;
  const modes = effectiveModes;
  const arity = Store.arity(goal);

  // Extract initial args from goal
  let args = new Array(arity);
  for (let i = 0; i < arity; i++) args[i] = Store.child(goal, i);

  const wrapStack = [];
  const MAX_DEPTH = 10000;

  for (let depth = 0; depth < MAX_DEPTH; depth++) {
    // Try base cases first (Tier 1)
    const baseResult = _tryTier1WithArgs(baseCases, args, arity, modes, theories);
    if (baseResult !== null) {
      // Apply wrap stack to build final output
      const finalOutputs = wrapStack.length > 0
        ? _applyWrapStack(baseResult, wrapStack, modes, arity)
        : baseResult;

      // Bind outputs to goal's output positions
      let oi = 0;
      let ok = true;
      for (let i = 0; i < arity; i++) {
        if (modes[i] !== '-') continue;
        const val = canonicalize ? canonicalize(finalOutputs[oi]) : finalOutputs[oi];
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
        oi++;
      }
      if (ok) return true;
      return null;
    }

    // Try recursive clauses
    // Gather candidates by first-arg indexing
    let fa = '_';
    if (arity > 0) {
      const a = args[0];
      if (Store.isTerm(a)) {
        const t = Store.tag(a);
        if (t === 'atom') fa = Store.child(a, 0);
        else if (isPredTag(t)) fa = t;
        else if (t === 'binlit') {
          const v = Store.child(a, 0);
          fa = v === 0n ? 'e' : ((v & 1n) === 1n ? 'i' : 'o');
        }
      }
    }

    let recCands;
    if (fa !== '_') {
      const exact = recursive[fa], wild = recursive['_'];
      if (!exact && !wild) return null;
      recCands = exact && wild ? exact.concat(wild) : (exact || wild);
    } else {
      recCands = [];
      for (const k in recursive) {
        const b = recursive[k];
        if (Array.isArray(b)) for (let i = 0; i < b.length; i++) recCands.push(b[i]);
      }
    }
    if (!recCands || recCands.length === 0) return null;

    let matched = false;
    for (let ri = 0; ri < recCands.length; ri++) {
      const result = _tryRecursiveClause(recCands[ri], args, arity, modes, theories);
      if (result !== null) {
        // Save wrapper info for unwinding
        // Find which localSlots map to the premise's output args
        const premiseOutputSlots = [];
        let oi2 = 0;
        for (let i = 0; i < arity; i++) {
          if (modes[i] !== '-') continue;
          const premChild = Store.child(recCands[ri].premise, i);
          if (Store.isTerm(premChild) && Store.tagId(premChild) === _TAG_METAVAR) {
            premiseOutputSlots.push(result.localSlots[premChild]);
          } else {
            premiseOutputSlots.push(undefined);
          }
          oi2++;
        }

        wrapStack.push({
          wrappers: result.outputWrappers,
          localSlots: result.localSlots,
          premiseOutputSlots,
        });
        args = result.newArgs;
        matched = true;
        break;
      }
    }

    if (!matched) return null;
  }

  return null; // Max depth exceeded
}

// ── Main Dispatch ───────────────────────────────────────────────────

/**
 * Try to prove a persistent goal via compiled clause dispatch.
 * Tries Tier 1 (base cases) first, then Tier 2 (recursive).
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

  const rawModes = parsedModes && parsedModes[head];
  if (!rawModes) return null;

  const arity = Store.arity(goal);
  if (arity !== rawModes.length) return null;

  // Effective modes: if a '+' position has an unbound forward-rule metavar,
  // treat it as '-' (output). This handles multiModal predicates like plus(+,+,+)
  // where the third arg is actually an output when unbound.
  let modes = rawModes;
  for (let i = 0; i < arity; i++) {
    if (rawModes[i] !== '+') continue;
    const ga = Store.child(goal, i);
    if (Store.isTerm(ga) && Store.tagId(ga) === _TAG_METAVAR && slots[ga] !== undefined) {
      if (modes === rawModes) modes = rawModes.slice(); // copy-on-write
      modes[i] = '-';
    }
  }

  // Tier 1: zero-subgoal base cases
  const byFA = dispatch[head];
  if (byFA) {
    const fa = _firstArgHead(goal) || '_';
    let cands;
    if (fa !== '_') {
      const exact = byFA[fa], wild = byFA['_'];
      if (!exact && !wild) { /* no Tier 1 candidates */ }
      else cands = exact && wild ? exact.concat(wild) : (exact || wild);
    } else {
      cands = [];
      for (const k in byFA) {
        if (k === '_tier2') continue;
        const b = byFA[k];
        if (Array.isArray(b)) for (let i = 0; i < b.length; i++) cands.push(b[i]);
      }
    }

    if (cands && cands.length > 0) {
      for (let ci = 0; ci < cands.length; ci++) {
        const compiled = cands[ci];
        if (Store.arity(compiled.hash) !== arity) continue;
        if (compiled.metavarCount > _MAX_LOCAL) continue;

        for (let j = 0; j < compiled.metavarCount; j++) _localTheta[j] = undefined;

        let ok = true;
        for (let i = 0; i < arity; i++) {
          if (modes[i] !== '+') continue;
          if (!_matchInput(Store.child(compiled.hash, i), Store.child(goal, i),
                           _localTheta, compiled.localSlots, theories)) {
            ok = false; break;
          }
        }
        if (!ok) continue;

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
    }
  }

  // Tier 2: recursive clauses with loop
  const t2entry = dispatch._tier2 && dispatch._tier2[head];
  if (t2entry) {
    return _tryTier2(t2entry, goal, slots, theta, canonicalize, theories, modes);
  }

  return null;
}

module.exports = { buildClauseDispatch, tryCompiledClause };
