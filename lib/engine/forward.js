/**
 * Forward Chaining Engine
 *
 * Multiset rewriting with committed choice (no backtracking).
 * Runs until quiescence (no rules can fire).
 *
 * State: { linear: { hash: count }, persistent: { hash: true } }
 * Rules: precompiled from MDE with { antecedent, consequent }
 */

const Store = require('../kernel/store');
const { NON_PRED_TAGS, getPredicateHead } = require('../kernel/ast');
const { matchIndexed: _matchIdx, undoSave, undoRestore, undoDiscard } = require('../kernel/unify');
const { applyIndexed: _subApplyIdx, subCompiled } = require('../kernel/substitute');
const ffi = require('./ffi');
const { analyzeDeltas, analyzeBufferLimits, computePatternRoles, compileSubstitution } = require('./rule-analysis');

// Profiling (enabled via CALC_PROFILE env var)
const PROFILE = process.env.CALC_PROFILE === '1';
const TRACE_MATCHES = process.env.CALC_TRACE_MATCHES === '1';
const profile = {
  matchTime: 0, matchCalls: 0,
  subTime: 0, subCalls: 0,
  proveTime: 0, proveCalls: 0,
};
// Per-tryMatch instrumentation (enabled via CALC_TRACE_MATCHES=1)
let _tmMatchCalls = 0;
const _tmLog = [];  // { rule, matchCalls, success }
function getTryMatchLog() { return _tmLog; }
function resetTryMatchLog() { _tmLog.length = 0; }

// Stage 6: indexed match wrapper (O(1) metavar lookup via compile-time slots)
function matchIdx(pattern, hash, theta, slots) {
  if (TRACE_MATCHES) _tmMatchCalls++;
  if (!PROFILE) return _matchIdx(pattern, hash, theta, slots);
  const t0 = performance.now();
  const result = _matchIdx(pattern, hash, theta, slots);
  profile.matchTime += performance.now() - t0;
  profile.matchCalls++;
  return result;
}

// Stage 6: indexed substitute wrapper (O(1) metavar lookup via compile-time slots)
function subApplyIdx(hash, theta, slots) {
  if (!PROFILE) return _subApplyIdx(hash, theta, slots);
  const t0 = performance.now();
  const result = _subApplyIdx(hash, theta, slots);
  profile.subTime += performance.now() - t0;
  profile.subCalls++;
  return result;
}

function getProfile() { return profile; }
function resetProfile() {
  profile.matchTime = profile.matchCalls = 0;
  profile.subTime = profile.subCalls = 0;
  profile.proveTime = profile.proveCalls = 0;
}


/**
 * Build index from state linear facts.
 * Groups facts by their predicate head for O(1) lookup.
 *
 * Optional secondary index: for a specified predicate, builds a mapping from
 * one child position (keyPos) to fact hash. This enables O(1) lookup when
 * matching patterns like `code(PC, OPCODE)` where PC is known from context.
 *
 * Generalized from EVM-specific `codeByPC` — works for any binary+ predicate.
 * See doc/dev/forward-optimization-roadmap.md "Fingerprint indexing".
 *
 * @param {{ [hash: number]: number }} linear
 * @param {Object} [fpConfig] - Fingerprint config: { pred, keyPos }
 * @returns {Object} byPred index with optional ._byKey secondary index
 */
function buildStateIndex(linear, fpConfig) {
  const byPred = {};
  const byKey = fpConfig ? {} : null;
  const fpPred = fpConfig ? fpConfig.pred : null;
  const fpKeyPos = fpConfig ? fpConfig.keyPos : -1;

  for (const hStr of Object.keys(linear)) {
    const h = Number(hStr);
    const pred = getPredicateHead(h);
    if (pred) {
      if (!byPred[pred]) byPred[pred] = [];
      byPred[pred].push(h);

      // Secondary index: map keyPos value → fact hash for fingerprint predicate
      if (pred === fpPred && Store.arity(h) > fpKeyPos) {
        byKey[Store.child(h, fpKeyPos)] = h;
      }
    } else {
      if (!byPred['*']) byPred['*'] = [];
      byPred['*'].push(h);
    }
  }

  // Attach secondary index metadata (avoids spread copy).
  // _fpPred/_fpKeyPos used by symexec indexAdd/indexRemove for incremental updates.
  byPred._byKey = byKey;
  byPred._fpPred = fpPred;
  byPred._fpKeyPos = fpKeyPos;
  // Backward compat alias
  byPred.codeByPC = byKey;
  return byPred;
}

/**
 * Flatten tensor spine into list of formulas
 * Extracts: linear resources and !-wrapped persistent facts
 *
 * Linear: must be consumed exactly once
 * Persistent: can be used any number of times (marked with !)
 *
 * @param {number} h - Hash of tensor expression
 * @returns {{ linear: number[], persistent: number[] }}
 */
function flattenTensor(h) {
  const linear = [];
  const persistent = [];

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;

    if (t === 'tensor') {
      walk(Store.child(hash, 0));
      walk(Store.child(hash, 1));
    } else if (t === 'bang') {
      persistent.push(Store.child(hash, 0));
    } else {
      linear.push(hash);
    }
  }

  walk(h);
  return { linear, persistent };
}

/**
 * Extract monad body (unwrap {A} -> A)
 * @param {number} h
 * @returns {number}
 */
function unwrapMonad(h) {
  if (Store.tag(h) === 'monad') return Store.child(h, 0);
  return h;
}

/**
 * Extract the second argument from a flat predicate. O(1).
 * {tag: 'code', children: [PC, OPCODE]} → OPCODE
 *
 * @param {number} h - Pattern hash
 * @returns {number|null} - Second argument hash or null
 */
function extractSecondArg(h) {
  const t = Store.tag(h);
  if (!t || NON_PRED_TAGS.has(t)) return null;
  return Store.arity(h) >= 2 ? Store.child(h, 1) : null;
}

/**
 * Check if a hash is a ground term (no freevars)
 * Ground terms can be used as keys in opcode index
 *
 * @param {number} h - Hash to check
 * @returns {boolean}
 */
function isGround(h) {
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'freevar') return false;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (typeof c === 'number' && !isGround(c)) return false;
  }
  return true;
}

// --- Choice expansion (moved from symexec.js for precomputation in compileRule) ---

/**
 * Expand a single hash into alternatives, recursing through with/tensor/bang.
 * Each alternative is { linear: number[], persistent: number[] }.
 */
function expandItem(h) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [] }];

  if (t === 'with') {
    return [
      ...expandItem(Store.child(h, 0)),
      ...expandItem(Store.child(h, 1))
    ];
  }
  if (t === 'tensor') {
    const lefts = expandItem(Store.child(h, 0));
    const rights = expandItem(Store.child(h, 1));
    const out = [];
    for (const l of lefts) {
      for (const r of rights) {
        out.push({
          linear: [...l.linear, ...r.linear],
          persistent: [...l.persistent, ...r.persistent]
        });
      }
    }
    return out;
  }
  if (t === 'bang') {
    return [{ linear: [], persistent: [Store.child(h, 0)] }];
  }
  if (t === 'loli') {
    const c0 = Store.child(h, 0);
    const c1 = Store.child(h, 1);
    if (Store.tag(c0) === 'bang' && Store.tag(c1) === 'monad') {
      const bodyAlts = expandItem(Store.child(c1, 0));
      return bodyAlts.map(a => ({
        linear: a.linear,
        persistent: [c0, ...a.persistent]
      }));
    }
  }
  return [{ linear: [h], persistent: [] }];
}

/**
 * Expand compiled consequent into choice alternatives.
 * @param {{ linear: number[], persistent: number[] }} consequent
 * @returns {{ linear: number[], persistent: number[] }[]}
 */
function expandConsequentChoices(consequent) {
  let alts = [{ linear: [], persistent: [] }];

  for (const h of (consequent.linear || [])) {
    const itemAlts = expandItem(h);
    const next = [];
    for (const acc of alts) {
      for (const ia of itemAlts) {
        next.push({
          linear: [...acc.linear, ...ia.linear],
          persistent: [...acc.persistent, ...ia.persistent]
        });
      }
    }
    alts = next;
  }

  const origPersistent = consequent.persistent || [];
  if (origPersistent.length > 0) {
    alts = alts.map(a => ({
      linear: a.linear,
      persistent: [...a.persistent, ...origPersistent]
    }));
  }

  return alts;
}

/**
 * Compile forward rule for efficient matching
 *
 * Input: hash of `A * B * !C -o { D * E }`
 * Output: { antecedent: { linear: [...], persistent: [...] },
 *           consequent: { linear: [...], persistent: [...] },
 *           triggerPreds: string[],
 *           opcodeHash: number|null }
 *
 * @param {{ hash: number, antecedent: number, consequent: number }} rule
 * @returns {Object} Compiled rule
 */
function compileRule(rule) {
  const anteFlat = flattenTensor(rule.antecedent);
  const conseqBody = unwrapMonad(rule.consequent);
  const conseqFlat = flattenTensor(conseqBody);

  // Extract trigger predicates from linear antecedents for rule indexing
  const triggerPreds = [];
  let discriminator = null;

  for (const h of (anteFlat.linear || [])) {
    const pred = getPredicateHead(h);
    if (pred && !triggerPreds.includes(pred)) {
      triggerPreds.push(pred);
    }
    // Detect fingerprint discriminator: any binary+ predicate with a ground child.
    // The ground child is the discriminator value (used for O(1) rule lookup).
    // The non-ground child position is the key (used for secondary index lookup).
    // See doc/dev/forward-optimization-roadmap.md "Fingerprint indexing".
    if (!discriminator) {
      const arity = Store.arity(h);
      if (arity >= 2) {
        for (let ci = 0; ci < arity; ci++) {
          const child = Store.child(h, ci);
          if (typeof child === 'number' && isGround(child)) {
            discriminator = {
              pred,
              groundPos: ci,
              groundValue: child,
              keyPos: ci === 0 ? 1 : 0
            };
            break;
          }
        }
      }
    }
  }

  // Backward compat: opcodeHash = discriminator's ground value
  const opcodeHash = discriminator ? discriminator.groundValue : null;

  // Precompute persistent output vars (freevars in last arg of persistent patterns)
  const persistentOutputVars = new Set();
  for (const p of (anteFlat.persistent || [])) {
    for (const v of collectOutputVars(p)) {
      persistentOutputVars.add(v);
    }
  }

  // Precompute per-linear-pattern metadata (eliminates Store.get walks in tryMatch)
  const linearMeta = {};
  for (const p of (anteFlat.linear || [])) {
    if (p in linearMeta) continue;
    const pred = getPredicateHead(p);
    const freevars = collectFreevars(p);
    const persistentDeps = new Set();
    for (const v of freevars) {
      if (persistentOutputVars.has(v)) persistentDeps.add(v);
    }
    // For fingerprint predicate: extract key sub-pattern for secondary index O(1) lookup
    let secondaryKeyPattern = null;
    if (discriminator && pred === discriminator.pred) {
      const kp = discriminator.keyPos;
      if (Store.arity(p) > kp) {
        secondaryKeyPattern = Store.child(p, kp);
      }
    }
    linearMeta[p] = { pred, freevars, persistentDeps, secondaryKeyPattern };
  }

  // Stage 6: de Bruijn slot assignment — compile-time metavar → slot index mapping.
  // Enables O(1) theta lookup in matchIndexed/applyIndexed instead of O(n) scan.
  // See doc/research/de-bruijn-indexed-matching.md.
  const allMetavars = new Set();
  for (const p of (anteFlat.linear || [])) collectMetavarsLocal(p, allMetavars);
  for (const p of (anteFlat.persistent || [])) collectMetavarsLocal(p, allMetavars);
  for (const p of (conseqFlat.linear || [])) collectMetavarsLocal(p, allMetavars);
  for (const p of (conseqFlat.persistent || [])) collectMetavarsLocal(p, allMetavars);

  const metavarSlots = {};
  let slotIdx = 0;
  for (const v of allMetavars) metavarSlots[v] = slotIdx++;
  const metavarCount = slotIdx;

  const compiled = {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: conseqFlat,
    triggerPreds,
    opcodeHash,
    discriminator,
    persistentOutputVars,
    linearMeta,
    metavarSlots,
    metavarCount
  };

  // Stage 2: attach preserved/delta analysis metadata
  compiled.analysis = analyzeDeltas(compiled);

  // Stage 5a: precompute buffer size limits
  compiled.limits = analyzeBufferLimits(compiled);

  // Stage 5f: precompute consequent choice alternatives
  compiled.consequentAlts = expandConsequentChoices(compiled.consequent);

  // Stage 7a: per-position pattern roles (preserved/delta/consumed)
  // Delta roles include precomputed bindings for bypass matching.
  compiled.patternRoles = computePatternRoles(
    anteFlat.linear || [], compiled.analysis, metavarSlots
  );

  // Stage 7c: compiled substitution recipes for consequent patterns.
  // Flat patterns (children are metavar slots or literals) get a recipe
  // that bypasses recursive applyIndexed traversal.
  compiled.compiledConseqLinear = (conseqFlat.linear || []).map(
    p => compileSubstitution(p, metavarSlots)
  );
  compiled.compiledConseqPersistent = (conseqFlat.persistent || []).map(
    p => compileSubstitution(p, metavarSlots)
  );

  return compiled;
}

/**
 * Build rule index by trigger predicates
 * Groups rules by predicates they care about for O(1) lookup
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ [predicate: string]: Object[] }}
 */
function buildRuleIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.triggerPreds && rule.triggerPreds.length > 0) {
      for (const pred of rule.triggerPreds) {
        if (!index[pred]) index[pred] = [];
        index[pred].push(rule);
      }
    } else {
      // Rules with no indexable predicates go to '*' bucket
      if (!index['*']) index['*'] = [];
      index['*'].push(rule);
    }
  }
  return index;
}

/**
 * Build opcode index for EVM-style rule selection
 * Maps opcode binary hash directly to rule for O(1) lookup
 *
 * @param {Object[]} rules - Compiled rules
 * @returns {{ [opcodeHash: number]: Object }}
 */
function buildOpcodeIndex(rules) {
  const index = {};
  for (const rule of rules) {
    if (rule.opcodeHash) {
      index[rule.opcodeHash] = rule;
    }
  }
  return index;
}

/**
 * Auto-detect fingerprint configuration from compiled rules.
 *
 * Finds the most common discriminator predicate across rules, then detects
 * the "pointer predicate" — a unary predicate that shares a variable with
 * the key position of the discriminator pattern.
 *
 * Example for EVM: discriminator pred = 'code' (40 rules have ground opcodes),
 * pointer pred = 'pc' (unary, shares _PC with code's key position 0).
 *
 * Generalizes EVM-specific opcodeLayer to work with any program structure.
 * See doc/dev/forward-optimization-roadmap.md "Fingerprint indexing".
 *
 * @param {Object[]} rules - Compiled rules with .discriminator
 * @returns {{ pred: string, keyPos: number, groundPos: number, pointerPred: string|null }|null}
 */
function detectFingerprintConfig(rules) {
  // Count discriminator predicates across rules
  const discCounts = {};
  for (const r of rules) {
    if (r.discriminator) {
      const key = r.discriminator.pred;
      discCounts[key] = (discCounts[key] || 0) + 1;
    }
  }

  // Find dominant discriminator predicate (need ≥2 rules to justify an index)
  let bestPred = null, bestCount = 0;
  for (const pred in discCounts) {
    if (discCounts[pred] > bestCount) {
      bestPred = pred;
      bestCount = discCounts[pred];
    }
  }
  if (!bestPred || bestCount < 2) return null;

  // Get representative positions from first matching rule
  const sample = rules.find(r => r.discriminator && r.discriminator.pred === bestPred);
  const { groundPos, keyPos } = sample.discriminator;

  // Auto-detect pointer predicate: a unary linear pattern that shares
  // a variable with the key position of the discriminator pattern.
  // For EVM: pc(_PC) shares _PC with code(_PC, OPCODE) at keyPos=0.
  let pointerPred = null;
  for (const r of rules) {
    if (!r.discriminator || r.discriminator.pred !== bestPred) continue;
    for (const lp of (r.antecedent.linear || [])) {
      if (getPredicateHead(lp) !== bestPred) continue;
      const keyVar = Store.child(lp, keyPos);
      if (Store.tag(keyVar) !== 'freevar') continue;
      for (const lp2 of (r.antecedent.linear || [])) {
        if (lp2 === lp) continue;
        const pred2 = getPredicateHead(lp2);
        if (pred2 && Store.arity(lp2) === 1 && Store.child(lp2, 0) === keyVar) {
          pointerPred = pred2;
          break;
        }
      }
      if (pointerPred) break;
    }
    if (pointerPred) break;
  }

  return { pred: bestPred, keyPos, groundPos, pointerPred };
}

/**
 * EVM strategy: Use PC→code→opcode for O(1) rule selection
 *
 * For EVM execution, the PC uniquely determines which rule fires:
 * 1. PC points to address X
 * 2. code X OPCODE tells us the opcode
 * 3. Opcode maps directly to rule
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object} stateIndex - State facts indexed by predicate
 * @param {Object} opcodeIndex - opcodeHash → rule mapping
 * @returns {Object|null} - The matching rule, or null if strategy doesn't apply
 */
function evmStrategy(state, stateIndex, opcodeIndex) {
  // 1. Get PC fact (must be exactly one)
  const pcFacts = stateIndex['pc'];
  if (!pcFacts || pcFacts.length !== 1) return null;

  // 2. Extract PC value: {tag: 'pc', children: [VALUE]}
  const pcHash = pcFacts[0];
  if (Store.arity(pcHash) < 1) return null;
  const pcValue = Store.child(pcHash, 0);

  // 3. Find code fact at this PC: code PC OPCODE
  const codeFacts = stateIndex['code'];
  if (!codeFacts) return null;

  for (const codeHash of codeFacts) {
    if (Store.arity(codeHash) < 2) continue;

    const codePC = Store.child(codeHash, 0);
    const opcodeHash = Store.child(codeHash, 1);

    if (codePC !== pcValue) continue;

    // 4. Look up rule by opcode
    const rule = opcodeIndex[opcodeHash];
    if (rule) return rule;
  }

  return null;
}

/**
 * Collect all metavar hashes from a pattern into a Set.
 * (Inline version — same as rule-analysis.collectMetavars.)
 */
function collectMetavarsLocal(h, out) {
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
    if (typeof c === 'number') collectMetavarsLocal(c, out);
  }
}

/**
 * Collect all freevars in a pattern
 * @param {number} h - Pattern hash
 * @returns {Set<number>}
 */
function collectFreevars(h) {
  const vars = new Set();

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === 'freevar') {
      vars.add(hash);
      return;
    }
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (typeof c === 'number') walk(c);
    }
  }

  walk(h);
  return vars;
}

/**
 * Collect OUTPUT freevars from a persistent pattern
 *
 * Convention: For patterns like inc(PC, PC') or plus(A, B, C),
 * the LAST argument is the output (result), others are inputs.
 *
 * @param {number} h - Persistent pattern hash
 * @returns {Set<number>}
 */
function collectOutputVars(h) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;

  const a = Store.arity(h);
  if (NON_PRED_TAGS.has(t) || a === 0) return vars;
  for (const v of collectFreevars(Store.child(h, a - 1))) {
    vars.add(v);
  }
  return vars;
}

// FFI metadata cache (avoid repeated object lookups)
const _ffiMeta = ffi.defaultMeta;

// Pre-parsed mode arrays for each FFI predicate (avoids parseMode allocation)
const _ffiParsedModes = {};
for (const key in _ffiMeta) {
  _ffiParsedModes[key] = ffi.mode.parseMode(_ffiMeta[key].mode);
}

// Reusable args buffer (max 4 children — covers all FFI arities)
const _ffiArgs = [0, 0, 0, 0];

/**
 * Try FFI directly for a goal, bypassing the full prove() machinery.
 * Returns FFI result or null if no FFI is available.
 *
 * @param {number} goal - Goal term hash (already substituted)
 * @returns {{ success: boolean, theta?: Array }|null}
 */
function tryFFIDirect(goal) {
  const goalTag = Store.tag(goal);
  if (!goalTag) return null;

  let head;
  if (!NON_PRED_TAGS.has(goalTag)) head = goalTag;
  else if (goalTag === 'atom') head = Store.child(goal, 0);
  else return null;

  const meta = _ffiMeta[head];
  if (!meta) return null;

  const fn = ffi.get(meta.ffi);
  if (!fn) return null;

  // Inline mode check + populate reusable args buffer (avoids Store.children allocation)
  const modes = _ffiParsedModes[head];
  const goalArity = Store.arity(goal);
  if (goalArity !== modes.length) return null;

  for (let i = 0; i < goalArity; i++) {
    const c = Store.child(goal, i);
    if (modes[i] === '+' && !ffi.convert.isGround(c)) return null;
    _ffiArgs[i] = c;
  }

  return fn(_ffiArgs);
}

/**
 * Try to match a rule against state with interleaved matching
 *
 * Uses worklist algorithm: try to match patterns, defer those that depend on
 * persistent output variables, use persistent proving to bind those vars, repeat.
 *
 * @param {Object} rule - Compiled rule
 * @param {Object} state - { linear, persistent, index }
 * @param {Object} calc - { clauses, types } for backward proving
 * @param {Object} [matchOpts] - { optimizePreserved }
 * @returns {{ rule, theta, consumed } | null}
 */
// Reusable work buffers for resourcePatterns (avoids [...antecedent.linear] copy per tryMatch)
const _workPatterns = new Array(32);
const _workPositions = new Array(32);  // parallel: original position in antecedent.linear
const _deltaWritten = new Array(8);   // Stage 7b: slots written during delta bypass (max ~4 per pattern)

function tryMatch(rule, state, calc, matchOpts) {
  const _tmStart = TRACE_MATCHES ? _tmMatchCalls : 0;
  const consumed = {};
  const reserved = {}; // preserved patterns: reserved but not consumed

  // Build index if not already present
  const index = state.index || buildStateIndex(state.linear);

  // Stage 6: indexed theta with O(1) metavar lookup via compile-time slots.
  // theta[slot] = value; slots[metavarHash] = slotIndex.
  // See doc/research/de-bruijn-indexed-matching.md.
  //
  // CRITICAL: save _undoLen at entry so we can reset it on exit (success or failure).
  // matchIndexed writes to the global _undoStack. If we don't reset on exit,
  // _undoLen grows monotonically across tryMatch calls, eventually overflowing.
  const topUndo = undoSave();
  const { linearMeta, metavarSlots: slots, metavarCount } = rule;
  const theta = new Array(metavarCount);

  // Build preserved count for O(1) lookup (how many of each hash are preserved)
  const preservedCount = {};
  const usePreserved = matchOpts && matchOpts.optimizePreserved && rule.analysis;
  if (usePreserved) {
    for (const h of rule.analysis.preserved) {
      preservedCount[h] = (preservedCount[h] || 0) + 1;
    }
  }
  const persistentList = rule.antecedent.persistent || [];

  // Copy linear patterns into reusable work buffer (avoids array allocation)
  const linearPats = rule.antecedent.linear || [];
  const patternRoles = rule.patternRoles;
  let rpLen = linearPats.length;
  for (let i = 0; i < rpLen; i++) {
    _workPatterns[i] = linearPats[i];
    _workPositions[i] = i;
  }

  let persistentIdx = 0;
  let iterations = 0;
  const maxIterations = rpLen + persistentList.length + 10;

  while (rpLen > 0 || persistentIdx < persistentList.length) {
    iterations++;
    if (iterations > maxIterations) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      undoRestore(theta, topUndo);
      return null;
    }

    let madeProgress = false;

    // Try to match resource patterns (in-place deferred tracking)
    let deferredLen = 0;
    for (let pi = 0; pi < rpLen; pi++) {
      const pattern = _workPatterns[pi];
      const origPos = _workPositions[pi];
      const meta = linearMeta[pattern];

      // Defer if pattern depends on persistent output vars not yet bound.
      // Stage 6: O(1) slot lookup instead of O(n) theta scan.
      if (meta.persistentDeps.size > 0) {
        let hasUnbound = false;
        for (const v of meta.persistentDeps) {
          if (theta[slots[v]] === undefined) { hasUnbound = true; break; }
        }
        if (hasUnbound) {
          _workPatterns[deferredLen] = pattern;
          _workPositions[deferredLen] = origPos;
          deferredLen++;
          continue;
        }
      }

      const pred = meta.pred;

      // Check if this pattern is preserved (reserve, don't consume)
      const isPreserved = usePreserved && preservedCount[pattern] > 0;

      // Stage 7b: delta bypass — direct child extraction instead of full matchIdx.
      // For flat delta patterns (all children are metavars or ground), extract
      // children directly via Store.child. Skips worklist decomposition entirely.
      // Skip for preserved patterns (those use reserve logic, not consume).
      const role = patternRoles[origPos];
      if (role && role.type === 'delta' && role.flat && !isPreserved) {
        const bindings = role.bindings;
        const gc = role.groundChecks;
        const candidates = index[pred] || [];
        let found = false;
        for (const h of candidates) {
          const count = state.linear[h] || 0;
          const available = count - (consumed[h] || 0) - (reserved[h] || 0);
          if (available <= 0) continue;

          // Verify ground children (if any)
          if (gc.length > 0) {
            let gcOk = true;
            for (let gi = 0; gi < gc.length; gi++) {
              if (Store.child(h, gc[gi].pos) !== gc[gi].value) { gcOk = false; break; }
            }
            if (!gcOk) continue;
          }

          // Bind metavar children directly. Track which slots we write
          // so we can undo on failure (max ~3 bindings per delta pattern).
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
            consumed[h] = (consumed[h] || 0) + 1;
            found = true;
            madeProgress = true;
            break;
          }

          // Undo: clear slots we wrote for this failed candidate
          for (let wi = 0; wi < writtenCount; wi++) {
            theta[_deltaWritten[wi]] = undefined;
          }
        }

        if (found) continue;
        // Fall through to regular matchIdx if bypass found no match
      }

      // Secondary index O(1) lookup for fingerprint predicate
      if (pred === index._fpPred && index._byKey && meta.secondaryKeyPattern !== null) {
        const keyValue = subApplyIdx(meta.secondaryKeyPattern, theta, slots);
        const codeFact = index._byKey[keyValue];
        if (codeFact) {
          const count = state.linear[codeFact] || 0;
          const available = count - (consumed[codeFact] || 0) - (reserved[codeFact] || 0);
          if (available > 0) {
            // Stage 6: save undo position, restore on failure
            const savedUndo = undoSave();
            const ok = matchIdx(pattern, codeFact, theta, slots);
            if (ok) {
              if (isPreserved) {
                reserved[codeFact] = (reserved[codeFact] || 0) + 1;
                preservedCount[pattern]--;
              } else {
                consumed[codeFact] = (consumed[codeFact] || 0) + 1;
              }
              madeProgress = true;
              continue;
            }
            undoRestore(theta, savedUndo);
          }
        }
      }

      // Get candidate facts from index
      let candidates;
      if (pred) {
        candidates = index[pred] || [];
      } else {
        candidates = index['*'] || Object.keys(state.linear).map(Number);
      }

      // Try to match against indexed candidates
      let found = false;
      for (const h of candidates) {
        const count = state.linear[h] || 0;
        const available = count - (consumed[h] || 0) - (reserved[h] || 0);
        if (available <= 0) continue;

        const savedUndo = undoSave();
        const ok = matchIdx(pattern, h, theta, slots);
        if (ok) {
          if (isPreserved) {
            reserved[h] = (reserved[h] || 0) + 1;
            preservedCount[pattern]--;
          } else {
            consumed[h] = (consumed[h] || 0) + 1;
          }
          found = true;
          madeProgress = true;
          break;
        }
        undoRestore(theta, savedUndo);
      }

      if (!found) {
        if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
        undoRestore(theta, topUndo);
        return null;
      }
    }

    rpLen = deferredLen;

    // Try persistent patterns
    while (persistentIdx < persistentList.length) {
      const pPattern = persistentList[persistentIdx];
      const goal = subApplyIdx(pPattern, theta, slots);

      // Try FFI directly (bypasses full prove() machinery)
      // FFI returns pair format [[v,t]], convert to indexed via slots
      const ffiResult = tryFFIDirect(goal);
      if (ffiResult) {
        if (ffiResult.success) {
          const ft = ffiResult.theta;
          for (let fi = 0; fi < ft.length; fi++) {
            const slot = slots[ft[fi][0]];
            if (slot !== undefined) theta[slot] = ft[fi][1];
          }
          persistentIdx++;
          madeProgress = true;
          continue;
        }
        // FFI available but returned false (e.g. neq(5,5)) — definitive failure
        break;
      }

      // Fallback to full backward proving (no FFI for this predicate)
      if (calc && calc.clauses && calc.types) {
        const backward = require('./prove');
        const t0 = PROFILE ? performance.now() : 0;
        const result = backward.prove(goal, calc.clauses, calc.types, {
          maxDepth: 50,
          index: calc.backwardIndex
        });
        if (PROFILE) {
          profile.proveTime += performance.now() - t0;
          profile.proveCalls++;
        }
        if (result.success) {
          const rt = result.theta;
          for (let ri = 0; ri < rt.length; ri++) {
            const slot = slots[rt[ri][0]];
            if (slot !== undefined) theta[slot] = rt[ri][1];
          }
          persistentIdx++;
          madeProgress = true;
          continue;
        }
      }

      break;
    }

    if (!madeProgress && (rpLen > 0 || persistentIdx < persistentList.length)) {
      if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: false });
      undoRestore(theta, topUndo);
      return null;
    }
  }

  if (TRACE_MATCHES) _tmLog.push({ rule: rule.name, matchCalls: _tmMatchCalls - _tmStart, success: true });
  // Reset undo stack position (keep theta bindings, just prevent _undoLen overflow)
  undoDiscard(topUndo);
  // Return indexed theta + slots for downstream consumers (applyMatch, mutateState)
  return { rule, theta, slots, consumed, optimized: !!usePreserved };
}

// Reusable state wrapper for findMatch (avoids { ...state, index } spread per step)
const _findMatchState = { linear: null, persistent: null, index: null };

/**
 * Find first matching rule (committed choice)
 *
 * Uses multiple optimization strategies:
 * 1. EVM strategy (optional): PC→code→opcode for O(1) rule selection
 * 2. State index: facts grouped by predicate for fast pattern matching
 * 3. Strict filtering: only try rules where ALL trigger predicates exist in state
 *
 * @param {Object} state - { linear, persistent }
 * @param {Object[]} rules - Compiled rules (or { rules, ruleIndex, opcodeIndex } for cached)
 * @param {Object} calc - { clauses, types } for backward proving
 * @param {Object} [matchOpts] - { optimizePreserved }
 * @returns {{ rule, theta, consumed } | null}
 */
function findMatch(state, rules, calc, matchOpts) {
  // Build state index once (reuse object to avoid { ...state } spread per step)
  const stateIndex = buildStateIndex(state.linear, rules.fpConfig || null);
  _findMatchState.linear = state.linear;
  _findMatchState.persistent = state.persistent;
  _findMatchState.index = stateIndex;
  const indexedState = _findMatchState;

  // Get rule list and optional opcode index
  const ruleList = rules.rules || rules;
  const opcodeIndex = rules.opcodeIndex || null;

  // Strategy 1: EVM opcode-based O(1) lookup
  // If we have an opcode index and PC+code facts, try exact rule first
  if (opcodeIndex) {
    const heuristicRule = evmStrategy(state, stateIndex, opcodeIndex);
    if (heuristicRule) {
      const m = tryMatch(heuristicRule, indexedState, calc, matchOpts);
      if (m) return m;
    }
  }

  // Strategy 2: Strict predicate filtering (direct stateIndex lookup, no Set/entries)
  for (const rule of ruleList) {
    const triggers = rule.triggerPreds;
    if (triggers && triggers.length > 0) {
      let allPresent = true;
      for (let i = 0; i < triggers.length; i++) {
        const arr = stateIndex[triggers[i]];
        if (!arr || arr.length === 0) { allPresent = false; break; }
      }
      if (!allPresent) continue;
    }
    const m = tryMatch(rule, indexedState, calc, matchOpts);
    if (m) return m;
  }
  return null;
}

/**
 * Apply match: consume resources, produce new ones
 *
 * @param {Object} state - { linear, persistent }
 * @param {{ rule, theta, consumed }} m - Match result
 * @returns {Object} New state
 */
function applyMatch(state, { rule, theta, slots, consumed, optimized }) {
  // Remove consumed linear resources
  const newLinear = { ...state.linear };
  for (const hStr in consumed) {
    const hash = Number(hStr);
    newLinear[hash] -= consumed[hStr];
    if (newLinear[hash] <= 0) delete newLinear[hash];
  }

  // Build skip count for preserved consequent patterns
  let skipCount = null;
  if (optimized && rule.analysis) {
    skipCount = {};
    for (const h of rule.analysis.preserved) {
      skipCount[h] = (skipCount[h] || 0) + 1;
    }
  }
  const skipUsed = {};

  // Add produced linear resources (Stage 7c: compiled substitution when available)
  const cLinear = rule.compiledConseqLinear;
  const linPats = rule.consequent.linear || [];
  for (let i = 0; i < linPats.length; i++) {
    const pattern = linPats[i];
    if (skipCount && skipCount[pattern] > 0 &&
        (skipUsed[pattern] || 0) < skipCount[pattern]) {
      skipUsed[pattern] = (skipUsed[pattern] || 0) + 1;
      continue;
    }
    const recipe = cLinear && cLinear[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(pattern, theta, slots);
    newLinear[h] = (newLinear[h] || 0) + 1;
  }

  const newPersistent = { ...state.persistent };
  const cPersistent = rule.compiledConseqPersistent;
  const persPats = rule.consequent.persistent || [];
  for (let i = 0; i < persPats.length; i++) {
    const pattern = persPats[i];
    const recipe = cPersistent && cPersistent[i];
    const h = recipe && recipe.compiled
      ? subCompiled(recipe, theta)
      : subApplyIdx(pattern, theta, slots);
    newPersistent[h] = true;
  }

  return { linear: newLinear, persistent: newPersistent };
}

/**
 * Run forward chaining until quiescence
 *
 * @param {Object} state - { linear: { hash: count }, persistent: { hash: true } }
 * @param {Object[]} rules - Compiled rules
 * @param {Object} opts - { maxSteps, trace, calc, useEvmStrategy }
 * @returns {{ state, quiescent: boolean, steps: number, trace?: string[] }}
 */
function run(state, rules, opts = {}) {
  const maxSteps = opts.maxSteps || 1000;
  const trace = opts.trace ? [] : null;
  const calc = opts.calc || null;
  const useEvmStrategy = opts.useEvmStrategy !== false; // enabled by default
  const optimizePreserved = opts.optimizePreserved !== false; // enabled by default
  let steps = 0;

  // Build indices once for all steps
  const ruleIndex = buildRuleIndex(rules);
  const opcodeIndex = useEvmStrategy ? buildOpcodeIndex(rules) : null;
  const fpConfig = detectFingerprintConfig(rules);
  const indexedRules = { rules, ruleIndex, opcodeIndex, fpConfig };

  const matchOpts = optimizePreserved ? { optimizePreserved: true } : undefined;

  // Build backward prover index once (2x speedup)
  if (calc && calc.clauses && calc.types && !calc.backwardIndex) {
    const backward = require('./prove');
    calc.backwardIndex = backward.buildIndex(calc.clauses, calc.types);
  }

  while (steps < maxSteps) {
    const m = findMatch(state, indexedRules, calc, matchOpts);
    if (!m) {
      return { state, quiescent: true, steps, trace };
    }

    if (trace) {
      trace.push(`[${steps}] ${m.rule.name}`);
    }

    state = applyMatch(state, m);
    steps++;
  }

  return { state, quiescent: false, steps, trace };
}

/**
 * Create initial state from multisets
 *
 * @param {{ [hash: number]: number }} linear
 * @param {{ [hash: number]: boolean }} persistent
 */
function createState(linear = {}, persistent = {}) {
  return { linear, persistent };
}

module.exports = {
  compileRule,
  flattenTensor,
  unwrapMonad,
  buildRuleIndex,
  buildStateIndex,
  buildOpcodeIndex,
  evmStrategy,
  detectFingerprintConfig,
  tryMatch,
  findMatch,
  applyMatch,
  run,
  createState,
  getPredicateHead,
  expandItem,
  expandConsequentChoices,
  // Profiling (enable with CALC_PROFILE=1)
  getProfile,
  resetProfile,
  // Per-tryMatch tracing (enable with CALC_TRACE_MATCHES=1)
  getTryMatchLog,
  resetTryMatchLog
};
