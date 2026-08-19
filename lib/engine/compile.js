/**
 * Rule Compiler — prepare forward rules for efficient matching.
 *
 * Input: raw rule { name, hash, antecedent, consequent }
 * Output: compiled rule with indexes, slots, analysis metadata
 *
 * Pure data transformation — no runtime state dependencies.
 */

import Store from '../kernel/store.js';
import { isPredTag, predHead } from '../kernel/ast.js';
import { deltaAnalysis, patternRoles, compileSub } from './rule-analysis.js';
import { isGround, collectMetavars, collectFreevars } from './pattern-utils.js';
import { resolveConn, flattenAnte, unwrapComp, expandChoice, expandConsqChoices } from './formula-utils.js';
import { classifyFirstArg as _classifyCompact } from '../kernel/eq-theory.js';
import { add as _ratAdd } from '../rat.js';
import { monadUnit } from './grades.js';
// ─── In-memory compile cache ─────────────────────────────────────────────────
// compileRule is pure (same hash + connectives → same result except name/sourceLabel).
// Cache keyed on rule.hash; name/sourceLabel patched on hit.
// Cleared on Store.clear() (hashes invalidated) but survives Store.restore().
const _compileCache = new Map();
Store.onClear(() => _compileCache.clear());

// --- Term walkers (see formula-utils.js for resolveConn, flattenAnte, unwrapComp) ---

/** Collect OUTPUT freevars from persistent pattern using mode info.
 *  Only positions with mode '-' are true outputs.
 *  Falls back to last-argument convention when no mode info is available.
 *  @param {number} h - Persistent pattern hash
 *  @param {Function|null} getModes - (pred) → string[]|null (e.g., ['+','+','-']) */
function outputVars(h, getModes) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;
  const a = Store.arity(h);
  if (!isPredTag(t) || a === 0) return vars;

  const pred = predHead(h);
  const modes = getModes ? getModes(pred) : null;
  if (modes) {
    for (let i = 0; i < Math.min(a, modes.length); i++) {
      if (modes[i] === '-') {
        for (const v of collectFreevars(Store.child(h, i))) vars.add(v);
      }
    }
    return vars;
  }

  // Fallback: last argument convention for unknown predicates
  for (const v of collectFreevars(Store.child(h, a - 1))) {
    vars.add(v);
  }
  return vars;
}

// --- Choice expansion (see formula-utils.js for expandChoice, expandConsqChoices) ---

// --- Rule compilation ---

/**
 * Compile a forward rule for efficient matching.
 *
 * Input: { name, hash, antecedent, consequent }
 * Output: compiled rule with trigger predicates, de Bruijn slots,
 *         discriminator, pattern roles, compiled substitutions.
 */
function compileRule(rule, opts = {}) {
  const ct = opts.connectives;
  if (!ct) throw new Error('compileRule requires opts.connectives');

  // Cache key is epoch-qualified: compilation depends on opts (connectives,
  // getModes, discriminatorPreds), so callers with distinct configs must not
  // share entries — the calculus config supplies a cacheEpoch string
  // (ILL: 'ill'); unconfigured direct callers share the '' namespace
  // (audit round 11: cross-config poisoning hazard).
  const _cacheKey = opts.cacheEpoch ? opts.cacheEpoch + ':' + rule.hash : rule.hash;
  const cached = _compileCache.get(_cacheKey);
  if (cached) {
    // SHALLOW clone: array/object fields (antecedent.linear, windows,
    // readOnly, consequentAlts, ...) are SHARED with the cached entry and
    // every other clone. Invariant: compiled-rule internals are immutable
    // after compileRule returns — callers may only reassign top-level
    // properties, never mutate nested arrays (audit round 12, Finding 3).
    const clone = Object.assign({}, cached);
    clone.name = rule.name;
    clone.sourceLabel = rule.sourceLabel || null;
    return clone;
  }

  const rc = resolveConn(ct, opts.gradeConfig);
  const getModes = opts.getModes || null;

  // Phase A: Flatten antecedent/consequent product spines
  const anteFlat = flattenAnte(rule.antecedent, rc);
  const conseqBody = unwrapComp(rule.consequent, rc);
  const conseqFlat = flattenAnte(conseqBody, rc);

  // Phase A2: timed wrapper stripping (TODO_0265 Phase 3).
  // after/before are scheduling annotations, never facts — they leave the
  // pattern list into rule-level guard metadata (slot-compiled below).
  // readPreserved(A) unwraps to the plain pattern A, recorded in readOnly:
  // the matcher routes it through the reserved path (E7.2 — matched, never
  // consumed, never re-produced). Kernel-tag wrappers, calculus-agnostic.
  const _windowsRaw = { after: [], before: [] };
  const _readOnly = [];
  {
    const lin = anteFlat.linear;
    for (let i = lin.length - 1; i >= 0; i--) {
      const t = Store.tag(lin[i]);
      if (t === 'after' || t === 'before') {
        _windowsRaw[t].push(Store.child(lin[i], 0));
        lin.splice(i, 1);
      } else if (t === 'readPreserved') {
        lin[i] = Store.child(lin[i], 0);
        _readOnly.push(lin[i]);
      }
    }
    _windowsRaw.after.reverse();
    _windowsRaw.before.reverse();
  }

  // Phase B: Trigger predicates and discriminator detection.
  // Stamped patterns at(P, t) report P's predicate: the till index policy
  // files at-wrapped facts under the INNER predicate group (D5), so
  // triggers, linearMeta and candidate enumeration must all agree on P —
  // reporting 'at' would make such rules invisible to hasPredicate /
  // groupForPred / disc-tree relevantTagIds (audit round 12, F1).
  const triggerPreds = [];
  let discriminator = null;

  for (const h of (anteFlat.linear || [])) {
    // Unwrap counted parcels (bang(k, A), D4) then stamps (at(A, t)) — the
    // trigger predicate is the INNERMOST pattern's head in both cases.
    const isCounted = Store.tag(h) === rc.exponential;
    const body = isCounted ? Store.child(h, 1) : h;
    const isAt = Store.tag(body) === 'at';
    const pred = isAt ? predHead(Store.child(body, 0)) : predHead(body);
    if (pred && !triggerPreds.includes(pred)) triggerPreds.push(pred);
    // Wrapped patterns don't drive fingerprint discriminators — the child
    // layout below indexes the wrapper node, not P (stamp fingerprints: Phase 4).
    if (isAt || isCounted) continue;

    // Detect fingerprint discriminator: predicate with ground child.
    // Prefer non-arrlit ground values (binlit/atom vary per-rule, arrlit shared).
    const arity = pred ? Store.arity(h) : 0;
    if (arity >= 1) {
      for (let ci = 0; ci < arity; ci++) {
        const child = Store.child(h, ci);
        if (typeof child === 'number' && isGround(child)) {
          const candidate = {
            pred,
            groundPos: ci,
            groundValue: child,
            keyPos: arity === 1 ? 0 : (ci === 0 ? 1 : 0)
          };
          if (!discriminator) {
            discriminator = candidate;
          } else if (Store.tag(discriminator.groundValue) === 'arrlit' && Store.tag(child) !== 'arrlit') {
            // Prefer non-arrlit (better discrimination across rules)
            discriminator = candidate;
          }
          break;
        }
      }
    }
  }

  // Phase B2: Virtual discriminator — scan persistent antecedents for
  // !<discPred> B PC GROUND. Which predicates qualify comes from the domain
  // config (opts.discriminatorPreds, e.g. ILL/EVM: ['arr_get']); each must
  // have the (array, index, value) argument shape. No config → no virtual
  // discriminators (TODO_0265 Phase 2b).
  const _discPreds = opts.discriminatorPreds;
  if (!discriminator && _discPreds && _discPreds.length > 0) {
    for (const p of (anteFlat.persistent || [])) {
      const pred = predHead(p);
      if (_discPreds.includes(pred) && Store.arity(p) >= 3) {
        const valueChild = Store.child(p, 2);
        const arrayVar = Store.child(p, 0);
        const indexVar = Store.child(p, 1);

        // Find unary linear patterns sharing array/pointer variables
        let arrayPred = null, pointerPred = null;
        for (const lp of (anteFlat.linear || [])) {
          const lpPred = predHead(lp);
          if (!lpPred || Store.arity(lp) !== 1) continue;
          if (Store.child(lp, 0) === arrayVar) arrayPred = lpPred;
          if (Store.child(lp, 0) === indexVar) pointerPred = lpPred;
        }
        if (!arrayPred || !pointerPred) continue;

        if (typeof valueChild === 'number' && isGround(valueChild)) {
          discriminator = {
            type: 'virtual',
            pred: pred,
            groundPos: 2,
            groundValue: valueChild,
            keyPos: 1,
            arrayPred,
            pointerPred
          };
          break;
        }
      }
    }
  }

  // Phase C: Persistent output vars (used locally for dependency detection)
  const persistentOutputVars = new Set();
  for (const p of (anteFlat.persistent || [])) {
    for (const v of outputVars(p, getModes)) persistentOutputVars.add(v);
  }

  // Phase D: Per-linear-pattern metadata (avoids Store.get walks in tryMatch)
  const linearMeta = {};
  let _hasCounted = false;
  for (const p of (anteFlat.linear || [])) {
    if (p in linearMeta) continue;
    // Counted parcel bang(k, A) (D4): record the count spec and the inner
    // pattern; matching/consumption semantics belong to the timed matcher.
    const isCounted = Store.tag(p) === rc.exponential;
    let countTake = 0, countVar = 0, body = p;
    if (isCounted) {
      _hasCounted = true;
      const g = Store.child(p, 0);
      const gTag = Store.tag(g);
      if (gTag === 'binlit') {
        const k = Store.child(g, 0);
        if (k < 1n) throw new Error(`Rule '${rule.name}': count grade must be >= 1 (got ${k})`);
        countTake = Number(k);
      } else if (gTag === 'metavar' || gTag === 'freevar') {
        countVar = g;
      } else {
        throw new Error(`Rule '${rule.name}': count grade must be a positive integer or a variable (D4), got '${gTag}'`);
      }
      body = Store.child(p, 1);
    }
    const isAtP = Store.tag(body) === 'at';
    const pred = isAtP ? predHead(Store.child(body, 0)) : predHead(body);
    const freevars = collectFreevars(p);
    const persistentDeps = new Set();
    for (const v of freevars) {
      if (persistentOutputVars.has(v)) persistentDeps.add(v);
    }
    let secondaryKeyPattern = null;
    if (!isAtP && !isCounted && discriminator && pred === discriminator.pred) {
      const kp = discriminator.keyPos;
      if (Store.arity(p) > kp) secondaryKeyPattern = Store.child(p, kp);
    }
    linearMeta[p] = { pred, freevars, persistentDeps, secondaryKeyPattern,
      countTake, countVar, body };
  }

  // Phase E: Expand consequent choices (opens exists binders, expands additive choices)
  const consequentAlts = expandConsqChoices(conseqFlat, rc);

  // Phase F: De Bruijn slot assignment (metavar → slot index)
  const anteMetavars = new Set();
  for (const p of (anteFlat.linear || [])) collectMetavars(p, anteMetavars);
  for (const p of (anteFlat.persistent || [])) collectMetavars(p, anteMetavars);

  // Collect metavars from expanded alternatives (includes exists-opened freevars)
  // Loli variables live in a deferred scope — they get bound when the loli fires,
  // NOT when the rule fires, so they must be excluded from existential detection.
  const allMetavars = new Set(anteMetavars);
  const loliMetavars = new Set();
  for (const alt of consequentAlts) {
    for (const p of (alt.linear || [])) {
      if (rc.implication && Store.tag(p) === rc.implication) {
        collectMetavars(p, loliMetavars);
        // Still add to allMetavars for slot assignment
        collectMetavars(p, allMetavars);
      } else {
        collectMetavars(p, allMetavars);
      }
    }
    for (const p of (alt.persistent || [])) collectMetavars(p, allMetavars);
  }

  const metavarSlots = {};
  let slotIdx = 0;
  for (const v of allMetavars) metavarSlots[v] = slotIdx++;
  const metavarCount = slotIdx;

  // Phase G: Existential slots (metavars in consequent but NOT in antecedent, NOT in lolis)
  const existentialSlots = [];
  for (const v of allMetavars) {
    if (!anteMetavars.has(v) && !loliMetavars.has(v)) existentialSlots.push(metavarSlots[v]);
  }

  // Map existential slot → persistent consequent patterns using that slot.
  // Only include goals shared by ALL consequent alternatives — these are genuine
  // existential resolvers (e.g., eq_bool, gt, to256). Goals specific to individual
  // alternatives are oplus guards (e.g., neq, eq) used by satFilter, not
  // by resolveEx. Including them would block existential resolution
  // when an unbound guard goal comes before the resolving goal in prove order.
  const existentialGoals = {};
  if (existentialSlots.length > 0) {
    const numAlts = consequentAlts.length;
    for (const p of (consequentAlts[0].persistent || [])) {
      // For multi-alt rules, skip goals not present in ALL alternatives
      if (numAlts > 1) {
        let inAll = true;
        for (let ai = 1; ai < numAlts; ai++) {
          if (!(consequentAlts[ai].persistent || []).includes(p)) { inAll = false; break; }
        }
        if (!inAll) continue;
      }
      const pvars = collectFreevars(p);
      for (const v of pvars) {
        if (!anteMetavars.has(v) && metavarSlots[v] !== undefined) {
          const slot = metavarSlots[v];
          if (!existentialGoals[slot]) existentialGoals[slot] = [];
          if (!existentialGoals[slot].includes(p)) existentialGoals[slot].push(p);
        }
      }
    }
  }

  // Phase H: Assemble compiled output + analysis metadata
  //
  // Always use first expanded alternative as effective consequent.
  // - Single-alt: the only alternative (exists opened, bang extracted)
  // - Multi-alt: first choice (committed choice picks first; explore uses consequentAlts)
  // This ensures deltaAnalysis, compiledConseq*, and resolveEx
  // all see opened patterns — NOT raw exists/with/oplus nodes.
  const effectiveConseq = consequentAlts[0];

  // Detect grade-0 content in antecedent or consequent
  const hasGrade0 = (anteFlat.grade0 && anteFlat.grade0.length > 0) ||
    consequentAlts.some(a => a.grade0 && a.grade0.length > 0);

  const compiled = {
    name: rule.name,
    hash: rule.hash,           // Original ILL formula hash (for guided-term.js proof reconstruction)
    sourceLabel: rule.sourceLabel || null,  // SELL import-scoped label (THY_0013)
    antecedent: anteFlat,
    consequent: effectiveConseq,
    triggerPreds,
    discriminator,
    linearMeta,
    metavarSlots,
    metavarCount,
    existentialSlots,
    existentialGoals,
    hasGrade0
  };

  // Timed guard metadata (only attached when present — zero delta for ILL).
  // Window expressions are atomic after convert's desugaring: a ground
  // rational ({ ground: hash }) or a rule variable ({ slot: i }) — the
  // timed matcher evaluates a(m) against them with a θ lookup, no
  // expression walker (Matching spec).
  if (_windowsRaw.after.length > 0 || _windowsRaw.before.length > 0) {
    const _compileWindow = (e) => {
      const t = Store.tag(e);
      if (t === 'metavar' || t === 'freevar') {
        // Must be ANTECEDENT-bound (pattern or persistent goal) — a slot
        // that exists only via the consequent would read θ = undefined at
        // match time (audit round 12, Finding 2).
        if (!anteMetavars.has(e)) {
          throw new Error(`Rule '${rule.name}': window variable '${Store.child(e, 0)}' is not bound by any antecedent pattern or goal`);
        }
        return { slot: metavarSlots[e] };   // slots are keyed by metavar hash
      }
      return { ground: e };
    };
    compiled.windows = {
      after: _windowsRaw.after.map(_compileWindow),
      before: _windowsRaw.before.map(_compileWindow),
    };
  }
  if (_readOnly.length > 0) compiled.readOnly = _readOnly;

  // Duration grade → delay slot (E2/E7.1, TODO_0265 Phase 4). A graded
  // computation's non-unit grade is the rule's delay: a ground rational or
  // an antecedent-bound variable (E7.1 mode check — the delay is
  // output-moded from the antecedent, e.g. via a !qdiv goal). Unit grades
  // attach nothing, so graded-but-undelayed calculi run on the untimed
  // engine unchanged — since the D6 merge-back every monad is binary, so
  // the unit defaults to the shared monadUnit (binlit 0, same hash as
  // till's putRat(0,1)); a different grade algebra overrides via
  // opts.gradeUnit, mirroring the parser's elision default.
  const _comp = rc.computation;
  if (_comp && _comp.gradeIdx !== null && Store.tag(rule.consequent) === _comp.tag) {
    const _g = Store.child(rule.consequent, _comp.gradeIdx);
    const _unit = opts.gradeUnit || monadUnit;
    if (_g !== _unit()) {
      const _gt = Store.tag(_g);
      if (_gt === 'metavar' || _gt === 'freevar') {
        if (!anteMetavars.has(_g)) {
          throw new Error(`Rule '${rule.name}': delay variable '${Store.child(_g, 0)}' is not bound by any antecedent pattern or goal (E7.1)`);
        }
        compiled.delay = { slot: metavarSlots[_g] };
      } else {
        compiled.delay = { ground: _g };
      }
    }
  }

  // Counted parcels anywhere (antecedent via linearMeta, consequent via a
  // kept-wrapped bang in an alternative) mark the rule as timed-matcher-only.
  if (_hasCounted ||
      consequentAlts.some(a => (a.linear || []).some(h => Store.tag(h) === rc.exponential))) {
    compiled.counted = true;
  }

  // Weighted internal choice `woplus Q A B` (TODO_0265 Phase 4b): the
  // expanded alternatives carry exact path weights. Fill absent weights
  // with 1 (single-alt), validate the distribution sums to exactly 1, and
  // mark the rule — the timed scheduler samples the branch by weight via
  // the D17 PRF; the untimed engine rejects (guard in forward.js).
  //
  // Fire-time weights (Phase 6): a weight may be symbolic ({ g, syms } from
  // expandChoice — a rule variable Q, e.g. bound by a `!winprob U V Q`
  // goal). Symbolic factors get the delay/window mode check (must be
  // antecedent-bound) and their slots resolved here; the [0,1]/sum-to-1
  // validation moves to firing (the Q/1−Q construction sums to 1 for any
  // resolved Q in [0,1], so only the range needs the runtime check).
  if (consequentAlts.some(a => a.weight)) {
    let sum = [0n, 1n];
    let dynamic = false;
    for (const a of consequentAlts) {
      if (!a.weight) a.weight = [1n, 1n];
      if (Array.isArray(a.weight)) { sum = _ratAdd(sum, a.weight); continue; }
      dynamic = true;
      for (const s of a.weight.syms) {
        if (!anteMetavars.has(s.v)) {
          throw new Error(`Rule '${rule.name}': woplus weight variable '${Store.child(s.v, 0)}' is not bound by any antecedent pattern or goal`);
        }
        s.slot = metavarSlots[s.v];
      }
    }
    if (!dynamic && sum[0] !== sum[1]) {
      throw new Error(`Rule '${rule.name}': branch weights sum to ${sum[0]}/${sum[1]}, expected exactly 1`);
    }
    compiled.weighted = true;
    if (dynamic) compiled.weightDynamic = true;
  }
  if (rc.weightedChoice) {
    for (const p of (anteFlat.linear || [])) {
      // A stamped pattern `w@3` wraps the inner form in at(_, stamp) — the
      // rejection must see through it (round 13: at(woplus …) slipped past).
      const inner = Store.tag(p) === 'at' ? Store.child(p, 0) : p;
      if (Store.tag(inner) === rc.weightedChoice) {
        throw new Error(`Rule '${rule.name}': woplus is a consequent form (internal choice) — not allowed in antecedents`);
      }
    }
  }

  const analysis = deltaAnalysis(compiled);
  compiled.preserved = analysis.preserved;
  compiled.analysis = analysis;  // kept for debug/test introspection
  compiled.consequentAlts = consequentAlts;
  compiled.patternRoles = patternRoles(
    anteFlat.linear || [], analysis, metavarSlots
  );
  compiled.compiledConseqLinear = (effectiveConseq.linear || []).map(
    p => compileSub(p, metavarSlots)
  );
  compiled.compiledConseqPersistent = (effectiveConseq.persistent || []).map(
    p => compileSub(p, metavarSlots)
  );

  _compileCache.set(_cacheKey, compiled);
  return compiled;
}

// ─── Compiled Pattern Matching ───────────────────────────────────────

// Instruction opcodes for compiled pattern matching
const PM_BIND = 0;     // { op: PM_BIND, slot }
const PM_GROUND = 2;   // { op: PM_GROUND, expected }
const PM_COMPOUND = 3; // { op: PM_COMPOUND, tagId, arity }

/**
 * Compile a pattern hash into a flat instruction array (DFS pre-order).
 * Replaces closure-based compilePM with a data structure
 * directly portable to Zig []const Instruction.
 *
 * Instruction types:
 *   PM_BIND(slot) — bind metavar to current fact node (or check equality if already bound)
 *   PM_GROUND(expected) — identity check (content-addressed)
 *   PM_COMPOUND(tagId, arity) — check tag+arity, then match children in order
 */
function compilePM(hash, slots) {
  const instructions = [];
  function emit(hash) {
    const t = Store.tag(hash);

    // Metavar: bind or check
    if (t === 'metavar' && slots[hash] !== undefined) {
      instructions.push({ op: PM_BIND, slot: slots[hash] });
      return;
    }

    // Ground: identity check
    if (isGround(hash)) {
      instructions.push({ op: PM_GROUND, expected: hash });
      return;
    }

    // Compound: tag check + recurse children
    const tid = Store.tagId(hash);
    const a = Store.arity(hash);
    instructions.push({ op: PM_COMPOUND, tagId: tid, arity: a });
    for (let i = 0; i < a; i++) {
      emit(Store.child(hash, i));
    }
  }
  emit(hash);
  return instructions;
}

// Pre-allocated stack for execPM (avoids per-call allocation)
const _pmStack = new Array(64); // pairs: [instructionIdx, hash]

/**
 * Execute compiled pattern instructions against a fact hash.
 * Stack-based interpreter: no recursion, pre-allocated stack.
 * Returns true if pattern matches fact, binding theta slots.
 */
function execPM(instructions, h, theta) {
  let sp = 0; // stack pointer
  _pmStack[sp++] = 0; // instruction index
  _pmStack[sp++] = h; // fact hash

  let ip = 0;
  while (sp > 0) {
    const factHash = _pmStack[--sp];
    ip = _pmStack[--sp];

    const inst = instructions[ip];
    switch (inst.op) {
      case PM_BIND: {
        const existing = theta[inst.slot];
        if (existing === undefined) { theta[inst.slot] = factHash; }
        else if (existing !== factHash) return false;
        break;
      }
      case PM_GROUND:
        if (factHash !== inst.expected) return false;
        break;
      case PM_COMPOUND: {
        if (Store.tagId(factHash) !== inst.tagId || Store.arity(factHash) !== inst.arity) return false;
        // Push children in reverse order so they are processed left-to-right
        let childIp = ip + 1;
        for (let ci = inst.arity - 1; ci >= 0; ci--) {
          // Find the ip for child ci by skipping forward from childIp
          let skipIp = childIp;
          for (let skip = 0; skip < ci; skip++) {
            skipIp = _skipInstruction(instructions, skipIp);
          }
          _pmStack[sp++] = skipIp;
          _pmStack[sp++] = Store.child(factHash, ci);
        }
        break;
      }
    }
  }
  return true;
}

/** Skip over one instruction and all its children. */
function _skipInstruction(instructions, ip) {
  const inst = instructions[ip];
  if (inst.op !== PM_COMPOUND) return ip + 1;
  let next = ip + 1;
  for (let i = 0; i < inst.arity; i++) {
    next = _skipInstruction(instructions, next);
  }
  return next;
}

// ─── Compiled Premise Construction (WAM "put" instructions) ─────────
//
// Dual of pattern matching (GET): while PM_* instructions deconstruct a
// goal to extract bindings, PUT_* instructions construct a goal from
// bindings. This is the WAM put_structure / put_value / put_constant
// family, adapted for our content-addressed Store.
//
// Instructions are emitted in **post-order** (children before parent)
// and executed with a result stack. This is the natural order for
// bottom-up term construction: Store.put(tag, children) needs all
// children to be Store hashes before the parent can be created.
//
// Eliminates the recursive _materializePremise tree walk:
// - No runtime Store.tagId() + metavar detection per node
// - No localSlots{} object property lookup (slot baked into instruction)
// - Flat instruction loop, no function call overhead
//
// Note: Store.put calls for compound construction are inherent — they
// are the content-addressed analogue of WAM heap allocation. These are
// O(1) amortized (DEDUP cache hit for repeated terms).

const PUT_GROUND   = 10;  // { op, hash }           — push ground Store hash (no metavars)
const PUT_SLOT     = 11;  // { op, slot }            — push theta[base+slot] or slot metavar
const PUT_COMPOUND = 12;  // { op, tagName, arity }  — pop arity children, Store.put
const PUT_ARRLIT   = 13;  // { op, count }           — pop count elements, Store.putArray

/**
 * Compile a premise hash into PUT instructions (post-order).
 *
 * Walks the Store term tree at compile time, classifying each node:
 * - Metavar in localSlots → PUT_SLOT (bound value or placeholder)
 * - Metavar NOT in localSlots → PUT_GROUND (external, pass through)
 * - Ground subtree (no metavars) → PUT_GROUND (single instruction)
 * - Compound with metavars → recurse children, then PUT_COMPOUND
 * - Arrlit with metavars → recurse elements, then PUT_ARRLIT
 *
 * @param {number} hash - Premise Store hash (template with metavar hashes)
 * @param {Object} localSlots - {metavarHash: localSlotIndex}
 * @returns {Array} Flat instruction array (post-order)
 */
function compilePut(hash, localSlots) {
  const instructions = [];

  function emit(h) {
    if (!Store.isTerm(h)) {
      // Non-term value (shouldn't appear at top level, but guard)
      instructions.push({ op: PUT_GROUND, hash: h });
      return;
    }
    const t = Store.tag(h);

    // Metavar: slot reference or external pass-through
    if (t === 'metavar') {
      const slot = localSlots[h];
      if (slot !== undefined) {
        instructions.push({ op: PUT_SLOT, slot });
      } else {
        // External metavar (not in this clause's scope) — leave as-is
        instructions.push({ op: PUT_GROUND, hash: h });
      }
      return;
    }

    // Ground subtree: single instruction, skip decomposition
    if (isGround(h)) {
      instructions.push({ op: PUT_GROUND, hash: h });
      return;
    }

    // Arrlit with metavar descendants
    const tid = Store.tagId(h);
    if (tid === Store.TAG.arrlit) {
      const elems = Store.getArrayElements(h);
      if (!elems || elems.length === 0) {
        instructions.push({ op: PUT_GROUND, hash: h });
        return;
      }
      for (let i = 0; i < elems.length; i++) emit(elems[i]);
      instructions.push({ op: PUT_ARRLIT, count: elems.length });
      return;
    }

    // Compound with metavar descendants: emit children post-order, then parent
    const a = Store.arity(h);
    if (a === 0) {
      instructions.push({ op: PUT_GROUND, hash: h });
      return;
    }
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (typeof c === 'number' && Store.isTerm(c)) {
        emit(c);
      } else {
        // Non-term child (string in atom, BigInt in binlit) — this node
        // should have been caught by isGround above. Defensive fallback.
        instructions.push({ op: PUT_GROUND, hash: h });
        return;
      }
    }
    instructions.push({ op: PUT_COMPOUND, tagName: t, arity: a });
  }

  emit(hash);
  return instructions;
}

/**
 * Precompute index lookup key for a premise.
 *
 * Returns { predHead, firstArgSlot, firstArgKey } where:
 * - predHead: predicate head string (always known at compile time)
 * - firstArgSlot: if first arg is a bare metavar, its local slot index; else null
 * - firstArgKey: if first arg is ground or compound, its index key; else null
 *
 * At runtime, the search loop can compute the index key without calling
 * predHead() or getFirstArgHead() on the materialized premise.
 */
function compileKey(hash, localSlots) {
  const head = predHead(hash);
  if (!head) return null;

  const a = Store.arity(hash);
  if (a === 0) return { predHead: head, firstArgSlot: null, firstArgKey: '_' };

  const firstArg = Store.child(hash, 0);
  if (!Store.isTerm(firstArg)) return { predHead: head, firstArgSlot: null, firstArgKey: '_' };

  const t = Store.tag(firstArg);

  // First arg is a metavar in scope → runtime-dependent
  if (t === 'metavar' && localSlots[firstArg] !== undefined) {
    return { predHead: head, firstArgSlot: localSlots[firstArg], firstArgKey: null };
  }

  // First arg is ground or compound with known outermost tag → known at compile time
  if (t === 'atom') return { predHead: head, firstArgSlot: null, firstArgKey: Store.child(firstArg, 0) };
  if (t === 'freevar' || t === 'metavar') return { predHead: head, firstArgSlot: null, firstArgKey: '_' };
  if (isPredTag(t)) return { predHead: head, firstArgSlot: null, firstArgKey: t };

  // Compact literals via the eq-theory registry (binlit → 'i'/'o'/'e'
  // registered by initILL, ratlit → 'rat' by installRatlitTheory).
  const ck = _classifyCompact(Store.tagId(firstArg), firstArg);
  if (ck) return { predHead: head, firstArgSlot: null, firstArgKey: ck };

  return { predHead: head, firstArgSlot: null, firstArgKey: '_' };
}

export { resolveConn, flattenAnte, unwrapComp, expandChoice, expandConsqChoices, compileRule, compilePM, execPM, PM_BIND, PM_GROUND, PM_COMPOUND, _skipInstruction, PUT_GROUND, PUT_SLOT, PUT_COMPOUND, PUT_ARRLIT, compilePut, compileKey };
export default { resolveConn, flattenAnte, unwrapComp, expandChoice, expandConsqChoices, compileRule, compilePM, execPM, PM_BIND, PM_GROUND, PM_COMPOUND, _skipInstruction, PUT_GROUND, PUT_SLOT, PUT_COMPOUND, PUT_ARRLIT, compilePut, compileKey };
