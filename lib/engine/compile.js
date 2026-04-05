/**
 * Rule Compiler — prepare forward rules for efficient matching.
 *
 * Input: raw rule { name, hash, antecedent, consequent }
 * Output: compiled rule with indexes, slots, analysis metadata
 *
 * Pure data transformation — no runtime state dependencies.
 */

const Store = require('../kernel/store');
const { GRADE_0, GRADE_W } = require('./grades');
const { isPredTag, getPredicateHead } = require('../kernel/ast');
const { analyzeDeltas, computePatternRoles, compileSubstitution } = require('./rule-analysis');
const { isGround, collectMetavars, collectFreevars } = require('./pattern-utils');
const { debruijnSubst } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');

// --- Connective resolution ---

/**
 * Derive structural role → tag name lookups from a connective table.
 * The connective table maps tag → { category, arity, polarity } (from .calc
 * annotations). This function inverts it for O(1) access by structural role.
 *
 * @param {Object} ct - Connective table (tag → { category, arity, polarity })
 * @returns {Object} Resolved roles { product, implication, exponential, computation,
 *   internalChoice, externalChoice, existential, unit, additiveZero }
 */
function resolveConnectives(ct) {
  const r = {};
  for (const tag in ct) {
    const { category: c, arity: a, polarity: p } = ct[tag];
    if (c === 'multiplicative' && a === 2 && p === 'positive') r.product = tag;
    else if (c === 'multiplicative' && a === 2 && p === 'negative') r.implication = tag;
    else if (c === 'multiplicative' && a === 0) r.unit = tag;
    else if (c === 'exponential' && a === 2) r.exponential = tag;
    else if (c === 'monad' && a === 1) r.computation = tag;
    else if (c === 'additive' && a === 2 && p === 'positive') r.internalChoice = tag;
    else if (c === 'additive' && a === 2 && p === 'negative') r.externalChoice = tag;
    else if (c === 'additive' && a === 0) r.additiveZero = tag;
    else if (c === 'quantifier' && a === 1 && p === 'positive') r.existential = tag;
  }
  return r;
}

// --- Term walkers ---

/**
 * Flatten multiplicative product spine into linear + persistent + grade0 lists.
 *
 * Three-way grade classification (SELL {0,1,ω} semiring):
 *   GRADE_0 → grade0[]   (compile-time, filtered before runtime)
 *   GRADE_W → persistent[] (weakening + contraction)
 *   bare    → linear[]    (grade-1 implicit, consumed once)
 *
 * @param {number} h - Antecedent hash
 * @param {Object} ct - Connectives config (needs product, exponential)
 * @returns {{ linear: number[], persistent: number[], grade0: number[] }}
 */
function flattenAntecedent(h, ct) {
  const linear = [];
  const persistent = [];
  const grade0 = [];
  const productTag = ct.product;
  const expTag = ct.exponential;

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === productTag) {
      walk(Store.child(hash, 0));
      walk(Store.child(hash, 1));
    } else if (t === expTag) {
      const grade = Store.child(hash, 0);
      const inner = Store.child(hash, 1);
      if (grade === GRADE_0) {
        grade0.push(inner);
      } else {
        // GRADE_W (or any future grade with structural rules) → persistent
        persistent.push(inner);
      }
    } else {
      linear.push(hash);
    }
  }

  walk(h);
  return { linear, persistent, grade0 };
}

/**
 * Unwrap computation body ({A} → A).
 * @param {number} h - Consequent hash
 * @param {Object} ct - Connectives config (needs computation)
 */
function unwrapComputation(h, ct) {
  if (Store.tag(h) === ct.computation) return Store.child(h, 0);
  return h;
}

/** Collect OUTPUT freevars from persistent pattern using mode info.
 *  Only positions with mode '-' are true outputs.
 *  Falls back to last-argument convention when no mode info is available.
 *  @param {number} h - Persistent pattern hash
 *  @param {Function|null} getModes - (pred) → string[]|null (e.g., ['+','+','-']) */
function collectOutputVars(h, getModes) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;
  const a = Store.arity(h);
  if (!isPredTag(t) || a === 0) return vars;

  const pred = getPredicateHead(h);
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

// --- Choice expansion ---

/**
 * Expand a hash into alternatives through choice/product/exponential/existential.
 * @param {number} h - Formula hash
 * @param {Object} ct - Connectives config
 */
function expandChoiceItem(h, ct) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [], grade0: [] }];

  if (t === ct.externalChoice || t === ct.internalChoice) {
    return [
      ...expandChoiceItem(Store.child(h, 0), ct),
      ...expandChoiceItem(Store.child(h, 1), ct)
    ];
  }
  if (t === ct.product) {
    const lefts = expandChoiceItem(Store.child(h, 0), ct);
    const rights = expandChoiceItem(Store.child(h, 1), ct);
    const out = [];
    for (const l of lefts) {
      for (const r of rights) {
        out.push({
          linear: [...l.linear, ...r.linear],
          persistent: [...l.persistent, ...r.persistent],
          grade0: [...l.grade0, ...r.grade0]
        });
      }
    }
    return out;
  }
  if (t === ct.exponential) {
    const grade = Store.child(h, 0);
    const inner = Store.child(h, 1);
    if (grade === GRADE_0) {
      return [{ linear: [], persistent: [], grade0: [inner] }];
    }
    return [{ linear: [], persistent: [inner], grade0: [] }];
  }
  if (t === ct.existential) {
    // Open binder with fresh metavar, recurse into body
    const body = Store.child(h, 0);
    const opened = debruijnSubst(body, 0n, freshMetavar());
    return expandChoiceItem(opened, ct);
  }
  // Lolis stay as opaque linear facts — fired by matchLoli at runtime
  return [{ linear: [h], persistent: [], grade0: [] }];
}

/**
 * Expand compiled consequent into choice alternatives.
 * @param {Object} consequent - { linear, persistent }
 * @param {Object} ct - Connectives config
 */
function expandConsequentChoices(consequent, ct) {
  let alts = [{ linear: [], persistent: [], grade0: [] }];

  for (const h of (consequent.linear || [])) {
    const itemAlts = expandChoiceItem(h, ct);
    const next = [];
    for (const acc of alts) {
      for (const ia of itemAlts) {
        next.push({
          linear: [...acc.linear, ...ia.linear],
          persistent: [...acc.persistent, ...ia.persistent],
          grade0: [...acc.grade0, ...ia.grade0]
        });
      }
    }
    alts = next;
  }

  const origPersistent = consequent.persistent || [];
  const origGrade0 = consequent.grade0 || [];
  if (origPersistent.length > 0 || origGrade0.length > 0) {
    alts = alts.map(a => ({
      linear: a.linear,
      persistent: origPersistent.length > 0 ? [...a.persistent, ...origPersistent] : a.persistent,
      grade0: origGrade0.length > 0 ? [...a.grade0, ...origGrade0] : a.grade0
    }));
  }

  return alts;
}

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
  const rc = resolveConnectives(ct);
  const getModes = opts.getModes || null;

  // Phase A: Flatten antecedent/consequent product spines
  const anteFlat = flattenAntecedent(rule.antecedent, rc);
  const conseqBody = unwrapComputation(rule.consequent, rc);
  const conseqFlat = flattenAntecedent(conseqBody, rc);

  // Phase B: Trigger predicates and discriminator detection
  const triggerPreds = [];
  let discriminator = null;

  for (const h of (anteFlat.linear || [])) {
    const pred = getPredicateHead(h);
    if (pred && !triggerPreds.includes(pred)) triggerPreds.push(pred);

    // Detect fingerprint discriminator: binary+ predicate with ground child
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

  // Phase B2: Virtual discriminator — scan persistent antecedents for !arr_get B PC GROUND
  if (!discriminator) {
    for (const p of (anteFlat.persistent || [])) {
      const pred = getPredicateHead(p);
      if (pred === 'arr_get' && Store.arity(p) >= 3) {
        const valueChild = Store.child(p, 2);
        if (typeof valueChild === 'number' && isGround(valueChild)) {
          const arrayVar = Store.child(p, 0);
          const indexVar = Store.child(p, 1);
          // Find unary linear patterns sharing these variables
          let arrayPred = null, pointerPred = null;
          for (const lp of (anteFlat.linear || [])) {
            const lpPred = getPredicateHead(lp);
            if (!lpPred || Store.arity(lp) !== 1) continue;
            if (Store.child(lp, 0) === arrayVar) arrayPred = lpPred;
            if (Store.child(lp, 0) === indexVar) pointerPred = lpPred;
          }
          if (arrayPred && pointerPred) {
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
  }

  // Phase C: Persistent output vars (used locally for dependency detection)
  const persistentOutputVars = new Set();
  for (const p of (anteFlat.persistent || [])) {
    for (const v of collectOutputVars(p, getModes)) persistentOutputVars.add(v);
  }

  // Phase D: Per-linear-pattern metadata (avoids Store.get walks in tryMatch)
  const linearMeta = {};
  for (const p of (anteFlat.linear || [])) {
    if (p in linearMeta) continue;
    const pred = getPredicateHead(p);
    const freevars = collectFreevars(p);
    const persistentDeps = new Set();
    for (const v of freevars) {
      if (persistentOutputVars.has(v)) persistentDeps.add(v);
    }
    let secondaryKeyPattern = null;
    if (discriminator && pred === discriminator.pred) {
      const kp = discriminator.keyPos;
      if (Store.arity(p) > kp) secondaryKeyPattern = Store.child(p, kp);
    }
    linearMeta[p] = { pred, freevars, persistentDeps, secondaryKeyPattern };
  }

  // Phase E: Expand consequent choices (opens exists binders, expands additive choices)
  const consequentAlts = expandConsequentChoices(conseqFlat, rc);

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

  // Map existential slot → persistent consequent patterns using that slot
  const existentialGoals = {};
  if (existentialSlots.length > 0) {
    for (const alt of consequentAlts) {
      for (const p of (alt.persistent || [])) {
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
  }

  // Phase H: Assemble compiled output + analysis metadata
  //
  // Always use first expanded alternative as effective consequent.
  // - Single-alt: the only alternative (exists opened, bang extracted)
  // - Multi-alt: first choice (committed choice picks first; explore uses consequentAlts)
  // This ensures analyzeDeltas, compiledConseq*, and resolveExistentials
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

  const analysis = analyzeDeltas(compiled);
  compiled.preserved = analysis.preserved;
  compiled.analysis = analysis;  // kept for debug/test introspection
  compiled.consequentAlts = consequentAlts;
  compiled.patternRoles = computePatternRoles(
    anteFlat.linear || [], analysis, metavarSlots
  );
  compiled.compiledConseqLinear = (effectiveConseq.linear || []).map(
    p => compileSubstitution(p, metavarSlots)
  );
  compiled.compiledConseqPersistent = (effectiveConseq.persistent || []).map(
    p => compileSubstitution(p, metavarSlots)
  );

  return compiled;
}

// ─── Compiled Pattern Matching ───────────────────────────────────────

// Instruction opcodes for compiled pattern matching
const PM_BIND = 0;     // { op: PM_BIND, slot }
const PM_CHECK = 1;    // { op: PM_CHECK, slot }
const PM_GROUND = 2;   // { op: PM_GROUND, expected }
const PM_COMPOUND = 3; // { op: PM_COMPOUND, tagId, arity }

/**
 * Compile a pattern hash into a flat instruction array (DFS pre-order).
 * Replaces closure-based compilePatternMatch with a data structure
 * directly portable to Zig []const Instruction.
 *
 * Instruction types:
 *   PM_BIND(slot) — bind metavar to current fact node
 *   PM_CHECK(slot) — check metavar equals current fact node
 *   PM_GROUND(expected) — identity check (content-addressed)
 *   PM_COMPOUND(tagId, arity) — check tag+arity, then match children in order
 */
function compilePatternMatch(hash, slots) {
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

// Pre-allocated stack for executePatternMatch (avoids per-call allocation)
const _pmStack = new Array(64); // pairs: [instructionIdx, hash]

/**
 * Execute compiled pattern instructions against a fact hash.
 * Stack-based interpreter: no recursion, pre-allocated stack.
 * Returns true if pattern matches fact, binding theta slots.
 */
function executePatternMatch(instructions, h, theta) {
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
      case PM_CHECK: {
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
function compilePremisePut(hash, localSlots) {
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
 * getPredicateHead() or getFirstArgHead() on the materialized premise.
 */
function compilePremiseKey(hash, localSlots) {
  const predHead = getPredicateHead(hash);
  if (!predHead) return null;

  const a = Store.arity(hash);
  if (a === 0) return { predHead, firstArgSlot: null, firstArgKey: '_' };

  const firstArg = Store.child(hash, 0);
  if (!Store.isTerm(firstArg)) return { predHead, firstArgSlot: null, firstArgKey: '_' };

  const t = Store.tag(firstArg);

  // First arg is a metavar in scope → runtime-dependent
  if (t === 'metavar' && localSlots[firstArg] !== undefined) {
    return { predHead, firstArgSlot: localSlots[firstArg], firstArgKey: null };
  }

  // First arg is ground or compound with known outermost tag → known at compile time
  if (t === 'atom') return { predHead, firstArgSlot: null, firstArgKey: Store.child(firstArg, 0) };
  if (t === 'freevar' || t === 'metavar') return { predHead, firstArgSlot: null, firstArgKey: '_' };
  if (isPredTag(t)) return { predHead, firstArgSlot: null, firstArgKey: t };
  if (t === 'binlit') {
    const v = Store.child(firstArg, 0);
    if (v === 0n) return { predHead, firstArgSlot: null, firstArgKey: 'e' };
    return { predHead, firstArgSlot: null, firstArgKey: v % 2n === 1n ? 'i' : 'o' };
  }

  return { predHead, firstArgSlot: null, firstArgKey: '_' };
}

module.exports = {
  resolveConnectives,
  compileRule,
  compilePatternMatch,
  executePatternMatch,
  flattenAntecedent,
  unwrapComputation,
  isGround,
  collectMetavars,
  collectFreevars,
  expandChoiceItem,
  expandConsequentChoices,
  PM_BIND,
  PM_CHECK,
  PM_GROUND,
  PM_COMPOUND,
  _skipInstruction,
  PUT_GROUND,
  PUT_SLOT,
  PUT_COMPOUND,
  PUT_ARRLIT,
  compilePremisePut,
  compilePremiseKey,
};
