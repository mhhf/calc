/**
 * Rule Compiler — prepare forward rules for efficient matching.
 *
 * Input: raw rule { name, hash, antecedent, consequent }
 * Output: compiled rule with indexes, slots, analysis metadata
 *
 * Pure data transformation — no runtime state dependencies.
 */

const Store = require('../kernel/store');
const { isPredTag, getPredicateHead } = require('../kernel/ast');
const { analyzeDeltas, computePatternRoles, compileSubstitution } = require('./rule-analysis');
const { isGround, collectMetavars, collectFreevars } = require('./pattern-utils');
const { debruijnSubst } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');
const ffi = require('./ffi');


// --- Default connective roles (ILL) ---

const DEFAULT_ROLES = {
  product: 'tensor', exponential: 'bang', computation: 'monad',
  'internal-choice': 'oplus', 'external-choice': 'with',
  existential: 'exists', implication: 'loli',
  unit: 'one', 'additive-zero': 'zero'
};

// --- Term walkers ---

/** Flatten tensor spine into linear + persistent lists */
function flattenTensor(h, roles = DEFAULT_ROLES) {
  const linear = [];
  const persistent = [];
  const productTag = roles.product || 'tensor';
  const bangTag = roles.exponential || 'bang';

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === productTag) {
      walk(Store.child(hash, 0));
      walk(Store.child(hash, 1));
    } else if (t === bangTag) {
      persistent.push(Store.child(hash, 0));
    } else {
      linear.push(hash);
    }
  }

  walk(h);
  return { linear, persistent };
}

/** Unwrap monad body ({A} → A) */
function unwrapMonad(h, roles = DEFAULT_ROLES) {
  const compTag = roles.computation || 'monad';
  if (Store.tag(h) === compTag) return Store.child(h, 0);
  return h;
}

/** Collect OUTPUT freevars from persistent pattern using FFI mode info.
 *  Only positions with mode '-' are true outputs.
 *  Falls back to last-argument convention when no FFI mode is available. */
function collectOutputVars(h) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;
  const a = Store.arity(h);
  if (!isPredTag(t) || a === 0) return vars;

  const pred = getPredicateHead(h);
  const meta = pred && ffi.defaultMeta[pred];
  if (meta) {
    const modes = ffi.mode.parseMode(meta.mode);
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

/** Expand a hash into alternatives through with/oplus/tensor/bang/exists */
function expandChoiceItem(h, roles = DEFAULT_ROLES) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [] }];

  const extChoice = roles['external-choice'] || 'with';
  const intChoice = roles['internal-choice'] || 'oplus';
  const productTag = roles.product || 'tensor';
  const bangTag = roles.exponential || 'bang';
  const existTag = roles.existential || 'exists';

  if (t === extChoice || t === intChoice) {
    return [
      ...expandChoiceItem(Store.child(h, 0), roles),
      ...expandChoiceItem(Store.child(h, 1), roles)
    ];
  }
  if (t === productTag) {
    const lefts = expandChoiceItem(Store.child(h, 0), roles);
    const rights = expandChoiceItem(Store.child(h, 1), roles);
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
  if (t === bangTag) {
    return [{ linear: [], persistent: [Store.child(h, 0)] }];
  }
  if (t === existTag) {
    // Open binder with fresh metavar, recurse into body
    const body = Store.child(h, 0);
    const opened = debruijnSubst(body, 0n, freshMetavar());
    return expandChoiceItem(opened, roles);
  }
  // Lolis stay as opaque linear facts — fired by matchLoli at runtime
  return [{ linear: [h], persistent: [] }];
}

/** Expand compiled consequent into choice alternatives */
function expandConsequentChoices(consequent, roles = DEFAULT_ROLES) {
  let alts = [{ linear: [], persistent: [] }];

  for (const h of (consequent.linear || [])) {
    const itemAlts = expandChoiceItem(h, roles);
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

// --- Rule compilation ---

/**
 * Compile a forward rule for efficient matching.
 *
 * Input: { name, hash, antecedent, consequent }
 * Output: compiled rule with trigger predicates, de Bruijn slots,
 *         discriminator, pattern roles, compiled substitutions.
 */
function compileRule(rule, opts = {}) {
  const roles = opts.roles || DEFAULT_ROLES;

  // Phase A: Flatten antecedent/consequent tensor spines
  const anteFlat = flattenTensor(rule.antecedent, roles);
  const conseqBody = unwrapMonad(rule.consequent, roles);
  const conseqFlat = flattenTensor(conseqBody, roles);

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
    for (const v of collectOutputVars(p)) persistentOutputVars.add(v);
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

  // Phase E: Expand consequent choices (opens exists binders, expands with/oplus)
  const consequentAlts = expandConsequentChoices(conseqFlat, roles);

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
      if (Store.tag(p) === (roles.implication || 'loli')) {
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

  const compiled = {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: effectiveConseq,
    triggerPreds,
    discriminator,
    linearMeta,
    metavarSlots,
    metavarCount,
    existentialSlots,
    existentialGoals
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

  // Phase I: Generate compiled matcher closure (if eligible)
  compilePersistentSteps(compiled);

  return compiled;
}

// ─── Compiled Pattern Matching ───────────────────────────────────────

const _ffiMeta = ffi.defaultMeta;
const _ffiParsedModes = ffi.parsedModes;

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
    if (t === 'freevar' && slots[hash] !== undefined) {
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

/**
 * Compile a persistent antecedent into a closure for FFI fast path.
 * Returns (theta) → true|false|null.
 * true = proved, false = definitive failure, null = needs generic fallback.
 */
function compilePersistentStep(pattern, slots) {
  const pred = getPredicateHead(pattern);
  if (!pred) return null;

  const meta = _ffiMeta[pred];
  if (!meta) return null;

  const ffiFn = ffi.get(meta.ffi);
  if (!ffiFn) return null;

  const modes = _ffiParsedModes[pred];
  const arity = Store.arity(pattern);
  if (arity !== modes.length) return null;

  const multiModal = !!meta.multiModal;

  // Precompute per-position spec
  const argSpecs = new Array(arity);
  for (let i = 0; i < arity; i++) {
    const c = Store.child(pattern, i);
    const slot = slots[c];
    if (slot !== undefined) {
      argSpecs[i] = { slot, freevar: c, isInput: modes[i] === '+' };
    } else if (isGround(c)) {
      argSpecs[i] = { literal: c, isInput: true };
    } else {
      return null;
    }
  }

  return { ffiFn, argSpecs, arity, multiModal, _slots: slots };
}

/**
 * Generate compiled persistent steps for a rule's persistent antecedents.
 * Attaches rule.persistentSteps (array parallel to antecedent.persistent).
 * Each step is a closure (theta) → true|false|null for FFI fast path,
 * or null if no FFI optimization applies for that antecedent.
 *
 * Used by matchAllLinear (match.js) to skip subApplyIdx + tryFFIDirect
 * overhead for FFI-known predicates (inc, plus, neq, mul).
 */
function compilePersistentSteps(rule) {
  const persistentPats = rule.antecedent.persistent || [];
  if (persistentPats.length === 0) return;

  const slots = rule.metavarSlots;
  const steps = persistentPats.map(p => compilePersistentStep(p, slots));

  // Only attach if at least one step compiled
  if (steps.some(s => s !== null)) {
    rule.persistentSteps = steps;
  }
}

module.exports = {
  DEFAULT_ROLES,
  compileRule,
  compilePersistentSteps,
  compilePatternMatch,
  executePatternMatch,
  compilePersistentStep,
  flattenTensor,
  unwrapMonad,
  isGround,
  collectMetavars,
  collectFreevars,
  expandChoiceItem,
  expandConsequentChoices,
};
