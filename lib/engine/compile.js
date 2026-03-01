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


// --- Term walkers ---

/** Flatten tensor spine into linear + persistent lists */
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

/** Unwrap monad body ({A} → A) */
function unwrapMonad(h) {
  if (Store.tag(h) === 'monad') return Store.child(h, 0);
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
function expandItem(h) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [] }];

  if (t === 'with' || t === 'oplus') {
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
  if (t === 'exists') {
    // Open binder with fresh metavar, recurse into body
    const body = Store.child(h, 0);
    const opened = debruijnSubst(body, 0n, freshMetavar());
    return expandItem(opened);
  }
  // Lolis stay as opaque linear facts — fired by matchLoli at runtime
  return [{ linear: [h], persistent: [] }];
}

/** Expand compiled consequent into choice alternatives */
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

// --- Rule compilation ---

/**
 * Compile a forward rule for efficient matching.
 *
 * Input: { name, hash, antecedent, consequent }
 * Output: compiled rule with trigger predicates, de Bruijn slots,
 *         discriminator, pattern roles, compiled substitutions.
 */
function compileRule(rule) {
  // Phase A: Flatten antecedent/consequent tensor spines
  const anteFlat = flattenTensor(rule.antecedent);
  const conseqBody = unwrapMonad(rule.consequent);
  const conseqFlat = flattenTensor(conseqBody);

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
  const consequentAlts = expandConsequentChoices(conseqFlat);

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
      if (Store.tag(p) === 'loli') {
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
  // - Multi-alt: first choice (committed choice picks first; symexec uses consequentAlts)
  // This ensures analyzeDeltas, compiledConseq*, and resolveExistentials
  // all see opened patterns — NOT raw exists/with/oplus nodes.
  const effectiveConseq = consequentAlts[0];

  const compiled = {
    name: rule.name,
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
  generateMatcher(compiled);

  return compiled;
}

// ─── Compiled Pattern Matching ───────────────────────────────────────

// Pre-parse FFI modes once (shared with match.js's _ffiParsedModes)
const _ffiMeta = ffi.defaultMeta;
const _ffiParsedModes = {};
for (const key in _ffiMeta) {
  _ffiParsedModes[key] = ffi.mode.parseMode(_ffiMeta[key].mode);
}

/**
 * Compile a pattern hash into a closure (fact, theta) → bool.
 * Three cases: metavar (bind/check), ground (identity), compound (tag+children).
 */
function compilePatternMatch(hash, slots) {
  const t = Store.tag(hash);

  // Metavar: bind or check equality
  if (t === 'freevar' && slots[hash] !== undefined) {
    const slot = slots[hash];
    return (h, theta) => {
      const existing = theta[slot];
      if (existing === undefined) { theta[slot] = h; return true; }
      return existing === h;
    };
  }

  // Ground: identity check (content-addressed dedup)
  if (isGround(hash)) {
    return (h) => h === hash;
  }

  // Compound: check tag + recurse children
  const tid = Store.tagId(hash);
  const a = Store.arity(hash);
  const childMatchers = new Array(a);
  for (let i = 0; i < a; i++) {
    childMatchers[i] = compilePatternMatch(Store.child(hash, i), slots);
  }

  // Specialize for common arities (avoid loop overhead)
  if (a === 1) {
    const cm0 = childMatchers[0];
    return (h, theta) =>
      Store.tagId(h) === tid && Store.arity(h) === 1 &&
      cm0(Store.child(h, 0), theta);
  }
  if (a === 2) {
    const cm0 = childMatchers[0], cm1 = childMatchers[1];
    return (h, theta) =>
      Store.tagId(h) === tid && Store.arity(h) === 2 &&
      cm0(Store.child(h, 0), theta) && cm1(Store.child(h, 1), theta);
  }
  if (a === 3) {
    const cm0 = childMatchers[0], cm1 = childMatchers[1], cm2 = childMatchers[2];
    return (h, theta) =>
      Store.tagId(h) === tid && Store.arity(h) === 3 &&
      cm0(Store.child(h, 0), theta) && cm1(Store.child(h, 1), theta) &&
      cm2(Store.child(h, 2), theta);
  }
  return (h, theta) => {
    if (Store.tagId(h) !== tid || Store.arity(h) !== a) return false;
    for (let i = 0; i < a; i++) {
      if (!childMatchers[i](Store.child(h, i), theta)) return false;
    }
    return true;
  };
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
  const _ffiIsGround = ffi.convert.isGround;

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

  const _args = [0, 0, 0, 0]; // pre-allocated, reused across calls

  return function(theta) {
    for (let i = 0; i < arity; i++) {
      const spec = argSpecs[i];
      if (spec.literal !== undefined) {
        _args[i] = spec.literal;
      } else {
        const val = theta[spec.slot];
        _args[i] = val !== undefined ? val : spec.freevar;
        if (!multiModal && spec.isInput &&
            (val === undefined || !_ffiIsGround(val))) {
          return null; // non-definitive: input not ground
        }
      }
    }

    const result = ffiFn(_args);
    if (result && result.success) {
      const ft = result.theta;
      for (let fi = 0; fi < ft.length; fi++) {
        const s = slots[ft[fi][0]];
        if (s !== undefined) theta[s] = ft[fi][1];
      }
      return true;
    }
    if (result && !result.success && !result.reason) return false; // definitive
    return null; // non-definitive → needs clause resolution
  };
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
function generateMatcher(rule) {
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
  compileRule,
  generateMatcher,
  compilePatternMatch,
  compilePersistentStep,
  flattenTensor,
  unwrapMonad,
  isGround,
  collectMetavars,
  collectFreevars,
  expandItem,
  expandConsequentChoices,
};
