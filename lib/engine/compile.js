/**
 * Rule Compiler — prepare forward rules for efficient matching.
 *
 * Input: raw rule { name, hash, antecedent, consequent }
 * Output: compiled rule with indexes, slots, analysis metadata
 *
 * Pure data transformation — no runtime state dependencies.
 */

const Store = require('../kernel/store');
const { NON_PRED_TAGS, getPredicateHead } = require('../kernel/ast');
const { analyzeDeltas, analyzeBufferLimits, computePatternRoles, compileSubstitution } = require('./rule-analysis');
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

/** Check if term is ground (no freevars) */
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

/** Collect metavar hashes (freevars starting with _) into a Set */
function collectMetavars(h, out) {
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
    if (typeof c === 'number') collectMetavars(c, out);
  }
}

/** Collect all freevars in a pattern */
function collectFreevars(h) {
  const vars = new Set();
  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === 'freevar') { vars.add(hash); return; }
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (typeof c === 'number') walk(c);
    }
  }
  walk(h);
  return vars;
}

/** Collect OUTPUT freevars from persistent pattern using FFI mode info.
 *  Only positions with mode '-' are true outputs.
 *  Falls back to last-argument convention when no FFI mode is available. */
function collectOutputVars(h) {
  const vars = new Set();
  const t = Store.tag(h);
  if (!t) return vars;
  const a = Store.arity(h);
  if (NON_PRED_TAGS.has(t) || a === 0) return vars;

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

/** Expand a hash into alternatives through with/tensor/bang/exists */
function expandItem(h) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [] }];

  if (t === 'with' || t === 'plus') {
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
  const anteFlat = flattenTensor(rule.antecedent);
  const conseqBody = unwrapMonad(rule.consequent);
  const conseqFlat = flattenTensor(conseqBody);

  // Trigger predicates for rule indexing
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

  const opcodeHash = discriminator ? discriminator.groundValue : null;

  // Persistent output vars (freevars in output positions of persistent patterns)
  const persistentOutputVars = new Set();
  for (const p of (anteFlat.persistent || [])) {
    for (const v of collectOutputVars(p)) persistentOutputVars.add(v);
  }

  // Per-linear-pattern metadata (avoids Store.get walks in tryMatch)
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

  // Expand consequent choices (opens exists binders, expands with/plus)
  const consequentAlts = expandConsequentChoices(conseqFlat);

  // De Bruijn slot assignment (metavar → slot index)
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

  // Existential slots: metavars in consequent but NOT in antecedent and NOT in lolis
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

  // For single-alt rules, use expanded consequent (opens exists binders)
  // so that analyzeDeltas, mutateState, and compiled substitution all see opened patterns.
  const effectiveConseq = consequentAlts.length === 1
    ? consequentAlts[0]
    : conseqFlat;

  const compiled = {
    name: rule.name,
    hash: rule.hash,
    antecedent: anteFlat,
    consequent: effectiveConseq,
    triggerPreds,
    opcodeHash,
    discriminator,
    persistentOutputVars,
    linearMeta,
    metavarSlots,
    metavarCount,
    existentialSlots,
    existentialGoals
  };

  // Analysis metadata
  compiled.analysis = analyzeDeltas(compiled);
  compiled.limits = analyzeBufferLimits(compiled);
  compiled.consequentAlts = consequentAlts;
  compiled.patternRoles = computePatternRoles(
    anteFlat.linear || [], compiled.analysis, metavarSlots
  );
  compiled.compiledConseqLinear = (effectiveConseq.linear || []).map(
    p => compileSubstitution(p, metavarSlots)
  );
  compiled.compiledConseqPersistent = (effectiveConseq.persistent || []).map(
    p => compileSubstitution(p, metavarSlots)
  );

  return compiled;
}

module.exports = {
  compileRule,
  flattenTensor,
  unwrapMonad,
  isGround,
  collectMetavars,
  collectFreevars,
  expandItem,
  expandConsequentChoices,
};
