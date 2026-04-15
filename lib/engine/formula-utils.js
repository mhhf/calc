/**
 * Connective-aware formula decomposition utilities.
 *
 * Pure tree-walking functions that inspect/transform content-addressed
 * formula hashes using knowledge of which tags are products, implications,
 * exponentials, etc.  Shared across pipeline stages (Compile, Compose,
 * Runtime) — extracted from compile.js to break lateral coupling.
 *
 * Complement to pattern-utils.js (tag-agnostic pattern operations).
 */

const Store = require('../kernel/store');
const { GRADE_0 } = require('./grades');
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
function resolveConn(ct) {
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
function flattenAnte(h, ct) {
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
function unwrapComp(h, ct) {
  if (Store.tag(h) === ct.computation) return Store.child(h, 0);
  return h;
}

// --- Choice expansion ---

/**
 * Expand a hash into alternatives through choice/product/exponential/existential.
 * @param {number} h - Formula hash
 * @param {Object} ct - Connectives config
 */
function expandChoice(h, ct) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [], grade0: [] }];

  if (t === ct.externalChoice || t === ct.internalChoice) {
    return [
      ...expandChoice(Store.child(h, 0), ct),
      ...expandChoice(Store.child(h, 1), ct)
    ];
  }
  if (t === ct.product) {
    const lefts = expandChoice(Store.child(h, 0), ct);
    const rights = expandChoice(Store.child(h, 1), ct);
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
    return expandChoice(opened, ct);
  }
  // Lolis stay as opaque linear facts — fired by matchLoli at runtime
  return [{ linear: [h], persistent: [], grade0: [] }];
}

/**
 * Expand compiled consequent into choice alternatives.
 * @param {Object} consequent - { linear, persistent }
 * @param {Object} ct - Connectives config
 */
function expandConsqChoices(consequent, ct) {
  let alts = [{ linear: [], persistent: [], grade0: [] }];

  for (const h of (consequent.linear || [])) {
    const itemAlts = expandChoice(h, ct);
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

module.exports = { resolveConn, flattenAnte, unwrapComp, expandChoice, expandConsqChoices };
