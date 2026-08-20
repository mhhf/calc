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

import Store from '../kernel/store.js';
import { defaultGradeConfig } from './grades.js';
import { debruijnSubst } from '../kernel/substitute.js';
import { freshMetavar } from '../kernel/fresh.js';
import { mul as _ratMul, sub as _ratSub, norm as _ratNorm } from '../rat.js';
import { ratParts } from './theories/ratlit-theory.js';
// --- Fact keys ---

/**
 * Lax fact key for the forward-engine fact space: the atom name or tag
 * name of a pattern/fact head, after unwrapping a counted parcel
 * (bang(k, A) via expTag) and a stamp (at(A, t)). Every GROUND head has
 * a key — sub-boundary kernel tags (e.g. a bare binlit fact) key by
 * their tag name. Returns null only for variable heads (metavar/freevar)
 * and non-terms.
 *
 * Contrast with kernel predHead (strict): null for sub-boundary tags,
 * used in the compile-time trigger/discriminator space where null means
 * "no index info, stay conservative". The two spaces must not be mixed:
 * any producer/consumer key pair (fire's producedPreds ↔ the dirty
 * scheduler's wake-up map, instant-feeding antePreds ↔ output heads)
 * must compute BOTH sides with THIS function — computing one side
 * strictly made literal-fact consumers invisible to dirty tracking
 * (round-14 fuzz find).
 */
function factKeyOf(h, expTag, stampTag = 'at') {
  let body = h;
  if (expTag && Store.tag(body) === expTag) body = Store.child(body, 1);
  if (stampTag && Store.tag(body) === stampTag) body = Store.child(body, 0);
  const t = Store.tag(body);
  if (!t || t === 'metavar' || t === 'freevar') return null;
  return t === 'atom' ? Store.child(body, 0) : t;
}

// --- Connective resolution ---

/**
 * Computation (lax monad) role record — the ONE shape every monad-aware
 * site reads (TODO_0265 Phase 2). Layouts by arity:
 *   arity 1: { tag, bodyIdx: 0, gradeIdx: null }   — ILL's {A}
 *   arity 2: { tag, bodyIdx: 1, gradeIdx: 0 }      — graded {A}@d (grade first,
 *            mirroring bang(grade, formula))
 * Other arities have no computation layout → no role.
 */
function computationRole(tag, arity) {
  if (arity === 1) return { tag, bodyIdx: 0, gradeIdx: null };
  if (arity === 2) return { tag, bodyIdx: 1, gradeIdx: 0 };
  return null;
}

/** The ILL instance of the computation role — the ONE shared default
 *  (audit round 11: was duplicated inline at six sites). Binary since the
 *  D6 merge-back (TODO_0157): ILL's `{A}` is monad(unit, A), the
 *  trivial-grade instance of the graded monad till also uses. */
const ILL_COMPUTATION = Object.freeze(computationRole('monad', 2));

/**
 * Derive structural role → tag name lookups from a connective table.
 * The connective table maps tag → { category, arity, polarity } (from .calc
 * annotations). This function inverts it for O(1) access by structural role.
 *
 * `computation` is a record { tag, bodyIdx, gradeIdx } (see computationRole),
 * not a bare tag — sites read child indices from it instead of assuming
 * unary layout. The result also carries the grade classification functions
 * { grade0, gradeOmega } (from gradeConfig; default = ILL's {0, 1, ω}
 * atoms) so every walker that classifies bang grades reads them from the
 * same resolved record the callers already thread.
 *
 * @param {Object} ct - Connective table (tag → { category, arity, polarity })
 * @param {Object} [gradeConfig] - { grade0: () => hash, gradeOmega: () => hash }
 * @returns {Object} Resolved roles { product, implication, exponential, computation,
 *   internalChoice, externalChoice, existential, unit, additiveZero, grade0, gradeOmega }
 */
function resolveConn(ct, gradeConfig) {
  const r = {};
  for (const tag in ct) {
    const { category: c, arity: a, polarity: p } = ct[tag];
    if (c === 'multiplicative' && a === 2 && p === 'positive') r.product = tag;
    else if (c === 'multiplicative' && a === 2 && p === 'negative') r.implication = tag;
    else if (c === 'multiplicative' && a === 0) r.unit = tag;
    else if (c === 'exponential' && a === 2) r.exponential = tag;
    else if (c === 'monad') { const rec = computationRole(tag, a); if (rec) r.computation = rec; }
    else if (c === 'additive' && a === 2 && p === 'positive') r.internalChoice = tag;
    else if (c === 'additive' && a === 3 && p === 'positive') r.weightedChoice = tag;
    else if (c === 'additive' && a === 2 && p === 'negative') r.externalChoice = tag;
    else if (c === 'additive' && a === 0) r.additiveZero = tag;
    else if (c === 'quantifier' && a === 1 && p === 'positive') r.existential = tag;
  }
  const g = gradeConfig || defaultGradeConfig;
  r.grade0 = g.grade0;
  r.gradeOmega = g.gradeOmega;
  return r;
}

/**
 * Derive a loader connTags record (convert.js loaderConfig) from a
 * connective table. The loader needs exactly the four structural tags plus
 * the 'preserved' wrapper — all four are already implied by the table, so
 * a calculus config never hand-writes them (TODO_0265 Phase 3 follow-up:
 * gtoy/till previously restated the computation record redundantly).
 * @param {Object} ct - Connective table (tag → { category, arity, polarity })
 */
function connTagsFrom(ct) {
  const r = resolveConn(ct);
  return {
    computation: r.computation,
    implication: r.implication,
    product: r.product,
    exponential: r.exponential,
    preserved: 'preserved',
  };
}

// --- Term walkers ---

/**
 * Flatten multiplicative product spine into linear + persistent + grade0 lists.
 *
 * FOUR-way grade classification (TODO_0265 P7 — D4 count grades):
 *   g0      → grade0[]     (compile-time, filtered before runtime)
 *   gradeW  → persistent[] (weakening + contraction)
 *   bare    → linear[]     (grade-1 implicit, consumed once)
 *   other   → linear[], KEPT WRAPPED — a counted parcel `!_k A` / `!_W A`
 *             (numeric or variable grade); compile reads countTake/countVar
 *             from the wrapper (P4), the timed matcher owns the semantics.
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
  // Hoisted per call: the Store is never reindexed mid-walk, so the ID is stable.
  const g0 = (ct.grade0 || defaultGradeConfig.grade0)();
  const gw = (ct.gradeOmega || defaultGradeConfig.gradeOmega)();

  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === ct.unit) return;               // multiplicative unit: no resource
    if (t === productTag) {
      walk(Store.child(hash, 0));
      walk(Store.child(hash, 1));
    } else if (t === expTag) {
      const grade = Store.child(hash, 0);
      const inner = Store.child(hash, 1);
      if (grade === g0) {
        grade0.push(inner);
      } else if (grade === gw) {
        persistent.push(inner);
      } else {
        // Counted parcel (D4): linear, kept wrapped for compile/matcher.
        linear.push(hash);
      }
    } else {
      linear.push(hash);
    }
  }

  walk(h);
  return { linear, persistent, grade0 };
}

/**
 * Unwrap computation body ({A} → A, {A}@d → A).
 * @param {number} h - Consequent hash
 * @param {Object} ct - Connectives config (needs computation record)
 */
function unwrapComp(h, ct) {
  const comp = ct.computation;
  if (comp && Store.tag(h) === comp.tag) return Store.child(h, comp.bodyIdx);
  return h;
}

// --- Choice expansion ---

/**
 * Weight expressions during choice expansion: a ground [n,d] BigInt pair,
 * or — when a woplus weight is a rule variable (fire-time weights, Phase 6)
 * — { g: [n,d], syms: [{ v: metavarHash, comp: bool }] }: a ground prefix
 * times a product of θ-resolved factors (comp: the 1−Q complement branch).
 * compileRule maps syms to slots; the timed scheduler resolves them at
 * firing (compile-time mode check guarantees boundness, like delays/windows).
 */
function _wxMul(a, b) {
  if (!a) return b;
  if (!b) return a;
  const aArr = Array.isArray(a), bArr = Array.isArray(b);
  if (aArr && bArr) return _ratMul(a, b);
  return {
    g: _ratMul(aArr ? a : a.g, bArr ? b : b.g),
    syms: [...(aArr ? [] : a.syms), ...(bArr ? [] : b.syms)],
  };
}

/** Multiply an alternative's path weight (weight expression; absent = 1). */
function _weighted(alt, w) {
  return { ...alt, weight: _wxMul(alt.weight, w) };
}

/**
 * Expand a hash into alternatives through choice/product/exponential/existential.
 * Weighted internal choice (`woplus Q A B`, ct.weightedChoice — TODO_0265
 * Phase 4b) expands like internalChoice but attaches exact path weights:
 * left alternatives get ×Q, right ×(1−Q); nested/tensored choices multiply,
 * so a rule's alternatives always carry a distribution summing to 1.
 * @param {number} h - Formula hash
 * @param {Object} ct - Connectives config
 */
function expandChoice(h, ct) {
  const t = Store.tag(h);
  if (!t) return [{ linear: [h], persistent: [], grade0: [] }];

  if (t === ct.unit) {
    // Multiplicative unit: the empty output (`A -o { I }` = affine discard).
    return [{ linear: [], persistent: [], grade0: [] }];
  }
  if (t === ct.externalChoice) {
    // External choice is the ENVIRONMENT's move, not the engine's: a rule
    // OFFERS `A & B` as ONE inert linear fact (the menu). The host collapses
    // it via with-projection (timed.js choose) — expanding it into
    // alternatives here would hand the environment's choice to the engine
    // (Phase 6, Denis: decisions collapse offered choices, injection is out).
    return [{ linear: [h], persistent: [], grade0: [] }];
  }
  if (t === ct.internalChoice) {
    return [
      ...expandChoice(Store.child(h, 0), ct),
      ...expandChoice(Store.child(h, 1), ct)
    ];
  }
  if (ct.weightedChoice && t === ct.weightedChoice) {
    // woplus parses via application, so ANY arity is syntactically reachable —
    // without this guard, arity 2 reads child(h, 2) out of bounds (a null
    // hash silently entering the alternative) and arity 4 drops an argument.
    if (Store.arity(h) !== 3) {
      throw new Error(`woplus requires exactly 3 arguments (weight A B), got ${Store.arity(h)}`);
    }
    const wh = Store.child(h, 0);
    const wTag = Store.tag(wh);
    if (wTag === 'metavar' || wTag === 'freevar') {
      // Fire-time weight (Phase 6): Q is a rule variable — expand the two
      // alternatives with symbolic factors Q and 1−Q; the pair sums to 1 by
      // construction once Q resolves to a rational in [0,1] (checked at
      // firing). Boundness is checked by compileRule (delay-style mode check).
      return [
        ...expandChoice(Store.child(h, 1), ct)
          .map(a => _weighted(a, { g: [1n, 1n], syms: [{ v: wh, comp: false }] })),
        ...expandChoice(Store.child(h, 2), ct)
          .map(a => _weighted(a, { g: [1n, 1n], syms: [{ v: wh, comp: true }] })),
      ];
    }
    const q = ratParts(wh);
    if (!q) {
      throw new Error(`woplus weight must be a ground rational literal or a rule variable (got '${wTag}')`);
    }
    if (q[0] < 0n || q[0] > q[1]) {
      throw new Error(`woplus weight must be in [0, 1] (got ${q[0]}/${q[1]})`);
    }
    const comp = _ratSub([1n, 1n], q);
    return [
      ...expandChoice(Store.child(h, 1), ct).map(a => _weighted(a, _ratNorm(q[0], q[1]))),
      ...expandChoice(Store.child(h, 2), ct).map(a => _weighted(a, comp)),
    ];
  }
  if (t === ct.product) {
    const lefts = expandChoice(Store.child(h, 0), ct);
    const rights = expandChoice(Store.child(h, 1), ct);
    const out = [];
    for (const l of lefts) {
      for (const r of rights) {
        const alt = {
          linear: [...l.linear, ...r.linear],
          persistent: [...l.persistent, ...r.persistent],
          grade0: [...l.grade0, ...r.grade0]
        };
        const w = _wxMul(l.weight, r.weight);
        if (w) alt.weight = w;
        out.push(alt);
      }
    }
    return out;
  }
  if (t === ct.exponential) {
    const grade = Store.child(h, 0);
    const inner = Store.child(h, 1);
    if (grade === (ct.grade0 || defaultGradeConfig.grade0)()) {
      return [{ linear: [], persistent: [], grade0: [inner] }];
    }
    if (grade === (ct.gradeOmega || defaultGradeConfig.gradeOmega)()) {
      return [{ linear: [], persistent: [inner], grade0: [] }];
    }
    // Counted parcel `!_k A` / `!_Y A` (D4): a LINEAR output, kept wrapped —
    // the timed matcher produces count copies at firing (P7).
    return [{ linear: [h], persistent: [], grade0: [] }];
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
        const alt = {
          linear: [...acc.linear, ...ia.linear],
          persistent: [...acc.persistent, ...ia.persistent],
          grade0: [...acc.grade0, ...ia.grade0]
        };
        const w = _wxMul(acc.weight, ia.weight);
        if (w) alt.weight = w;
        next.push(alt);
      }
    }
    alts = next;
  }

  const origPersistent = consequent.persistent || [];
  const origGrade0 = consequent.grade0 || [];
  if (origPersistent.length > 0 || origGrade0.length > 0) {
    alts = alts.map(a => ({
      ...a,
      persistent: origPersistent.length > 0 ? [...a.persistent, ...origPersistent] : a.persistent,
      grade0: origGrade0.length > 0 ? [...a.grade0, ...origGrade0] : a.grade0
    }));
  }

  return alts;
}

export { computationRole, ILL_COMPUTATION, resolveConn, connTagsFrom, flattenAnte, unwrapComp, expandChoice, expandConsqChoices, factKeyOf };
export default { computationRole, ILL_COMPUTATION, resolveConn, connTagsFrom, flattenAnte, unwrapComp, expandChoice, expandConsqChoices, factKeyOf };
