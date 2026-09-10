/**
 * Well-modedness checker (task #81 / P7) — the load-time mode system that
 * discharges THY_0039 Theorem 3's hypothesis. See doc/theory/0039 §6.
 *
 * A pure load-time fence beside the datasort/priors/sort validators. It reads
 * the compiled rule set + clause set and produces, per program:
 *   - functionalPreds : Set<"pred#outPos">  — the certified-functional forced
 *     modes (§6.1), consumed by the forcing-goal check and (future) task #84.
 *   - { warnings, errors }                  — well-modedness violations.
 *
 * Enforcement is WARN-FIRST: every finding is a warning surfaced on
 * calc.wellModedLint. A calculus flips it to a hard load error by setting
 * cc.wellModed === 'strict' (the cc.typeCheck: 'strict' pattern) once its
 * corpus is confirmed inside the accepted set.
 *
 * SOUNDNESS DIRECTION (§6.4): the analysis over-approximates — it may reject a
 * well-moded program, never accept an ill-moded one. Certification is sound
 * (certified ⇒ functional): input-disjoint heads bound the clause count to ≤ 1
 * per ground input, AND a coinductive body-determinism check ensures each
 * clause's output is functionally determined from its inputs (so a relational
 * body — `p X Y <- edge X Y` — is NOT certified, and forcing it is flagged).
 *
 * This module imports only lib/ (kernel Store + the eq/neq solver); the
 * calculus supplies modes as DATA through cc (layer-dag clean).
 */

import Store from '../kernel/store.js';

// Leaf tags that denote a VARIABLE (an opaque hole a parameter may fill).
// metavar: rule/clause slot; freevar: clause body var; evar: runtime
// eigenvariable; var/bound: quantifier machinery (defensive — not expected in
// flat fact patterns, but treated as opaque rather than structural).
const _VAR_TAGS = new Set([
  Store.TAG.metavar, Store.TAG.freevar, Store.TAG.evar,
  Store.TAG.var, Store.TAG.bound,
].filter((t) => t !== undefined));

function isVar(h) {
  return _VAR_TAGS.has(Store.tagId(h));
}

/** Predicate tag of a fact/goal hash, or null if it is not a predicate. */
function predTagOf(h) {
  const t = Store.tagId(h);
  return t >= Store.PRED_BOUNDARY ? t : null;
}

/**
 * Sound non-unifiability: returns true only when a and b DEFINITELY cannot
 * unify (a witness of input-disjointness). A variable on either side unifies
 * with anything (⇒ false, conservatively "may overlap"). Distinct constructor
 * heads, distinct arities, or distinct leaf values at aligned positions ⇒ true.
 */
function nonUnifiable(a, b) {
  if (isVar(a) || isVar(b)) return false;
  const ta = Store.tagId(a);
  const tb = Store.tagId(b);
  if (ta !== tb) return true;
  const na = Store.arity(a);
  const nb = Store.arity(b);
  if (na !== nb) return true;
  for (let i = 0; i < na; i++) {
    const ca = Store.child(a, i);
    const cb = Store.child(b, i);
    if (Store.isTerm(ca) && Store.isTerm(cb)) {
      if (nonUnifiable(ca, cb)) return true;
    } else if (ca !== cb) {
      // Non-term children (atom name string, binlit/ratlit bigint index):
      // different interned value ⇒ the leaves are distinct ⇒ disjoint.
      return true;
    }
  }
  return false;
}

/** Collect the metavar/freevar hashes occurring anywhere under h into `out`. */
function collectVars(h, out) {
  if (isVar(h)) { out.add(h); return; }
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) {
    const c = Store.child(h, i);
    if (Store.isTerm(c)) collectVars(c, out);
  }
}

/** First arg index of `goal` whose subterm contains metavar `v`, or -1. */
function argIndexContaining(goal, v) {
  const n = Store.arity(goal);
  for (let i = 0; i < n; i++) {
    const c = Store.child(goal, i);
    if (!Store.isTerm(c)) continue;
    const vs = new Set();
    collectVars(c, vs);
    if (vs.has(v)) return i;
  }
  return -1;
}

/** Whether every var under arg `i` of `goal` is in `ground`. */
function argGround(goal, i, ground) {
  const c = Store.child(goal, i);
  if (!Store.isTerm(c)) return true;
  const vs = new Set();
  collectVars(c, vs);
  for (const v of vs) if (!ground.has(v)) return false;
  return true;
}

/** Antecedent-bound metavar hashes of a compiled rule (ground at match). */
function anteVars(rule) {
  const g = new Set();
  const a = rule.antecedent || {};
  for (const p of (a.linear || [])) collectVars(p, g);
  for (const p of (a.persistent || [])) collectVars(p, g);
  return g;
}

/**
 * §6.1 — certify the functional forced modes of the program.
 *
 * Returns Set<"predName#outPos">: predicate p is certified functional with
 * output position `out` (inputs = the other positions) when
 *   (a) its clause heads are pairwise input-disjoint (some input position is
 *       non-unifiable across every pair — ≤ 1 clause per ground input), AND
 *   (b) every clause's body functionally determines the head's output vars
 *       from its input vars, using only currently-certified premise modes
 *       (a greatest fixpoint: assume all input-disjoint modes, drop any whose
 *       body fails — so mutual/self recursion like plus is admitted, while a
 *       body that grounds its output through a non-certified (relational or
 *       EDB) predicate is rejected).
 *
 * Zero-clause predicates are certified ONLY through the FFI mode table (their
 * declared `-` positions, the documented spec-functional carve-out); a
 * zero-clause predicate with no FFI mode is a relational EDB fact and is never
 * certified — forcing it is a G1 violation.
 */
function certifyFunctional(clauses, cc) {
  // Group clause heads by predicate tag.
  const byPred = new Map(); // tag -> [{ head, premises }]
  for (const c of clauses.values()) {
    const t = predTagOf(c.hash);
    if (t === null) continue;
    if (!byPred.has(t)) byPred.set(t, []);
    byPred.get(t).push({ head: c.hash, premises: c.premises || [] });
  }

  // Candidate clausal modes: (pred, out) whose heads are input-disjoint.
  const candidate = new Set();
  for (const [t, cls] of byPred) {
    const name = Store.TAG_NAMES[t];
    const ar = Store.arity(cls[0].head);
    for (let out = 0; out < ar; out++) {
      if (inputDisjoint(cls, out, ar)) candidate.add(name + '#' + out);
    }
  }

  // FFI spec-functional certification (§6.1 carve-out): a non-multiModal FFI
  // predicate is functional at each declared `-` (output) position — the FFI
  // is the property-tested oracle, and the FFI≡clause invariant (noFFI arms)
  // makes the clause resolution compute the same unique function. This applies
  // whether or not the predicate also has clauses (their body-determinism need
  // not be re-provable by this analysis).
  const ffiCertified = new Set();
  const ffi = cc && cc.ffi;
  const modes = ffi && ffi.parsedModes;
  if (modes) {
    for (const name of Object.keys(modes)) {
      const meta = ffi.getModeMeta ? ffi.getModeMeta(name) : { modes: modes[name], multiModal: false };
      if (!meta || !meta.modes || meta.multiModal) continue;
      for (let i = 0; i < meta.modes.length; i++) {
        if (meta.modes[i] === '-') ffiCertified.add(name + '#' + i);
      }
    }
  }

  // Greatest fixpoint on body-determinism for the CLAUSAL candidates: start
  // optimistic, drop a clausal mode whose some clause body no longer grounds
  // its output through certified premises (mutual/self recursion admitted).
  const certified = new Set([...candidate, ...ffiCertified]);
  for (;;) {
    let changed = false;
    for (const key of [...certified]) {
      if (ffiCertified.has(key)) continue; // spec-functional, no body to check
      const hashPos = key.lastIndexOf('#');
      const name = key.slice(0, hashPos);
      const out = +key.slice(hashPos + 1);
      const cls = byPred.get(Store.TAG[name]) || [];
      for (const c of cls) {
        if (!bodyDetermines(c, out, certified)) { certified.delete(key); changed = true; break; }
      }
    }
    if (!changed) break;
  }
  return certified;
}

/** Heads pairwise non-unifiable on some input position (complement of `out`). */
function inputDisjoint(cls, out, ar) {
  for (let i = 0; i < cls.length; i++) {
    for (let j = i + 1; j < cls.length; j++) {
      let sep = false;
      for (let k = 0; k < ar; k++) {
        if (k === out) continue;
        if (nonUnifiable(Store.child(cls[i].head, k), Store.child(cls[j].head, k))) { sep = true; break; }
      }
      if (!sep) return false;
    }
  }
  return true;
}

/**
 * Does clause `c` functionally determine its head's `out` vars from its input
 * vars, given the currently-certified premise modes? Left-to-right saturation:
 * seed the ground set with the head's INPUT vars; a premise grounds its output
 * vars once it has a certified output mode whose other positions are all
 * ground; a premise all of whose positions are already ground is a pure guard.
 * Succeeds iff the head's OUTPUT vars end up ground.
 */
function bodyDetermines(c, out, certified) {
  const ground = new Set();
  const ar = Store.arity(c.head);
  for (let k = 0; k < ar; k++) {
    if (k === out) continue;
    const a = Store.child(c.head, k);
    if (Store.isTerm(a)) collectVars(a, ground);
  }
  const pending = (c.premises || []).slice();
  for (;;) {
    let progressed = false;
    for (let pi = 0; pi < pending.length; pi++) {
      const g = pending[pi];
      if (g === undefined) continue;
      const pt = predTagOf(g);
      if (pt === null) { pending[pi] = undefined; continue; } // non-predicate premise: ignore
      const pname = Store.TAG_NAMES[pt];
      const gar = Store.arity(g);
      // A premise is a resolvable "determiner" if it has a certified output
      // position whose every other position's vars are already ground.
      let firedOut = -1;
      for (let o = 0; o < gar; o++) {
        if (!certified.has(pname + '#' + o)) continue;
        let inputsGround = true;
        for (let k = 0; k < gar && inputsGround; k++) {
          if (k === o) continue;
          const a = Store.child(g, k);
          if (!Store.isTerm(a)) continue;
          const vs = new Set(); collectVars(a, vs);
          for (const v of vs) if (!ground.has(v)) { inputsGround = false; break; }
        }
        if (inputsGround) { firedOut = o; break; }
      }
      // Or a pure guard: every position already ground.
      let allGround = true;
      for (let k = 0; k < gar && allGround; k++) {
        const a = Store.child(g, k);
        if (!Store.isTerm(a)) continue;
        const vs = new Set(); collectVars(a, vs);
        for (const v of vs) if (!ground.has(v)) { allGround = false; break; }
      }
      if (firedOut >= 0) {
        const a = Store.child(g, firedOut);
        if (Store.isTerm(a)) collectVars(a, ground);
        pending[pi] = undefined; progressed = true;
      } else if (allGround) {
        pending[pi] = undefined; progressed = true;
      }
    }
    if (!progressed) break;
  }
  // Head output vars must all be ground.
  const outVars = new Set();
  if (out < ar) {
    const a = Store.child(c.head, out);
    if (Store.isTerm(a)) collectVars(a, outVars);
  }
  for (const v of outVars) if (!ground.has(v)) return false;
  return true;
}

/**
 * §6.1 enforcement — a forcing goal (a persistent goal determining an
 * existential slot, `compile.js` existentialGoals) must name a
 * certified-functional predicate at the slot's output position. A non-certified
 * force is the G1 violation class: committing to one witness of a possibly
 * non-functional predicate.
 */
function checkForcingGoals(compiledRules, certified, warnings) {
  for (const rule of compiledRules) {
    const eg = rule.existentialGoals;
    if (!eg) continue;
    const slotToHash = {};
    for (const h in rule.metavarSlots) slotToHash[rule.metavarSlots[h]] = +h;

    // Determiner discovery mirrors the runtime resolver's dataflow: seed the
    // ground set with the antecedent-bound vars; a goal DETERMINES a slot at
    // position i when the slot sits at i and every OTHER position is already
    // ground (antecedent var or an earlier-determined slot). That output
    // position — not any input occurrence — is what must be certified.
    const ground = anteVars(rule);
    // Gather the distinct resolver goals (existentialGoals may repeat a goal
    // under several slots — e.g. to256 C C' under both C and C').
    const goals = new Set();
    for (const slot in eg) for (const g of eg[slot]) goals.add(g);

    const flagged = new Set();
    for (;;) {
      let progressed = false;
      for (const goal of goals) {
        const pt = predTagOf(goal);
        if (pt === null) continue;
        const gar = Store.arity(goal);
        for (let i = 0; i < gar; i++) {
          const c = Store.child(goal, i);
          if (!Store.isTerm(c)) continue;
          // slot at position i not yet ground, all others ground ⇒ this goal
          // determines the slot(s) here.
          const vs = new Set(); collectVars(c, vs);
          let hasUngroundSlot = false;
          for (const v of vs) if (!ground.has(v)) { hasUngroundSlot = true; break; }
          if (!hasUngroundSlot) continue;
          let othersGround = true;
          for (let k = 0; k < gar && othersGround; k++) {
            if (k === i) continue;
            if (!argGround(goal, k, ground)) othersGround = false;
          }
          if (!othersGround) continue;
          // Determined here. Ground the slot vars.
          for (const v of vs) ground.add(v);
          progressed = true;
          const pname = Store.TAG_NAMES[pt];
          const key = pname + '#' + i;
          if (!certified.has(key) && !flagged.has(rule.name + '|' + key)) {
            flagged.add(rule.name + '|' + key);
            warnings.push(
              `rule '${rule.name}': forces non-certified-functional predicate ` +
              `'${pname}' at output position ${i} (G1 — the witness may not be ` +
              `unique; §6.1). Declare it functional or leave the goal deferred.`,
            );
          }
        }
      }
      if (!progressed) break;
    }
  }
}

/**
 * The load-time well-modedness check. Presence-gated by the caller (run only
 * when some rule has an existential slot or an internal choice). Returns
 * { functionalPreds, warnings, errors }; warn-first ⇒ errors stays empty
 * unless cc.wellModed === 'strict' (applied by the caller).
 */
function checkWellModed({ compiledRules, clauses, cc }) {
  const functionalPreds = certifyFunctional(clauses || new Map(), cc);
  const warnings = [];
  const errors = [];
  checkForcingGoals(compiledRules || [], functionalPreds, warnings);
  return { functionalPreds, warnings, errors };
}

export {
  checkWellModed,
  certifyFunctional,
  nonUnifiable,
  isVar,
  predTagOf,
  collectVars,
  argIndexContaining,
};
export default { checkWellModed };
