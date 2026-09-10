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

// ── §6.2 — parameter-flow analysis + V1 (structural match) ──────────────
//
// Parameter-freeness over predicate-argument LEAF PATHS. A path is the index
// route from a fact's predicate root to a leaf, e.g. [0,0] = "arg0 → child0".
// taint(pred) ⊆ leaf paths that MAY hold a parameter (an eigenvariable).
//
// Taint marks only LEAF positions (where a variable/parameter sits), never the
// constructor SPINE — matching a list's cons cells is never a violation; only
// decomposing a parameter VALUE is. Unbounded recursion (a runtime stack of
// parameters, values at 0.1ᵏ.0) is handled by a REGULAR STAR PATH abstraction:
// a maximal run of a repeated child index collapses to a star `c*` (0+ repeats).
// The star keeps the value/spine distinction exact — 0.1*.0 is "a value at any
// tail depth", 0.1* is "any cons cell" — and canonicalisation bounds the path
// set, so the fixpoint terminates without the value↔spine confusion a plain
// depth truncation would introduce.
//
// Path component encoding: a concrete child index c ≥ 0, or a star of c encoded
// as the negative -(c+2). All paths in the taint sets are canonical.

const STAR = (c) => -(c + 2);
const isStarC = (x) => x < 0;
const starBase = (x) => -x - 2;

/**
 * Canonicalise a path. A run of a concrete index whose length reaches `thr`
 * collapses to a star — `thr` exceeds the deepest fixed nesting any pattern
 * inspects, so only genuine UNBOUNDED recursion (arbitrarily long runs, e.g. a
 * cons list's repeated tail-descent) is starred; fixed multi-level nesting like
 * arg0→child0 stays concrete. The absorb pass (c·c* ⇒ c*) then converges the
 * recursion under the fixpoint's shifts. A hard safety collapse at 4·thr keeps
 * any non-run growth terminating.
 */
function canonPath(p, thr) {
  const T = thr || 2;
  let src = p;
  if (src.length > 4 * T) {
    // safety: collapse the longest concrete run to a star, else drop the tail.
    let bi = -1, bl = 0;
    for (let i = 0; i < src.length;) {
      const x = src[i]; if (isStarC(x)) { i++; continue; }
      let j = i; while (j < src.length && src[j] === x) j++;
      if (j - i > bl) { bl = j - i; bi = i; } i = j;
    }
    if (bl >= 2) src = src.slice(0, bi).concat([STAR(src[bi])], src.slice(bi + bl));
    else src = src.slice(0, 4 * T);
  }
  const a = [];
  for (let i = 0; i < src.length;) {
    const x = src[i];
    if (isStarC(x)) { a.push(x); i++; continue; }
    let j = i; while (j < src.length && src[j] === x) j++;
    if (j - i >= T) a.push(STAR(x));
    else for (let q = i; q < j; q++) a.push(x);
    i = j;
  }
  const res = [];
  for (const x of a) {
    const last = res.length ? res[res.length - 1] : null;
    if (last !== null && isStarC(last)) {
      const b = starBase(last);
      if ((isStarC(x) && starBase(x) === b) || (!isStarC(x) && x === b)) continue; // absorbed into star
    }
    if (last !== null && !isStarC(last) && isStarC(x) && starBase(x) === last) {
      res[res.length - 1] = x; continue; // c · c* ⇒ c*
    }
    res.push(x);
  }
  return res;
}

const keyOfPath = (arr) => arr.join(',');
const parsePath = (s) => (s === '' ? [] : s.split(',').map(Number));

/** Predicate name of a fact/goal hash, or null. */
function predName(h) {
  const t = predTagOf(h);
  return t === null ? null : Store.TAG_NAMES[t];
}

/** Variable leaves of a fact with their (concrete) leaf paths: [{ v, path }]. */
function leafVars(fact) {
  const out = [];
  const rec = (h, path) => {
    if (isVar(h)) { out.push({ v: h, path }); return; }
    const n = Store.arity(h);
    for (let i = 0; i < n; i++) {
      const c = Store.child(h, i);
      if (Store.isTerm(c)) rec(c, path.concat(i));
    }
  };
  const n = Store.arity(fact);
  for (let i = 0; i < n; i++) {
    const c = Store.child(fact, i);
    if (Store.isTerm(c)) rec(c, [i]);
  }
  return out;
}

/**
 * V1 test: does linear pattern `pat` DEMAND structure at a parameter leaf whose
 * position is described by the (possibly starred) path `tau`? DFS the NFA of
 * tau against the finite pattern: a star `c*` traverses 0+ child-c steps
 * (matching the cons SPINE — always fine); when tau is fully consumed we are at
 * the parameter leaf, and a NON-variable there decomposes the parameter (V1);
 * an ancestor variable carries the parameter opaquely (OK).
 */
function structuralAtStar(pat, tau) {
  const seen = new Set();
  const stack = [[pat, 0]];
  while (stack.length) {
    const [cur, ti] = stack.pop();
    const k = cur + '@' + ti;
    if (seen.has(k)) continue;
    seen.add(k);
    if (ti === tau.length) { if (!isVar(cur)) return true; continue; }
    if (isVar(cur)) continue;
    const comp = tau[ti];
    if (isStarC(comp)) {
      const b = starBase(comp);
      stack.push([cur, ti + 1]); // zero repeats
      if (b < Store.arity(cur)) { const c = Store.child(cur, b); if (Store.isTerm(c)) stack.push([c, ti]); }
    } else if (comp < Store.arity(cur)) {
      const c = Store.child(cur, comp); if (Store.isTerm(c)) stack.push([c, ti + 1]);
    }
  }
  return false;
}

/**
 * Consume concrete path `pi` (a variable's leaf path in a matched pattern)
 * against starred taint path `tau`. Returns { exact, residuals }: exact ⇒ the
 * variable IS the parameter (relative ε); each residual is the starred tail of
 * tau below pi — the parameter that variable then carries.
 */
function tauResiduals(pi, tau) {
  const residuals = [];
  let exact = false;
  const seen = new Set();
  const stack = [[0, 0]];
  while (stack.length) {
    const [pj, ti] = stack.pop();
    const k = pj + '@' + ti;
    if (seen.has(k)) continue;
    seen.add(k);
    if (pj === pi.length) {
      if (ti === tau.length) exact = true;
      else residuals.push(tau.slice(ti));
      continue;
    }
    if (ti === tau.length) continue;
    const comp = tau[ti];
    if (isStarC(comp)) {
      const b = starBase(comp);
      stack.push([pj, ti + 1]);                 // zero repeats
      if (pi[pj] === b) stack.push([pj + 1, ti]); // one repeat consumes pi[pj]
    } else if (pi[pj] === comp) {
      stack.push([pj + 1, ti + 1]);
    }
  }
  return { exact, residuals };
}

/**
 * Least-fixpoint parameter-flow. Sources: every existential slot (conservatively
 * all may defer, §6.2). Transfer: a consumed pattern's variable that binds a
 * tainted position carries the parameter (as a RELATIVE starred path);
 * reproducing that variable seeds taint at the shifted position — the conduit
 * that keeps value leaves tainted while the spine stays clean.
 */
/** Max node depth (path length) in a term's argument structure. */
function maxNodeDepth(fact) {
  let mx = 0;
  const rec = (h, d) => {
    if (d > mx) mx = d;
    const n = Store.arity(h);
    for (let i = 0; i < n; i++) { const c = Store.child(h, i); if (Store.isTerm(c)) rec(c, d + 1); }
  };
  const n = Store.arity(fact);
  for (let i = 0; i < n; i++) { const c = Store.child(fact, i); if (Store.isTerm(c)) rec(c, 1); }
  return mx;
}

function buildTaint(compiledRules) {
  const taint = new Map(); // predName -> Set<pathKey>
  const getT = (p) => { let s = taint.get(p); if (!s) { s = new Set(); taint.set(p, s); } return s; };

  // Star threshold: exceed the deepest fixed nesting any pattern inspects, so
  // only unbounded recursion (arbitrarily long runs) is starred.
  let maxD = 1;
  for (const r of compiledRules) {
    for (const p of ((r.antecedent && r.antecedent.linear) || [])) { const d = maxNodeDepth(p); if (d > maxD) maxD = d; }
    for (const alt of (r.consequentAlts || [])) for (const p of ((alt.linear || []).concat(alt.persistent || []))) { const d = maxNodeDepth(p); if (d > maxD) maxD = d; }
  }
  const THR = maxD + 1;

  for (;;) {
    let changed = false;
    for (const r of compiledRules) {
      const exHashes = new Set();
      if (r.existentialSlots && r.existentialSlots.length) {
        const exSet = new Set(r.existentialSlots);
        for (const h in r.metavarSlots) if (exSet.has(r.metavarSlots[h])) exHashes.add(+h);
      }
      if (exHashes.size === 0 && !(r.consequentAlts && r.consequentAlts.length)) continue;

      const varRel = new Map(); // varHash -> Set<relPathKey>
      const addRel = (v, arr) => { let s = varRel.get(v); if (!s) { s = new Set(); varRel.set(v, s); } s.add(keyOfPath(canonPath(arr, THR))); };
      for (const v of exHashes) addRel(v, []); // ε — the slot IS a parameter

      const ante = r.antecedent || {};
      for (const pat of [...(ante.linear || []), ...(ante.persistent || [])]) {
        const pred = predName(pat); if (!pred) continue;
        const ts = taint.get(pred); if (!ts) continue;
        for (const { v, path } of leafVars(pat)) {
          for (const tauStr of ts) {
            const { exact, residuals } = tauResiduals(path, parsePath(tauStr));
            if (exact) addRel(v, []);
            for (const rd of residuals) addRel(v, rd);
          }
        }
      }

      const conseqFacts = [];
      for (const alt of (r.consequentAlts || [])) {
        for (const p of (alt.linear || [])) conseqFacts.push(p);
        for (const p of (alt.persistent || [])) conseqFacts.push(p);
      }
      for (const fact of conseqFacts) {
        const pred = predName(fact); if (!pred) continue;
        const dst = getT(pred);
        for (const { v, path } of leafVars(fact)) {
          const rels = varRel.get(v); if (!rels) continue;
          for (const relStr of rels) {
            const full = canonPath(path.concat(parsePath(relStr)), THR);
            const fk = keyOfPath(full);
            if (!dst.has(fk)) { dst.add(fk); changed = true; }
          }
        }
      }
    }
    if (!changed) break;
  }
  return taint;
}

/** §6.2 V1 — flag every linear pattern that decomposes a parameter. */
function checkStructuralMatch(compiledRules, taint, warnings) {
  const flagged = new Set();
  for (const r of compiledRules) {
    for (const pat of ((r.antecedent && r.antecedent.linear) || [])) {
      const pred = predName(pat); if (!pred) continue;
      const ts = taint.get(pred); if (!ts) continue;
      for (const tauStr of ts) {
        if (tauStr === '') continue;
        const tau = parsePath(tauStr);
        if (!structuralAtStar(pat, tau)) continue;
        const fk = r.name + '|' + pred + '|' + tauStr;
        if (flagged.has(fk)) continue;
        flagged.add(fk);
        warnings.push(
          `rule '${r.name}': matches structure against a parameter at ` +
          `${pred} arg-path [${tauStr}] (V1 — a parameter is opaque; §6.2). ` +
          `No committed-choice pattern may decompose a parameter.`,
        );
      }
    }
  }
}

// ── §6.3 — guard-coverage (V2) ──────────────────────────────────────────

/** Antecedent variables of a rule that bind EXACTLY a parameter leaf. */
function paramVarsOf(rule, taint) {
  const params = new Set();
  const ante = rule.antecedent || {};
  for (const pat of [...(ante.linear || []), ...(ante.persistent || [])]) {
    const pred = predName(pat); if (!pred) continue;
    const ts = taint.get(pred); if (!ts) continue;
    for (const { v, path } of leafVars(pat)) {
      for (const tauStr of ts) {
        if (tauResiduals(path, parsePath(tauStr)).exact) { params.add(v); break; }
      }
    }
  }
  return params;
}

/**
 * §6.3 V2 — when a parameter is the scrutinee of a ⊕ (its value decides which
 * alternative via eq/neq guards), the alternatives must COVER the value space
 * and be mutually EXCLUSIVE. Decided by region enumeration over the declared
 * constraint fragment (the EqNeqSolver): the regions are V = k for each guard
 * constant k, plus the generic V ∉ {k}. In every region exactly one alternative
 * must be feasible — zero ⇒ a value with no branch (coverage fails), more than
 * one ⇒ overlap (exclusion fails). A guard comparing the scrutinee to a
 * non-constant (outside the decidable fragment) is not certifiable here —
 * flagged, the eq/neq boundary (task #84).
 */
function checkGuardCoverage(compiledRules, taint, cc, warnings) {
  const dom = cc && cc.domain;
  const cp = dom && dom.constraintPreds;
  if (!cp || !cp.eq || !cp.neq) return; // no decidable fragment declared
  const eqName = cp.eq;
  const neqName = cp.neq;
  const evalNumeric = dom.evalNumeric || null;
  if (!evalNumeric) return; // cannot evaluate guard constants → cannot decide

  for (const rule of compiledRules) {
    const alts = rule.consequentAlts;
    if (!alts || alts.length < 2) continue;
    const params = paramVarsOf(rule, taint);
    if (params.size === 0) continue;

    const guardAtoms = alts.map((a) =>
      (a.persistent || []).filter((h) => { const pn = predName(h); return pn === eqName || pn === neqName; }));

    for (const V of params) {
      // Per-alternative V-guards, reduced to { isEq, c } with c the constant's
      // numeric value; a guard comparing V to a non-constant is undecidable.
      let mentioned = false;
      let undecidable = false;
      const perAlt = guardAtoms.map((atoms) => {
        const gs = [];
        for (const h of atoms) {
          const a0 = Store.child(h, 0);
          const a1 = Store.child(h, 1);
          const other = a0 === V ? a1 : (a1 === V ? a0 : null);
          if (other === null) continue;
          mentioned = true;
          const c = evalNumeric(other);
          if (c === null) { undecidable = true; continue; }
          gs.push({ isEq: predName(h) === eqName, c });
        }
        return gs;
      });
      if (!mentioned) continue; // V carried opaquely through the ⊕ — well-moded
      if (undecidable) {
        warnings.push(
          `rule '${rule.name}': ⊕-guard on parameter '${varLabel(V)}' compares it to ` +
          `a non-constant — coverage is undecidable in the {${eqName},${neqName}} ` +
          `fragment (V2; §6.3). Certifiable via task #84.`);
        continue;
      }

      // Regions: each distinct guard constant, plus the generic value distinct
      // from all of them (represented by null). A guard holds under a region by
      // ground evaluation — this is exact for eq/neq over a single scrutinee.
      const Kvals = [];
      for (const gs of perAlt) for (const g of gs) if (!Kvals.some((k) => k === g.c)) Kvals.push(g.c);
      const holds = (g, rv) => (rv === null
        ? (g.isEq ? false : true)          // generic (≠ every constant)
        : (g.isEq ? rv === g.c : rv !== g.c));
      const regions = Kvals.concat([null]);
      for (const rv of regions) {
        let feasible = 0;
        for (const gs of perAlt) if (gs.every((g) => holds(g, rv))) feasible++;
        if (feasible === 0) {
          warnings.push(
            `rule '${rule.name}': ⊕-guards on parameter '${varLabel(V)}' do not COVER ` +
            `its value space — some value takes no branch (V2 coverage; §6.3).`);
          break;
        }
        if (feasible > 1) {
          warnings.push(
            `rule '${rule.name}': ⊕-guards on parameter '${varLabel(V)}' are not mutually ` +
            `EXCLUSIVE — a value takes more than one branch (V2 exclusion; §6.3).`);
          break;
        }
      }
    }
  }
}

/** Human-readable name of a metavar/freevar hash (its interned label). */
function varLabel(v) {
  const c = Store.child(v, 0);
  return typeof c === 'string' ? c : String(v);
}

/**
 * The load-time well-modedness check (THY_0039 §6). Returns
 * { functionalPreds, warnings, errors }; warn-first ⇒ errors stays empty
 * unless cc.wellModed === 'strict' (applied by the caller).
 */
function checkWellModed({ compiledRules, clauses, cc }) {
  const rules = compiledRules || [];
  const functionalPreds = certifyFunctional(clauses || new Map(), cc);
  const warnings = [];
  const errors = [];
  checkForcingGoals(rules, functionalPreds, warnings);
  const taint = buildTaint(rules);
  checkStructuralMatch(rules, taint, warnings);
  checkGuardCoverage(rules, taint, cc, warnings);
  return { functionalPreds, warnings, errors, taint };
}

export {
  checkWellModed,
  certifyFunctional,
  buildTaint,
  nonUnifiable,
  isVar,
  predTagOf,
  predName,
  collectVars,
  leafVars,
  structuralAtStar,
  canonPath,
  argIndexContaining,
};
export default { checkWellModed };
