/**
 * @fire step checker (TODO_0294 B1) — kernel-side verification of ONE
 * timed firing against the PROGRAM'S DECLARED RULE DATA.
 *
 * Non-circularity: the check never runs settle. A fire node carries the
 * event-record witness (`state.fire`); the checker re-derives everything
 * from the program's declarative rule record + the calculus theory:
 *
 *   - consumed/read multisets = the rule's antecedent patterns under the
 *     recorded theta (bag equality, ground after substitution)
 *   - activation a: every input/read stamp and after-bound is ⊑ a (theory
 *     `le`), and a is ATTAINED (member of that stamp set; = unit if empty)
 *     — the forced-join discipline of THY_0018 §5
 *   - before-windows: a strictly below each bound (theory `lt`)
 *   - done stamp u: `sub(u, d, a)` — the same partial residual ⊖ that
 *     monad_l uses; no signed subtraction exists, so an illegal step is
 *     underivable, not merely rejected (THY_0022)
 *   - produced = consequent patterns stamped at u (bag equality)
 *   - persistent goals: membership in the sequent's cartesian zone, else
 *     theory derivation
 *
 * The tree-level check additionally threads the kernel's lazy delta
 * discipline: premise linear = produced ⊎ (pool − consumed)-submultiset,
 * reads must be present and survive, persistent conclusions must appear
 * in the premise's cartesian zone.
 *
 * Sequent form is STRICT at-form: context entries and event facts are
 * at(inner, stamp) terms (the elaborator canonicalizes A@0 ≡ A at the
 * boundary before building sequents — B2).
 *
 * Config comes from `calculus.fire` (declared at the calculus assembly
 * point, never defaulted here): { stampTag, le, lt, sub, unit() }.
 */

import Store from '../../kernel/store.js';
import Seq from '../../kernel/sequent.js';
import Context from '../context.js';
import { predHead } from '../../kernel/ast.js';
import { ratParts } from '../../engine/theories/ratlit-theory.js';
import { checkGoalCert } from '../sld-check.js';

const UNBOUND_TAGS = new Set(['metavar', 'freevar']);

/** VALUE equality on stamps (le both ways) — hashes may differ across
 *  canon boundaries (parsed binlit vs engine-reified ratlit). One
 *  definition for both check levels (TODO_0296 P3 dedupe); the le-prover
 *  is the caller's CLAUSE-ONLY discipline. */
const mkValEq = (proveLe) => (x, y) => x === y || (proveLe(x, y) && proveLe(y, x));

/** Decode a numeral count term (binlit/ratlit integer ≥ 0) → BigInt|null. */
function countOf(h) {
  if (h === undefined || h === null) return null;
  const p = ratParts(h);
  if (!p || p[1] !== 1n || p[0] < 0n) return null;
  return p[0];
}

/**
 * Derive a rule record from a POSSESSED loli token's own structure
 * (Phase 6c: ground lolis in the state are rules; the token is consumed
 * by its firing, so its structure IS the justification — no program
 * lookup). Returns null when `inner` is not a ground loli. `roles` maps
 * connective roles to tags (sequent-calculus deriveRoles record); the
 * fallbacks are the pre-registered kernel tags.
 */
function deriveLoliRecord(inner, roles = {}) {
  const implTag = roles.implication || 'loli';
  if (Store.tag(inner) !== implTag || hasUnbound(inner)) return null;
  const compTag = roles.computation?.tag || 'monad';
  const prodTag = roles.product || 'tensor';
  const unitTag = roles.unit || 'one';
  const expTag = roles.exponential || 'bang';
  const lhs = Store.child(inner, 0), rhs = Store.child(inner, 1);
  let delay = null, body = rhs;
  if (Store.tag(rhs) === compTag) { delay = Store.child(rhs, 0); body = Store.child(rhs, 1); }
  const flat = (h, out) => {
    if (Store.tag(h) === prodTag) { flat(Store.child(h, 0), out); flat(Store.child(h, 1), out); return out; }
    if (Store.tag(h) === unitTag) return out;
    out.push(h);
    return out;
  };
  const consume = [], goals = [];
  for (const q of flat(lhs, [])) {
    if (Store.tag(q) === expTag) {
      const k = countOf(Store.child(q, 0));
      if (k === null) goals.push(Store.child(q, 1));            // ω: persistent goal
      else for (let i = 0n; i < k; i++) consume.push(Store.child(q, 1));
    } else consume.push(q);
  }
  consume.push(inner);           // the loli token itself is consumed (one-shot)
  const produce = [], producePers = [];
  for (const q of flat(body, [])) {
    if (Store.tag(q) === expTag && countOf(Store.child(q, 0)) === null) {
      producePers.push(Store.child(q, 1));                      // ω: persistent conclusion
    } else produce.push(q);       // counted parcels expand in the produce check
  }
  return { slots: [], consume, read: [], produce, producePers, goals,
    delay, after: [], before: [], wholeBind: [], derivedLoli: true };
}

/** Substitute a binding map (metavar hash → ground hash) through a term. */
function subst(h, bind) {
  const b = bind.get(h);
  if (b !== undefined) return b;
  if (!Store.isTerm(h)) return h;
  const n = Store.arity(h);
  if (n === 0) return h;
  const ch = new Array(n);
  let changed = false;
  for (let i = 0; i < n; i++) {
    const c = Store.child(h, i);
    const s = Store.isTermChild(c) ? subst(c, bind) : c;
    ch[i] = s;
    if (s !== c) changed = true;
  }
  return changed ? Store.put(Store.tag(h), ch) : h;
}

function hasUnbound(h) {
  if (!Store.isTerm(h)) return false;
  if (UNBOUND_TAGS.has(Store.tag(h))) return true;
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && hasUnbound(c)) return true;
  }
  return false;
}

const bagAdd = (m, h, c = 1) => m.set(h, (m.get(h) || 0) + c);

function bagEq(a, b) {
  if (a.size !== b.size) return false;
  for (const [h, c] of a) if (b.get(h) !== c) return false;
  return true;
}

const bagShow = (m) =>
  [...m].map(([h, c]) => `${Store.pretty ? Store.pretty(h) : h}×${c}`).join(', ') || '∅';

/**
 * Check the DATA of one fire step (no resource threading).
 *
 * @param {Object} seq - the node's conclusion sequent (cartesian zone is
 *   consulted for persistent goals)
 * @param {Object} fire - the witness record: { rule, activation, done,
 *   theta: [hash], consumed: {atHash:count}, reserved: {atHash:count},
 *   produced: {atHash:count}, producedPers: [hash] }
 * @param {Object} deps - { program, theory, config }
 * @returns {{ error?: string, consumed?, reserved?, produced?, producedPers? }}
 *   the ground bags (Map hash→count) on success
 */
function checkFireData(seq, fire, { program, theory, config, roles = {} }) {
  if (!fire) return { error: 'fire step carries no state.fire record' };
  if (!program || !program.rules) return { error: 'fire step requires a program (opts.program)' };
  if (!theory || typeof theory.prove !== 'function') {
    return { error: 'fire step requires a calculus theory' };
  }
  let pr = program.rules[fire.rule];
  if (!pr) {
    // possessed rule (Phase 6c): derive the record from a consumed ground
    // loli token — the token's structure is the justification
    for (const k in fire.consumed || {}) {
      const h = Number(k);
      const inner = Store.tag(h) === config.stampTag ? Store.child(h, 0) : h;
      const rec = deriveLoliRecord(inner, roles);
      if (rec) { pr = rec; break; }
    }
    if (!pr) return { error: `unknown program rule '${fire.rule}'` };
  }
  if (pr.unsupported) return { error: `rule '${fire.rule}': ${pr.unsupported}` };

  // theta → binding map over the rule's declared slot order
  const slots = pr.slots || [];
  const theta = fire.theta || [];
  if (theta.length !== slots.length) {
    return { error: `theta arity mismatch: rule '${fire.rule}' has ${slots.length} slot(s), witness has ${theta.length}` };
  }
  const bind = new Map();
  for (let i = 0; i < slots.length; i++) {
    // undefined slots (metavars only in grade0/unused positions) stay
    // unbound — a CHECKED pattern referencing one errors at grounding
    if (theta[i] !== undefined && theta[i] !== null) bind.set(slots[i], theta[i]);
  }
  const ground = (h) => {
    const g = subst(h, bind);
    if (hasUnbound(g)) return null;
    return g;
  };
  const groundAll = (hs, what) => {
    const out = [];
    for (const h of hs || []) {
      const g = ground(h);
      if (g === null) return { error: `unbound slot in ${what} pattern of '${fire.rule}'` };
      out.push(g);
    }
    return { out };
  };

  // CLAUSE-ONLY proving (useFFI: false): the checker takes the SEMANTICS
  // path so the numeric FFI (rat-ffi/lib-rat) stays out of the trust base
  // — TCB = kernel + eq-theory canon + the prelude clauses (TODO_0296 P1).
  const proveGoal = (g) => theory.prove(g, { useFFI: false });
  const prove = (tag, args) => proveGoal(Store.put(tag, args)) !== null;
  const ST = config.stampTag;
  const unit = config.unit();
  const valEq = mkValEq((x, y) => prove(config.le, [x, y]));

  // decompose a recorded fact map {hash: count} → entries with the A@0 ≡ A
  // boundary canon: a BARE (un-stamped) fact reads as stamped at the unit
  const splitAt = (obj) => {
    const entries = [];   // { rec, inner, stamp, count }
    for (const k in obj || {}) {
      const h = Number(k);
      if (Store.tag(h) === ST) {
        entries.push({ rec: h, inner: Store.child(h, 0), stamp: Store.child(h, 1), count: obj[k] });
      } else {
        entries.push({ rec: h, inner: h, stamp: unit, count: obj[k] });
      }
    }
    return entries;
  };

  const consumed = splitAt(fire.consumed);
  const reserved = splitAt(fire.reserved);

  // fact correspondence: wants are {inner, stamp|null} records — stamped
  // wants must find a VALUE-equal (inner, stamp) entry; null-stamp wants
  // then bag-match the remaining inners. Shared by consume/read/produce.
  const matchFacts = (wants, entries, what) => {
    const remaining = entries.map(e => ({ ...e }));
    const wantPlain = new Map();
    for (const w of wants) {
      if (w.stamp === null) { bagAdd(wantPlain, w.inner); continue; }
      const e = remaining.find(x => x.count > 0 && x.inner === w.inner && valEq(x.stamp, w.stamp));
      if (!e) return { error: `${what}: no recorded fact matches stamped pattern` };
      e.count--;
    }
    const gotPlain = new Map();
    for (const e of remaining) if (e.count > 0) bagAdd(gotPlain, e.inner, e.count);
    if (!bagEq(wantPlain, gotPlain)) {
      return { error: `${what} multiset ≠ rule patterns: want {${bagShow(wantPlain)}}, got {${bagShow(gotPlain)}}` };
    }
    return {};
  };
  // a ground pattern → want record (at-tagged keeps its stamp)
  const wantOf = (g, stamp = null) => (Store.tag(g) === ST
    ? { inner: Store.child(g, 0), stamp: Store.child(g, 1) } : { inner: g, stamp });

  // whole-bind (!_W) premises: the witness count for each pattern must
  // equal the bound total theta[slot]; the tree step adds the global
  // none-left condition (D4: !_W A takes ALL cohorts, !_W A@T one cohort)
  const wholeBind = [];
  const consumeGround = groundAll(pr.consume, 'consume');
  if (consumeGround.error) return consumeGround;
  const consumeWant = consumeGround.out.map(g => wantOf(g));
  for (const w of pr.wholeBind || []) {
    const gb = ground(w.body);
    if (gb === null) return { error: `unbound slot in whole-bind pattern of '${fire.rule}'` };
    const k = countOf(theta[w.slot]);
    if (k === null) return { error: 'whole-bind count witness is not a numeral' };
    for (let i = 0n; i < k; i++) consumeWant.push(wantOf(gb));
    wholeBind.push({ body: gb });
  }

  const mc = matchFacts(consumeWant, consumed, 'consumed');
  if (mc.error) return mc;
  const readGround = groundAll(pr.read, 'read');
  if (readGround.error) return readGround;
  const mr = matchFacts(readGround.out.map(g => wantOf(g)), reserved, 'read');
  if (mr.error) return mr;

  // activation: every input stamp and after-bound ⊑ a, and a is attained
  const a = fire.activation;
  const ga = groundAll(pr.after, 'after');
  if (ga.error) return ga;
  const candidates = new Set([
    ...consumed.map(e => e.stamp), ...reserved.map(e => e.stamp), ...ga.out,
  ]);
  for (const s of candidates) {
    if (s === a) continue;
    if (!prove(config.le, [s, a])) {
      return { error: 'activation below an input stamp or after-bound' };
    }
  }
  if (candidates.size > 0) {
    if (![...candidates].some(sc => valEq(sc, a))) {
      return { error: 'activation is not attained (must be the join of its inputs)' };
    }
  } else if (!valEq(a, unit)) {
    return { error: 'inputless firing must activate at the unit stamp' };
  }

  // before-windows: a strictly below each bound
  const gb = groundAll(pr.before, 'before');
  if (gb.error) return gb;
  for (const b of gb.out) {
    if (!prove(config.lt, [a, b])) return { error: 'activation violates a before-window' };
  }

  // done stamp: u = a ⊕ d via the partial residual (u ⊖ d = a). The
  // theory's residual arg is OUTPUT-mode (it computes, never checks a
  // ground value), so derive with a fresh metavar and compare the
  // binding by value.
  const u = fire.done;
  if (pr.delay == null) {
    if (!valEq(u, a)) return { error: 'delayless firing must stamp outputs at its activation' };
  } else {
    const d = ground(pr.delay);
    if (d === null) return { error: `unbound slot in delay of '${fire.rule}'` };
    const H = Store.put('metavar', ['_fire_residual']);
    const sub = proveGoal(Store.put(config.sub, [u, d, H]));
    let residual = null;
    if (sub !== null) for (const [k, v] of sub) if (k === H) residual = v;
    if (residual === null || !valEq(residual, a)) {
      return { error: 'done stamp ≠ activation ⊕ delay' };
    }
  }

  // additive alternatives (woplus): the witness picks the branch; the
  // CHOICE is free — derivability is per-branch
  let produce = pr.produce, producePers = pr.producePers;
  if (fire.alt != null) {
    if (!pr.alts || !pr.alts[fire.alt]) {
      return { error: `witness names alternative ${fire.alt} but rule '${fire.rule}' has none` };
    }
    produce = pr.alts[fire.alt].produce;
    producePers = pr.alts[fire.alt].producePers;
  }

  // produced: consequent patterns stamped at u (recorded facts canon via
  // splitAt; want side uses the same (inner, stamp) reading — an
  // at-tagged consequent pattern keeps its own stamp)
  const gp = groundAll(produce, 'produce');
  if (gp.error) return gp;
  const expTag = roles.exponential || 'bang';
  const wantProduced = [];
  for (const g of gp.out) {
    if (Store.tag(g) === expTag) {
      // counted parcel !_k A in a consequent: k copies of the body
      const k = countOf(Store.child(g, 0));
      if (k === null) return { error: 'counted consequent with a non-numeral count' };
      for (let i = 0n; i < k; i++) wantProduced.push(wantOf(Store.child(g, 1), u));
      continue;
    }
    wantProduced.push(wantOf(g, u));
  }
  const gotProduced = splitAt(fire.produced);
  const mp = matchFacts(wantProduced, gotProduced, 'produced');
  if (mp.error) return mp;

  // persistent conclusions
  const gpp = groundAll(producePers, 'producePers');
  if (gpp.error) return gpp;
  const wantPers = new Map();
  for (const g of gpp.out) bagAdd(wantPers, g);
  const gotPers = new Map();
  for (const h of fire.producedPers || []) bagAdd(gotPers, h);
  if (!bagEq(wantPers, gotPers)) {
    return { error: 'persistent conclusions ≠ rule persistent consequent' };
  }

  // persistent goals: state membership (cartesian zone), a CHECKED SLD
  // certificate over the program's declared clauses (TODO_0295 — the
  // witness carries it; verification is matching, never search), or the
  // definitional numeric theory. No trusted clause-prover fallback.
  const cart = new Set(Seq.getContext(seq, 'cartesian'));
  const gg = groundAll(pr.goals, 'goal');
  if (gg.error) return gg;
  for (const g of gg.out) {
    if (cart.has(g)) continue;
    const cert = fire.goalCerts && fire.goalCerts[g];
    if (cert) {
      const r = checkGoalCert(cert, g, program.clauses, program.definitions);
      if (r.error) return { error: `persistent goal certificate: ${r.error}` };
      continue;
    }
    // definitional-theory fallback, SCOPE-GUARDED: only goals the theory
    // can speak about (the numeric prelude) may pass uncertified — a goal
    // outside that scope must carry an SLD certificate (TODO_0296 P1)
    if ((typeof theory.has !== 'function' || theory.has(predHead(g))) &&
        proveGoal(g) !== null) continue;
    return { error: 'unprovable persistent goal' };
  }

  const toBag = (entries) => {
    const m = new Map();
    for (const e of entries) bagAdd(m, e.rec, e.count);
    return m;
  };
  return {
    consumed: toBag(consumed),
    reserved: toBag(reserved),
    produced: toBag(gotProduced),
    producedPers: gpp.out,
    wholeBind,
  };
}

/**
 * Full tree-level check of one fire node: data check + linear resource
 * threading in the kernel's lazy delta discipline.
 *
 * @returns {{ error?: string, leftover?: Context }}
 */
function checkFireTreeStep(node, childLeftovers, deps) {
  const seq = node.conclusion;
  const data = checkFireData(seq, node.state && node.state.fire, deps);
  if (data.error) return data;

  if (node.premises.length !== 1) {
    return { error: `fire expects exactly 1 premise, got ${node.premises.length}` };
  }
  const child = node.premises[0];
  if (child.conclusion.succedent !== seq.succedent) {
    return { error: 'fire must not change the succedent' };
  }

  let pool = Context.fromArray(Seq.getContext(seq, 'linear'));

  // consumed: removed from the pool
  for (const [h, c] of data.consumed) {
    for (let i = 0; i < c; i++) {
      if (!Context.has(pool, h)) return { error: 'consumed token not in the available context' };
      pool = Context.remove(pool, h);
    }
  }
  // reads: present (post-consumption) and NOT removed
  let probe = pool;
  for (const [h, c] of data.reserved) {
    for (let i = 0; i < c; i++) {
      if (!Context.has(probe, h)) return { error: 'read token not in the available context' };
      probe = Context.remove(probe, h);
    }
  }

  // premise linear = produced (intro) ⊎ a sub-multiset of the pool
  const intro = [];
  for (const [h, c] of data.produced) for (let i = 0; i < c; i++) intro.push(h);
  let di = Context.fromArray(Seq.getContext(child.conclusion, 'linear'));
  for (const h of intro) {
    if (!Context.has(di, h)) return { error: 'premise missing a produced token' };
    di = Context.remove(di, h);
  }
  if (!Context.contains(pool, di)) {
    return { error: 'premise carries formulas not in the available context' };
  }

  // whole-bind global condition: after the take, NO matching token
  // remains — !_W A across all cohorts (bare body), !_W A@T one cohort
  // (at-tagged body; stamps compared by value)
  if (data.wholeBind && data.wholeBind.length) {
    const ST = deps.config.stampTag;
    const unit = deps.config.unit();
    const valEq = mkValEq((x, y) =>
      deps.theory.prove(Store.put(deps.config.le, [x, y]), { useFFI: false }) !== null);
    for (const w of data.wholeBind) {
      const stamped = Store.tag(w.body) === ST;
      const wi = stamped ? Store.child(w.body, 0) : w.body;
      const ws = stamped ? Store.child(w.body, 1) : null;
      for (const h of Context.toArray(pool)) {
        const hi = Store.tag(h) === ST ? Store.child(h, 0) : h;
        if (hi !== wi) continue;
        if (stamped) {
          const hs = Store.tag(h) === ST ? Store.child(h, 1) : unit;
          if (!valEq(hs, ws)) continue;
        }
        return { error: 'whole-bind did not take the whole cohort (matching tokens remain)' };
      }
    }
  }

  // persistent conclusions must appear in the premise's cartesian zone
  const childCart = new Set(Seq.getContext(child.conclusion, 'cartesian'));
  for (const h of data.producedPers) {
    if (!childCart.has(h)) return { error: 'premise missing a persistent conclusion' };
  }

  const leftover = Context.merge(Context.subtract(pool, di), childLeftovers[0]);
  return { leftover };
}

/**
 * The checker pair a timed calculus binds via `calculus.stepCheckers`
 * (kit.js makeSequentLoader) — the kernel dispatches on the binding and
 * knows nothing about fire steps (P1 slot routing).
 */
const fireChecker = Object.freeze({
  step(conclusion, state, { calculus, program }) {
    if (!calculus.fire) return { error: 'calculus declares no fire config' };
    return checkFireData(conclusion, state && state.fire,
      { program, theory: calculus.theory, config: calculus.fire, roles: calculus.roles || {} });
  },
  tree(node, childLeftovers, { calculus, program }) {
    if (!calculus.fire) return { error: 'calculus declares no fire config' };
    return checkFireTreeStep(node, childLeftovers,
      { program, theory: calculus.theory, config: calculus.fire, roles: calculus.roles || {} });
  },
});

export { checkFireData, checkFireTreeStep, subst, fireChecker, deriveLoliRecord, countOf };
export default { checkFireData, checkFireTreeStep, subst, fireChecker, deriveLoliRecord, countOf };
