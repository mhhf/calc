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

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';
import Context from './context.js';

const UNBOUND_TAGS = new Set(['metavar', 'freevar']);

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
function checkFireData(seq, fire, { program, theory, config }) {
  if (!fire) return { error: 'fire step carries no state.fire record' };
  if (!program || !program.rules) return { error: 'fire step requires a program (opts.program)' };
  const pr = program.rules[fire.rule];
  if (!pr) return { error: `unknown program rule '${fire.rule}'` };
  if (!theory || typeof theory.prove !== 'function') {
    return { error: 'fire step requires a calculus theory' };
  }

  // theta → binding map over the rule's declared slot order
  const slots = pr.slots || [];
  const theta = fire.theta || [];
  if (theta.length !== slots.length) {
    return { error: `theta arity mismatch: rule '${fire.rule}' has ${slots.length} slot(s), witness has ${theta.length}` };
  }
  const bind = new Map();
  for (let i = 0; i < slots.length; i++) bind.set(slots[i], theta[i]);
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

  const prove = (tag, args) => theory.prove(Store.put(tag, args)) !== null;
  const ST = config.stampTag;
  const unit = config.unit();

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

  // antecedent correspondence, stamped patterns first: a ground at-tagged
  // pattern (A@Q antecedent) must match a recorded fact at exactly its
  // (inner, stamp); unstamped patterns then bag-match the remaining inners
  const matchFacts = (patterns, entries, what) => {
    const g = groundAll(patterns, what);
    if (g.error) return g;
    const remaining = entries.map(e => ({ ...e }));
    const wantPlain = new Map();
    for (const p of g.out) {
      if (Store.tag(p) !== ST) { bagAdd(wantPlain, p); continue; }
      const pi = Store.child(p, 0), ps = Store.child(p, 1);
      const e = remaining.find(x => x.count > 0 && x.inner === pi &&
        (x.stamp === ps || (prove(config.le, [x.stamp, ps]) && prove(config.le, [ps, x.stamp]))));
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

  const mc = matchFacts(pr.consume, consumed, 'consumed');
  if (mc.error) return mc;
  const mr = matchFacts(pr.read, reserved, 'read');
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
    // attained = VALUE-equal to some input stamp (le both ways), not
    // hash-equal — program-pattern bounds may canon differently
    let attained = false;
    for (const s of candidates) {
      if (s === a || (prove(config.le, [a, s]) && prove(config.le, [s, a]))) { attained = true; break; }
    }
    if (!attained) return { error: 'activation is not attained (must be the join of its inputs)' };
  } else {
    if (a !== unit && !(prove(config.le, [a, unit]) && prove(config.le, [unit, a]))) {
      return { error: 'inputless firing must activate at the unit stamp' };
    }
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
    if (u !== a && !(prove(config.le, [u, a]) && prove(config.le, [a, u]))) {
      return { error: 'delayless firing must stamp outputs at its activation' };
    }
  } else {
    const d = ground(pr.delay);
    if (d === null) return { error: `unbound slot in delay of '${fire.rule}'` };
    const H = Store.put('metavar', ['_fire_residual']);
    const sub = theory.prove(Store.put(config.sub, [u, d, H]));
    let residual = null;
    if (sub !== null) for (const [k, v] of sub) if (k === H) residual = v;
    if (residual === null ||
        (residual !== a && !(prove(config.le, [residual, a]) && prove(config.le, [a, residual])))) {
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
  const wantProduced = [];
  for (const g of gp.out) {
    if (Store.tag(g) === ST) wantProduced.push({ inner: Store.child(g, 0), stamp: Store.child(g, 1) });
    else wantProduced.push({ inner: g, stamp: u });
  }
  const gotProduced = splitAt(fire.produced);
  const remaining = gotProduced.map(e => ({ ...e }));
  for (const w of wantProduced) {
    const e = remaining.find(x => x.count > 0 && x.inner === w.inner &&
      (x.stamp === w.stamp || (prove(config.le, [x.stamp, w.stamp]) && prove(config.le, [w.stamp, x.stamp]))));
    if (!e) return { error: 'produced multiset ≠ rule consequent at the done stamp' };
    e.count--;
  }
  if (remaining.some(e => e.count > 0)) {
    return { error: 'produced multiset ≠ rule consequent at the done stamp' };
  }

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

  // persistent goals: state membership (cartesian zone), theory
  // derivation, or the program's clause prover (backward SLD over the
  // program's declared clauses — a derivation, never settle)
  const cart = new Set(Seq.getContext(seq, 'cartesian'));
  const gg = groundAll(pr.goals, 'goal');
  if (gg.error) return gg;
  for (const g of gg.out) {
    if (cart.has(g)) continue;
    if (theory.prove(g) !== null) continue;
    if (program.prove && program.prove(g)) continue;
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

  // persistent conclusions must appear in the premise's cartesian zone
  const childCart = new Set(Seq.getContext(child.conclusion, 'cartesian'));
  for (const h of data.producedPers) {
    if (!childCart.has(h)) return { error: 'premise missing a persistent conclusion' };
  }

  const leftover = Context.merge(Context.subtract(pool, di), childLeftovers[0]);
  return { leftover };
}

export { checkFireData, checkFireTreeStep, subst };
export default { checkFireData, checkFireTreeStep, subst };
