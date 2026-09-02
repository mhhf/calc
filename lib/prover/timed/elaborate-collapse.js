/**
 * Collapse-run certification (TODO_0298 item 2) — a decimation run as a
 * kernel-checked derivation whose ENDSEQUENT carries the trace.
 *
 * THY_0026 §5 (collapse = principal cut) + THY_0027 §1 (weight is a
 * function of the endsequent) made executable: a `calc.collapse` sample
 * run elaborates into ONE proof tree
 *
 *   Γ₀ ; Δ₀, ⟨Θ⟩ ⊢ {⊗ residual}@h
 *
 * where ⟨Θ⟩ is the multiset of ground `drawn c s` tokens, one per drawn
 * head — so Π ρ(c) over the hypotheses IS the run's prior mass, readable
 * off the endsequent alone. The elaboration is POST-HOC GROUNDING: the
 * final witness substitution σ is applied through the whole recorded
 * trace, which is sound because bias derivation is monotone (facts
 * derivable between an opening and its draw remain derivable after the
 * draw) and evars are opaque constants to matching — a σ-instance of a
 * legal @fire is a legal @fire.
 *
 * Node inventory (all fully re-derived by the kernel — no trust):
 *   @fire  settle segments, exactly as certifyRun (elaborate-trace.js)
 *   @draw  each wave's open+draw pair, folded to ONE node at the OPENING
 *          position with the σ-ground witness. A structured (rung-2)
 *          witness is certified as the COMPOSITE of its per-head draws:
 *          the checker walks the witness tree and demands one token per
 *          drawn head (iterated ∃_ρ — THY_0027 §8); an evar subterm is a
 *          wave dropped un-observed (no choice, no token, no factor).
 *   @draw (open record)  a suspension opened but never drawn — a wave
 *          whose evar stopped occurring, or a plain-∃ SKOLEM (M1). The
 *          step is ∃-L (superpose_l / exists_l) with the evar as
 *          eigenvariable; freshness is checked syntactically, so even
 *          these nodes verify with no unverified:['binding'] flag.
 *
 * Skolems surviving into the residual are ∃-CLOSED in the goal — the
 * endsequent asserts {∃T. ⊗residual[T]}@h (a skolem is an opaque fresh
 * constant, so only its existential is claimed), keeping the opening's
 * eigenvariable fresh w.r.t. the succedent. The closing then peels the
 * closure with exists_r steps witnessed by the evars; metavar-witness
 * premises verify by instance, so skolem runs also certify with no
 * unverified flags (the ['binding'] allowance below is a safety valve
 * for kernels that degrade metavar steps).
 *
 * The certified weight is the PRIOR product Π ρ(c). Posterior/bias
 * factors are conditioning — their derivations are part of the @fire
 * segments (bias facts are ordinary derived facts), not of the
 * endsequent weight (THY_0027 §1: the token discipline counts draws,
 * the bias discipline is program data). Likewise woplus branch weights
 * ride the @fire records (the alt field), not ⟨Θ⟩ — so Π ρ over the
 * endsequent equals run.mass exactly on bias- AND woplus-free programs.
 */

import Store from '../../kernel/store.js';
import Seq from '../../kernel/sequent.js';
import { debruijnSubst } from '../../kernel/substitute.js';
import { substEvarInTerm, splitBody, DECIMATE_PREDS } from '../../engine/decimate.js';
import { checkDrawData, verifyMasses } from '../draw-check.js';
import {
  programFromCalc, elabContext, healToPool, applyEvents,
  foldChain, bagList, decompose, stampTools,
} from './elaborate-trace.js';
import { ProofTree } from '../pt.js';

const atom = (n) => Store.put('atom', [n]);

/**
 * Final witness substitution σ from the trace's draw entries. Built in
 * reverse run order so arg-wave witnesses (drawn later) are already
 * ground when substituted into their parent's witness — after one pass
 * every mapped value contains only NEVER-drawn evars (dropped waves,
 * skolems), which stay by design.
 */
function buildSigma(trace) {
  const sigma = new Map();
  const draws = trace.filter((t) => t.draw).map((t) => t.draw);
  for (let i = draws.length - 1; i >= 0; i--) {
    let w = draws[i].witness;
    for (const [e, v] of sigma) w = substEvarInTerm(w, e, v);
    sigma.set(draws[i].evar, w);
  }
  return sigma;
}

/** Apply σ to one term. */
function ground(sigma, h) {
  let out = h;
  for (const [e, v] of sigma) out = substEvarInTerm(out, e, v);
  return out;
}

/** Apply σ to a { hash: count } record, merging count collisions. */
function groundCounts(sigma, rec) {
  if (!rec) return rec;
  const out = {};
  for (const k in rec) {
    const h = ground(sigma, Number(k));
    out[h] = (out[h] || 0) + rec[k];
  }
  return out;
}

/** Apply σ to a settle event record. */
function groundEvent(sigma, ev) {
  return {
    ...ev,
    consumed: groundCounts(sigma, ev.consumed),
    produced: groundCounts(sigma, ev.produced),
    reserved: groundCounts(sigma, ev.reserved),
    theta: (ev.theta || []).map((t) => (t == null ? t : ground(sigma, t))),
  };
}

/** Abstract evar e out of h as a de Bruijn variable (the inverse of
 *  debruijnSubst at the matching depth) — the ∃-closure constructor. */
function abstractEvar(h, e, depth = 0n) {
  if (h === e) return Store.put('bound', [depth]);
  const a = Store.arity(h);
  if (a === 0) return h;
  const t = Store.tag(h);
  const inner = (t === 'exists' || t === 'forall') ? depth + 1n : depth;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = abstractEvar(c, e, inner);
      if (r !== c) changed = true;
      nc.push(r);
    } else nc.push(c);
  }
  return changed ? Store.put(t, nc) : h;
}

/** Collect the evars occurring in a term, in first-occurrence order. */
function collectEvars(h, out = []) {
  if (Store.tag(h) === 'evar') {
    if (!out.includes(h)) out.push(h);
    return out;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) collectEvars(c, out);
  }
  return out;
}

/**
 * Close a collapse chain: monad_r, then exists_r peels for the
 * surviving-skolem ∃-closure (each witnessed by its evar — the standard
 * metavar-witness step, so these carry the kernel's ['binding'] flag),
 * then the exact-context decomposition of the ground(ed) residual.
 */
function closeCollapse(ctx, calculus, skolems) {
  const { ST, prove, config, stampEq } = ctx.tools;
  const residualSeq = Seq.seq({ [ctx.CZ]: bagList(ctx.pool), [ctx.SZ]: ctx.cart }, ctx.succ);
  if (Store.tag(ctx.succ) !== (calculus.roles?.computation?.tag || 'monad')) {
    return { unsupported: 'succedent is not monadic' };
  }
  let goal = Store.child(ctx.succ, 1);
  const fullCtx = bagList(ctx.pool);
  const peels = [];
  for (const e of skolems) {
    if (Store.tag(goal) !== 'exists') {
      return { unsupported: 'skolem ∃-closure does not match the succedent' };
    }
    const opened = debruijnSubst(Store.child(goal, 0), 0n, e);
    peels.push({ goal, opened });
    goal = opened;
  }
  const closing = decompose(goal, ctx.pool, ctx.cart,
    { ST, prove, config, stampEq, roles: calculus.roles || {}, CZ: ctx.CZ, SZ: ctx.SZ });
  if (closing.unsupported) return closing;
  if (closing.remaining.size > 0) {
    return { unsupported: 'residual tokens not covered by the succedent' };
  }
  let node = closing.node;
  for (let i = peels.length - 1; i >= 0; i--) {
    node = new ProofTree({
      conclusion: Seq.seq({ [ctx.CZ]: fullCtx, [ctx.SZ]: ctx.cart }, peels[i].goal),
      rule: 'exists_r', proven: true, premises: [node],
    });
  }
  return {
    node: new ProofTree({
      conclusion: residualSeq, rule: 'monad_r', proven: true, premises: [node],
    }),
  };
}

/**
 * Elaborate a recorded collapse trace into a proof tree for `sequent`
 * (Δ₀, ⟨Θ⟩ ⊢ {∃skolems. ⊗ residual}@h). `sigma` must be
 * buildSigma(trace); `skolems` the evars ∃-closed in the succedent, in
 * closure order. Returns { tree } or { unsupported }.
 */
function elaborateCollapse({ sequent, trace, sigma, program, calculus, skolems = [] }) {
  const ctx = elabContext(sequent, calculus);
  if (ctx.unsupported) return ctx;
  const ST = ctx.tools.ST;
  const roles = calculus.roles || {};
  const chain = [];
  // effective conditioning state per drawn evar (slice 4: within-derived
  // product states ride the certificate and are re-checked)
  const stateOf = new Map(trace.filter((t) => t.draw && t.draw.state)
    .map((t) => [t.draw.evar, t.draw.state]));

  for (const entry of trace) {
    if (entry.settle) {
      const events = entry.settle.map((ev) => groundEvent(sigma, ev));
      const applied = applyEvents(ctx, events, program, calculus);
      if (applied.unsupported) return applied;
      chain.push(...applied.chain);
      continue;
    }
    if (!entry.open) continue;   // draw entries are folded into their open

    const { evar, sort } = entry.open;
    const factG = ground(sigma, entry.open.fact);
    const fact = healToPool(ctx, factG);
    if (fact === null) {
      return { unsupported: 'opened suspension missing from the elaborated pool' };
    }
    const { inner, stamp } = Store.tag(fact) === ST
      ? { inner: Store.child(fact, 0), stamp: Store.child(fact, 1) }
      : { inner: fact, stamp: null };
    const ex = sort !== null ? Store.child(inner, 1) : inner;
    if (Store.tag(ex) !== 'exists') {
      return { unsupported: 'opened suspension is not an exists fact' };
    }
    const body = Store.child(ex, 0);

    const drawn = sigma.has(evar);
    const witness = drawn ? sigma.get(evar) : evar;
    let draw;
    if (drawn) {
      const member = Store.tag(witness) === 'atom' ? Store.child(witness, 0) : Store.tag(witness);
      const st = stateOf.get(evar);
      draw = { sort, member, witness, wave: fact, ...(st ? { state: st } : {}) };
    } else {
      // never drawn: ∃-L with the evar as eigenvariable (wave dropped
      // un-observed, or a plain-∃ skolem)
      draw = { open: true, sort, witness: evar, wave: fact };
    }
    // re-derive the token multiset + weight the checker will demand
    const data = checkDrawData(draw, { program });
    if (data.error) return { unsupported: `draw record: ${data.error}` };
    // Pre-populating weight makes the kernel's weight re-check (draw-
    // check.js) TAUTOLOGICAL on this local-elaboration path — by design:
    // the check has content for EXTERNALLY-received trees, where a
    // doctored weight must disagree with the checker's own Π ρ
    // re-derivation (pinned in will-certify-collapse tamper tests).
    if (drawn) draw.weight = data.weight;

    chain.push({
      conclusion: Seq.seq({ [ctx.CZ]: bagList(ctx.pool), [ctx.SZ]: ctx.cart }, ctx.succ),
      rule: 'draw',
      state: { draw },
    });

    // advance the pool exactly as the checker expects the premise
    const take = (h) => {
      const c = ctx.pool.get(h);
      if (!c) return false;
      if (c === 1) ctx.pool.delete(h); else ctx.pool.set(h, c - 1);
      return true;
    };
    if (!take(fact)) return { unsupported: 'opened suspension vanished from the pool' };
    for (const tok of data.tokens) {
      if (!take(tok)) return { unsupported: 'draw token missing from the elaborated pool (⟨Θ⟩ not threaded)' };
    }
    const opened = debruijnSubst(body, 0n, witness);
    const parts = splitBody(opened, roles);
    for (const f of parts.linear) {
      const g = stamp === null ? f : Store.put(ST, [f, stamp]);
      ctx.pool.set(g, (ctx.pool.get(g) || 0) + 1);
    }
    for (const f of parts.persistent) {
      if (!ctx.cart.includes(f)) ctx.cart = [...ctx.cart, f];
    }
  }

  const closed = closeCollapse(ctx, calculus, skolems);
  if (closed.unsupported) return closed;
  return { tree: foldChain(chain, closed.node) };
}

/**
 * Certify a decimation run end-to-end (the collapse analogue of
 * certifyRun): run `engineCalc.collapse` in sample mode with trace
 * recording, elaborate the trace post-hoc-grounded, kernel-verify.
 *
 * @param {Object} args - { engineCalc, calculus, kernel, state,
 *   horizonTerm?, collapseOpts? } — `calculus` the sequent calculus,
 *   `kernel` a createKernel(calculus) instance, `state` the initial
 *   boundary state, `horizonTerm` the succedent's grade term (defaults
 *   to binlit 0 matching the driver's default horizon '0').
 * @returns {{ verdict: 'certified'|'unsupported'|'invalid', tree?,
 *   run, sequent?, tokens?, errors?, reason? }} — `run` is the raw
 *   collapse result (mass, importance, collapses, trace, …); `tokens`
 *   the ⟨Θ⟩ multiset injected into the endsequent.
 */
function certifyCollapse({ engineCalc, calculus, kernel, state, horizonTerm, collapseOpts = {} }) {
  const ctxStruct = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const CZ = ctxStruct.consumableZone;
  const SZ = ctxStruct.copySource;
  const run = engineCalc.collapse(state, { ...collapseOpts, mode: 'sample', trace: true });
  const trace = run.trace || [];
  const sigma = buildSigma(trace);
  const program = programFromCalc(engineCalc);

  // ⟨Θ⟩: one ground token per drawn head, in run order
  const tokens = trace.filter((t) => t.draw)
    .map((t) => Store.put(DECIMATE_PREDS.DRAWN, [atom(t.draw.member), atom(t.draw.sort)]));

  // goal: ⊗ of the final state's residual at the horizon (boundary
  // canon A@0 ≡ A), under the graded monad — as in certifyRun, but
  // ∃-CLOSED over surviving skolem evars (M1: a skolem is an opaque
  // fresh constant; the endsequent asserts its plain existential, so
  // the ∃-L opening's eigenvariable stays fresh w.r.t. the succedent)
  const { zeroCanon } = ctxTools(calculus);
  const residual = [];
  for (const k in run.state.linear) {
    for (let i = 0; i < run.state.linear[k]; i++) residual.push(zeroCanon(Number(k)));
  }
  const unitTag = calculus.roles?.unit || 'one';
  const prodTag = calculus.roles?.product || 'tensor';
  let innerGoal = residual.length === 0
    ? Store.put(unitTag, [])
    : residual.reduce((acc, h) => (acc === null ? h : Store.put(prodTag, [acc, h])), null);
  const skolems = collectEvars(innerGoal);
  for (let i = skolems.length - 1; i >= 0; i--) {
    innerGoal = Store.put('exists', [abstractEvar(innerGoal, skolems[i])]);
  }
  const compTag = calculus.roles?.computation?.tag || 'monad';
  const hTerm = horizonTerm !== undefined ? horizonTerm : Store.put('binlit', [0n]);
  const succ = Store.put(compTag, [hTerm, innerGoal]);

  const linear = [];
  for (const k in state.linear) {
    for (let i = 0; i < state.linear[k]; i++) linear.push(Number(k));
  }
  linear.push(...tokens);
  const cart = Object.keys(state.persistent || {}).map(Number);
  const sequent = Seq.seq({ [CZ]: linear, [SZ]: cart }, succ);

  // Mass verification (slice 4, B7): every STRUCTURED conditioning state
  // the run drew from must carry a claimed mass satisfying its own
  // equation — checked by substitution against the program's declared
  // priors and clauses (stateInfo); the solver is never consulted.
  const massStates = new Set();
  for (const t of trace) {
    if (!t.draw) continue;
    for (const key of [t.draw.state, t.draw.sort]) {
      if (key == null) continue;
      const info = program.sorts && program.sorts.stateInfo ? program.sorts.stateInfo(key) : null;
      if (info && info.trans.size > 0) massStates.add(key);
    }
  }
  if (massStates.size > 0) {
    const mv = verifyMasses(program, [...massStates]);
    if (mv.errors.length > 0) {
      return { verdict: 'invalid', errors: mv.errors.map((e) => `mass: ${e}`), run, tokens };
    }
  }

  const elab = elaborateCollapse({ sequent, trace, sigma, program, calculus, skolems });
  if (elab.unsupported) return { verdict: 'unsupported', reason: elab.unsupported, run, tokens };
  const v = kernel.verifyTree(elab.tree, { program });
  // skolem-free runs verify FULLY; a run with skolems carries exactly
  // the standard exists_r metavar-witness degradation from its
  // ∃-closure peels (reported, never silent)
  const okUnverified = !v.unverified ||
    (skolems.length > 0 && v.unverified.length === 1 && v.unverified[0] === 'binding');
  if (!v.valid || !okUnverified) {
    return { verdict: 'invalid', errors: v.errors, tree: elab.tree, run, tokens, sequent };
  }
  return {
    verdict: 'certified', tree: elab.tree, run, tokens, sequent,
    ...(v.unverified ? { unverified: v.unverified } : {}),
  };
}

function ctxTools(calculus) {
  const t = stampTools(calculus);
  if (!t) throw new Error('certifyCollapse: calculus lacks fire config or theory');
  return t;
}

export { buildSigma, elaborateCollapse, certifyCollapse };
export default { buildSigma, elaborateCollapse, certifyCollapse };
