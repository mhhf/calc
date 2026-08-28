/**
 * Trace elaboration (TODO_0294 B2) — settle event traces as kernel-checked
 * @fire derivations.
 *
 * The trace≅term observation (THY_0018 §8) made executable: a settle run
 * IS a chain of @fire instances, so its event trace elaborates into a
 * proof tree — one `fire` node per firing (RLE multiplicities expanded),
 * closed by `monad_r` + a decomposition of the succedent against the
 * residual state (tensor_r / at_l retiming / id / one_r). The kernel then
 * re-derives every step from the PROGRAM'S DECLARED RULE DATA
 * (fire-check.js) — full verification, no `unverified: 'modeSwitch'`.
 *
 * Elaboration is TOTAL on legal traces of supported rules (THY_0018 §5:
 * residual partiality makes illegal steps unconstructible) — a failed
 * elaboration of a supported trace is a found engine bug. Unsupported
 * shapes return { unsupported } and the caller falls back to the trusted
 * modeSwitch node: whole-bind (!_W) antecedents, counted/bang consequents,
 * bang succedents.
 *
 * Canon: the engine's boundary is A@0 ≡ A; recorded facts are healed to
 * the live pool's hashes by VALUE (theory `le` both ways) so that parsed
 * initial tokens (binlit stamps) thread against engine-reified event
 * stamps (ratlit canon) — off the hot path, small states.
 */

import Store from '../../kernel/store.js';
import Seq from '../../kernel/sequent.js';
import { ProofTree } from '../pt.js';
import { subst } from './fire-check.js';

/**
 * Adapt a loaded engine calculus into the kernel's program-record form
 * (fire-check.js). Rules with unsupported shapes get { unsupported } —
 * traces touching them fall back to the modeSwitch path.
 */
function programFromCalc(engineCalc) {
  const rules = {};
  for (const r of engineCalc.forwardRules || []) {
    rules[r.name] = adaptRule(r);
  }
  const prove = (g) => {
    try {
      const res = engineCalc.prove(g);
      return !!(res && (res.success === true || res === true || Array.isArray(res)));
    } catch { return false; }
  };
  return { rules, prove };
}

function adaptRule(r) {
  const slots = new Array(r.metavarCount || 0);
  for (const [mv, i] of Object.entries(r.metavarSlots || {})) slots[i] = Number(mv);

  const expand = (patterns) => {
    const out = [];
    for (const p of patterns || []) {
      const meta = r.linearMeta && r.linearMeta[p];
      // linearMeta defaults: countTake=0, countVar=0 (plain); a counted
      // take has countTake=k>0; whole-bind stores the METAVAR HASH in
      // countVar (compile.js:226-236)
      if (meta && meta.countVar) {
        return { unsupported: 'whole-bind (!_W) antecedent' };
      }
      const body = meta ? meta.body : p;
      const take = meta && meta.countTake > 0 ? meta.countTake : 1;
      for (let i = 0; i < take; i++) out.push(body);
    }
    return { out };
  };

  const conseq = (alt) => {
    for (const p of alt.linear || []) {
      if (Store.tag(p) === 'bang') return { unsupported: 'counted/bang consequent' };
    }
    return { produce: alt.linear || [], producePers: alt.persistent || [] };
  };

  const consume = expand(r.antecedent.linear);
  if (consume.unsupported) return { unsupported: consume.unsupported };
  const read = expand(r.readOnly);
  if (read.unsupported) return { unsupported: read.unsupported };

  const main = conseq(r.consequent);
  if (main.unsupported) return { unsupported: main.unsupported };
  let alts = null;
  if (r.consequentAlts && r.consequentAlts.length > 1) {
    alts = [];
    for (const a of r.consequentAlts) {
      const c = conseq(a);
      if (c.unsupported) return { unsupported: c.unsupported };
      alts.push(c);
    }
  }

  const winTerm = (w) => (w.ground !== undefined ? w.ground : slots[w.slot]);
  return {
    slots,
    consume: consume.out,
    read: read.out,
    produce: main.produce,
    producePers: main.producePers,
    alts,
    goals: r.antecedent.persistent || [],
    delay: r.delay ? (r.delay.ground !== undefined ? r.delay.ground : slots[r.delay.slot]) : null,
    after: (r.windows?.after || []).map(winTerm),
    before: (r.windows?.before || []).map(winTerm),
  };
}

/**
 * Elaborate a settle trace into a proof tree for `sequent` (Δ ⊢ {S}@T).
 *
 * @param {Object} args - { sequent, events, program, calculus }
 *   calculus: the SEQUENT calculus (supplies .theory and .fire config)
 * @returns {{ tree?: ProofTree, unsupported?: string }}
 */
function elaborateTrace({ sequent, events, program, calculus }) {
  const config = calculus.fire;
  const theory = calculus.theory;
  if (!config || !theory) return { unsupported: 'calculus lacks fire config or theory' };
  const ST = config.stampTag;
  const unit = config.unit();
  const prove = (tag, args) => theory.prove(Store.put(tag, args)) !== null;
  const stampEq = (x, y) => x === y || (prove(config.le, [x, y]) && prove(config.le, [y, x]));
  const split = (h) => (Store.tag(h) === ST
    ? [Store.child(h, 0), Store.child(h, 1)] : [h, unit]);

  // succedent {S}@T
  const succ = sequent.succedent;

  // live pool as a count map; cartesian as an ordered list
  const pool = new Map();
  for (const h of Seq.getContext(sequent, 'linear')) pool.set(h, (pool.get(h) || 0) + 1);
  let cart = [...Seq.getContext(sequent, 'cartesian')];

  // heal a recorded fact hash to the pool's hash for the same VALUE
  const healToPool = (h) => {
    if (pool.has(h)) return h;
    const [inner, stamp] = split(h);
    for (const [k] of pool) {
      const [ki, ks] = split(k);
      if (ki === inner && stampEq(ks, stamp)) return k;
    }
    return null;
  };

  // one fire record per firing, RLE multiplicities expanded
  const fires = [];
  for (const ev of events || []) {
    const pr = program.rules[ev.rule];
    if (!pr) return { unsupported: `trace fires unknown rule '${ev.rule}'` };
    if (pr.unsupported) return { unsupported: `rule '${ev.rule}': ${pr.unsupported}` };
    const theta = ev.theta || [];
    if (theta.length !== pr.slots.length || theta.some(t => t === undefined || t === null)) {
      return { unsupported: `rule '${ev.rule}': incomplete theta witness` };
    }
    // persistent conclusions are NOT in the event record — ground them
    // from the rule's declared patterns under theta (the checker
    // recomputes the same grounds)
    const bind = new Map();
    for (let i = 0; i < pr.slots.length; i++) bind.set(pr.slots[i], theta[i]);
    const persGrounds = (pr.alts && ev.alt !== undefined
      ? pr.alts[ev.alt].producePers : pr.producePers).map(p => subst(p, bind));
    const mult = ev.multiplicity || 1;
    for (let i = 0; i < mult; i++) {
      const consumed = {}, reserved = {};
      for (const k in ev.consumed || {}) {
        const h = healToPool(Number(k));
        if (h === null) return { unsupported: 'consumed fact missing from the elaborated pool' };
        consumed[h] = (consumed[h] || 0) + ev.consumed[k];
      }
      for (const k in ev.reserved || {}) {
        const h = healToPool(Number(k));
        if (h === null) return { unsupported: 'read fact missing from the elaborated pool' };
        reserved[h] = (reserved[h] || 0) + ev.reserved[k];
      }
      // produced: engine canon becomes the pool's canon, except the
      // boundary law A@0 ≡ A — zero-stamped facts read bare
      const produced = {};
      for (const k in ev.produced || {}) {
        const h = Number(k);
        const [pi, ps] = split(h);
        const key = stampEq(ps, unit) ? pi : h;
        produced[key] = (produced[key] || 0) + ev.produced[k];
      }
      const producedPers = persGrounds.slice();

      const conclusion = Seq.fromArrays(bagList(pool), cart, succ);
      // advance the pool
      for (const h in consumed) {
        const left = (pool.get(Number(h)) || 0) - consumed[h];
        if (left < 0) return { unsupported: 'consumed fact missing from the elaborated pool' };
        if (left === 0) pool.delete(Number(h)); else pool.set(Number(h), left);
      }
      for (const h in produced) pool.set(Number(h), (pool.get(Number(h)) || 0) + produced[h]);
      for (const p of producedPers) if (!cart.includes(p)) cart = [...cart, p];

      fires.push({
        conclusion,
        fire: {
          rule: ev.rule, activation: ev.activation, done: ev.done,
          theta, consumed, reserved, produced, producedPers,
          ...(ev.alt !== undefined ? { alt: ev.alt } : {}),
        },
      });
    }
  }

  // closing: residual ⊢ {S}@T via monad_r, then decompose S
  const residualSeq = Seq.fromArrays(bagList(pool), cart, succ);
  if (Store.tag(succ) !== (calculus.roles?.computation?.tag || 'monad')) {
    return { unsupported: 'succedent is not monadic' };
  }
  const inner = Store.child(succ, 1);
  const closing = decompose(inner, pool, cart, { ST, prove, config, stampEq });
  // (env.stampEq is used by decompose's exact-first retiming pass)
  if (closing.unsupported) return closing;
  if (closing.remaining.size > 0) {
    return { unsupported: 'residual tokens not covered by the succedent' };
  }
  const monadR = new ProofTree({
    conclusion: residualSeq, rule: 'monad_r', proven: true,
    premises: [closing.node],
  });

  // fold the fire chain over the closing tree
  let tree = monadR;
  for (let i = fires.length - 1; i >= 0; i--) {
    tree = new ProofTree({
      conclusion: fires[i].conclusion, rule: 'fire', proven: true,
      premises: [tree], state: { fire: fires[i].fire },
    });
  }
  return { tree };
}

function bagList(pool) {
  const out = [];
  for (const [h, c] of pool) for (let i = 0; i < c; i++) out.push(h);
  return out;
}

/**
 * Emit an exact-context decomposition tree of `formula` against the pool.
 * Consumes from `pool` (a copy is NOT taken — pass a clone if needed).
 * Returns { node, remaining: pool } or { unsupported }.
 */
function decompose(formula, pool, cart, env) {
  const tag = Store.tag(formula);

  if (tag === 'tensor') {
    const left = decompose(Store.child(formula, 0), pool, cart, env);
    if (left.unsupported) return left;
    const right = decompose(Store.child(formula, 1), pool, cart, env);
    if (right.unsupported) return right;
    const ctx = [...ctxOf(left.node), ...ctxOf(right.node)];
    return {
      node: new ProofTree({
        conclusion: Seq.fromArrays(ctx, cart, formula), rule: 'tensor_r',
        proven: true, premises: [left.node, right.node],
      }),
      remaining: pool,
    };
  }

  if (tag === 'one') {
    return {
      node: new ProofTree({
        conclusion: Seq.fromArrays([], cart, formula), rule: 'one_r', proven: true, premises: [],
      }),
      remaining: pool,
    };
  }

  if (tag === env.ST) {
    // stamped goal: retiming axiom from a value-⊑ token of the same
    // inner. EXACT stamp first — greedy up-retiming could spend an early
    // token on a late goal and strand the late token for the early goal
    // (two same-inner residuals at different stamps)
    const gi = Store.child(formula, 0), gs = Store.child(formula, 1);
    const passes = [
      (s) => s === gs || env.stampEq(s, gs),
      (s) => env.prove(env.config.le, [s, gs]),
    ];
    for (const admit of passes) {
      for (const [h, c] of pool) {
        if (c <= 0) continue;
        if (Store.tag(h) !== env.ST) continue;
        if (Store.child(h, 0) !== gi) continue;
        if (!admit(Store.child(h, 1))) continue;
        take(pool, h);
        return {
          node: new ProofTree({
            conclusion: Seq.fromArrays([h], cart, formula), rule: 'at_l', proven: true, premises: [],
          }),
          remaining: pool,
        };
      }
    }
    return { unsupported: 'no residual token retimes to the stamped goal' };
  }

  // atoms and ground predicates: identity against an exact token
  if (pool.get(formula) > 0) {
    take(pool, formula);
    return {
      node: new ProofTree({
        conclusion: Seq.fromArrays([formula], cart, formula), rule: 'id', proven: true, premises: [],
      }),
      remaining: pool,
    };
  }
  return { unsupported: `no residual token matches the goal (${Store.tag(formula)})` };
}

const ctxOf = (node) => Seq.getContext(node.conclusion, 'linear');
const take = (pool, h) => {
  const c = pool.get(h);
  if (c === 1) pool.delete(h); else pool.set(h, c - 1);
};

/**
 * Certify an arbitrary settle run (TODO_0294 B3): settle → elaborate →
 * kernel-verify. The certificate goal is the residual state itself
 * (tensor-fold), observed at the horizon.
 *
 * @param {Object} args - { engineCalc, calculus, kernel, state, horizon,
 *   settleOpts } where `calculus` is the sequent calculus and `kernel` a
 *   createKernel(calculus) instance
 * @returns {{ verdict: 'certified'|'unsupported'|'invalid', tree?, events?,
 *   errors?, reason? }}
 */
function certifyRun({ engineCalc, calculus, kernel, state, horizon, horizonTerm, settleOpts = {} }) {
  const result = engineCalc.settle(state, horizon, settleOpts);
  const events = result.events || [];
  const program = programFromCalc(engineCalc);

  // goal: ⊗ of the residual state at the horizon, in boundary canon
  // (A@0 ≡ A — the engine at-wraps unconsumed initial tokens at zero,
  // which the calculus writes bare: an unstamped hypothesis is not
  // retimable, so the GOAL must be bare too)
  const cfg = calculus.fire;
  const theory = calculus.theory;
  const unit = cfg.unit();
  const zeroCanon = (h) => {
    if (Store.tag(h) !== cfg.stampTag) return h;
    const s = Store.child(h, 1);
    const eq = s === unit ||
      (theory.prove(Store.put(cfg.le, [s, unit])) !== null &&
       theory.prove(Store.put(cfg.le, [unit, s])) !== null);
    return eq ? Store.child(h, 0) : h;
  };
  const residual = [];
  for (const k in result.state.linear) {
    for (let i = 0; i < result.state.linear[k]; i++) residual.push(zeroCanon(Number(k)));
  }
  const inner = residual.length === 0
    ? Store.put('one', [])
    : residual.reduce((acc, h) => (acc === null ? h : Store.put('tensor', [acc, h])), null);
  const compTag = calculus.roles?.computation?.tag || 'monad';
  const hTerm = horizonTerm !== undefined ? horizonTerm
    : (typeof horizon === 'object' && horizon.stamp !== undefined ? horizon.stamp : horizon);
  const succ = Store.put(compTag, [hTerm, inner]);

  const linear = [];
  for (const k in state.linear) {
    for (let i = 0; i < state.linear[k]; i++) linear.push(Number(k));
  }
  const cart = Object.keys(state.persistent || {}).map(Number);
  const sequent = Seq.fromArrays(linear, cart, succ);

  const elab = elaborateTrace({ sequent, events, program, calculus });
  if (elab.unsupported) return { verdict: 'unsupported', reason: elab.unsupported, events };
  const v = kernel.verifyTree(elab.tree, { program });
  if (!v.valid || v.unverified) {
    return { verdict: 'invalid', errors: v.errors, tree: elab.tree, events };
  }
  return { verdict: 'certified', tree: elab.tree, events };
}

export { programFromCalc, elaborateTrace, certifyRun };
export default { programFromCalc, elaborateTrace, certifyRun };
