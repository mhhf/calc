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
 * Elaboration is TOTAL on legal traces (THY_0018 §5: residual partiality
 * makes illegal steps unconstructible) and covers the full D4/Phase-6c
 * surface — counted takes and consequents, whole-bind (!_W), possessed
 * rules, ω- and counted-bang succedents. With a bound fire checker a
 * failed elaboration THROWS in the bridge (engine/elaborator
 * disagreement — a found bug, never a fallback); the trusted modeSwitch
 * node survives only for calculi that bind no checker.
 *
 * Canon: the engine's boundary is A@0 ≡ A; recorded facts are healed to
 * the live pool's hashes by VALUE (theory `le` both ways) so that parsed
 * initial tokens (binlit stamps) thread against engine-reified event
 * stamps (ratlit canon) — off the hot path, small states.
 */

import Store from '../../kernel/store.js';
import Seq from '../../kernel/sequent.js';
import { ProofTree } from '../pt.js';
import { subst, deriveLoliRecord, countOf } from './fire-check.js';

/**
 * Adapt a loaded engine calculus into the kernel's program-record form
 * (fire-check.js). Rules with unsupported shapes get { unsupported } —
 * a trace touching one fails elaboration (throw, with a bound checker).
 */
function programFromCalc(engineCalc) {
  const rules = {};
  for (const r of engineCalc.forwardRules || []) {
    rules[r.name] = adaptRule(r);
  }
  // certificate emission (TODO_0295): clause-only backchain with the
  // term builders — the FFI fast path is the UNCERTIFIED optimization,
  // certificates take the semantics path. The emitted tree is checked
  // deterministically by sld-check.js; emission itself is search.
  const certifyGoal = (g) => {
    try {
      const res = engineCalc.prove(g, {
        useFFI: false, buildTerm: true, maxDepth: 40000,
        buildClauseTerm: (_gp, pt, gh, name) => ({ rule: name || 'clause', goal: gh, premises: pt || [] }),
        buildTypeTerm: (gg, name) => ({ rule: name, goal: gg, premises: [] }),
        buildFFITerm: (gh) => ({ rule: 'ffi', goal: gh, premises: [] }),
      });
      return res && res.success && res.term ? res.term : null;
    } catch { return null; }
  };
  return {
    rules, clauses: engineCalc.clauses, definitions: engineCalc.definitions, certifyGoal,
    // the draw checker's data (absent on sortless programs — draw nodes
    // then fail honestly with 'requires a program with a sort system')
    sorts: engineCalc.sorts || null, priors: engineCalc.priors || null,
  };
}

function adaptRule(r) {
  const slots = new Array(r.metavarCount || 0);
  for (const [mv, i] of Object.entries(r.metavarSlots || {})) slots[i] = Number(mv);

  const wholeBind = [];
  const expand = (patterns) => {
    const out = [];
    for (const p of patterns || []) {
      const meta = r.linearMeta && r.linearMeta[p];
      // linearMeta defaults: countTake=0, countVar=0 (plain); a counted
      // take has countTake=k>0; whole-bind stores the METAVAR HASH in
      // countVar (compile.js:226-236) — recorded for the checker's
      // count + none-left conditions
      if (meta && meta.countVar) {
        const slot = r.metavarSlots ? r.metavarSlots[meta.countVar] : undefined;
        if (slot === undefined) return { unsupported: 'whole-bind without a theta slot' };
        wholeBind.push({ body: meta.body, slot });
        continue;
      }
      const body = meta ? meta.body : p;
      const take = meta && meta.countTake > 0 ? meta.countTake : 1;
      for (let i = 0; i < take; i++) out.push(body);
    }
    return { out };
  };

  // counted parcels (!_k A) in consequents expand in the checker's
  // produce check — pass patterns through unchanged
  const conseq = (alt) => ({ produce: alt.linear || [], producePers: alt.persistent || [] });

  // read premises live INSIDE antecedent.linear (readOnly marks the
  // subset) — consume is the complement, or the checker double-demands
  // the read token (found by gill's depot certification, TODO_0296 P2)
  const reads = new Set(r.readOnly || []);
  const consume = expand((r.antecedent.linear || []).filter((p) => !reads.has(p)));
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
    wholeBind,
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
/** Stamp tooling over a calculus's fire config + theory (shared by
 *  elaborateTrace and certifyRun). */
function stampTools(calculus) {
  const config = calculus.fire, theory = calculus.theory;
  if (!config || !theory) return null;
  const ST = config.stampTag;
  const unit = config.unit();
  const prove = (tag, args) => theory.prove(Store.put(tag, args)) !== null;
  const stampEq = (x, y) => x === y || (prove(config.le, [x, y]) && prove(config.le, [y, x]));
  const split = (h) => (Store.tag(h) === ST
    ? [Store.child(h, 0), Store.child(h, 1)] : [h, unit]);
  const zeroCanon = (h) => {
    const [inner, stamp] = split(h);
    return stampEq(stamp, unit) ? inner : h;
  };
  return { config, ST, unit, prove, stampEq, split, zeroCanon };
}

/** Build the elaboration context — live pool (count map) + cartesian
 *  zone + stamp tools over a boundary sequent. Shared by elaborateTrace
 *  and the collapse elaborator (elaborate-collapse.js). */
function elabContext(sequent, calculus) {
  const tools = stampTools(calculus);
  if (!tools) return { unsupported: 'calculus lacks fire config or theory' };
  const pool = new Map();
  for (const h of Seq.getContext(sequent, 'linear')) pool.set(h, (pool.get(h) || 0) + 1);
  return { tools, pool, cart: [...Seq.getContext(sequent, 'cartesian')], succ: sequent.succedent };
}

/** Heal a recorded fact hash to the pool's hash for the same VALUE. */
function healToPool(ctx, h) {
  if (ctx.pool.has(h)) return h;
  const [inner, stamp] = ctx.tools.split(h);
  for (const [k] of ctx.pool) {
    const [ki, ks] = ctx.tools.split(k);
    if (ki === inner && ctx.tools.stampEq(ks, stamp)) return k;
  }
  return null;
}

/**
 * Advance the context through a list of settle events, emitting one
 * chain entry ({ conclusion, rule: 'fire', state }) per firing, RLE
 * multiplicities expanded. Returns { chain } or { unsupported }.
 */
function applyEvents(ctx, events, program, calculus) {
  const { ST, zeroCanon } = ctx.tools;
  const { pool, succ } = ctx;
  let cart = ctx.cart;

  const fires = [];
  for (const ev of events || []) {
    let pr = program.rules[ev.rule];
    if (!pr) {
      // possessed rule (Phase 6c): derive the record from a consumed
      // ground loli token — its structure is the justification
      for (const k in ev.consumed || {}) {
        const h = Number(k);
        const inner = Store.tag(h) === ST ? Store.child(h, 0) : h;
        const rec = deriveLoliRecord(inner, calculus.roles || {});
        if (rec) { pr = rec; break; }
      }
      if (!pr) return { unsupported: `trace fires unknown rule '${ev.rule}'` };
    }
    if (pr.unsupported) return { unsupported: `rule '${ev.rule}': ${pr.unsupported}` };
    const theta = ev.theta || [];
    if (theta.length !== pr.slots.length) {
      return { unsupported: `rule '${ev.rule}': theta arity mismatch` };
    }
    // persistent conclusions are NOT in the event record — ground them
    // from the rule's declared patterns under theta (the checker
    // recomputes the same grounds)
    const bind = new Map();
    for (let i = 0; i < pr.slots.length; i++) {
      if (theta[i] !== undefined && theta[i] !== null) bind.set(pr.slots[i], theta[i]);
    }
    const persGrounds = (pr.alts && ev.alt !== undefined
      ? pr.alts[ev.alt].producePers : pr.producePers).map(p => subst(p, bind));
    // persistent-goal certificates (TODO_0295): goals not in the
    // cartesian zone get clause-only SLD certificates the checker
    // verifies — numeric-theory goals need none (definitional layer)
    const goalCerts = {};
    for (const gp of pr.goals || []) {
      const gg = subst(gp, bind);
      if (cart.includes(gg)) continue;
      const cert = program.certifyGoal ? program.certifyGoal(gg) : null;
      if (cert) goalCerts[gg] = cert;
    }
    const hasCerts = Object.keys(goalCerts).length > 0;
    const mult = ev.multiplicity || 1;
    for (let i = 0; i < mult; i++) {
      const consumed = {}, reserved = {};
      for (const k in ev.consumed || {}) {
        const h = healToPool(ctx, Number(k));
        if (h === null) return { unsupported: 'consumed fact missing from the elaborated pool' };
        consumed[h] = (consumed[h] || 0) + ev.consumed[k];
      }
      for (const k in ev.reserved || {}) {
        const h = healToPool(ctx, Number(k));
        if (h === null) return { unsupported: 'read fact missing from the elaborated pool' };
        reserved[h] = (reserved[h] || 0) + ev.reserved[k];
      }
      // produced: engine canon becomes the pool's canon, except the
      // boundary law A@0 ≡ A — zero-stamped facts read bare
      const produced = {};
      for (const k in ev.produced || {}) {
        const key = zeroCanon(Number(k));
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
        rule: 'fire',
        state: {
          fire: {
            rule: ev.rule, activation: ev.activation, done: ev.done,
            theta, consumed, reserved, produced, producedPers,
            ...(hasCerts ? { goalCerts } : {}),
            ...(ev.alt !== undefined ? { alt: ev.alt } : {}),
          },
        },
      });
    }
  }
  ctx.cart = cart;
  return { chain: fires };
}

/** Close the residual: monad_r over an exact-context decomposition of
 *  the succedent body against the remaining pool. { node } | { unsupported }. */
function closeResidual(ctx, calculus) {
  const { ST, prove, config, stampEq } = ctx.tools;
  const { pool, cart, succ } = ctx;
  const residualSeq = Seq.fromArrays(bagList(pool), cart, succ);
  if (Store.tag(succ) !== (calculus.roles?.computation?.tag || 'monad')) {
    return { unsupported: 'succedent is not monadic' };
  }
  const inner = Store.child(succ, 1);
  const closing = decompose(inner, pool, cart,
    { ST, prove, config, stampEq, roles: calculus.roles || {} });
  if (closing.unsupported) return closing;
  if (closing.remaining.size > 0) {
    return { unsupported: 'residual tokens not covered by the succedent' };
  }
  return {
    node: new ProofTree({
      conclusion: residualSeq, rule: 'monad_r', proven: true,
      premises: [closing.node],
    }),
  };
}

/** Fold a chain of single-premise entries over a leaf tree. */
function foldChain(chain, leaf) {
  let tree = leaf;
  for (let i = chain.length - 1; i >= 0; i--) {
    tree = new ProofTree({
      conclusion: chain[i].conclusion, rule: chain[i].rule, proven: true,
      premises: [tree], ...(chain[i].state ? { state: chain[i].state } : {}),
    });
  }
  return tree;
}

function elaborateTrace({ sequent, events, program, calculus }) {
  const ctx = elabContext(sequent, calculus);
  if (ctx.unsupported) return ctx;
  const applied = applyEvents(ctx, events, program, calculus);
  if (applied.unsupported) return applied;
  const closed = closeResidual(ctx, calculus);
  if (closed.unsupported) return closed;
  return { tree: foldChain(applied.chain, closed.node) };
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
  const prodTag = env.roles?.product || 'tensor';
  const unitTag = env.roles?.unit || 'one';

  if (tag === prodTag) {
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

  if (tag === unitTag) {
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

  const expTag = env.roles?.exponential || 'bang';
  if (tag === expTag && countOf(Store.child(formula, 0)) !== null) {
    // counted-bang goal !_k A: the SELL peel chain bang_r2^k · bang_r3 —
    // each peel proves one A from the pool, the zero tail closes empty
    const k = countOf(Store.child(formula, 0));
    const body = Store.child(formula, 1);
    if (k === 0n) {
      return {
        node: new ProofTree({
          conclusion: Seq.fromArrays([], cart, formula), rule: 'bang_r3',
          proven: true, premises: [],
        }),
        remaining: pool,
      };
    }
    const head = decompose(body, pool, cart, env);
    if (head.unsupported) return head;
    const restGoal = Store.put(tag, [Store.put('binlit', [k - 1n]), body]);
    const rest = decompose(restGoal, pool, cart, env);
    if (rest.unsupported) return rest;
    const ctx = [...ctxOf(head.node), ...ctxOf(rest.node)];
    return {
      node: new ProofTree({
        conclusion: Seq.fromArrays(ctx, cart, formula), rule: 'bang_r2',
        proven: true, premises: [head.node, rest.node],
      }),
      remaining: pool,
    };
  }
  if (tag === expTag) {
    // ω-bang goal: close from the persistent zone (bang_r + copy + id)
    const inner = Store.child(formula, 1);
    if (!cart.includes(inner)) {
      return { unsupported: 'bang goal not in the persistent zone' };
    }
    const idN = new ProofTree({
      conclusion: Seq.fromArrays([inner], cart, inner), rule: 'id', proven: true, premises: [],
    });
    const copyN = new ProofTree({
      conclusion: Seq.fromArrays([], cart, inner), rule: 'copy', proven: true, premises: [idN],
    });
    return {
      node: new ProofTree({
        conclusion: Seq.fromArrays([], cart, formula), rule: 'bang_r', proven: true, premises: [copyN],
      }),
      remaining: pool,
    };
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
  const { zeroCanon } = stampTools(calculus);
  const residual = [];
  for (const k in result.state.linear) {
    for (let i = 0; i < result.state.linear[k]; i++) residual.push(zeroCanon(Number(k)));
  }
  const unitTag = calculus.roles?.unit || 'one';
  const prodTag = calculus.roles?.product || 'tensor';
  const inner = residual.length === 0
    ? Store.put(unitTag, [])
    : residual.reduce((acc, h) => (acc === null ? h : Store.put(prodTag, [acc, h])), null);
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

export {
  programFromCalc, elaborateTrace, certifyRun,
  stampTools, elabContext, healToPool, applyEvents, closeResidual, foldChain,
  bagList, decompose,
};
export default { programFromCalc, elaborateTrace, certifyRun };
