/**
 * certifyCI — the executable witness of THY_0031 (TODO_0302 M5).
 *
 * Decides the SEPARATION criterion of THY_0031 §4 on a computable cover
 * of the class dependency graph: run-level wave nodes (from a recorded
 * collapse trace, UNGROUNDED — evars are exactly the draw-dependent
 * positions, so templates are auto-widened where other class runs
 * differ) + static rule/clause nodes (fired or not — pin 3's lesson:
 * per-run actual edges are unsound) + the three conditioning-site kinds
 * (Z-draws, observed-fact colliders O_F, mass-children V_e) + latent
 * allocation forks for linear contests + directed drop-decider edges
 * (a consumer of a wave's carrier can force outcome `dropped`).
 *
 * SOUNDNESS-ONLY, by construction: every approximation ADDS edges or
 * sites (predicate-level unifiability with wildcards, numeric tags as
 * one theory-equal class, bias targeting widened to all sort-compatible
 * waves, V_e on whenever bias is possible or the sort total ≠ 1).
 * `separated: true` therefore implies X ⊥ Y | Z by THY_0031 §5;
 * `separated: false` means "cannot certify" and carries a witness walk
 * for diagnosis — it never asserts dependence (the criterion is sound,
 * not complete; pin 4b's value-erasing chain is refused despite being
 * independent).
 *
 * Scope fences (loud refusals, not silent unsoundness): dynamic rules
 * (loli emissions) and timed-window rules are v1-out-of-scope — both
 * are influence channels the graph does not yet model.
 */

'use strict';

import Store from '../kernel/store.js';
import { STATE_ZONES } from './fact-set.js';
import { debruijnSubst } from '../kernel/substitute.js';
import { freshEvar } from '../kernel/fresh.js';
import { splitBody, DECIMATE_PREDS } from './decimate.js';
import { _parseSignature } from './type-check.js';

const WILD = new Set(['evar', 'metavar', 'freevar', 'bound']);
// eq-theory-equal value class (binlit ↔ i/o/e chains, rationals):
// cross-tag matches are over-approximated to "unifiable" — sound.
const NUMISH = new Set(['binlit', 'frac', 'i', 'o', 'e']);

function stripStamp(h, stampTag) {
  return Store.tag(h) === stampTag ? Store.child(h, 0) : h;
}

/** Conservative unifiability: wildcards match anything, numeric tags
 *  match each other, atoms are exact, structure recurses. */
function unifiable(a, b) {
  if (a === b) return true;
  const ta = Store.tag(a);
  const tb = Store.tag(b);
  if (WILD.has(ta) || WILD.has(tb)) return true;
  if (NUMISH.has(ta) || NUMISH.has(tb)) return NUMISH.has(ta) && NUMISH.has(tb);
  if (ta !== tb) return false;
  const ar = Store.arity(a);
  if (ar !== Store.arity(b)) return false;
  for (let i = 0; i < ar; i++) {
    const ca = Store.child(a, i);
    const cb = Store.child(b, i);
    const ia = Store.isTermChild(ca);
    if (ia !== Store.isTermChild(cb)) return false;
    if (!ia) { if (ca !== cb) return false; continue; }
    if (!unifiable(ca, cb)) return false;
  }
  return true;
}

/** Wave records from a recorded sample trace (open entries, ungrounded). */
function collectWaves(calc, trace, stampTag) {
  const waves = [];
  for (const entry of trace) {
    if (!entry.open) continue;
    const { evar, sort, fact } = entry.open;
    const inner = stripStamp(fact, stampTag);
    const ex = sort !== null ? Store.child(inner, 1) : inner;
    if (Store.tag(ex) !== 'exists') continue;
    const body = debruijnSubst(Store.child(ex, 0), 0n, evar);
    const parts = splitBody(body, calc.roles || {});
    waves.push({
      id: `wave:${evar}`,
      evar, sort,
      suspension: inner,
      emits: [...parts.linear, ...parts.persistent],
      // rewrite reading (THY_0031 §2a): the draw consumes its
      // suspension and its evar-carrying facts
      consumes: [inner, ...parts.linear],
    });
  }
  return waves;
}

/** Exact total prior weight of a flat sort; null when not decidable
 *  flat (structured members → caller consults masses or goes
 *  conservative). Totals are [n, d] BigInt fractions. */
function flatTotal(calc, sort) {
  if (!calc.sorts || !calc.sorts.isClassifier(sort)) return null;
  let n = 0n;
  let d = 1n;
  for (const m of calc.sorts.membersOf(sort)) {
    const sigHash = calc.definitions.get(m);
    const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
    if (sig && sig.argSorts.length > 0) return null; // structured member
    const [pn, pd] = (calc.priors && calc.priors.get(m)) || [1n, 1n];
    n = n * pd + pn * d;
    d = d * pd;
  }
  return [n, d];
}

function totalIsOne(calc, sort) {
  if (sort === null) return true; // skolem: no draw weight at all
  const info = calc.sorts && calc.sorts.stateInfo ? calc.sorts.stateInfo(sort) : null;
  if (info) {
    const m = calc.masses ? calc.masses.get(sort) : null;
    return m ? m[0] === m[1] : false; // datasort without a mass: conservative
  }
  const t = flatTotal(calc, sort);
  return t ? t[0] === t[1] : false; // structured flat total: conservative
}

/**
 * Decide the separation criterion for a query on a loaded program.
 *
 * @param {Object} calc - the loaded engine api (needs forwardRules,
 *   clauses, definitions, sorts, priors, masses, roles)
 * @param {Object} q - { trace, init, X, Y, Z?, stampTag? }
 *   trace: a `calc.collapse(state, { trace: true, seed })` trace
 *   init:  the initial boundary state (its facts are the init node)
 *   X, Y:  evar hashes of the query waves (see wavesOf)
 *   Z:     { waves?: [evar...], observed?: [factHash...] }
 * @returns {{ separated: boolean, reason?: string, path?: string[],
 *   sites: string[], waves: Array<{evar, sort, id}> }}
 */
function certifyCI(calc, q) {
  const stampTag = q.stampTag || 'at';
  const Z = q.Z || {};
  const rules = calc.forwardRules || [];

  // v1 scope fences — refuse loudly rather than model incompletely
  const implTag = calc.roles && calc.roles.implication;
  for (const r of rules) {
    if (r.windows) {
      return { separated: false, sites: [], waves: [],
        reason: `rule '${r.name}' has timed-window premises — out of certifyCI v1 scope (THY_0031 §7 temporal fence)` };
    }
    if (implTag) {
      for (const alt of r.consequentAlts || []) {
        for (const p of alt.linear || []) {
          if (Store.tag(stripStamp(p, stampTag)) === implTag) {
            return { separated: false, sites: [], waves: [],
              reason: `rule '${r.name}' emits a dynamic rule (loli) — out of certifyCI v1 scope` };
          }
        }
      }
    }
  }

  const waves = collectWaves(calc, q.trace || [], stampTag);
  const strip0 = (h) => stripStamp(h, stampTag);

  // Per-rule consuming premises: a premise is NON-consuming if it is a
  // $-read — recorded either in compiled readOnly or, for the convert
  // desugaring, by verbatim re-emission in EVERY consequent alternative.
  const consumingOf = (r) => {
    const readOnly = new Set((r.readOnly || []).map(strip0));
    const alts = r.consequentAlts || [];
    const preserved = (t) =>
      alts.length > 0 && alts.every((a) => (a.linear || []).some((p) => strip0(p) === t));
    const out = [];
    for (const p of (r.antecedent && r.antecedent.linear) || []) {
      const t = strip0(p);
      if (!readOnly.has(t) && !preserved(t)) out.push(t);
    }
    return out;
  };

  // Fires per rule in the trace (RLE reading: one event = one firing
  // slot; multiplicity only raises saturation, so counting events is
  // the conservative direction).
  const firesOf = new Map();
  for (const entry of q.trace || []) {
    for (const ev of entry.settle || []) {
      firesOf.set(ev.rule, (firesOf.get(ev.rule) || 0) + (ev.multiplicity || 1));
    }
  }
  const initCounts = new Map();
  for (const zone of STATE_ZONES) {
    for (const [k, n] of Object.entries((q.init || {})[zone] || {})) {
      const t = strip0(Number(k));
      initCounts.set(t, (initCounts.get(t) || 0) + n);
    }
  }
  // All templates any rule/clause/wave-body can emit — for deciding
  // whether a premise is init-only (bounded supply).
  const emittable = [];
  for (const r of rules) {
    for (const alt of r.consequentAlts || []) {
      for (const p of [...(alt.linear || []), ...(alt.persistent || [])]) {
        const t = strip0(p);
        emittable.push(t);
        if (Store.tag(t) === DECIMATE_PREDS.SUPERPOSE && Store.tag(Store.child(t, 1)) === 'exists') {
          const body = debruijnSubst(Store.child(Store.child(t, 1), 0), 0n, freshEvar());
          const parts = splitBody(body, calc.roles || {});
          emittable.push(...parts.linear, ...parts.persistent);
        }
      }
    }
  }
  for (const [, cl] of calc.clauses || new Map()) {
    if (cl && cl.hash !== undefined) emittable.push(cl.hash);
  }
  for (const w of waves) emittable.push(...w.emits);
  const initOnlySupply = (p) => {
    if (emittable.some((t) => unifiable(t, p))) return null;
    let n = 0;
    for (const [t, c] of initCounts) { if (unifiable(t, p)) n += c; }
    return n;
  };
  // A rule is SATURATED when an init-only consuming premise bounds its
  // firing count and the trace already realized that bound — no class
  // run fires it more often, so its spawns are fully represented by
  // run waves and no phantom is needed.
  const saturated = (r) => {
    const fired = firesOf.get(r.name) || 0;
    let bound = null;
    for (const p of consumingOf(r)) {
      const s = initOnlySupply(p);
      if (s !== null) bound = bound === null ? s : Math.min(bound, s);
    }
    return bound !== null && fired >= bound;
  };

  // Context pruning from Z-wave existence (THY_0031 §2e): conditioning
  // on a wave restricts the class to runs where its SPAWNER fired; a
  // rule contesting the spawner's single-copy init-only trigger is
  // starved in every class run — prune it (and its phantoms).
  const prunedRules = new Set();
  const spawnerOf = (w) => {
    for (const entry of q.trace || []) {
      for (const ev of entry.settle || []) {
        for (const k of Object.keys(ev.produced || {})) {
          if (strip0(Number(k)) === w.suspension) return ev.rule;
        }
      }
    }
    return null;
  };
  const waveByEvar0 = new Map(waves.map((w) => [w.evar, w]));
  for (const e of Z.waves || []) {
    const w = waveByEvar0.get(e);
    if (!w) continue;
    const sName = spawnerOf(w);
    const S = rules.find((r) => r.name === sName);
    if (!S) continue;
    for (const s of consumingOf(S)) {
      if (initOnlySupply(s) !== 1) continue;
      for (const R of rules) {
        if (R.name === S.name) continue;
        if (consumingOf(R).some((p) => unifiable(p, s))) prunedRules.add(R.name);
      }
    }
  }
  const liveRules = rules.filter((r) => !prunedRules.has(r.name));

  // PHANTOM waves (D1 at the tool level): a wave that exists only in
  // OTHER class runs is invisible to the trace — pin 2 sampled on an
  // x ≠ y seed never spawns W, yet W's existence leak is real. Every
  // superpose template an UNSATURATED live rule can emit gets a static
  // wave node (fresh evar for body opening); saturated rules' spawns
  // are already the run waves, and duplicating them would let phantom
  // copies escape Z-conditioning.
  for (const r of liveRules) {
    if (saturated(r)) continue;
    let idx = 0;
    for (const alt of r.consequentAlts || []) {
      for (const p of [...(alt.linear || []), ...(alt.persistent || [])]) {
        const t = strip0(p);
        if (Store.tag(t) !== DECIMATE_PREDS.SUPERPOSE) continue;
        const sAtom = Store.child(t, 0);
        const ex = Store.child(t, 1);
        if (Store.tag(ex) !== 'exists') continue;
        const sort = Store.tag(sAtom) === 'atom' ? Store.child(sAtom, 0) : null;
        const e = freshEvar();
        const body = debruijnSubst(Store.child(ex, 0), 0n, e);
        const parts = splitBody(body, calc.roles || {});
        waves.push({
          id: `pwave:${r.name}:${idx++}`,
          evar: e, sort,
          suspension: t,
          emits: [...parts.linear, ...parts.persistent],
          consumes: [t, ...parts.linear],
        });
      }
    }
  }
  const waveByEvar = new Map(waves.map((w) => [w.evar, w]));
  const wx = waveByEvar.get(q.X);
  const wy = waveByEvar.get(q.Y);
  if (!wx || !wy) {
    throw new Error('certifyCI: X and Y must be evars of waves opened in the trace (use wavesOf)');
  }

  // ── node/template assembly ─────────────────────────────────────────
  const strip = (h) => stripStamp(h, stampTag);
  const emitters = []; // { node, templates }
  const consumers = []; // { node, templates: [{ t, consuming }] }

  const initFacts = [];
  for (const zone of STATE_ZONES) {
    for (const k of Object.keys((q.init || {})[zone] || {})) initFacts.push(strip(Number(k)));
  }
  emitters.push({ node: 'init', templates: initFacts });

  for (const r of liveRules) {
    const consuming = new Set(consumingOf(r));
    // preserved ($-read) premises re-emit the IDENTICAL instance: the
    // pass-through is not a new emission and must not make the reader a
    // producer on the fact's flow path
    const anteLin = new Set(((r.antecedent && r.antecedent.linear) || []).map(strip));
    const passThrough = (t) => anteLin.has(t) && !consuming.has(t);
    const templates = [];
    for (const alt of r.consequentAlts || []) {
      for (const p of alt.linear || []) {
        const t = strip(p);
        if (!passThrough(t)) templates.push(t);
      }
      for (const p of alt.persistent || []) templates.push(strip(p));
    }
    emitters.push({ node: `rule:${r.name}`, templates });
    const cons = [];
    for (const p of (r.antecedent && r.antecedent.linear) || []) {
      const t = strip(p);
      cons.push({ t, consuming: consuming.has(t) });
    }
    for (const p of (r.antecedent && r.antecedent.persistent) || []) {
      cons.push({ t: strip(p), consuming: false });
    }
    consumers.push({ node: `rule:${r.name}`, templates: cons });
  }

  for (const [name, cl] of calc.clauses || new Map()) {
    if (!cl || cl.hash === undefined) continue;
    emitters.push({ node: `clause:${name}`, templates: [cl.hash] });
    consumers.push({
      node: `clause:${name}`,
      templates: (cl.premises || []).map((p) => ({ t: p, consuming: false })),
    });
  }

  for (const w of waves) {
    emitters.push({ node: w.id, templates: w.emits });
    consumers.push({ node: w.id, templates: w.consumes.map((t) => ({ t, consuming: true })) });
  }

  // ── edges ──────────────────────────────────────────────────────────
  const children = new Map();
  const parents = new Map();
  const addEdge = (u, v) => {
    if (u === v) return;
    if (!children.has(u)) children.set(u, new Set());
    if (!parents.has(v)) parents.set(v, new Set());
    children.get(u).add(v);
    parents.get(v).add(u);
  };

  // flow: emission → consumption/read; contests collected per template
  const contests = new Map(); // emitted template → [{node, premise}]
  for (const em of emitters) {
    for (const t of em.templates) {
      for (const co of consumers) {
        for (const { t: p, consuming } of co.templates) {
          if (!unifiable(t, p)) continue;
          addEdge(em.node, co.node);
          if (consuming) {
            if (!contests.has(t)) contests.set(t, []);
            contests.get(t).push({ node: co.node, premise: p });
          }
        }
      }
    }
  }

  // spawn/existence + drop-deciders + bias/within targeting
  const biasSources = new Map(); // wave id → Set(source nodes)
  const contains = (h, x) => {
    if (h === x) return true;
    const a = Store.arity(h);
    for (let i = 0; i < a; i++) {
      const c = Store.child(h, i);
      if (Store.isTermChild(c) && contains(c, x)) return true;
    }
    return false;
  };
  // Does premise pattern p, matched against wave emission em, bind the
  // metavar mv to the wave's evar? true / false / 'unknown' (alignment
  // broken by other wildcards above an mv occurrence — widen).
  const alignsEvar = (p, em, mv, evar) => {
    if (p === mv) return em === evar ? true : false;
    if (!contains(p, mv)) return false;
    const tp = Store.tag(p);
    const te = Store.tag(em);
    if (WILD.has(tp) || WILD.has(te)) return 'unknown';
    if (tp !== te || Store.arity(p) !== Store.arity(em)) return 'unknown';
    let unknown = false;
    for (let i = 0; i < Store.arity(p); i++) {
      const cp = Store.child(p, i);
      const ce = Store.child(em, i);
      if (!Store.isTermChild(cp) || !Store.isTermChild(ce)) continue;
      const r = alignsEvar(cp, ce, mv, evar);
      if (r === true) return true;
      if (r === 'unknown') unknown = true;
    }
    return unknown ? 'unknown' : false;
  };
  const memberFiltered = (t) => {
    const member = Store.tag(t) === DECIMATE_PREDS.BIAS && Store.arity(t) > 1
      ? Store.child(t, 1) : null;
    const mName = member !== null && Store.isTermChild(member) && Store.tag(member) === 'atom'
      ? Store.child(member, 0) : null;
    return waves.filter((w) => {
      if (w.sort === null) return false;
      if (mName === null) return true;
      const base = calc.sorts.stateInfo && calc.sorts.stateInfo(w.sort)
        ? calc.sorts.stateInfo(w.sort).base : w.sort;
      return calc.sorts.membersOf(base).has(mName);
    });
  };
  const targetWaves = (t, premises) => {
    // bias(E, m, ...) / within(E, s): child 0 names the wave when it is
    // an evar; a METAVAR target is resolved through the premise that
    // binds it against wave emissions (premise-aligned targeting); any
    // ambiguity widens to all member-compatible waves — conservative.
    const e0 = Store.arity(t) > 0 ? Store.child(t, 0) : null;
    if (e0 !== null && Store.isTermChild(e0)) {
      if (Store.tag(e0) === 'evar' && waveByEvar.has(e0)) return [waveByEvar.get(e0)];
      if (Store.tag(e0) === 'metavar') {
        const out = new Set();
        let widen = false;
        let bound = false;
        for (const p of premises) {
          if (!contains(p, e0)) continue;
          bound = true;
          for (const w of waves) {
            for (const emT of w.emits) {
              if (!unifiable(p, emT)) continue;
              const r = alignsEvar(p, emT, e0, w.evar);
              if (r === true) out.add(w);
              else if (r === 'unknown') widen = true;
            }
          }
        }
        if (bound && !widen) return [...out];
        return memberFiltered(t);
      }
    }
    return memberFiltered(t);
  };
  const premisesOf = new Map(consumers.map((c) => [c.node, c.templates.map((x) => x.t)]));
  for (const em of emitters) {
    const prems = premisesOf.get(em.node) || [];
    for (const t of em.templates) {
      const tag = Store.tag(t);
      if (tag === DECIMATE_PREDS.SUPERPOSE || tag === 'exists') {
        for (const w of waves) {
          if (unifiable(t, w.suspension)) addEdge(em.node, w.id);
        }
      }
      if (tag === DECIMATE_PREDS.BIAS || tag === DECIMATE_PREDS.WITHIN) {
        for (const w of targetWaves(t, prems)) {
          addEdge(em.node, w.id);
          if (!biasSources.has(w.id)) biasSources.set(w.id, new Set());
          biasSources.get(w.id).add(em.node);
        }
      }
    }
  }
  // drop-deciders: a CONSUMING premise unifiable with a wave's carrier
  // gets a directed edge INTO the draw node (it can force `dropped`)
  for (const co of consumers) {
    for (const { t: p, consuming } of co.templates) {
      if (!consuming) continue;
      for (const w of waves) {
        if (co.node === w.id) continue;
        if (w.consumes.some((c) => unifiable(c, p))) addEdge(co.node, w.id);
      }
    }
  }
  // allocation forks: two consuming takers contest an emitted template
  // only when their premise templates are MUTUALLY unifiable (they can
  // grab the same instance) — two waves at different cells do not
  const allocNodes = new Set();
  for (const [t, takers] of contests) {
    for (let i = 0; i < takers.length; i++) {
      for (let j = i + 1; j < takers.length; j++) {
        if (takers[i].node === takers[j].node) continue;
        if (!unifiable(takers[i].premise, takers[j].premise)) continue;
        const fork = `alloc:${t}:${takers[i].node}:${takers[j].node}`;
        allocNodes.add(fork);
        addEdge(fork, takers[i].node);
        addEdge(fork, takers[j].node);
      }
    }
  }

  // ── conditioning sites ─────────────────────────────────────────────
  const M = new Set();
  for (const e of Z.waves || []) {
    const w = waveByEvar.get(e);
    if (!w) throw new Error('certifyCI: Z.waves entries must be opened-wave evars');
    if (w.evar === q.X || w.evar === q.Y) throw new Error('certifyCI: query waves cannot be conditioned');
    M.add(w.id);
  }
  (Z.observed || []).forEach((f, i) => {
    const F = strip(f);
    const o = `O:${i}`;
    M.add(o);
    for (const em of emitters) {
      if (em.templates.some((t) => unifiable(t, F))) addEdge(em.node, o);
    }
    for (const co of consumers) {
      if (co.templates.some(({ t }) => unifiable(t, F))) addEdge(co.node, o);
    }
  });
  // mass-children (THY_0031 §2d): V_e whenever bias/within is possible
  // or the sort's total posterior weight can differ from 1
  for (const w of waves) {
    if (w.sort === null) continue;
    const biased = biasSources.has(w.id) && biasSources.get(w.id).size > 0;
    if (!biased && totalIsOne(calc, w.sort)) continue;
    const v = `V:${w.evar}`;
    M.add(v);
    addEdge(w.id, v);
    for (const src of biasSources.get(w.id) || []) addEdge(src, v);
  }

  // ── d-separation: Bayes-ball reachability ──────────────────────────
  const kids = (v) => children.get(v) || new Set();
  const pars = (v) => parents.get(v) || new Set();

  // Constant pruning (THY_0031 §5, L2′'s shadow): a node with no wave
  // ancestor is deterministic across the class — it transmits nothing
  // and conditioning on it is vacuous. Traversal is restricted to the
  // RANDOM closure: waves + allocation forks + their forward cones.
  // (Without this, init and shared spawn rules would be spurious common
  // causes of everything.)
  const random = new Set([...waves.map((w) => w.id), ...allocNodes]);
  {
    const rq = [...random];
    while (rq.length) {
      const v = rq.pop();
      for (const c of kids(v)) {
        if (!random.has(c)) { random.add(c); rq.push(c); }
      }
    }
  }

  // ancM: nodes with a directed path to some site (collider openers)
  const ancM = new Set(M);
  {
    const queue = [...M];
    while (queue.length) {
      const v = queue.pop();
      for (const p of pars(v)) {
        if (!ancM.has(p)) { ancM.add(p); queue.push(p); }
      }
    }
  }

  const X = wx.id;
  const Y = wy.id;
  const seen = new Set();
  const pred = new Map();
  const queue = [];
  const go = (v, dir, from) => {
    if (!random.has(v)) return; // constant node: transmits nothing
    const key = `${v}|${dir}`;
    if (seen.has(key)) return;
    seen.add(key);
    pred.set(key, from);
    queue.push([v, dir]);
  };
  for (const c of kids(X)) go(c, 'down', null);
  for (const p of pars(X)) go(p, 'up', null);
  let hit = null;
  while (queue.length && !hit) {
    const [v, dir] = queue.shift();
    const key = `${v}|${dir}`;
    if (v === Y) { hit = key; break; }
    const inM = M.has(v);
    if (dir === 'down') {
      if (!inM) for (const c of kids(v)) go(c, 'down', key);
      if (ancM.has(v)) for (const p of pars(v)) go(p, 'up', key);
    } else {
      if (!inM) {
        for (const p of pars(v)) go(p, 'up', key);
        for (const c of kids(v)) go(c, 'down', key);
      }
    }
  }

  const out = {
    separated: hit === null,
    sites: [...M],
    waves: waves.map((w) => ({ evar: w.evar, sort: w.sort, id: w.id })),
  };
  if (q.debug) {
    out.graph = {};
    for (const [u, cs] of children) out.graph[u] = [...cs];
    out.random = [...random];
    out.ancM = [...ancM];
  }
  if (hit !== null) {
    const path = [];
    for (let k = hit; k !== null; k = pred.get(k)) path.push(k.split('|')[0]);
    path.push(X);
    out.path = path.reverse();
    out.reason = 'active walk found (cannot certify independence — sound refusal, not a dependence claim)';
  }
  return out;
}

/** The opened waves of a recorded trace — the query handles for certifyCI. */
function wavesOf(trace) {
  return (trace || []).filter((t) => t.open)
    .map((t) => ({ evar: t.open.evar, sort: t.open.sort, fact: t.open.fact }));
}

export { certifyCI, wavesOf, unifiable };
export default { certifyCI, wavesOf, unifiable };
