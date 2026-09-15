/**
 * gov-api — server-side backend for the governance sandbox (TODO_0318 S0).
 *
 * One framework-agnostic entry point, `handleGov(route, body)`, mounted by both
 * server.js (Hono, prod) and src/ui/plugins/vite-docs.ts (dev middleware). It
 * holds a LIVE dill governance State per session (the run-api.js sessions
 * pattern) and exposes admin/actor verbs over it:
 *
 *   gov/start      — open a session on a program (file under calculus/dill, or a
 *                    blank prelude); returns the session id + initial view
 *   gov/state      — the full context view (facts by zone/principal + consensus +
 *                    timeline) — the web context panel
 *   gov/inject     — add a fact (admin: any; actor K: only `says K (...)`)
 *   gov/retract    — remove a fact (admin only)
 *   gov/propose    — actor K: add a candidate  !candidate P X SEQ
 *   gov/vote       — actor K: add/replace a vote !vote K P X W
 *   gov/settle     — advance the State (run the engine to quiescence)
 *   gov/kernel     — set the session's voting kernel (+ params)
 *   gov/consensus  — the read-time consensus view for a proposal under a kernel
 *   gov/enact      — mint the computed winner and settle it into `current`
 *   gov/query      — backward prove a sequent (the entity-veil / legitimacy)
 *   gov/snapshot | gov/fork | gov/reset
 *
 * ROLE-SCOPING IS THE LOGIC: admin = the mint authority (any `says K X`); actor K
 * is confined to its own `says K (...)` zone — the operational twin of poss_l's
 * index unification (THY_0046 NI-1) enforced at the API boundary. (Sandbox auth
 * is a role selector, not crypto; `!signed A Act` is v2.)
 */

import path from 'path';
import fs from 'fs';
import crypto from 'crypto';
import { fileURLToPath } from 'url';

import Seq from '../../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../../lib/prover/rule-interpreter.js';
import { createProver } from '../../lib/prover/focused.js';
import { show } from '../../lib/engine/show.js';
import dillCalculusConfig from '../../calculus/dill/calculus-config.js';
import G from '../../calculus/dill/lib/govern.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const DILL = path.join(ROOT, 'calculus', 'dill');

// Programs may only be loaded from the dill subtree.
const ALLOWED = ['calculus/dill/'];
const DEFAULT_PROGRAM = 'calculus/dill/prelude/governance.ill';

const MAX_STEPS = 5000;

// ─── sessions ─────────────────────────────────────────────────────────────────

const sessions = new Map();
const SESSION_TTL = 60 * 60 * 1000;
const SESSION_CAP = 50;

function newSession(data) {
  const now = Date.now();
  for (const [id, s] of sessions) if (now - s.touched > SESSION_TTL) sessions.delete(id);
  while (sessions.size >= SESSION_CAP) sessions.delete(sessions.keys().next().value);
  const id = crypto.randomBytes(9).toString('hex');
  sessions.set(id, { ...data, touched: now });
  return id;
}
function getSession(id) {
  const s = sessions.get(id);
  if (!s) throw new Error('unknown or expired session');
  s.touched = Date.now();
  return s;
}

// ─── program loading ──────────────────────────────────────────────────────────

function resolveProgram(program) {
  const rel = path.normalize(program || DEFAULT_PROGRAM).replace(/^\/+/, '');
  if (rel.includes('..') || !ALLOWED.some((d) => rel.startsWith(d))) {
    throw new Error(`program not allowed: ${program}`);
  }
  const p = path.join(ROOT, rel);
  if (!fs.existsSync(p)) throw new Error(`program not found: ${rel}`);
  return p;
}

function initState(calc, query) {
  if (!query) return { linear: {}, persistent: {} };
  return G.initFrom(calc, query);
}

// ─── role scoping (operational NI-1) ────────────────────────────────────────────

/** admin may inject anything; actor K may inject only `says K (...)`. */
function assertInjectAllowed(role, factStr) {
  if (role === 'admin' || role == null) return;
  const k = Number(role);
  if (!Number.isFinite(k)) throw new Error(`unknown role: ${role}`);
  const f = G.decodeFact(G.parseFact(factStr));
  const ok = f && f.pred === 'poss' && f.args[0] === k;
  if (!ok) throw new Error(`actor ${k} may only inject 'says ${k} (...)' facts (operational NI-1 / poss_l); got: ${factStr}`);
}

// ─── views ────────────────────────────────────────────────────────────────────

/** Render the state as display rows + the structured governance view. */
function stateView(sess) {
  const { state } = sess;
  const rows = [];
  for (const [h, c] of Object.entries(state.linear || {})) {
    rows.push({ zone: 'linear', text: show(Number(h)), count: c });
  }
  for (const h of Object.keys(state.persistent || {})) {
    rows.push({ zone: 'persistent', text: show(Number(h)), count: 1 });
  }
  rows.sort((a, b) => (a.zone < b.zone ? -1 : a.zone > b.zone ? 1 : a.text < b.text ? -1 : 1));

  const gov = G.extractGov(state);
  // group possessions by principal (the zones)
  const zones = {};
  for (const f of gov.facts) {
    if (f.pred === 'poss') {
      const k = f.args[0];
      (zones[k] = zones[k] || []).push(show(f.hash));
    }
  }
  // proposals present (from candidates / votes)
  const proposals = [...new Set([...gov.candidates.map((c) => c.p), ...gov.votes.map((v) => v.p)])];
  const consensus = {};
  for (const p of proposals) {
    try { consensus[p] = G.consensus(gov, p, sess.kernel, sess.kernelParams); }
    catch (e) { consensus[p] = { error: e.message }; }
  }

  return {
    rows,
    zones,
    shares: gov.shares,
    votes: gov.votes,
    candidates: gov.candidates,
    currents: gov.currents,
    proposals,
    consensus,
    kernel: sess.kernel,
    kernelParams: sess.kernelParams,
    kernels: Object.keys(G.KERNELS),
    program: sess.program,
    timeline: sess.timeline,
  };
}

function respond(id, sess, extra = {}) {
  return { ok: true, id, ...extra, view: stateView(sess) };
}

function log(sess, actor, action, detail) {
  sess.timeline.push({ n: sess.timeline.length, actor, action, detail });
}

// ─── verbs ──────────────────────────────────────────────────────────────────────

function start(body) {
  const { program, query = null, kernel = 'argmax-oldest', kernelParams = {} } = body;
  const p = resolveProgram(program);
  const calc = G.loadGovernance(p);
  const state = initState(calc, query);
  const sess = { calc, program: program || DEFAULT_PROGRAM, state, kernel, kernelParams, timeline: [] };
  // settle the genesis once so views reflect derived facts
  sess.state = calc.settle(state, 0, { maxSteps: MAX_STEPS }).state;
  log(sess, 'admin', 'start', { program: sess.program, query });
  const id = newSession(sess);
  return respond(id, sess);
}

function state(body) {
  const sess = getSession(body.id);
  return respond(body.id, sess);
}

function inject(body) {
  const sess = getSession(body.id);
  const role = body.role ?? 'admin';
  const fact = String(body.fact || '').trim();
  if (!fact) throw new Error('fact required');
  assertInjectAllowed(role, fact);
  sess.state = G.inject(sess.state, fact);
  if (body.settle !== false) sess.state = sess.calc.settle(sess.state, 0, { maxSteps: MAX_STEPS }).state;
  log(sess, String(role), 'inject', { fact });
  return respond(body.id, sess);
}

function retract(body) {
  const sess = getSession(body.id);
  const role = body.role ?? 'admin';
  if (role !== 'admin') throw new Error('only admin may retract facts');
  const fact = String(body.fact || '').trim();
  if (!fact) throw new Error('fact required');
  sess.state = G.retract(sess.state, fact);
  log(sess, 'admin', 'retract', { fact });
  return respond(body.id, sess);
}

function propose(body) {
  const sess = getSession(body.id);
  const role = body.role ?? 'admin';
  const { p, x } = body;
  if (p == null || x == null) throw new Error('propose requires { p, x }');
  const gov = G.extractGov(sess.state);
  const seq = gov.candidates.filter((c) => c.p === Number(p)).length + 1;
  const fact = `!candidate ${p} ${x} ${seq}`;
  sess.state = G.inject(sess.state, fact);
  log(sess, String(role), 'propose', { p, x, seq });
  return respond(body.id, sess);
}

function vote(body) {
  const sess = getSession(body.id);
  const role = body.role ?? 'admin';
  const { p, x, w } = body;
  const k = role === 'admin' ? body.k : Number(role);
  if (k == null || p == null || x == null || w == null) throw new Error('vote requires { p, x, w } (+ k for admin)');
  // one vote per (k,p,x): retract any prior, then add
  sess.state = G.retract(sess.state, `!vote ${k} ${p} ${x} ${w}`);
  sess.state = G.inject(sess.state, `!vote ${k} ${p} ${x} ${w}`);
  log(sess, String(role), 'vote', { k, p, x, w });
  return respond(body.id, sess);
}

function settle(body) {
  const sess = getSession(body.id);
  const before = Object.keys(sess.state.linear).length + Object.keys(sess.state.persistent).length;
  const res = sess.calc.settle(sess.state, 0, { maxSteps: Number(body.maxSteps) || MAX_STEPS });
  sess.state = res.state;
  log(sess, 'admin', 'settle', { steps: res.steps });
  return respond(body.id, sess, { steps: res.steps, before });
}

function setKernel(body) {
  const sess = getSession(body.id);
  if (!G.KERNELS[body.kernel]) throw new Error(`unknown kernel: ${body.kernel}`);
  sess.kernel = body.kernel;
  sess.kernelParams = body.kernelParams || {};
  log(sess, 'admin', 'kernel', { kernel: body.kernel, params: sess.kernelParams });
  return respond(body.id, sess);
}

function consensus(body) {
  const sess = getSession(body.id);
  const gov = G.extractGov(sess.state);
  const kernel = body.kernel || sess.kernel;
  const params = body.kernelParams || sess.kernelParams;
  const r = G.consensus(gov, Number(body.p), kernel, params);
  return { ok: true, id: body.id, proposal: Number(body.p), kernel, result: r };
}

function enact(body) {
  const sess = getSession(body.id);
  const gov = G.extractGov(sess.state);
  const r = G.consensus(gov, Number(body.p), sess.kernel, sess.kernelParams);
  if (!r.decided || r.winner == null) {
    return { ok: false, id: body.id, error: `no decision for proposal ${body.p} under kernel '${sess.kernel}'`, result: r };
  }
  sess.state = G.inject(sess.state, `winner ${body.p} ${r.winner}`);
  sess.state = sess.calc.settle(sess.state, 0, { maxSteps: MAX_STEPS }).state;
  log(sess, 'admin', 'enact', { p: Number(body.p), winner: r.winner });
  return respond(body.id, sess, { winner: r.winner });
}

// paren-aware split on a top-level separator token
function splitTop(s, sep) {
  const out = []; let depth = 0, last = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    else if (depth === 0 && s.startsWith(sep, i)) { out.push(s.slice(last, i)); i += sep.length - 1; last = i + 1; }
  }
  out.push(s.slice(last));
  return out.map((x) => x.trim()).filter(Boolean);
}

let _seq = null;
function query(body) {
  // backward prove a sequent "A * B |- C" against the dill rules (poss_l veil).
  const q = String(body.sequent || '').trim();
  if (!q.includes('|-')) throw new Error("query must be a sequent 'LHS |- RHS' (use |-)");
  if (!_seq) {
    const calc = G.governanceSequent();
    const fp = dillCalculusConfig.loader.buildParser();
    const { specs, alternatives } = buildRuleSpecs(calc);
    const prover = createProver(calc);
    _seq = { fp, specs, alternatives, prover };
  }
  const [lhs, rhs] = q.split('|-');
  const ants = splitTop(lhs, '*');
  const succ = rhs.trim();
  const seq = Seq.fromArrays(ants.map(_seq.fp), [], _seq.fp(succ));
  const res = _seq.prover.prove(seq, { rules: _seq.specs, alternatives: _seq.alternatives, maxDepth: 300, exhaustive: true });
  return { ok: true, id: body.id, sequent: q, provable: !!res.success };
}

function snapshot(body) {
  const sess = getSession(body.id);
  return { ok: true, id: body.id, snapshot: { state: sess.state, kernel: sess.kernel, kernelParams: sess.kernelParams, program: sess.program } };
}

function fork(body) {
  const sess = getSession(body.id);
  const clone = {
    calc: sess.calc,
    program: sess.program,
    state: { linear: { ...sess.state.linear }, persistent: { ...sess.state.persistent } },
    kernel: sess.kernel,
    kernelParams: { ...sess.kernelParams },
    timeline: sess.timeline.slice(),
  };
  const id = newSession(clone);
  log(clone, 'admin', 'fork', { from: body.id });
  return respond(id, clone, { forkedFrom: body.id });
}

function reset(body) {
  const sess = getSession(body.id);
  const calc = sess.calc;
  const st = initState(calc, body.query || null);
  sess.state = calc.settle(st, 0, { maxSteps: MAX_STEPS }).state;
  sess.timeline = [];
  log(sess, 'admin', 'reset', { query: body.query || null });
  return respond(body.id, sess);
}

// ─── dispatch ────────────────────────────────────────────────────────────────────

async function handleGov(route, body) {
  try {
    switch (route) {
      case 'start': return start(body || {});
      case 'state': return state(body || {});
      case 'inject': return inject(body || {});
      case 'retract': return retract(body || {});
      case 'propose': return propose(body || {});
      case 'vote': return vote(body || {});
      case 'settle': return settle(body || {});
      case 'kernel': return setKernel(body || {});
      case 'consensus': return consensus(body || {});
      case 'enact': return enact(body || {});
      case 'query': return query(body || {});
      case 'snapshot': return snapshot(body || {});
      case 'fork': return fork(body || {});
      case 'reset': return reset(body || {});
      default: return { ok: false, error: `unknown gov route: ${route}` };
    }
  } catch (e) {
    return { ok: false, error: e.message };
  }
}

export { handleGov };
export default { handleGov };
