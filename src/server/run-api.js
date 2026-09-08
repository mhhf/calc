/**
 * run-api — server-side execution backend for the book's interactive
 * widgets (TODO_0308 P3).
 *
 * One framework-agnostic entry point, `handleRun(route, body)`, mounted by
 * both server.js (Hono) and src/ui/plugins/vite-docs.ts (dev middleware):
 *
 *   exec           — one-shot forward execution with a captured step trace
 *   game/start     — open a timed session (settle → menus → choose loop)
 *   game/act       — settle | choose | end on an open session
 *   collapse/start — open a decimation session (will ∃_ρ waves)
 *   collapse/act   — draw | auto | restart | end
 *
 * View rendering goes through tools/timed-view.js — the same view-model
 * as the TTY shell (one mechanism, two faces).
 */

import path from 'path';
import fs from 'fs';
import os from 'os';
import crypto from 'crypto';
import { fileURLToPath } from 'url';

import mde from '../../lib/engine/index.js';
import convert from '../../lib/engine/convert.js';
import Store from '../../lib/kernel/store.js';
import { show } from '../../lib/engine/show.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { substEvarInTerm } from '../../lib/engine/decimate.js';
import { mix32 } from '../../lib/engine/prf.js';
import { horizonOf, innerOf, stampOf, menuLabel, menuOptions } from '../../tools/timed-view.js';

import illConfig from '../../calculus/ill/calculus-config.js';
import tillConfig from '../../calculus/till/calculus-config.js';
import gillConfig from '../../calculus/gill/calculus-config.js';
import willConfig from '../../calculus/will/calculus-config.js';
import sillConfig from '../../calculus/sill/calculus-config.js';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

const CONFIGS = {
  ill: illConfig,
  till: tillConfig,
  gill: gillConfig,
  will: willConfig,
  sill: sillConfig,
};
const EXT = { ill: '.ill', till: '.till', gill: '.gill', will: '.will', sill: '.sill' };

// Programs may only be loaded from these repo subtrees.
const ALLOWED_DIRS = ['calculus/', 'tests/fixtures/'];

const MAX_SOURCE = 16384;
const MAX_STEPS = 200;

// ─── program loading ────────────────────────────────────────────────

function loadProgram({ calculus = 'ill', file, source }) {
  const cfg = CONFIGS[calculus];
  if (!cfg) throw new Error(`unknown calculus: ${calculus}`);

  let p;
  let cleanup = null;
  if (file) {
    const rel = path.normalize(file).replace(/^\/+/, '');
    if (rel.includes('..') || !ALLOWED_DIRS.some(d => rel.startsWith(d))) {
      throw new Error(`file not allowed: ${file}`);
    }
    p = path.join(ROOT, rel);
    if (!fs.existsSync(p)) throw new Error(`file not found: ${rel}`);
  } else if (typeof source === 'string' && source.trim()) {
    if (source.length > MAX_SOURCE) throw new Error('source too large');
    const tmp = path.join(os.tmpdir(), `calc-run-${crypto.randomBytes(6).toString('hex')}${EXT[calculus]}`);
    fs.writeFileSync(tmp, source);
    p = tmp;
    cleanup = () => { try { fs.unlinkSync(tmp); } catch { /* already gone */ } };
  } else {
    throw new Error('file or source required');
  }

  try {
    return { calc: mde.load(p, { calculusConfig: cfg, cache: false }) };
  } finally {
    if (cleanup) cleanup();
  }
}

function initialEntry(calc, name) {
  const entry = name ? calc.splitQueries.get(name) : calc.splitQueries.values().next().value;
  if (!entry || !entry.lhsHash) {
    throw new Error(name ? `no directive '${name}' with an initial state` : 'program has no directive with an initial state');
  }
  return entry;
}

// ─── fact rendering ─────────────────────────────────────────────────

function factList(stateObj) {
  const out = [];
  for (const [k, c] of Object.entries(stateObj.linear || {})) {
    const text = show(Number(k));
    out.push(c > 1 ? `${c} ${text}` : text);
  }
  for (const k of Object.keys(stateObj.persistent || {})) {
    out.push(`!${show(Number(k))}`);
  }
  return out.sort();
}

/** produced = facts in next that were not in prev (per-count). */
function diffProduced(prev, next) {
  const count = new Map();
  for (const f of prev) count.set(f, (count.get(f) || 0) + 1);
  const produced = [];
  for (const f of next) {
    const c = count.get(f) || 0;
    if (c > 0) count.set(f, c - 1);
    else produced.push(f);
  }
  return produced;
}

// ─── sessions ───────────────────────────────────────────────────────

const sessions = new Map();
const SESSION_TTL = 30 * 60 * 1000;
const SESSION_CAP = 50;

function newSession(data) {
  // evict stale / excess
  const now = Date.now();
  for (const [id, s] of sessions) {
    if (now - s.touched > SESSION_TTL) sessions.delete(id);
  }
  while (sessions.size >= SESSION_CAP) {
    sessions.delete(sessions.keys().next().value);
  }
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

// ─── exec (one-shot, traced) ────────────────────────────────────────

function runExec({ calculus, file, source, query, maxSteps }) {
  const { calc } = loadProgram({ calculus, file, source });
  const entry = initialEntry(calc, query);
  const state = convert.decomposeQuery(entry.lhsHash);
  const cap = Math.min(Number(maxSteps) || 50, MAX_STEPS);

  const initial = factList(state);
  const steps = [];
  let prevFacts = initial;

  const result = calc.exec(state, {
    maxSteps: cap,
    onStep: ({ step, rule, consumed, state: liveState }) => {
      const snap = factList(toObject(liveState));
      // consumed is a { hash: count } map snapshot
      const consumedList = Array.isArray(consumed)
        ? consumed.map(h => show(h))
        : Object.entries(consumed || {}).map(([h, c]) => (c > 1 ? `${c} ${show(Number(h))}` : show(Number(h))));
      steps.push({
        step,
        rule: (rule && rule.name) || String(rule),
        consumed: consumedList,
        produced: diffProduced(prevFacts, snap),
        state: snap,
      });
      prevFacts = snap;
    },
  });

  return {
    ok: true,
    initial,
    steps,
    final: factList(result.state),
    quiescent: !!result.quiescent,
  };
}

// ─── timed game sessions ────────────────────────────────────────────

function gameView(s) {
  const { calc, state, t } = s;
  const stock = [];
  const pending = [];
  for (const hStr in state.linear) {
    const h = Number(hStr);
    const inner = innerOf(h);
    const tag = Store.tag(inner);
    if (tag === 'with' || tag === 'loli') continue;
    const c = state.linear[hStr];
    const at = stampOf(h);
    if (at <= t + 1e-9) {
      stock.push({ text: show(inner), count: c });
    } else {
      pending.push({ text: `${c > 1 ? `${c} ` : ''}${show(inner)}  @${at.toFixed(1)}s`, at });
    }
  }
  stock.sort((a, b) => a.text.localeCompare(b.text));
  pending.sort((a, b) => a.at - b.at);

  const { menus } = menuOptions(calc, state, t);
  const viewMenus = menus.map((m, mi) => ({
    index: mi,
    fact: Store.tag(m.fact) === 'with' || Store.tag(innerOf(m.fact)) === 'with' ? 'choose:' : show(m.fact),
    alts: m.alts.map((alt, ai) => ({
      index: ai,
      label: menuLabel(alt.formula),
      enabled: !!alt.enabled,
    })),
  }));

  return {
    ok: true,
    id: s.id,
    t,
    state: stock,
    pending: pending.map(p => p.text),
    menus: viewMenus,
    events: [],
  };
}

function gameStart({ calculus = 'till', file, init }) {
  const { calc } = loadProgram({ calculus, file });
  if (typeof calc.settle !== 'function') throw new Error(`${calculus} program has no timed API (settle)`);
  const entry = initialEntry(calc, init);
  let state = convert.decomposeQuery(entry.lhsHash);
  state = calc.settle(state, horizonOf(0), { coalesce: true }).state;
  const id = newSession({ kind: 'game', calc, state, t: 0 });
  const s = getSession(id);
  s.id = id;
  return gameView(s);
}

function gameAct({ id, action, t, menuIndex, altIndex }) {
  if (action === 'end') {
    sessions.delete(id);
    return { ok: true };
  }
  const s = getSession(id);
  if (s.kind !== 'game') throw new Error('not a game session');
  const T = Math.max(s.t, Number(t) || 0);

  if (action === 'settle') {
    s.state = s.calc.settle(s.state, horizonOf(T), { coalesce: true }).state;
    s.t = T;
    return gameView(s);
  }
  if (action === 'choose') {
    s.state = s.calc.settle(s.state, horizonOf(T), { coalesce: true }).state;
    s.t = T;
    const { menus } = menuOptions(s.calc, s.state, T);
    const menu = menus[Number(menuIndex)];
    if (!menu) throw new Error(`no menu ${menuIndex}`);
    s.state = s.calc.choose(s.state, menu.fact, Number(altIndex), { at: horizonOf(T) });
    s.state = s.calc.settle(s.state, horizonOf(T), { coalesce: true }).state;
    return gameView(s);
  }
  throw new Error(`unknown game action: ${action}`);
}

// ─── collapse sessions ──────────────────────────────────────────────

function containsEvar(h, e) {
  if (h === e) return true;
  if (Store.tag(h) === 'evar') return false;
  for (let i = 0; i < Store.arity(h); i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && containsEvar(c, e)) return true;
  }
  return false;
}

function collapseWaves(s) {
  return s.calc.collapseView(s.session, { seed: mix32(s.seed ^ mix32(s.attempt >>> 0)) });
}

function collapseViewJson(s) {
  const waves = collapseWaves(s);
  const qm = Store.put('atom', ['?']);
  const evarFacts = (e) => {
    const out = [];
    for (const k of Object.keys(s.session.state.linear)) {
      const h = Number(k);
      if (containsEvar(h, e)) out.push(show(substEvarInTerm(h, e, qm)));
    }
    return out.sort();
  };
  const viewWaves = waves.map((w, i) => ({
    index: i,
    fact: evarFacts(w.e).join(' · ') || String(w.sort),
    entropy: w.entropy,
    members: w.posterior.members
      .map((m, mi) => {
        const [n, d] = w.posterior.weights[mi];
        if (n === 0n) return null;
        return { label: String(m), weight: d === 1n ? String(n) : `${n}/${d}` };
      })
      .filter(Boolean),
  }));

  const state = [];
  for (const k of Object.keys(s.session.state.linear)) {
    const h = Number(k);
    if (waves.some(w => containsEvar(h, w.e))) continue;
    const c = s.session.state.linear[k];
    const text = show(innerOf(h));
    state.push(c > 1 ? `${c} ${text}` : text);
  }

  return {
    ok: true,
    id: s.id,
    waves: viewWaves,
    drawn: s.drawLog.map(d => `${d.member} (${d.weight[0]}${d.weight[1] === 1n ? '' : `/${d.weight[1]}`})`),
    state: state.sort(),
    contradiction: s.contradiction,
    attempts: s.attempt + 1,
    done: viewWaves.length === 0 && !s.contradiction,
  };
}

function collapseStart({ calculus = 'will', file, seed }) {
  const { calc } = loadProgram({ calculus, file });
  if (typeof calc.collapseView !== 'function') throw new Error(`${calculus} program has no collapse API`);
  const entry = initialEntry(calc, undefined);
  let state = convert.decomposeQuery(entry.lhsHash);
  state = calc.settle(state, '0', { maxSteps: 10000 }).state;
  const id = newSession({
    kind: 'collapse',
    calc,
    initialState: state,
    session: { state, waveMap: new Map(), skolemSet: new Set() },
    seed: (Number(seed) || 0) >>> 0,
    attempt: 0,
    stepN: 0,
    drawLog: [],
    contradiction: false,
  });
  const s = getSession(id);
  s.id = id;
  return collapseViewJson(s);
}

function drawOne(s, waveIndex) {
  const waves = collapseWaves(s);
  const w = waves[Number(waveIndex) || 0];
  if (!w) return false;
  const rec = s.calc.collapseDraw(s.session, w, {
    seed: mix32(s.seed ^ mix32(s.attempt >>> 0)),
    step: s.stepN++,
  });
  if (rec.contradiction) {
    s.contradiction = true;
    return false;
  }
  s.drawLog.push(rec);
  return true;
}

function collapseAct({ id, action, waveIndex }) {
  if (action === 'end') {
    sessions.delete(id);
    return { ok: true };
  }
  const s = getSession(id);
  if (s.kind !== 'collapse') throw new Error('not a collapse session');

  if (action === 'draw') {
    drawOne(s, waveIndex ?? 0);
    return collapseViewJson(s);
  }
  if (action === 'auto') {
    for (let i = 0; i < 200 && !s.contradiction; i++) {
      if (!drawOne(s, 0)) break;
    }
    return collapseViewJson(s);
  }
  if (action === 'restart') {
    s.session = { state: s.initialState, waveMap: new Map(), skolemSet: new Set() };
    s.attempt++;
    s.stepN = 0;
    s.drawLog = [];
    s.contradiction = false;
    return collapseViewJson(s);
  }
  throw new Error(`unknown collapse action: ${action}`);
}

// ─── entry point ────────────────────────────────────────────────────

/**
 * @param {string} route — 'exec' | 'game/start' | 'game/act' | 'collapse/start' | 'collapse/act'
 * @param {object} body — parsed JSON request body
 * @returns {Promise<object>} JSON-serializable response ({ ok: false, error } on failure)
 */
async function handleRun(route, body) {
  try {
    switch (route) {
      case 'exec': return runExec(body || {});
      case 'game/start': return gameStart(body || {});
      case 'game/act': return gameAct(body || {});
      case 'collapse/start': return collapseStart(body || {});
      case 'collapse/act': return collapseAct(body || {});
      default: return { ok: false, error: `unknown run route: ${route}` };
    }
  } catch (e) {
    return { ok: false, error: e.message };
  }
}

export { handleRun };
export default { handleRun };
