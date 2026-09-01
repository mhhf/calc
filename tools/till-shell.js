#!/usr/bin/env node
/**
 * till-shell — a live TTY for till programs (TODO_0265 Phase 6).
 *
 * Loads a .till/.ill program, seeds the state from a directive's LHS, and
 * runs the interactive loop the player model is built on:
 *
 *     settle(state, T)  →  render  →  choose(menu, i, {at: T})  →  …
 *
 * Wall-clock seconds ARE the horizon (scaled by --speed): each tick
 * re-settles to now — sound by the composability law (E5), so the shell
 * never simulates, it only observes.
 *
 * Display:
 *   stock rows   — grouped by CLASSIFIER SORTS (`wood: resource.` after
 *                  `resource: sort.` — TODO_0011 rung 1, membership facts
 *                  checked at load); every known token stays on its row,
 *                  zeros included
 *   arriving     — outputs of fired jobs whose stamp is still in the
 *                  future (in-flight work), fixed lines, sorted by ETA
 *   menus        — every & fact, alternatives numbered GLOBALLY: any
 *                  visible option is one digit away; costed lolis render
 *                  as shop lines ("5 space ⊸ farm (20s)"); greyed
 *                  alternatives would be refused (cut) or queue (plan)
 *   rules        — toggle with `r`: the game's static laws as cost ⊸
 *                  product lines
 *
 * Usage:
 *   node tools/till-shell.js <file> [--init <directive>] [--speed <x>]
 *                                   [--demo "t:i,t:i,..."] [--seed <n>]
 *   --demo: non-interactive scripted clicks (game-time t, GLOBAL option
 *   number i), printing a frame per event — the testable core.
 *
 * Keys: 1-9 choose · r rules · p pause · +/- speed · q quit
 *
 * COLLAPSE MODE (TODO_0298 — will programs with ∃_ρ waves): entered via
 * --collapse, or automatically when the initial settle leaves suspended
 * superpose/exists facts (which plain settle can never fire — D4). The
 * loop becomes the stepwise decimation face:
 *
 *     collapseView(session) → render wave menu → draw → …
 *
 * The wave menu is the with-projection analogue: each still-open wave is
 * one numbered line (its facts with the evar as `?`, live members with
 * posterior weights, entropy), entropy-sorted — [1] is the driver's own
 * next pick. Digits draw that wave (PRF over the posterior, M9 attempt
 * counter in the inputs); each draw is a frame. Demo grammar in collapse
 * mode: --demo "a,a,1,a" — 'a' draws the min-entropy wave, a digit the
 * n-th menu line.
 *
 * Collapse keys: 1-9 draw wave · a auto-draw · R restart · r rules · q quit
 */

import path from 'path';
import mde from '../lib/engine/index.js';
import convert from '../lib/engine/convert.js';
import tillConfig from '../calculus/till/calculus-config.js';
import gillConfig from '../calculus/gill/calculus-config.js';
import willConfig from '../calculus/will/calculus-config.js';
import Store from '../lib/kernel/store.js';
import { show } from '../lib/engine/show.js';
import { ratParts } from '../lib/engine/theories/ratlit-theory.js';
import { substEvarInTerm } from '../lib/engine/decimate.js';
import { mix32 } from '../lib/engine/prf.js';

// ─── args ───────────────────────────────────────────────────────────

const args = process.argv.slice(2);
const file = args.find(a => !a.startsWith('--'));
const opt = (name, dflt) => {
  const i = args.indexOf(`--${name}`);
  return i >= 0 ? args[i + 1] : dflt;
};
if (!file) {
  console.error('usage: till-shell <file.till> [--init <directive>] [--speed <x>] [--demo "t:i,..."]');
  process.exit(1);
}

// Config by extension: the shell serves every timed calculus in the
// family (.till/.ill → till, .gill → gill, .will → will).
const _cfgByExt = { '.gill': gillConfig, '.will': willConfig };
const calc = mde.load(path.resolve(file), {
  calculusConfig: _cfgByExt[path.extname(file)] || tillConfig, cache: false,
});

const initName = opt('init', null);
const entry = initName
  ? calc.splitQueries.get(initName)
  : calc.splitQueries.values().next().value;
if (!entry || !entry.lhsHash) {
  console.error(`no ${initName ? `directive '${initName}'` : 'directive'} with an initial state found`);
  process.exit(1);
}
let state = convert.decomposeQuery(entry.lhsHash);
let speed = Number(opt('speed', '1'));
const ARRIVING_LINES = 10;

// ─── time and stamps ────────────────────────────────────────────────

const secs = (h) => { const [n, d] = ratParts(h); return Number(n) / Number(d); };
const horizonOf = (gameSecs) => `${Math.max(0, Math.floor(gameSecs * 1000))}/1000`;
const innerOf = (h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h);
const stampOf = (h) => (Store.tag(h) === 'at' ? secs(Store.child(h, 1)) : 0);

// ─── display kinds: classifier sorts (TODO_0011 rung 1) ─────────────
// `wood: resource.` after `resource: sort.` classifies the token IN-LOGIC
// (a membership fact, checked at load); the shell just reads the loaded
// sort system. This replaced the %#display comment directive — grouping
// is knowledge now, not presentation metadata.
const kindOf = (name) => {
  if (!calc.sorts) return null;
  const s = calc.sorts.leastSortOfName(name);
  return s && calc.sorts.isClassifier(s) ? s : null;
};

// display name of a fact's head (atom name or predicate tag)
const nameOf = (h) => {
  let x = innerOf(h);
  if (Store.tag(x) === 'bang') x = Store.child(x, 1);
  x = innerOf(x);                        // !_2 plank@25 — stamp under the bang
  const t = Store.tag(x);
  return t === 'atom' ? Store.child(x, 0) : t;
};
const SKIP = new Set(['with', 'loli', 'after', 'before', 'readPreserved', 'one', 'metavar', 'freevar', 'preserved']);

// vocabulary: every token the rules or the session ever mentioned — rows
// keep their entries (zeros included), so nothing flickers
const vocab = new Map();   // name -> kind (null = other)
function learn(name) {
  if (!name || SKIP.has(name)) return;
  if (!vocab.has(name)) vocab.set(name, kindOf(name));
}
for (const r of calc.forwardRules) {
  const lists = [r.antecedent.linear || []];
  for (const alt of (r.consequentAlts || [r.consequent])) lists.push(alt.linear || []);
  for (const list of lists) for (const h of list) learn(nameOf(h));
}
// … and from the initial state, INCLUDING menu lolis (so tokens that only
// exist behind a build order still hold a stable 0-entry on their row)
(function walk(h) {
  const t = Store.tag(h);
  if (!t) return;
  // structural wrappers: recurse into BODY positions only (grades, stamps
  // and weights are not tokens)
  const bodies = { bang: [1], at: [0], monad: [1], woplus: [1, 2] }[t]
    || (t === 'with' || t === 'loli' || t === 'tensor'
      ? [...Array(Store.arity(h)).keys()] : null);
  if (bodies) {
    for (const i of bodies) {
      const c = Store.child(h, i);
      if (typeof c === 'number' && Store.isTerm(c)) walk(c);
    }
    return;
  }
  learn(nameOf(h));
})(entry.lhsHash);

// ─── frame rendering ────────────────────────────────────────────────

function parts(h) {
  const t = Store.tag(h);
  if (t === 'tensor') return [...parts(Store.child(h, 0)), ...parts(Store.child(h, 1))];
  if (t === 'one') return [];
  if (t === 'monad') return parts(Store.child(h, 1));
  if (t === 'at') return parts(Store.child(h, 0));
  if (t === 'after' || t === 'before') return [`[${t} ${show(Store.child(h, 0))}]`];
  if (t === 'readPreserved') return [`read ${show(Store.child(h, 0))}`];
  if (t === 'preserved') return [`$${show(Store.child(h, 0))}`];
  if (t === 'bang') {
    const g = Store.child(h, 0), inner = Store.child(h, 1);
    if (Store.tag(g) === 'binlit') return [`${Store.child(g, 0)} ${show(inner)}`];
    if (Store.tag(g) === 'metavar' || Store.tag(g) === 'freevar') {
      return [`all ${parts(inner).join(' ')}`];   // !_W — whole-cohort bind
    }
    if (Store.tag(inner) === 'with') return ['…menu'];
    return [`!${show(inner)}`];
  }
  if (t === 'with') return ['…menu'];
  if (t === 'loli') return [`(${menuLabel(h)})`];
  return [show(h)];
}

function menuLabel(f) {
  if (Store.tag(f) !== 'loli') return show(f);
  const cost = parts(Store.child(f, 0));
  let body = Store.child(f, 1), delay = '';
  if (Store.tag(body) === 'monad') {
    const d = secs(Store.child(body, 0));
    if (d) delay = `  (${d}s)`;
    body = Store.child(body, 1);
  }
  return `${cost.join(' + ') || '∅'} ⊸ ${parts(body).join(' + ')}${delay}`;
}

function ruleLabel(r) {
  const ante = (r.antecedent.linear || []).flatMap(parts)
    .concat((r.antecedent.persistent || []).map(h => `!${show(h)}`));
  const alts = (r.weighted && r.consequentAlts) ? r.consequentAlts : [r.consequent];
  const conseq = alts.map(a =>
    ((a.linear || []).flatMap(parts))
      .concat((a.persistent || []).map(h => `!${show(h)}`))
      .join(' + ') || '∅'
  ).join('  |  ');
  let delay = '';
  if (r.delay) delay = r.delay.ground !== undefined ? `  (${secs(r.delay.ground)}s)` : '  (var)';
  return `${r.name}: ${ante.join(' + ') || '∅'} ⊸ ${conseq}${delay}`;
}

// all menus + a GLOBAL flat option list (digit k = options[k-1])
function menuOptions(state, T) {
  const menus = [];
  for (const hStr in state.persistent) {
    if (Store.tag(Number(hStr)) === 'with') menus.push({ fact: Number(hStr), standing: true });
  }
  for (const hStr in state.linear) {
    const h = Number(hStr);
    if (Store.tag(innerOf(h)) === 'with' && stampOf(h) <= T + 1e-9) {
      menus.push({ fact: h, standing: false });
    }
  }
  const options = [];
  for (const m of menus) {
    m.alts = calc.menuStatus(state, m.fact, horizonOf(T));
    for (const [i, alt] of m.alts.entries()) options.push({ menu: m, alt: i, info: alt });
  }
  return { menus, options };
}

function frame(state, T) {
  const lines = [];
  // stock (stamp ≤ T) and arriving (stamp > T)
  const stock = new Map();      // display term -> { name, have, future }
  const arriving = [];
  for (const hStr in state.linear) {
    const h = Number(hStr);
    const inner = innerOf(h);
    if (Store.tag(inner) === 'with' || Store.tag(inner) === 'loli') continue;
    const c = state.linear[hStr];
    const s = stampOf(h);
    const name = nameOf(h);
    learn(name);
    const key = show(inner);
    const e = stock.get(key) || { name, have: 0, future: 0 };
    if (s <= T + 1e-9) e.have += c;
    else { e.future += c; arriving.push({ label: key, at: s, c }); }
    stock.set(key, e);
  }
  const fmt = (e, key) => `${e.have}${e.future ? `(+${e.future})` : ''} ${key}`;
  lines.push(`t = ${T.toFixed(1)}s   [${speed}x]   1-9 choose · r rules · p pause · +/- speed · q quit`);
  lines.push('─'.repeat(74));

  // stock rows grouped by kind; vocabulary entries always shown (0 included)
  const rows = new Map();       // kind (or 'other') -> [text]
  const rowOf = (k) => { const key = k || 'other'; if (!rows.has(key)) rows.set(key, []); return rows.get(key); };
  for (const [name, kind] of vocab) {
    // atoms render one fixed entry; predicate families render their live terms
    const terms = [...stock.entries()].filter(([, e]) => e.name === name);
    if (terms.length === 0) {
      rowOf(kind).push(`0 ${name}`);
    } else {
      for (const [key, e] of terms) rowOf(kind).push(fmt(e, key));
    }
  }
  for (const [key, e] of stock) {
    if (!vocab.has(e.name)) rowOf(kindOf(e.name)).push(fmt(e, key));
  }
  const rowOrder = [...rows.keys()].sort((a, b) =>
    (a === 'other') - (b === 'other') || a.localeCompare(b));
  for (const kind of rowOrder) {
    lines.push(`${kind.padEnd(9)}  ${rows.get(kind).join('   ')}`);
  }

  // arriving: fixed lines, ETA-sorted
  arriving.sort((a, b) => a.at - b.at);
  lines.push('');
  lines.push('arriving:');
  for (let i = 0; i < ARRIVING_LINES; i++) {
    const f = arriving[i];
    if (!f) { lines.push(''); continue; }
    if (i === ARRIVING_LINES - 1 && arriving.length > ARRIVING_LINES) {
      lines.push(`   +${arriving.length - ARRIVING_LINES + 1} more`);
    } else {
      lines.push(`   ${(f.c > 1 ? `${f.c} ` : '') + f.label}`.padEnd(28) + `@${f.at.toFixed(1)}  (+${(f.at - T).toFixed(1)}s)`);
    }
  }

  // menus with GLOBAL numbering
  const { menus, options } = menuOptions(state, T);
  let n = 0;
  for (const m of menus) {
    lines.push('');
    lines.push(`menu${m.standing ? '' : ' (one-shot)'}:`);
    for (const alt of m.alts) {
      n++;
      const note = alt.enabled ? '' : (alt.strict ? '   (unavailable)' : '   (would queue)');
      lines.push(`  [${n}] ${menuLabel(alt.formula)}${note}`);
    }
  }
  if (!menus.length) { lines.push(''); lines.push('  (no menus offered)'); }

  if (showRules) {
    lines.push('');
    lines.push('rules:');
    for (const r of calc.forwardRules) lines.push(`  ${ruleLabel(r)}`);
  }
  return lines.join('\n');
}

function click(T, globalIdx) {
  const { options } = menuOptions(state, T);
  const o = options[globalIdx];
  if (!o) return `no option [${globalIdx + 1}]`;
  try {
    state = calc.choose(state, o.menu.fact, o.alt, { at: horizonOf(T) });
    state = calc.settle(state, horizonOf(T), { coalesce: true }).state;
    return null;
  } catch (e) {
    return e.message;
  }
}

let showRules = false;

// ─── collapse mode (TODO_0298): the stepwise decimation face ────────
// Entered explicitly (--collapse) or automatically when the initial
// settle leaves suspended superpose/exists facts — plain settle can
// never fire those (D4), so the settle loop would show a frozen frame.

const seedOpt = Number(opt('seed', '0')) >>> 0;
const demo = opt('demo', null);

const _hasSuspended = (st) => Object.keys(st.linear || {}).some((k) => {
  let h = Number(k);
  if (Store.tag(h) === 'at') h = Store.child(h, 0);
  const t = Store.tag(h);
  return t === 'superpose' || t === 'exists';
});
const collapseMode = typeof calc.collapseView === 'function' &&
  (args.includes('--collapse') ||
   _hasSuspended(calc.settle(state, '0', { maxSteps: 10000 }).state));

function _containsEvar(h, e) {
  if (h === e) return true;
  if (Store.tag(h) === 'evar') return false;
  for (let i = 0; i < Store.arity(h); i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && _containsEvar(c, e)) return true;
  }
  return false;
}

if (collapseMode) {
  const initialState = state;
  let session = { state, waveMap: new Map(), skolemSet: new Set() };
  let attempt = 0;
  let stepN = 0;
  let drawLog = [];
  let lastMsg = null;

  // M9 attempt counter in every PRF input, like the driver's restarts
  const aSeed = () => mix32(seedOpt ^ mix32(attempt >>> 0));
  const view = () => calc.collapseView(session, { seed: aSeed() });

  // a wave's display: its facts with the evar as `?` (value-derived,
  // like the driver's wave keys — never the evar id)
  const evarFacts = (e) => {
    const out = [];
    for (const k of Object.keys(session.state.linear)) {
      const h = Number(k);
      if (_containsEvar(h, e)) out.push(show(substEvarInTerm(h, e, Store.put('atom', ['?']))));
    }
    return out.sort();
  };
  const waveLine = (w) => {
    const { members, weights } = w.posterior;
    const live = members
      .map((m, i) => (weights[i][0] === 0n ? null
        : `${m} ${weights[i][0]}${weights[i][1] === 1n ? '' : `/${weights[i][1]}`}`))
      .filter(Boolean);
    return `${evarFacts(w.e).join(' · ') || w.sort}  —  ${live.join(' · ') || '∅ CONTRADICTION'}   H=${w.entropy.toFixed(2)}`;
  };

  const collapseFrame = (waves) => {
    const lines = [];
    lines.push(`collapse   seed ${seedOpt}${attempt ? `   attempt ${attempt + 1}` : ''}   draws ${drawLog.length}   1-9 draw · a auto · R restart · r rules · q quit`);
    lines.push('─'.repeat(74));
    // ground stock: everything not holding a wave evar
    const stock = new Map();
    for (const k of Object.keys(session.state.linear)) {
      const h = Number(k);
      if (waves.some((w) => _containsEvar(h, w.e))) continue;   // shown in the menu
      const key = show(innerOf(h));
      stock.set(key, (stock.get(key) || 0) + session.state.linear[k]);
    }
    lines.push('state:');
    for (const [key, c] of [...stock.entries()].sort()) {
      lines.push(`  ${c > 1 ? `${c} ` : ''}${key}`);
    }
    lines.push('');
    if (waves.length) {
      lines.push('waves (entropy-sorted — [1] is the driver\'s pick):');
      waves.forEach((w, i) => lines.push(`  [${i + 1}] ${waveLine(w)}`));
    } else {
      lines.push('waves: none — GROUND');
    }
    if (drawLog.length) {
      lines.push('');
      lines.push('log: ' + drawLog.map((d) => `${d.member} ${d.weight[0]}/${d.weight[1]}`).join(' → '));
    }
    if (showRules) {
      lines.push('');
      lines.push('rules:');
      for (const r of calc.forwardRules) lines.push(`  ${ruleLabel(r)}`);
    }
    return lines.join('\n');
  };

  const draw = (waves, i) => {
    const w = waves[i];
    if (!w) return `no wave [${i + 1}]`;
    const rec = calc.collapseDraw(session, w, { seed: aSeed(), step: stepN++ });
    if (rec.contradiction) return 'contradiction (zero posterior mass) — R to restart';
    drawLog.push(rec);
    return null;
  };
  const restart = () => {
    session = { state: initialState, waveMap: new Map(), skolemSet: new Set() };
    attempt++;
    stepN = 0;
    drawLog = [];
  };

  if (demo) {
    // collapse demo grammar: "a,a,1,a" — 'a' = min-entropy wave, digit =
    // menu line n; a frame per draw (the testable core)
    for (const tok0 of demo.split(',')) {
      const tok = tok0.trim();
      const waves = view();
      const idx = tok === 'a' ? 0 : Number(tok) - 1;
      const err = draw(waves, idx);
      const last = drawLog[drawLog.length - 1];
      console.log(`\n══ draw ${tok === 'a' ? '[auto]' : `[${idx + 1}]`}${err ? ` → ${err}` : ` → ${last.member}`}`);
      console.log(collapseFrame(view()));
    }
    process.exit(0);
  }

  if (!process.stdin.isTTY) {
    console.error('interactive mode needs a TTY (use --demo "a,a,..." for scripted collapse runs)');
    process.exit(1);
  }
  const render = () => {
    const waves = view();
    const extra = lastMsg ? `\n  ⚠ ${lastMsg}\n` : '\n';
    process.stdout.write('\x1b[2J\x1b[H' + collapseFrame(waves) + extra);
  };
  process.stdin.setRawMode(true);
  process.stdin.resume();
  process.stdin.on('data', (b) => {
    const k = b.toString();
    lastMsg = null;
    if (k === 'q' || k === '\x03') { process.stdout.write('\n'); process.exit(0); }
    else if (k === 'r') showRules = !showRules;
    else if (k === 'R') restart();
    else if (k === 'a') lastMsg = draw(view(), 0);
    else if (k >= '1' && k <= '9') lastMsg = draw(view(), Number(k) - 1);
    render();
  });
  render();
}

// ─── demo mode (scripted, non-interactive — the testable core) ──────

if (demo && !collapseMode) {
  const events = demo.split(',').map(s => {
    const [t, i] = s.split(':');
    return { t: Number(t), idx: Number(i) - 1 };
  }).sort((a, b) => a.t - b.t);
  for (const e of events) {
    state = calc.settle(state, horizonOf(e.t), { coalesce: true }).state;
    const err = click(e.t, e.idx);
    console.log(`\n══ click [${e.idx + 1}] at t=${e.t} ${err ? `→ ${err}` : ''}`);
    console.log(frame(state, e.t));
  }
  const tail = (events.at(-1)?.t ?? 0) + 5;
  state = calc.settle(state, horizonOf(tail), { coalesce: true }).state;
  console.log(`\n══ +5s later`);
  console.log(frame(state, tail));
  process.exit(0);
}

// ─── interactive loop (settle mode) ─────────────────────────────────

if (!collapseMode) {
  let start = Date.now();
  let pausedAt = null;
  let lastMsg = null;
  const gameNow = () => (((pausedAt ?? Date.now()) - start) / 1000) * speed;

  const tick = () => {
    const T = gameNow();
    state = calc.settle(state, horizonOf(T), { coalesce: true }).state;
    const extra = lastMsg ? `\n  ⚠ ${lastMsg}\n` : '\n';
    process.stdout.write('\x1b[2J\x1b[H' + frame(state, T) + extra);
  };

  if (!process.stdin.isTTY) {
    console.error('interactive mode needs a TTY (use --demo "t:i,..." for scripted runs)');
    process.exit(1);
  }
  process.stdin.setRawMode(true);
  process.stdin.resume();
  process.stdin.on('data', (b) => {
    const k = b.toString();
    if (k === 'q' || k === '\x03') { process.stdout.write('\n'); process.exit(0); }
    else if (k === 'p') {
      if (pausedAt === null) pausedAt = Date.now();
      else { start += Date.now() - pausedAt; pausedAt = null; }
    } else if (k === 'r') showRules = !showRules;
    else if (k === '+') speed *= 2;
    else if (k === '-') speed /= 2;
    else if (k >= '1' && k <= '9') {
      const T = gameNow();
      state = calc.settle(state, horizonOf(T), { coalesce: true }).state;
      lastMsg = click(T, Number(k) - 1);
    }
    tick();
  });
  setInterval(tick, 200);
  tick();
}
