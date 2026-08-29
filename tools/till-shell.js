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
 *                                   [--demo "t:i,t:i,..."]
 *   --demo: non-interactive scripted clicks (game-time t, GLOBAL option
 *   number i), printing a frame per event — the testable core.
 *
 * Keys: 1-9 choose · r rules · p pause · +/- speed · q quit
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

// ─── demo mode (scripted, non-interactive — the testable core) ──────

const demo = opt('demo', null);
if (demo) {
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

// ─── interactive loop ───────────────────────────────────────────────

let start = Date.now();
let pausedAt = null;
let lastMsg = null;
const gameNow = () => (((pausedAt ?? Date.now()) - start) / 1000) * speed;

function tick() {
  const T = gameNow();
  state = calc.settle(state, horizonOf(T), { coalesce: true }).state;
  const extra = lastMsg ? `\n  ⚠ ${lastMsg}\n` : '\n';
  process.stdout.write('\x1b[2J\x1b[H' + frame(state, T) + extra);
}

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
