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
 * never simulates, it only observes. Menus (& facts) render straight from
 * the state; digits project alternatives at the current time; menuStatus
 * greys alternatives whose act could not fire yet ("inactive").
 *
 * Usage:
 *   bun tools/till-shell.js <file> [--init <directive>] [--speed <x>]
 *                                  [--demo "t:i[/menu],t:i,..."]
 *
 *   --init   directive whose LHS seeds the state (default: first found)
 *   --speed  game-seconds per wall-second (default 1)
 *   --demo   non-interactive: scripted clicks (game-time t, alternative i,
 *            optional menu index), printing a frame per event — the
 *            testable core; the TTY loop is a thin shell around it.
 *
 * Keys: 1-9 choose · tab/m next menu · p pause · +/- speed · q quit
 */

import path from 'path';
import mde from '../lib/engine/index.js';
import convert from '../lib/engine/convert.js';
import tillConfig from '../calculus/till/calculus-config.js';
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

const calc = mde.load(path.resolve(file), { calculusConfig: tillConfig, cache: false });

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

// ─── time and stamps ────────────────────────────────────────────────

const secs = (h) => { const [n, d] = ratParts(h); return Number(n) / Number(d); };
const horizonOf = (gameSecs) => `${Math.max(0, Math.floor(gameSecs * 1000))}/1000`;

// ─── frame rendering ────────────────────────────────────────────────

const innerOf = (h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h);
const stampOf = (h) => (Store.tag(h) === 'at' ? secs(Store.child(h, 1)) : 0);

function menus(state, T) {
  const out = [];
  for (const hStr in state.persistent) {
    const h = Number(hStr);
    if (Store.tag(h) === 'with') out.push({ fact: h, standing: true });
  }
  for (const hStr in state.linear) {
    const h = Number(hStr);
    if (Store.tag(innerOf(h)) === 'with' && stampOf(h) <= T + 1e-9) {
      out.push({ fact: h, standing: false });
    }
  }
  return out;
}

function frame(state, T, sel) {
  const lines = [];
  const now = new Map();
  const flight = [];
  for (const hStr in state.linear) {
    const h = Number(hStr);
    const c = state.linear[hStr];
    const s = stampOf(h);
    const name = show(innerOf(h));
    if (s <= T + 1e-9) now.set(name, (now.get(name) || 0) + c);
    else flight.push({ name, at: s, c });
  }
  lines.push(`t = ${T.toFixed(1)}s   [speed ${speed}x]   1-9 choose · tab menu · p pause · q quit`);
  lines.push('─'.repeat(72));
  const bag = [...now.entries()].filter(([n]) => !n.includes('&')).sort()
    .map(([n, c]) => (c > 1 ? `${n} ×${c}` : n));
  lines.push(`now:       ${bag.join('   ') || '(empty)'}`);
  if (flight.length) {
    flight.sort((a, b) => a.at - b.at);
    lines.push(`in flight: ${flight.map(f => `${f.name}${f.c > 1 ? ` ×${f.c}` : ''} @${f.at.toFixed(1)} (+${(f.at - T).toFixed(1)}s)`).join('   ')}`);
  }
  const ms = menus(state, T);
  ms.forEach((m, mi) => {
    const cur = mi === (sel % Math.max(1, ms.length));
    lines.push('');
    lines.push(`${cur ? '▶' : ' '} menu ${mi}${m.standing ? '' : ' (one-shot)'}:`);
    for (const [i, alt] of calc.menuStatus(state, m.fact, horizonOf(T)).entries()) {
      lines.push(`    [${i + 1}] ${show(alt.formula)}${alt.enabled ? '' : '   (inactive)'}`);
    }
  });
  if (!ms.length) { lines.push(''); lines.push('  (no menus offered)'); }
  return lines.join('\n');
}

function click(T, alt, menuIdx, sel) {
  const ms = menus(state, T);
  if (!ms.length) return 'no menu to choose from';
  const m = ms[(menuIdx !== undefined ? menuIdx : sel) % ms.length];
  try {
    state = calc.choose(state, m.fact, alt, { at: horizonOf(T) });
    state = calc.settle(state, horizonOf(T)).state;
    return null;
  } catch (e) {
    return e.message;
  }
}

// ─── demo mode (scripted, non-interactive — the testable core) ──────

const demo = opt('demo', null);
if (demo) {
  const events = demo.split(',').map(s => {
    const [t, rest] = s.split(':');
    const [i, m] = rest.split('/');
    return { t: Number(t), alt: Number(i) - 1, menu: m !== undefined ? Number(m) : undefined };
  }).sort((a, b) => a.t - b.t);
  for (const e of events) {
    state = calc.settle(state, horizonOf(e.t)).state;
    const err = click(e.t, e.alt, e.menu, 0);
    console.log(`\n══ click [${e.alt + 1}]${e.menu !== undefined ? ` on menu ${e.menu}` : ''} at t=${e.t} ${err ? `→ ${err}` : ''}`);
    console.log(frame(state, e.t, 0));
  }
  const tail = (events.at(-1)?.t ?? 0) + 5;
  state = calc.settle(state, horizonOf(tail)).state;
  console.log(`\n══ +5s later`);
  console.log(frame(state, tail, 0));
  process.exit(0);
}

// ─── interactive loop ───────────────────────────────────────────────

let start = Date.now();
let pausedAt = null;
let sel = 0;
const gameNow = () => (((pausedAt ?? Date.now()) - start) / 1000) * speed;

function tick() {
  const T = gameNow();
  state = calc.settle(state, horizonOf(T)).state;
  process.stdout.write('\x1b[2J\x1b[H' + frame(state, T, sel) + '\n');
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
  } else if (k === '\t' || k === 'm') sel++;
  else if (k === '+') speed *= 2;
  else if (k === '-') speed /= 2;
  else if (k >= '1' && k <= '9') {
    const T = gameNow();
    state = calc.settle(state, horizonOf(T)).state;
    click(T, Number(k) - 1, undefined, sel);
  }
  tick();
});
setInterval(tick, 200);
tick();
