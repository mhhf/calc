/**
 * timed-view — shared view-model helpers for timed-calculus frontends.
 *
 * Extracted from tools/till-shell.js (TODO_0308) so the TTY shell and the
 * web run-API (src/server/run-api.js) render states and menus through ONE
 * mechanism. Pure functions over (Store, show); no module state.
 */

import Store from '../lib/kernel/store.js';
import { show } from '../lib/engine/show.js';
import { ratParts } from '../lib/engine/theories/ratlit-theory.js';

// ─── time and stamps ────────────────────────────────────────────────

const secs = (h) => { const [n, d] = ratParts(h); return Number(n) / Number(d); };
const horizonOf = (gameSecs) => `${Math.max(0, Math.floor(gameSecs * 1000))}/1000`;
const innerOf = (h) => (Store.tag(h) === 'at' ? Store.child(h, 0) : h);
const stampOf = (h) => (Store.tag(h) === 'at' ? secs(Store.child(h, 1)) : 0);

// display name of a fact's head (atom name or predicate tag)
const nameOf = (h) => {
  let x = innerOf(h);
  if (Store.tag(x) === 'bang') x = Store.child(x, 1);
  x = innerOf(x);                        // !_2 plank@25 — stamp under the bang
  const t = Store.tag(x);
  return t === 'atom' ? Store.child(x, 0) : t;
};

const SKIP = new Set(['with', 'loli', 'after', 'before', 'readPreserved', 'one', 'metavar', 'freevar', 'preserved']);

// ─── formula display ────────────────────────────────────────────────

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

// ─── menus: every & fact + a GLOBAL flat option list ────────────────

function menuOptions(calc, state, T) {
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

export { secs, horizonOf, innerOf, stampOf, nameOf, SKIP, parts, menuLabel, ruleLabel, menuOptions };
export default { secs, horizonOf, innerOf, stampOf, nameOf, SKIP, parts, menuLabel, ruleLabel, menuOptions };
