/**
 * Pattern utilities — tree walkers for content-addressed rule patterns.
 *
 * Shared by compile.js (rule compilation) and rule-analysis.js (delta analysis).
 */

const Store = require('../kernel/store');

/** Check if term is ground (no metavars). Named freevars are ground. */
function isGround(h) {
  const t = Store.tag(h);
  if (!t) return true;
  if (t === 'freevar') return !Store.child(h, 0)?.startsWith('_');
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems) return true;
    for (let i = 0; i < elems.length; i++) {
      if (!isGround(elems[i])) return false;
    }
    return true;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && !isGround(c)) return false;
  }
  return true;
}

/** Collect metavar hashes (freevars starting with _) into a Set. */
function collectMetavars(h, out) {
  const t = Store.tag(h);
  if (!t) return;
  if (t === 'freevar') {
    const name = Store.child(h, 0);
    if (typeof name === 'string' && name.startsWith('_')) out.add(h);
    return;
  }
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (elems) for (let i = 0; i < elems.length; i++) collectMetavars(elems[i], out);
    return;
  }
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) collectMetavars(c, out);
  }
}

/** Collect all freevars in a pattern. */
function collectFreevars(h) {
  const vars = new Set();
  function walk(hash) {
    const t = Store.tag(hash);
    if (!t) return;
    if (t === 'freevar') { vars.add(hash); return; }
    if (t === 'arrlit') {
      const elems = Store.getArrayElements(hash);
      if (elems) for (let i = 0; i < elems.length; i++) walk(elems[i]);
      return;
    }
    const a = Store.arity(hash);
    for (let i = 0; i < a; i++) {
      const c = Store.child(hash, i);
      if (Store.isTermChild(c)) walk(c);
    }
  }
  walk(h);
  return vars;
}

module.exports = { isGround, collectMetavars, collectFreevars };
