// tools/ic-probe.child.mjs — V8 IC probe child.
//
// Spawned by tools/ic-probe.js with `--log-ic`. Loads the calculus, builds a
// varied mix of terms+thetas, and hammers apply() hard enough to evolve V8's
// inline caches past premonomorphic. The parent then parses the V8 log to
// detect new megamorphic IC sites (RES_0069 regression canary).
//
// Node-only: bun has no equivalent of V8 `--log-ic`. Loaded via dynamic
// import so default-vs-named export shape doesn't matter.

import path from 'node:path';
import { loadILL } from '../calculus/ill/index.js';

const ROOT = path.resolve(import.meta.dirname, '..');

async function loadDefault(spec) {
  const m = await import(spec);
  return m.default ?? m;
}

(async () => {
  const calculus = await loadDefault(path.join(ROOT, 'lib/calculus/index.js'));
  const Store    = await loadDefault(path.join(ROOT, 'lib/kernel/store.js'));
  const subst    = await loadDefault(path.join(ROOT, 'lib/kernel/substitute.js'));
  const apply    = subst.apply;

  const ill = await loadILL();
  const AST = ill.AST;

  function rng(seed) {
    let a = seed >>> 0;
    return () => {
      a = (a + 0x6D2B79F5) >>> 0;
      let t = a;
      t = Math.imul(t ^ (t >>> 15), t | 1);
      t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  }
  function pick(r, arr) { return arr[Math.floor(r() * arr.length)]; }

  const atoms = ['p','q','r','s'].map(n => AST.atom(n));
  const mvs   = ['m0','m1','m2','m3','m4','m5'].map(n => AST.metavar(n));

  function genTerm(r, d) {
    if (d <= 0) return r() < 0.4 ? pick(r, mvs) : pick(r, atoms);
    const k = r();
    if (k < 0.2) {
      const n = 2 + Math.floor(r() * 3);
      const arr = new Uint32Array(n);
      for (let i = 0; i < n; i++) arr[i] = genTerm(r, d - 1);
      return Store.putArray(arr);
    }
    if (k < 0.45) return AST.tensor(genTerm(r, d - 1), genTerm(r, d - 1));
    if (k < 0.7)  return AST.loli(genTerm(r, d - 1), genTerm(r, d - 1));
    if (k < 0.85) return AST.with(genTerm(r, d - 1), genTerm(r, d - 1));
    return AST.oplus(genTerm(r, d - 1), genTerm(r, d - 1));
  }

  const r = rng(42);
  for (let i = 0; i < 5000; i++) {
    const h = genTerm(r, 3 + Math.floor(r() * 3));
    const n = Math.floor(r() * 8);
    const theta = [];
    for (let k = 0; k < n; k++) theta.push([pick(r, mvs), genTerm(r, 1 + Math.floor(r() * 2))]);
    for (let k = 0; k < theta.length; k++) {
      theta[k][1] = apply(theta[k][1], theta);
    }
    apply(h, theta);
  }
  console.log('__IC_PROBE_DONE__');
})().catch(err => { console.error('CHILD_FAIL:', err && err.stack || err); process.exit(1); });
