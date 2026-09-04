/**
 * sill product-stamp differential fuzz (TODO_0285 audit).
 *
 * The (time × dist) algebra is implemented twice: productValues (JS —
 * the scheduler's value algebra) and the spatial.sill clause face (le /
 * lt / qsub / sjoin — what the clause-only certifier proves). Nothing
 * ties them together but discipline; this fuzz crosses them at scale:
 *
 *   1. productValues vs an independent BigInt cross-multiplication
 *      reference (cmp/add/merge/sub, ∞-dist cases included).
 *   2. clause face vs productValues: le/lt provability ⟺ lex order,
 *      sjoin derives EXACTLY the componentwise join, qsub derives the
 *      residual ⟺ componentwise dominance — FFI and clause-only paths
 *      both (FFI failure on pairs must fall through, not corrupt).
 *      ∞ never reaches the clause face (it exists only in engine-side
 *      horizon widening), so this leg generates finite stamps only.
 *   3. engine vs algebra: a random two-input join program's output
 *      stamp must equal reify(add(merge(a, b), d)).
 *   4. certifyRun on random product chain/join programs: every settle
 *      run must certify clause-only (engine ∥ checker, end-to-end).
 *
 * One fixed master seed — failures reproduce exactly.
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import { putRat } from '../../lib/kernel/rat-term.js';
import mde from '../../lib/engine/index.js';
import backward from '../../lib/engine/backchain.js';
import { makeILLBackchainOpts } from '../../calculus/ill/lib/backchain-ill.js';
import { binlitTheory } from '../../calculus/ill/lib/binlit-theory.js';
import { ratlitTheory } from '../../lib/engine/theories/ratlit-theory.js';
import { defaultTheories, buildCanonicalizer } from '../../lib/kernel/eq-theory.js';
import { apply } from '../../lib/kernel/substitute.js';
import Seq from '../../lib/kernel/sequent.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { certifyRun } from '../../lib/prover/timed/elaborate-trace.js';
import sillConfig, { productGrades, loadSillSequent } from '../../calculus/sill/calculus-config.js';

const MASTER_SEED = 0x51117;
const TRIALS = 200;

let rngState = MASTER_SEED | 1;
const rand = () => {
  rngState ^= rngState << 13; rngState ^= rngState >>> 17; rngState ^= rngState << 5;
  return (rngState >>> 0) / 0x100000000;
};
const randInt = (n) => Math.floor(rand() * n);

const v = productGrades.values;
const INF = [1n, 0n];
const gcd = (a, b) => { a = a < 0n ? -a : a; while (b) [a, b] = [b, a % b]; return a; };
const norm = ([n, d]) => { if (n === 0n) return [0n, 1n]; const g = gcd(n, d); return [n / g, d / g]; };
/** Random ℚ≥0 rational, small (keeps clause search fast). */
const randRat = () => norm([BigInt(randInt(13)), BigInt(1 + randInt(4))]);
/** Random FINITE product value [tn,td,dn,dd] (dist 0 → scalar embedding). */
const randVal = () => { const t = randRat(), d = rand() < 0.3 ? [0n, 1n] : randRat(); return [t[0], t[1], d[0], d[1]]; };
const isInf = (x) => x[3] === 0n;

// ── independent BigInt reference (cross-multiplication; ∞ = [1n,0n]) ──
const qcmp = (a, b) => { const l = a[0] * b[1], r = b[0] * a[1]; return l < r ? -1 : l > r ? 1 : 0; };
const dcmp = (a, b) => {
  const ai = a[1] === 0n, bi = b[1] === 0n;
  if (ai || bi) return ai && bi ? 0 : (ai ? 1 : -1);
  return qcmp(a, b);
};
const qadd = (a, b) => norm([a[0] * b[1] + b[0] * a[1], a[1] * b[1]]);
const th = (x) => [x[0], x[1]];
const dh = (x) => [x[2], x[3]];
const refCmp = (a, b) => { const t = qcmp(th(a), th(b)); return t !== 0 ? t : dcmp(dh(a), dh(b)); };
const refAdd = (a, b) => {
  const t = qadd(th(a), th(b));
  const d = (isInf(a) || isInf(b)) ? INF : qadd(dh(a), dh(b));
  return [t[0], t[1], d[0], d[1]];
};
const refMerge = (a, b) => {
  const t = qcmp(th(a), th(b)) >= 0 ? th(a) : th(b);
  const d = (isInf(a) || isInf(b)) ? INF : (qcmp(dh(a), dh(b)) >= 0 ? dh(a) : dh(b));
  return [t[0], t[1], d[0], d[1]];
};
const dominates = (a, b) =>            // a ⊒ b componentwise (finite only)
  qcmp(th(a), th(b)) >= 0 && qcmp(dh(a), dh(b)) >= 0;
const refSub = (a, b) => {             // finite componentwise − (assumes dominance)
  const t = norm([a[0] * b[1] - b[0] * a[1], a[1] * b[1]]);
  const d = norm([a[2] * b[3] - b[2] * a[3], a[3] * b[3]]);
  return [t[0], t[1], d[0], d[1]];
};

function loadTmp(dir, name, source) {
  const file = path.join(dir, name);
  fs.writeFileSync(file, source);
  return mde.load(file, { calculusConfig: sillConfig, cache: false });
}

describe('sill product-stamp differential fuzz', () => {
  let dir, ec, canonicalize, baseOpts;
  const atom = (n) => Store.put('atom', [n]);
  const at = (a, s) => Store.put('at', [a, s]);
  const mv = (name) => Store.put('metavar', [name]);

  before(() => {
    dir = fs.mkdtempSync(path.join(os.tmpdir(), 'sill-fuzz-'));
    // The clause face: spatial.sill (imports gill's tower transitively).
    const SPATIAL = path.resolve(import.meta.dirname, '../../calculus/sill/prelude/spatial.sill');
    ec = mde.load(SPATIAL, { calculusConfig: sillConfig, cache: false });
    const theories = [...defaultTheories, binlitTheory, ratlitTheory];
    canonicalize = buildCanonicalizer(theories);
    baseOpts = makeILLBackchainOpts({
      theories, normalize: canonicalize, getFFIMeta: sillConfig.backward.getFFIMeta,
    });
  });
  after(() => { fs.rmSync(dir, { recursive: true, force: true }); });

  const prove = (goal, useFFI) => backward.prove(goal, ec.clauses, ec.definitions, {
    ...baseOpts, maxDepth: 20000, allBuckets: true, useFFI,
  });
  const ground = (val, theta) => {
    let x = val;
    for (let k = 0; k < 500; k++) { const n = apply(x, theta); if (n === x) break; x = n; }
    return canonicalize(x);
  };

  it('leg 1: productValues ≡ BigInt reference (cmp/add/merge/sub, ∞ dist)', () => {
    for (let i = 0; i < TRIALS; i++) {
      let a = randVal(), b = randVal();
      if (rand() < 0.15) a = [a[0], a[1], 1n, 0n];       // ∞ dist arms
      if (rand() < 0.15) b = [b[0], b[1], 1n, 0n];
      assert.equal(Math.sign(v.cmp(a, b)), Math.sign(refCmp(a, b)),
        `cmp ${a} ${b}`);
      assert.deepEqual(v.canon(v.add(a, b)), refAdd(a, b), `add ${a} ${b}`);
      assert.deepEqual(v.canon(v.merge(a, b)), refMerge(a, b), `merge ${a} ${b}`);
      if (!isInf(b) && dominates(refCmp(a, b) >= 0 ? a : b, refCmp(a, b) >= 0 ? b : a)) {
        const [hi, lo] = refCmp(a, b) >= 0 ? [a, b] : [b, a];
        if (dominates(hi, lo)) {
          assert.deepEqual(v.canon(v.sub(hi, lo)), refSub(hi, lo), `sub ${hi} ${lo}`);
        }
      }
    }
  });

  it('leg 2: clause face ≡ productValues (le/lt/sjoin/qsub, FFI and clause-only)', () => {
    for (let i = 0; i < Math.floor(TRIALS / 4); i++) {
      const a = randVal(), b = randVal();               // finite only — ∞ never reaches clauses
      const ta = v.reify(a), tb = v.reify(b);          // canonical terms (dist-0 → scalar)
      const cmp = refCmp(a, b);
      for (const useFFI of [true, false]) {
        const leg = useFFI ? 'FFI' : 'clause';
        assert.equal(prove(Store.put('le', [ta, tb]), useFFI).success, cmp <= 0,
          `le(${a}, ${b}) ${leg}: want ${cmp <= 0}`);
        assert.equal(prove(Store.put('lt', [ta, tb]), useFFI).success, cmp < 0,
          `lt(${a}, ${b}) ${leg}: want ${cmp < 0}`);
        // sjoin: the derived value must be EXACTLY the componentwise join
        const C = mv('C');
        const rj = prove(Store.put('sjoin', [ta, tb, C]), useFFI);
        assert.ok(rj.success, `sjoin(${a}, ${b}) ${leg}: no derivation`);
        assert.equal(ground(C, rj.theta), v.reify(refMerge(a, b)),
          `sjoin(${a}, ${b}) ${leg}: wrong join value`);
        // qsub: derivable ⟺ componentwise dominance; value = residual
        const H = mv('H');
        const rq = prove(Store.put('qsub', [ta, tb, H]), useFFI);
        const dom = dominates(a, b);
        assert.equal(rq.success, dom, `qsub(${a}, ${b}) ${leg}: want ${dom}`);
        if (dom) {
          assert.equal(ground(H, rq.theta), v.reify(refSub(a, b)),
            `qsub(${a}, ${b}) ${leg}: wrong residual`);
        }
      }
    }
  });

  it('leg 3: engine output stamp ≡ reify(add(merge(a, b), delay))', () => {
    for (let p = 0; p < 12; p++) {
      const dt = randRat(), dd = randRat();
      const calc = loadTmp(dir, `join-${p}.sill`, `
a1: type.
b1: type.
c1: type.
jr: a1 * b1 -o { c1 }@(${dt[0]}/${dt[1]} ~ ${dd[0]}/${dd[1]}).
`);
      const a = randVal(), b = randVal();
      const r = calc.settle({
        linear: { [at(atom('a1'), v.reify(a))]: 1, [at(atom('b1'), v.reify(b))]: 1 },
        persistent: {},
      }, '100');
      const want = v.canon(refAdd(refMerge(a, b), [dt[0], dt[1], dd[0], dd[1]]));
      const key = at(atom('c1'), v.reify(want));
      assert.equal(r.state.linear[key], 1,
        `join program p${p}: expected c1 at ${want} (a=${a}, b=${b})`);
    }
  });

  it('leg 4: certifyRun certifies random product chain/join runs (clause-only checker)', () => {
    const seqCalc = loadSillSequent();
    const kernel = createKernel(seqCalc);
    const horizonTerm = Store.child(seqCalc.parse('x@50'), 1);
    for (let p = 0; p < 8; p++) {
      const rat = () => { const q = randRat(); return `${q[0]}/${q[1]}`; };
      const text = [
        'x0: type.', 'y0: type.', 'x1: type.', 'x2: type.', 'x3: type.',
        `r0: x0 -o { x1 }@(${rat()} ~ ${rat()}).`,
        `r1: y0 -o { x2 }@(${rat()} ~ ${rat()}).`,
        `r2: x1 * x2 -o { x3 }@(${rat()} ~ ${rat()}).`,   // activation = componentwise join
      ].join('\n');
      const calc = loadTmp(dir, `cert-${p}.sill`, text);
      const r = certifyRun({
        engineCalc: calc, calculus: seqCalc, kernel,
        state: { linear: { [atom('x0')]: 1, [atom('y0')]: 1 }, persistent: {} },
        horizon: '50', horizonTerm,
      });
      assert.equal(r.verdict, 'certified',
        `p${p}: ${r.reason || (r.errors || []).join('; ')}\n${text}`);
      assert.equal(r.events.length, 3);
    }
  });
});
