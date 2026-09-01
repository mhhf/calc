/**
 * Decimation-run certification (TODO_0298 item 2) — certifyCollapse.
 *
 * Pins THY_0026 §5 / THY_0027 §1 as executable facts:
 *   - a sample run elaborates into ONE kernel-checked tree whose
 *     endsequent is Γ₀ ; Δ₀, ⟨Θ⟩ ⊢ {⊗ residual}@0 — one ground
 *     `drawn c s` token per drawn head, and for a bias-free program
 *     Π ρ(c) over ⟨Θ⟩ equals the run's mass (weight is a function of
 *     the endsequent)
 *   - fires interleaved with draws certify (bias facts are ordinary
 *     derived facts inside @fire segments)
 *   - rung-2 recursion certifies: the root wave's node carries the
 *     fully-ground witness tree and consumes one token per head
 *     (composite iterated ∃_ρ)
 *   - skolems and dropped waves certify as token-free OPEN records
 *     (∃-L with a syntactically fresh eigenvariable — no
 *     unverified:['binding'] degradation)
 *   - tampering is caught: a doctored draw weight fails kernel
 *     verification; a truncated ⟨Θ⟩ fails elaboration
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import Seq from '../../lib/kernel/sequent.js';
import mde from '../../lib/engine/index.js';
import { createKernel } from '../../lib/prover/kernel.js';
import { certifyCollapse, buildSigma, elaborateCollapse } from '../../lib/prover/timed/elaborate-collapse.js';
import { programFromCalc } from '../../lib/prover/timed/elaborate-trace.js';
import willConfig, { loadWillSequent } from '../../calculus/will/calculus-config.js';

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'will-certify-collapse-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));
const MEASURE = path.join(import.meta.dirname, '../../calculus/will/prelude/measure.will');

const HEADER = `#import(${MEASURE})
pos2: sort.
a0: pos2.
a1: pos2.
tile_t: sort.
sea: tile_t @w 2.
coast: tile_t @w 1.
land: tile_t @w 2.
mk: (c: pos2) -> type.
tile: (c: pos2) -> (t: tile_t) -> type.
bias: (x: tile_t) -> (c: tile_t) -> (w: q) -> type.
spawn: mk C -o { exists T: tile_t @w. tile C T }.
`;

const loadProg = (name, src) => {
  const f = path.join(tmp, name);
  fs.writeFileSync(f, src);
  return mde.load(f, { calculusConfig: willConfig, cache: false });
};
const atom = (n) => Store.put('atom', [n]);
const init2 = () => ({
  linear: { [Store.put('mk', [atom('a0')])]: 1, [Store.put('mk', [atom('a1')])]: 1 },
  persistent: {},
});

let seqCalc, kernel;
before(() => {
  seqCalc = loadWillSequent();
  kernel = createKernel(seqCalc);
});

const certify = (calc, state, collapseOpts = {}) =>
  certifyCollapse({ engineCalc: calc, calculus: seqCalc, kernel, state, collapseOpts });

/** Π ρ(c) over the endsequent's tokens, from the program's priors. */
const priorProduct = (calc, tokens) => tokens.reduce(([n, d], tok) => {
  const member = Store.child(Store.child(tok, 0), 0);
  const [pn, pd] = (calc.priors && calc.priors.get(member)) || [1n, 1n];
  return [n * pn, d * pd];
}, [1n, 1n]);
const ratEq = ([a, b], [c, d]) => a * d === c * b;

describe('certifyCollapse — unbiased two-wave program', () => {
  let calc;
  before(() => { calc = loadProg('plain.will', HEADER); });

  it('certifies; ⟨Θ⟩ carries one token per draw; Π ρ over ⟨Θ⟩ = mass', () => {
    for (const seed of [0, 1, 2]) {
      const r = certify(calc, init2(), { seed });
      assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
      assert.equal(r.tokens.length, 2);
      assert.ok(ratEq(priorProduct(calc, r.tokens), r.run.mass),
        'endsequent prior product must equal the run mass (bias-free)');
      // the tokens really are hypotheses of the endsequent
      const lin = Seq.getContext(r.tree.conclusion, 'linear');
      for (const tok of r.tokens) assert.ok(lin.includes(tok));
    }
  });

  it('every draw node in the tree is checker-routed (rule "draw")', () => {
    const r = certify(calc, init2(), { seed: 0 });
    let draws = 0;
    (function walk(n) {
      if (n.rule === 'draw') { draws++; assert.ok(n.state && n.state.draw); }
      for (const p of n.premises || []) walk(p);
    })(r.tree);
    assert.equal(draws, 2);
  });
});

describe('certifyCollapse — fires interleaved with draws (bias program)', () => {
  // Symmetric watch rules from the decimate suite: collapsing one cell
  // to sea fires a rule deriving a bias fact before the second draw.
  const PROG = HEADER + `
watch1: type.
watch2: type.
nosea1: watch1 * $tile a0 sea * $tile a1 X -o { !bias X sea 0 }.
nosea2: watch2 * $tile a1 sea * $tile a0 X -o { !bias X sea 0 }.
`;
  it('certifies across restarts and interleavings', () => {
    const calc = loadProg('bias.will', PROG);
    for (let seed = 0; seed < 8; seed++) {
      const s = init2();
      s.linear[atom('watch1')] = 1;
      s.linear[atom('watch2')] = 1;
      const r = certify(calc, s, { seed });
      assert.equal(r.verdict, 'certified', `seed ${seed}: ${r.reason || (r.errors || []).join('; ')}`);
    }
  });
});

describe('certifyCollapse — rung-2 recursion (PCFG lists)', () => {
  const PROG = `#import(${MEASURE})
lst: sort.
nil: lst @w 1.
cons: (a: lst) -> lst @w 1/2.
kick: type.
out: (x: lst) -> type.
go: kick -o { exists X: lst @w. out X }.
`;
  it('the root node carries the ground witness tree, one token per head', () => {
    const calc = loadProg('pcfg.will', PROG);
    const init = { linear: { [atom('kick')]: 1 }, persistent: {} };
    let sawCons = false;
    for (let seed = 0; seed < 12; seed++) {
      const r = certify(calc, init, { seed });
      assert.equal(r.verdict, 'certified', `seed ${seed}: ${r.reason || (r.errors || []).join('; ')}`);
      assert.equal(r.tokens.length, r.run.collapses.length, 'one token per drawn head');
      assert.ok(ratEq(priorProduct(calc, r.tokens), r.run.mass));
      if (r.tokens.length > 1) sawCons = true;
    }
    assert.ok(sawCons, 'no seed drew a cons — recursion path untested');
  });
});

describe('certifyCollapse — skolems certify as open records', () => {
  const PROG = HEADER + `
kick: type.
opaque: (t: tile_t) -> type.
skol: kick -o { exists T. opaque T }.
`;
  it('token-free ∃-L open node; goal ∃-closed; only the closure peel flags binding', () => {
    const calc = loadProg('skol.will', PROG);
    const init = { linear: { [atom('kick')]: 1 }, persistent: {} };
    const r = certify(calc, init, { seed: 0 });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.tokens.length, 0);
    // the exists_r peel verifies outright (metavar-witness premises
    // check by instance) — skolem runs carry no degradation either
    assert.equal(r.unverified, undefined);
    let opens = 0, peels = 0;
    (function walk(n) {
      if (n.rule === 'draw' && n.state?.draw?.open) opens++;
      if (n.rule === 'exists_r') peels++;
      for (const p of n.premises || []) walk(p);
    })(r.tree);
    assert.equal(opens, 1);
    assert.equal(peels, 1);
    // the succedent's monad body is the ∃-closure (no free evar leaks)
    const succ = r.tree.conclusion.succedent;
    assert.equal(Store.tag(Store.child(succ, 1)), 'exists');
  });
});

describe('certifyCollapse — correlation (one binder over a tensor body)', () => {
  const PROG = HEADER + `
mark: (t: tile_t) -> type.
mk2: (c: pos2) -> type.
spawn2: mk2 C -o { exists T: tile_t @w. (tile C T * mark T) }.
`;
  it('both conjuncts introduced by the one draw node', () => {
    const calc = loadProg('corr.will', PROG);
    const init = { linear: { [Store.put('mk2', [atom('a0')])]: 1 }, persistent: {} };
    const r = certify(calc, init, { seed: 0 });
    assert.equal(r.verdict, 'certified', r.reason || (r.errors || []).join('; '));
    assert.equal(r.tokens.length, 1);
  });
});

describe('certifyCollapse — tamper rejection', () => {
  let calc;
  before(() => { calc = loadProg('tamper.will', HEADER); });

  it('a doctored draw weight fails kernel verification', () => {
    const r = certify(calc, init2(), { seed: 0 });
    assert.equal(r.verdict, 'certified');
    let node = r.tree;
    while (node && node.rule !== 'draw') node = node.premises[0];
    assert.ok(node, 'no draw node found');
    node.state.draw.weight = [7n, 1n];
    const v = kernel.verifyTree(r.tree, { program: programFromCalc(calc) });
    assert.ok(!v.valid, 'doctored weight must not verify');
    assert.ok(v.errors.some((e) => /prior/.test(e)), v.errors.join('; '));
  });

  it('a truncated ⟨Θ⟩ fails elaboration (tokens must be threaded)', () => {
    const run = calc.collapse(init2(), { seed: 0, trace: true });
    const sigma = buildSigma(run.trace);
    const program = programFromCalc(calc);
    // endsequent WITHOUT the tokens: the draw nodes cannot consume them
    const linear = [];
    for (const k in init2().linear) linear.push(Number(k));
    const succ = Store.put('monad', [Store.put('binlit', [0n]), Store.put('one', [])]);
    const sequent = Seq.fromArrays(linear, [], succ);
    const elab = elaborateCollapse({ sequent, trace: run.trace, sigma, program, calculus: seqCalc });
    assert.ok(elab.unsupported, 'elaboration must fail without ⟨Θ⟩');
    assert.match(elab.unsupported, /token/);
  });
});
