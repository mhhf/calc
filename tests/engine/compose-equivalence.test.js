/**
 * Compose optimization-pass equivalence pins (RES_0143 E2b + audit item 3).
 *
 * The compose pipeline's optimization passes must be semantics-
 * preserving. Two differentials, each with a non-vacuity guard:
 *
 * - P5/P5.5 fusion: the toy pc-chain program below (minimal shape on
 *   which P5 fires — verified via ruleCount) with fusion ON vs OFF.
 * - P6 SROA, ISOLATED: the multisig symex program (the production
 *   SROA driver) with fuse+SROA vs fuse+SROA-neutered — both arms
 *   fused, so the diff is exactly P6; sroaTransformed from onPhase
 *   diagnostics guards against a vacuous pin (the pre-audit version
 *   claimed P6 coverage on a program where SROA fired zero times).
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import illcc from '../../calculus/ill/calculus-config.js';
import { show } from '../../lib/engine/show.js';
import { loadBytecode, bytecodeArrGetGuard } from '../../calculus/ill/lib/bytecode-loader.js';
import { ILL_SROA_CONFIG } from '../../calculus/ill/lib/compose-config.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';

const SYMEX_PATH = path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
const CODE_PATH = path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');

const PROG =
  'pc : bin -> type.\n' +
  'ceq_acc : bin -> type.\n' +
  'ceq_done : bin -> type.\n' +
  'plus: (a: bin) -> (b: bin) -> (c: bin) -> type.\n' +
  'ceq_code: (a: bin) -> (op: bin) -> type.\n' +
  'ceq_code/c0: !_0 ceq_code 0 1.\n' +
  'ceq_code/c1: !_0 ceq_code 1 1.\n' +
  'ceq_code/c2: !_0 ceq_code 2 2.\n' +
  'istep: pc PC * !ceq_code PC 1 * ceq_acc X * !plus PC 1 PC2 -o { pc PC2 * ceq_acc X }.\n' +
  'ihalt: pc PC * !ceq_code PC 2 * ceq_acc X -o { ceq_done X }.\n' +
  '#symex pc 0 * ceq_acc 3.\n';

function runArm(fuse) {
  Store.clear();
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'compose-eq-'));
  const file = path.join(tmpDir, 'prog.ill');
  fs.writeFileSync(file, PROG);
  try {
    const calc = mde.load(file, {
      cache: false,
      fuseBasicBlocks: fuse,
      residualResolver: illcc.compose.residualResolver,
    });
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const res = calc.exec(state, { maxSteps: 20 });
    return {
      ruleCount: calc.forwardRules.length,
      quiescent: res.quiescent,
      // Value-level final state (show renders by content, not by hash id —
      // Store ids differ across the two loads)
      finalLinear: Object.keys(res.state.linear).map(h => show(Number(h))).sort(),
    };
  } finally {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  }
}

describe('compose fusion equivalence (RES_0143 E2b)', () => {
  it('fusion ON reaches the same final state as fusion OFF', () => {
    const off = runArm(false);
    const on = runArm(true);

    // The pin is non-vacuous: fusion must actually have fired.
    assert.equal(off.ruleCount, 3, 'unfused arm: 3 specialized rules');
    assert.equal(on.ruleCount, 1, 'fused arm: one mega-rule (P5 fired)');

    // Semantic equivalence.
    assert.equal(on.quiescent, off.quiescent, 'both quiescent');
    assert.deepEqual(on.finalLinear, off.finalLinear,
      'fused and unfused arms reach the same final state');
    assert.deepEqual(off.finalLinear, ['ceq_done(0x3)'], 'expected result');
  });
});

describe('compose SROA equivalence — P6 isolated (audit item 3)', () => {
  it('fuse+SROA explores to the same leaf states as fuse without SROA', () => {
    const hex = fs.readFileSync(CODE_PATH, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];

    function arm(sroaConfig) {
      Store.clear();
      const bc = loadBytecode(hex);
      let diag = null;
      const calc = mde.load(SYMEX_PATH, {
        cache: false,
        extraGrade0Facts: bc.facts,
        scopeGuard: bytecodeArrGetGuard,
        // JUMPDEST fusion barriers (TODO_0307 Bug A): the raw extraGrade0Facts
        // path does not auto-wire them (only the {bytecode} API does), so pass
        // them explicitly — without them fusion swallows jump targets and both
        // arms leave 6 states RUNNING at pc 0x225 with SROA-vs-fusion diffs.
        fusionBarriers: bc.barrierRefs,
        fuseBasicBlocks: true,
        sroaConfig,
        onPhase: (name, ms, meta) => { if (name === 'load/compose') diag = meta; },
      });
      const state = mde.normalizeQuery(calc.queries.get('symex'));
      const tree = calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true });
      const leaves = getAllLeaves(tree).filter(l => l.type === 'leaf');
      // Value-level leaf states (Store ids differ across the two loads).
      // Eigenvariables are compared MODULO RENAMING: SROA and fusion mint
      // different numbers of evars (SROA scalarizes, so it defers at different
      // points), so two alpha-equivalent symbolic states carry different
      // evar(N) ids. Canonicalize each state's evar ids to first-appearance
      // rank — the sound equivalence for symbolic execution with fresh
      // eigenvariables (TODO_0307 P3).
      const canonEvars = (s) => {
        const seen = new Map();
        return s.replace(/evar\((\d+)\)/g, (_, n) => {
          if (!seen.has(n)) seen.set(n, seen.size);
          return `evar(${seen.get(n)})`;
        });
      };
      const states = leaves.map(l =>
        canonEvars(Object.keys(toObject(l.state).linear).map(h => show(Number(h))).sort().join(' | '))
      ).sort();
      return { diag, states };
    }

    const on = arm(undefined); // default ILL_SROA_CONFIG via the calculus config
    const off = arm({ ...ILL_SROA_CONFIG, arrayPreds: [] }); // P6 neutered, fusion intact

    // Non-vacuity: SROA must actually have transformed rules in the ON
    // arm — a program where it fires zero times pins nothing.
    assert.ok(on.diag.sroaTransformed > 0,
      `SROA fired in the ON arm (sroaTransformed=${on.diag.sroaTransformed})`);
    assert.equal(off.diag.sroaTransformed, 0, 'OFF arm: SROA disabled');

    assert.equal(on.states.length, off.states.length, 'same leaf count');
    assert.deepEqual(on.states, off.states,
      'SROA-transformed and untransformed rule sets reach identical leaf-state sets');
  });
});
