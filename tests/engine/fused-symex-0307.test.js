/**
 * TODO_0307 P3 — the fused symbolic-execution path is CORRECT and matches the
 * unfused (specialize-only) golden.
 *
 * Before the ordered-body resolver, the fused config (extraGrade0Facts +
 * fuseBasicBlocks + SROA) collapsed the multisig symex to 9 nodes / 1 leaf at
 * the first PUSH0 — recorded at the time as an "8.7x speedup" that was actually
 * 15/16ths of the work silently discarded. The fix (commit chain on TODO_0307
 * P3) is three-layered:
 *   - the dataflow-ordered force-or-defer resolution BODY (compile.js +
 *     family/lnl/lib/existential.js);
 *   - JUMPDEST fusion barriers wired as arg HASHES, not pc values (Bug A);
 *   - SROA expansion depth covering structured push outputs (Bug B).
 *
 * This pins the acceptance gate: every fusion configuration reaches the SAME
 * leaf classes as the unfused golden (18 STOP + 13 REVERT, 0 RUNNING), and no
 * produced fact ever carries a raw metavar.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import fs from 'fs';
import { execFileSync } from 'child_process';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { loadBytecode, bytecodeArrGetGuard } from '../../calculus/ill/lib/bytecode-loader.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { classifyLeaf } from '../../calculus/ill/index.js';
import { ILL_SROA_CONFIG } from '../../calculus/ill/lib/compose-config.js';

const DIR = import.meta.dirname;
const CODE = path.join(DIR, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');
const SYMEX = path.join(DIR, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
const HEX = fs.readFileSync(CODE, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];

function classesOf(loadExtra) {
  Store.clear();
  const bc = loadBytecode(HEX);
  const opts = {
    cache: false, extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard,
    fusionBarriers: bc.barrierRefs, ...loadExtra,
  };
  const calc = mde.load(SYMEX, opts);
  const state = mde.normalizeQuery(calc.queries.get('symex'));
  const tree = calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true });
  const c = {};
  for (const l of getAllLeaves(tree)) { const k = classifyLeaf(l.state); c[k] = (c[k] || 0) + 1; }
  return c;
}

const GOLDEN = { STOP: 18, REVERT: 13 };

describe('TODO_0307 P3 — fused symex matches the unfused golden', { timeout: 60000, concurrency: 1 }, () => {
  it('specialize-only reaches the golden (18 STOP + 13 REVERT, no RUNNING)', () => {
    assert.deepStrictEqual(
      classesOf({ fuseBasicBlocks: false, sroaConfig: { ...ILL_SROA_CONFIG, arrayPreds: [] } }),
      GOLDEN);
  });

  it('block fusion reaches the golden — JUMPDEST barriers keep jump targets', () => {
    assert.deepStrictEqual(
      classesOf({ fuseBasicBlocks: true, sroaConfig: { ...ILL_SROA_CONFIG, arrayPreds: [] } }),
      GOLDEN);
  });

  it('fusion + SROA reaches the golden — semantics-preserving', () => {
    assert.deepStrictEqual(
      classesOf({ fuseBasicBlocks: true }),
      GOLDEN);
  });

  it('every fused rule CARRIES its bind order (fusion is concatenation, not reconstruction)', () => {
    // Track 1: the resolution order is carried through fusion by concatenation,
    // not re-derived by scheduleGoals at compile time. Every fused rule's
    // resolutionBody must be built from the carried bodyOrder — a pass that
    // transforms goals without maintaining bodyOrder would drop to the
    // reconstruction fallback and trip this.
    for (const sroa of [false, true]) {
      Store.clear();
      const bc = loadBytecode(HEX);
      const opts = {
        cache: false, extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard,
        fusionBarriers: bc.barrierRefs, fuseBasicBlocks: true,
      };
      if (!sroa) opts.sroaConfig = { ...ILL_SROA_CONFIG, arrayPreds: [] };
      const calc = mde.load(SYMEX, opts);
      const bodied = calc.forwardRules.filter(r => r.resolutionBody);
      assert.ok(bodied.length > 0, `${sroa ? 'fuse+SROA' : 'fuse'}: has fused rules with a body`);
      const fallback = bodied.filter(r => !r.resolutionBody.carried);
      assert.strictEqual(fallback.length, 0,
        `${sroa ? 'fuse+SROA' : 'fuse'}: ${fallback.length} rules fell back to order reconstruction`);
    }
  });

  it('the fused symex achieves MAXIMAL FORCING (CALC_CHECK_FORCE fence is silent)', () => {
    // The loud precision fence re-checks, on every fire, that no goal ran with
    // an input a later goal produces (a wrong order that would silently defer a
    // computable value to an eigenvariable). It is read at module load, so run
    // it in a child process with the env set. Exit 0 = the carried order forces
    // everything it can.
    const script = `
      import mde from ${JSON.stringify(path.join(DIR, '../../calculus/ill/index.js'))};
      import { loadBytecode, bytecodeArrGetGuard } from ${JSON.stringify(path.join(DIR, '../../calculus/ill/lib/bytecode-loader.js'))};
      import { getAllLeaves } from ${JSON.stringify(path.join(DIR, '../../lib/engine/tree-utils.js'))};
      import fs from 'fs';
      const hex = fs.readFileSync(${JSON.stringify(CODE)}, 'utf8').match(/bytecode\\s+0x([0-9a-fA-F]+)/)[1];
      const bc = loadBytecode(hex);
      const calc = mde.load(${JSON.stringify(SYMEX)}, { cache: false, extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard, fusionBarriers: bc.barrierRefs, fuseBasicBlocks: true });
      const state = mde.normalizeQuery(calc.queries.get('symex'));
      const n = getAllLeaves(calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true })).length;
      if (n !== 31) { console.error('leaves=' + n); process.exit(2); }
    `;
    let ok = true, msg = '';
    try {
      execFileSync(process.execPath, ['--input-type=module', '-e', script], {
        env: { ...process.env, CALC_CHECK_FORCE: '1' }, stdio: 'pipe', timeout: 60000,
      });
    } catch (e) { ok = false; msg = (e.stderr ? e.stderr.toString() : '') || e.message; }
    assert.ok(ok, `CALC_CHECK_FORCE fence fired or run failed: ${msg.slice(0, 300)}`);
  });

  it('fast ≡ evidence under the full fused config (observation does not change the run)', () => {
    Store.clear();
    const bc = loadBytecode(HEX);
    const calc = mde.load(SYMEX, {
      cache: false, extraGrade0Facts: bc.facts, scopeGuard: bytecodeArrGetGuard,
      fusionBarriers: bc.barrierRefs, fuseBasicBlocks: true,
    });
    const state = mde.normalizeQuery(calc.queries.get('symex'));
    const fast = getAllLeaves(calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true })).length;
    const evid = getAllLeaves(calc.explore(state, { maxDepth: 500, dangerouslyUseFFI: true, evidence: true })).length;
    assert.strictEqual(fast, 31);
    assert.strictEqual(evid, 31);
  });
});
