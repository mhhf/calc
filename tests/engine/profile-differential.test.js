/**
 * Optimizer-profile differential (RES_0143 E2a).
 *
 * The opt/ boundary's contract: every optimization profile flag is
 * semantics-free — 'bare' (all optimizations off) must produce the same
 * exec results and the same explore leaf set as the all-on profile.
 * This turns the "engine is correct with every opt disabled" claim from
 * an audit statement into a standing gate.
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { show } from '../../lib/engine/show.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { stateHashStr } from '../../lib/engine/explore.js';

const EXEC_PROG =
  'pd_tok : bin -> type.\n' +
  'pd_out : bin -> type.\n' +
  'pd_gate : type.\n' +
  's1: pd_tok 1 -o { pd_tok 2 }.\n' +
  's2: pd_tok 2 -o { pd_tok 3 * pd_gate }.\n' +
  's3: pd_tok 3 * pd_gate -o { pd_out 3 }.\n' +
  '#symex pd_tok 1.\n';

const EXPLORE_PROG =
  'pd_coin : type.\n' +
  'pd_heads : type.\n' +
  'pd_tails : type.\n' +
  'pd_win : type.\n' +
  'flip: pd_coin -o { pd_heads + pd_tails }.\n' +
  'cash: pd_heads -o { pd_win }.\n' +
  '#symex pd_coin.\n';

function loadProg(text, profile) {
  Store.clear();
  const tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'profile-diff-'));
  const file = path.join(tmpDir, 'prog.ill');
  fs.writeFileSync(file, text);
  try {
    const calc = mde.load(file, { cache: false, profile });
    return { calc, state: mde.normalizeQuery(calc.queries.get('symex')) };
  } finally {
    for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
    fs.rmdirSync(tmpDir);
  }
}

describe('optimizer profile differential (RES_0143 E2a)', () => {
  it('exec: bare profile reaches the same final state as the all-on profile', () => {
    const results = {};
    for (const profile of ['bare', undefined]) {
      const { calc, state } = loadProg(EXEC_PROG, profile);
      const res = calc.exec(state, { maxSteps: 20 });
      results[profile || 'full'] = {
        quiescent: res.quiescent,
        final: Object.keys(res.state.linear).map(h => show(Number(h))).sort(),
      };
    }
    assert.deepEqual(results.bare, results.full,
      'bare and all-on profiles must agree on exec');
    assert.deepEqual(results.full.final, ['pd_out(0x3)']);
  });

  it('explore: bare profile reaches the same leaf set as the all-on profile', () => {
    const leafSets = {};
    for (const profile of ['bare', undefined]) {
      const { calc, state } = loadProg(EXPLORE_PROG, profile);
      const tree = calc.explore(state, { maxDepth: 16 });
      const leaves = getAllLeaves(tree).filter(l => l.type === 'leaf');
      // Value-level leaf fingerprints (Store ids differ across loads)
      leafSets[profile || 'full'] = leaves
        .map(l => Object.keys(toObject(l.state).linear || {})
          .map(h => show(Number(h))).sort().join(' | '))
        .sort();
    }
    assert.ok(leafSets.full.length >= 2, 'the choice actually branches');
    assert.deepEqual(leafSets.bare, leafSets.full,
      'bare and all-on profiles must agree on the explore leaf set');
  });
});
