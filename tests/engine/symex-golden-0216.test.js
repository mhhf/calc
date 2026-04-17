/**
 * TODO_0216 Phase 0 H8 — Multisig symex golden canary
 *
 * Catches silent correctness regressions across every phase of
 * TODO_0216 by fingerprinting the exploration of
 *   calculus/ill/programs/multisig_nocall_solc_symbolic.ill
 *
 * Canaries:
 *   • total node count
 *   • total leaf count
 *   • sorted classifyLeaf multiset
 *   • sha256 of the sorted leaf-signature set (type + classifyLeaf
 *     + showInteresting excluding bytecode/calldata)
 *
 * Baseline stored in tests/fixtures/0216-multisig-golden.json.
 *
 * Regeneration: delete the fixture, re-run, inspect, commit.
 */

const { describe, it, before } = require('node:test');
const assert = require('node:assert');
const path = require('path');
const fs = require('fs');
const crypto = require('crypto');

const mde = require('../../lib/engine');
const Store = require('../../lib/kernel/store');
const { getAllLeaves, countNodes } = require('../../lib/engine/tree-utils');
const { classifyLeaf, showInteresting } = require('../../lib/engine/show');

const FIXTURE_PATH = path.join(__dirname, '../fixtures/0216-multisig-golden.json');
const PROGRAM = path.join(__dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');

function leafSignature(leaf) {
  const cls = classifyLeaf(leaf.state);
  const facts = showInteresting(leaf.state).slice().sort();
  return { type: leaf.type, cls, facts };
}

function fingerprint(tree) {
  const nodeCount = countNodes(tree);
  const leaves = getAllLeaves(tree);
  const sigs = leaves.map(leafSignature);
  // Stable sort by the JSON form — content-addressed hashes can vary by run,
  // but the rendered text is deterministic.
  const sorted = sigs
    .map(s => JSON.stringify(s))
    .sort();
  const classMultiset = {};
  for (const s of sigs) {
    classMultiset[s.cls] = (classMultiset[s.cls] || 0) + 1;
  }
  const sha = crypto.createHash('sha256').update(sorted.join('\n')).digest('hex');
  return { nodeCount, leafCount: leaves.length, classMultiset, sha };
}

describe('TODO_0216 H8 — multisig symex golden canary', { timeout: 60000, concurrency: 1 }, () => {
  let fp;

  before(async () => {
    Store.clear();
    const calc = await mde.load(PROGRAM);
    const state = mde.decomposeQuery(calc.queries.get('symex'));
    const tree = calc.explore(state, {
      maxDepth: 500,
      structuralMemo: false,
      dangerouslyUseFFI: true,
    });
    fp = fingerprint(tree);

    if (!fs.existsSync(FIXTURE_PATH)) {
      // Seed baseline (first run only).
      fs.mkdirSync(path.dirname(FIXTURE_PATH), { recursive: true });
      fs.writeFileSync(FIXTURE_PATH, JSON.stringify({
        schema: '0216-multisig-golden/v1',
        seeded: new Date().toISOString(),
        note: 'TODO_0216 Phase 0 H8. Delete and re-run to regenerate.',
        ...fp,
      }, null, 2) + '\n');
    }
  });

  it('matches golden fingerprint', () => {
    const golden = JSON.parse(fs.readFileSync(FIXTURE_PATH, 'utf8'));
    assert.strictEqual(fp.nodeCount, golden.nodeCount,
      `nodeCount drift: ${fp.nodeCount} vs ${golden.nodeCount}`);
    assert.strictEqual(fp.leafCount, golden.leafCount,
      `leafCount drift: ${fp.leafCount} vs ${golden.leafCount}`);
    assert.deepStrictEqual(fp.classMultiset, golden.classMultiset,
      'classifyLeaf multiset drift');
    assert.strictEqual(fp.sha, golden.sha,
      `leaf-signature sha drift: ${fp.sha} vs ${golden.sha}`);
  });
});
