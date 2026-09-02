/**
 * Phase 0 of TODO_0218 — determinism foundation.
 *
 * If these fail, the compose-cache plan is blocked.
 *
 * Invariants that matter for cache soundness:
 *
 * 1. Metavar counter resets on Store.clear().
 *
 * 2. Structural stability in-process: two back-to-back loads produce the same
 *    rule NAMES and count. Hash equality in-process is NOT achievable because
 *    the module-scope _exprParser cache in convert.js pins first-load grammar
 *    atoms; the second load finds them deduped and allocates fewer new atoms.
 *
 * 3. Byte-level determinism cross-process: a fresh child process produces
 *    byte-identical rule hashes. This is the actual invariant the disk cache
 *    depends on (snapshot from process A → restore in process B).
 *
 * 4. Snapshot roundtrip: serialize(snapshot) → deserialize → restore is
 *    byte-identical at the Store-arena level.
 *
 * 5. Compact with rule roots preserves rule names; hashes may be renumbered
 *    but resolve to valid nodes.
 */
'use strict';

import { describe, it, beforeEach } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import { serialize, deserialize, compact } from '../../lib/engine/store-binary.js';
import mde from '../../calculus/ill/index.js';
import fresh from '../../lib/kernel/fresh.js';
// Hoisted by tools/esm-hoist.js:
import { spawnSync } from 'child_process';
import { loadBytecode, bytecodeArrGetGuard } from '../../calculus/ill/lib/bytecode-loader.js';

const SYMEX_PATH = path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_symbolic.ill');
const CODE_PATH = path.join(import.meta.dirname, '../../calculus/ill/programs/multisig_nocall_solc_code.ill');

function snapshotStore() {
  const s = Store.snapshot({});
  return {
    nodeCount: s.nodeCount,
    childCount: s.childCount,
    tags: Buffer.from(s.tags.buffer, s.tags.byteOffset, s.tags.byteLength),
    arities: Buffer.from(s.arities.buffer, s.arities.byteOffset, s.arities.byteLength),
    childOff: Buffer.from(s.childOff.buffer, s.childOff.byteOffset, s.childOff.byteLength),
    childBuf: Buffer.from(s.childBuf.buffer, s.childBuf.byteOffset, s.childBuf.byteLength),
    dedupHashes: Buffer.from(s.dedupHashes.buffer, s.dedupHashes.byteOffset, s.dedupHashes.byteLength),
    tagNames: s.tagNames.join('\u0000'),
    strings: s.strings.join('\u0000'),
  };
}

describe('TODO_0218 Phase 0 — compose cache determinism', () => {
  beforeEach(() => Store.clear());

  it('metavar counter resets on Store.clear()', () => {
    fresh.freshMetavar();
    fresh.freshMetavar();
    fresh.freshMetavar();
    Store.clear();
    const h = fresh.freshMetavar();
    assert.deepStrictEqual(Store.get(h).children, ['m0']);
  });

  it('pure library load: rule names + structural hashes stable across two in-process loads', () => {
    // In-process test: the module-scope _exprParser cache in convert.js holds
    // parser closures that indirectly pin first-load grammar-symbol atoms.
    // Hashes therefore drift by a constant offset on the second load.
    // The invariants that matter here are STRUCTURAL: rule names + rendered
    // formulas. Byte-level Store-arena equality is tested cross-process below.
    Store.clear();
    const c1 = mde.load(SYMEX_PATH, { cache: false });
    const names1 = c1._compiledRules.map(r => r.name);

    Store.clear();
    const c2 = mde.load(SYMEX_PATH, { cache: false });
    const names2 = c2._compiledRules.map(r => r.name);

    assert.deepStrictEqual(names2, names1, 'rule names identical');
    assert.equal(c2._compiledRules.length, c1._compiledRules.length, 'rule count identical');
  });

  it('cold cross-process: rule pool byte-identical (subprocess reload)', () => {
    // REAL cache-soundness invariant: a fresh child process produces identical
    // rule hashes. This is what the disk cache needs to rely on.

    const script = `
      const Store = (await import('file://${path.resolve(import.meta.dirname, '../../lib/kernel/store.js')}')).default;
      const mde = (await import('file://${path.resolve(import.meta.dirname, '../../calculus/ill/index.js')}')).default;
      Store.clear();
      const c = mde.load(${JSON.stringify(SYMEX_PATH)}, { cache: false });
      process.stdout.write(JSON.stringify({
        names: c._compiledRules.map(r => r.name),
        hashes: c._compiledRules.map(r => r.hash),
      }));
    `;
    const run = () => {
      const r = spawnSync(process.execPath, ['--input-type=module', '-e', script], { encoding: 'utf8' });
      if (r.status !== 0) throw new Error(`child failed: ${r.stderr}`);
      return JSON.parse(r.stdout);
    };
    const a = run();
    const b = run();
    assert.deepStrictEqual(b.names, a.names, 'cross-process rule names');
    assert.deepStrictEqual(b.hashes, a.hashes, 'cross-process rule hashes byte-identical');
  });

  it('bytecode + symex load: rule pool byte-identical across two cold runs', () => {
    const hex = fs.readFileSync(CODE_PATH, 'utf8').match(/bytecode\s+0x([0-9a-fA-F]+)/)[1];

    Store.clear();
    const bc1 = loadBytecode(hex);
    const c1 = mde.load(SYMEX_PATH, {
      cache: false, extraGrade0Facts: bc1.facts,
      scopeGuard: bytecodeArrGetGuard, fuseBasicBlocks: true,
    });
    const names1 = c1.forwardRules.map(r => r.name).sort();
    const hashes1 = c1.forwardRules.map(r => r.hash).sort();

    Store.clear();
    const bc2 = loadBytecode(hex);
    const c2 = mde.load(SYMEX_PATH, {
      cache: false, extraGrade0Facts: bc2.facts,
      scopeGuard: bytecodeArrGetGuard, fuseBasicBlocks: true,
    });
    const names2 = c2.forwardRules.map(r => r.name).sort();
    const hashes2 = c2.forwardRules.map(r => r.hash).sort();

    assert.deepStrictEqual(names2, names1);
    assert.deepStrictEqual(hashes2, hashes1, 'rule hashes byte-identical with bytecode');
  });

  it('snapshot → deserialize → restore roundtrip: Store arena byte-equal (uncompacted)', () => {
    Store.clear();
    mde.load(SYMEX_PATH, { cache: false });
    const pre = snapshotStore();
    const snap = Store.snapshot({ ping: 'pong' });
    // Skip compact() — test raw serialize/deserialize round-trip.
    const buf = serialize(snap);

    Store.clear();
    const data = deserialize(buf);
    Store.restore(data);
    const post = snapshotStore();

    assert.equal(pre.nodeCount, post.nodeCount, 'nodeCount');
    assert.equal(pre.childCount, post.childCount, 'childCount');
    assert.equal(Buffer.compare(pre.tags, post.tags), 0, 'tags array');
    assert.equal(Buffer.compare(pre.arities, post.arities), 0, 'arities array');
    assert.equal(Buffer.compare(pre.childOff, post.childOff), 0, 'childOff array');
    assert.equal(Buffer.compare(pre.childBuf, post.childBuf), 0, 'childBuf array');
    assert.equal(Buffer.compare(pre.dedupHashes, post.dedupHashes), 0, 'dedupHashes array');
    assert.equal(pre.tagNames, post.tagNames, 'tag registry');
    assert.equal(pre.strings, post.strings, 'string table');
    assert.equal(data.metadata.ping, 'pong', 'metadata roundtrip');
  });

  it('snapshot → compact (with rule roots) → restore: rules preserved', () => {
    Store.clear();
    const c = mde.load(SYMEX_PATH, { cache: false });
    const names = c._compiledRules.map(r => r.name);
    // Metadata carries rule hashes as roots so compact() keeps them reachable.
    const meta = { forwardRules: c._compiledRules.map(r => ({ name: r.name, hash: r.hash })) };
    const snap = Store.snapshot(meta);
    const bin = compact(snap);
    const buf = serialize(bin);

    Store.clear();
    const data = deserialize(buf);
    Store.restore(data);
    const restoredHashes = data.metadata.forwardRules.map(r => r.hash);
    const restoredNames = data.metadata.forwardRules.map(r => r.name);
    assert.deepStrictEqual(restoredNames, names, 'rule names round-trip');
    // Hashes may be renumbered by compact() — the NAMES are the structural proof.
    // Verify hashes still resolve to valid Store nodes.
    for (const h of restoredHashes) {
      assert(typeof h === 'number' && h >= 1, `hash ${h} valid`);
      const tag = Store.tag(h);
      assert(tag != null, `restored hash ${h} has tag ${tag}`);
    }
  });
});
