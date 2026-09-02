/**
 * TODO_0216 Phase 0 H3 — pool-invariant assertion stub verification
 *
 * Proves:
 *   • default (flag off): assertion is a no-op — existing fusions succeed
 *     with rules that carry no meta.disjointInPool.
 *   • CALC_POOL_DISJOINT='strict' (flag on): assertion throws on untagged
 *     rules (this is the contract B will depend on in Phase 4).
 *
 * The "strict" case runs the assertion in a child process so the flag is
 * set before module load.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import { execFileSync } from 'child_process';
import Store from '../../lib/kernel/store.js';
// Hoisted by tools/esm-hoist.js:
import mde from '../../calculus/ill/index.js';
import ccfg from '../../calculus/ill/calculus-config.js';
import { resolveConn } from '../../lib/engine/compile.js';
import { fusePair as _fusePair } from '../../lib/engine/compose.js';
import { monadUnit as U } from '../../lib/engine/grades.js';
import { loadILL } from '../../calculus/ill/index.js';

describe('TODO_0216 H3 — pool-disjoint assertion stub', () => {
  let fusePair, rc;

  before(() => {
    Store.clear();
    delete process.env.CALC_POOL_DISJOINT; // ensure flag off in-process

    mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill'), { cache: true });


    rc = resolveConn(ccfg.connectives);
    fusePair = _fusePair;
  });

  it('no-op when CALC_POOL_DISJOINT unset (default): fusion succeeds without meta tag', () => {
    const a = Store.put('atom', ['a']);
    const mvX = Store.put('metavar', ['X']);
    const mvY = Store.put('metavar', ['Y']);
    const producer = {
      name: 'p', // no .meta
      hash: Store.put('loli', [
        Store.put('gas', [a]),
        Store.put('monad', [U(), Store.put('pc', [mvX])]),
      ]),
    };
    const consumer = {
      name: 'c',
      hash: Store.put('loli', [
        Store.put('pc', [mvY]),
        Store.put('monad', [U(), Store.put('stack', [mvY])]),
      ]),
    };
    // Should succeed with no assertion fire.
    const r = fusePair(producer, consumer, 'pc', rc, null);
    assert.ok(r, 'fusion with no disjointInPool tag should still succeed when flag is off');
  });

  it('strict mode: untagged rule in a fresh child process triggers the assertion', () => {
    // Run a one-off script with CALC_POOL_DISJOINT=strict and verify the
    // assertion fires when fusePair is called with an untagged rule.
    const script = `
    (async () => {

      const Store = (await import('file://${path.resolve(import.meta.dirname, '../../lib/kernel/store.js').replace(/\\\\/g, '/')}')).default;
      const { loadILL } = await import('file://${path.resolve(import.meta.dirname, '../../calculus/ill/index.js').replace(/\\\\/g, '/')}');
      loadILL();
      const ccfg = (await import('file://${path.resolve(import.meta.dirname, '../../calculus/ill/calculus-config.js').replace(/\\\\/g, '/')}')).default;
      const { resolveConn } = await import('file://${path.resolve(import.meta.dirname, '../../lib/engine/compile.js').replace(/\\\\/g, '/')}');
      const { fusePair } = await import('file://${path.resolve(import.meta.dirname, '../../lib/engine/compose.js').replace(/\\\\/g, '/')}');
      const rc = resolveConn(ccfg.connectives);
      const a = Store.put('atom', ['a']);
      const mvX = Store.put('metavar', ['X']);
      const mvY = Store.put('metavar', ['Y']);
      const producer = {
        name: 'p',
        hash: Store.put('loli', [Store.put('gas', [a]), Store.put('monad', [Store.put('binlit', [0n]), Store.put('pc', [mvX])])]),
      };
      const consumer = {
        name: 'c',
        hash: Store.put('loli', [Store.put('pc', [mvY]), Store.put('monad', [Store.put('binlit', [0n]), Store.put('stack', [mvY])])]),
      };
      try {
        fusePair(producer, consumer, 'pc', rc, null);
        console.log('OK_NO_THROW');
      } catch (e) {
        if (/Pool-invariant is violated/.test(e.message)) {
          console.log('OK_ASSERTED');
        } else {
          console.log('BAD: ' + e.message);
        }
      }
    })();
    `;
    const out = execFileSync(process.execPath, ['--input-type=module', '-e', script], {
      env: { ...process.env, CALC_POOL_DISJOINT: 'strict' },
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    assert.match(out, /OK_ASSERTED/,
      `expected assertion fire, got: ${out.trim()}`);
  });

  it('strict mode: tagged rule (meta.disjointInPool=true) passes without throwing', () => {
    const script = `
    (async () => {

      const Store = (await import('file://${path.resolve(import.meta.dirname, '../../lib/kernel/store.js').replace(/\\\\/g, '/')}')).default;
      const { loadILL } = await import('file://${path.resolve(import.meta.dirname, '../../calculus/ill/index.js').replace(/\\\\/g, '/')}');
      loadILL();
      const ccfg = (await import('file://${path.resolve(import.meta.dirname, '../../calculus/ill/calculus-config.js').replace(/\\\\/g, '/')}')).default;
      const { resolveConn } = await import('file://${path.resolve(import.meta.dirname, '../../lib/engine/compile.js').replace(/\\\\/g, '/')}');
      const { fusePair } = await import('file://${path.resolve(import.meta.dirname, '../../lib/engine/compose.js').replace(/\\\\/g, '/')}');
      const rc = resolveConn(ccfg.connectives);
      const a = Store.put('atom', ['a']);
      const mvX = Store.put('metavar', ['X']);
      const mvY = Store.put('metavar', ['Y']);
      const producer = {
        name: 'p',
        meta: { disjointInPool: true },
        hash: Store.put('loli', [Store.put('gas', [a]), Store.put('monad', [Store.put('binlit', [0n]), Store.put('pc', [mvX])])]),
      };
      const consumer = {
        name: 'c',
        hash: Store.put('loli', [Store.put('pc', [mvY]), Store.put('monad', [Store.put('binlit', [0n]), Store.put('stack', [mvY])])]),
      };
      try {
        const r = fusePair(producer, consumer, 'pc', rc, null);
        console.log(r ? 'OK_FUSED' : 'OK_NULL');
      } catch (e) {
        console.log('BAD: ' + e.message);
      }
    })();
    `;
    const out = execFileSync(process.execPath, ['--input-type=module', '-e', script], {
      env: { ...process.env, CALC_POOL_DISJOINT: 'strict' },
      encoding: 'utf8',
      stdio: ['ignore', 'pipe', 'pipe'],
    });
    assert.match(out, /OK_FUSED/, `expected fusion success, got: ${out.trim()}`);
  });
});
