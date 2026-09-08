/**
 * Translation-covariance guard (TODO_0277 soundness audit) — covariance.js.
 *
 * Confirmed divergences pinned here:
 *  - rebase + ground `after N`: the state shifts, the compiled-in absolute
 *    bound does not — the rule fires B late in the rebased pipeline
 *    (repro: direct settle(3.5) fires `after 3`; rebased pipeline never).
 *  - rebase + ground `before N`: the shifted activation passes a deadline
 *    the absolute frame already closed.
 * Both now REFUSE loudly at settle entry. Covariant bounds (`Q + c`, shift
 * degree 1) keep rebasing; diagonal (`Q1 + Q2`, degree 2) and opaque
 * (persistent-fed) bounds are refused — the timed-automata diagonal-
 * constraint pitfall, mechanized (Bouyer et al. 2005 analog).
 */

import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import { loadTill, bagStr, initQuery } from './till-helpers.js';
import { ratParts } from '../../lib/kernel/rat-term.js';
import Store from '../../lib/kernel/store.js';

const RAT = path.resolve('calculus/till/prelude/rat.ill');
let _dir = null;
function prog(text, { rat = false } = {}) {
  if (!_dir) _dir = fs.mkdtempSync(path.join(os.tmpdir(), 'till-cov-'));
  const f = path.join(_dir, `p${fs.readdirSync(_dir).length}.ill`);
  fs.writeFileSync(f, (rat ? `#import(${RAT})\n\n` : '') + text);
  return loadTill(f);
}
const state = (...atoms) => {
  const linear = {};
  for (const a of atoms) {
    const h = Store.put('atom', [a]);
    linear[h] = (linear[h] || 0) + 1;
  }
  return { linear, persistent: {} };
};

describe('covariance — rebase refuses absolute-time programs', () => {
  it('ground after-bound: loud refusal (audit repro: rule fired B late)', () => {
    const calc = prog('aa: type.\nbb: type.\nr: aa * after 3 -o { bb }.\n');
    assert.throws(() => calc.settle(state('aa'), '2', { coalesce: true, rebase: true }),
      /rebase refused.*not translation-invariant/);
  });

  it('ground before-bound: loud refusal (audit repro: closed deadline reopened)', () => {
    const calc = prog('aa: type.\nbb: type.\nr: aa * before 3 -o { bb }.\n');
    assert.throws(() => calc.settle(state('aa'), '2', { coalesce: true, rebase: true }),
      /rebase refused/);
  });

  it('diagonal bound before (Q1+Q2): degree 2, refused', () => {
    const calc = prog('aa: type.\nbb: type.\ncc: type.\n' +
      'r: aa@Q1 * bb@Q2 * before (Q1 + Q2) -o { cc }.\n', { rat: true });
    assert.throws(() => calc.settle(state('aa'), '2', { coalesce: true, rebase: true }),
      /rebase refused/);
  });

  it('covariant bound after (Q+2): degree 1, rebase composability holds', () => {
    const calc = prog('aa: type.\nbb: type.\n' +
      'spawn: aa -o { aa * bb }@3.\n' +
      'decay: bb@Q * after (Q + 2) -o { I }.\n', { rat: true });
    const S = state('aa');
    const direct = calc.settle(S, '20', { coalesce: true }).state;
    const r1 = calc.settle(S, '7', { coalesce: true, rebase: true });
    const [n, d] = ratParts(r1.rebase);
    assert.equal(d, 1n, 'integral shift');
    assert.ok(n > 0n, 'a shift actually happened');
    const r2 = calc.settle(r1.state, String(20 - Number(n)), { coalesce: true });
    assert.equal(bagStr(r2.state), bagStr(direct));
  });

  it('consequent-embedded windowed rule: static refusal at entry', () => {
    const calc = prog('aa: type.\nbb: type.\n' +
      'mk: aa -o { (bb * before 100 -o { aa }) }@1.\n');
    assert.throws(() => calc.settle(state('aa'), '5', { coalesce: true, rebase: true }),
      /consequent-embedded rule or menu carries a window bound/);
  });

  it('dynamic guard: a possessed windowed rule in the STATE downgrades rebase to a no-op', () => {
    // Static rules are covariant; the initial state carries the windowed
    // loli directly. Entry passes; _rebaseNow refuses the shift (rebase 0).
    const calc = prog('aa: type.\nbb: type.\ncc: type.\n' +
      'tick: cc -o { cc }@1.\n' +
      '#expect_loli (settle: 5)\n' +
      '  (bb * before 100 -o { aa }) * cc\n' +
      '  =>\n' +
      '  cc .\n');
    const S = initQuery(calc, 'expect_loli');
    const r = calc.settle(S, '5', { coalesce: true, rebase: true });
    const [n, d] = ratParts(r.rebase);
    assert.equal(n, 0n, `windowed loli in state: shift must be 0, got ${n}/${d}`);
  });
});
