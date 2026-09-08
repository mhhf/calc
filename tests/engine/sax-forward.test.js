/**
 * sax forward guard (TODO_0309 P1) — the SAX machine running SAX-NATIVE:
 * calculus/sax/programs/machine.sax under the sax config on the
 * unmodified generic engine, with the sax family's all-null engine
 * hooks (state-lookup-only persistent proving, no dynamic rules).
 *
 * The P0 encoding (tests/engine/sax-encoding.test.js, under plain ILL)
 * and this file pin the same dynamics from both sides of the family
 * boundary — the engine cannot tell the families apart.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert/strict';
import path from 'path';
import mde from '../../lib/engine/index.js';
import saxConfig from '../../calculus/sax/calculus-config.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { stateHashStr } from '../../lib/engine/explore.js';

const MACHINE = path.join(import.meta.dirname, '../../calculus/sax/programs/machine.sax');

describe('sax forward (TODO_0309 P1): sax-native machine', () => {
  let calc, parse;

  before(() => {
    calc = mde.load(MACHINE, { calculusConfig: saxConfig, cache: false });
    parse = (s) => mde.parseExpr(s, saxConfig.loader);
  });

  const initialOf = (facts) => mde.decomposeQuery(parse(facts));

  it('family record: sax with all-null engine hooks', () => {
    assert.equal(saxConfig.family.name, 'sax');
    for (const k of ['proveNaive', 'matchDynamicRule', 'drainDynamicRules', 'resolveEx']) {
      assert.equal(saxConfig.family.engine[k], null, `${k} must be null`);
    }
  });

  it('negation runs to quiescence with no linear residue', () => {
    const res = calc.exec(initialOf('!cell c vin1 * hole d * proc d (pcase c win2 win1)'), { maxSteps: 100 });
    assert.ok(res.quiescent);
    assert.ok(res.state.persistent[parse('cell d vin2')]);
    assert.deepEqual(res.state.linear, {});
  });

  it('swap is confluent sax-native: every interleaving, one final state', () => {
    const initial = initialOf(
      '!cell (p1 c) vin1 * !cell (p2 c) vin2 * !cell c vpair * ' +
      'hole d * hole (p1 d) * hole (p2 d) * ' +
      'proc d wpr * proc (p1 d) (fwd (p2 c)) * proc (p2 d) (fwd (p1 c))');
    const tree = calc.explore(initial, { maxDepth: 64 });
    const leaves = getAllLeaves(tree).filter(l => l.type === 'leaf');
    assert.ok(leaves.length > 1, 'multiple interleavings explored');
    const distinct = new Set(leaves.map(l => stateHashStr(toObject(l.state))));
    assert.equal(distinct.size, 1, 'confluent');
  });

  it('write-once violated is non-confluent sax-native (the control)', () => {
    const tree = calc.explore(initialOf('hole d * proc d win1 * proc d win2'), { maxDepth: 16 });
    const leaves = getAllLeaves(tree).filter(l => l.type === 'leaf');
    const distinct = new Set(leaves.map(l => stateHashStr(toObject(l.state))));
    assert.equal(distinct.size, 2, 'the race is observable');
  });
});
