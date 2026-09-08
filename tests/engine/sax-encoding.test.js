/**
 * SAX-as-program (TODO_0309 P0) — the semi-axiomatic sequent calculus's
 * operational semantics encoded as ordinary ILL forward rules, run on the
 * UNMODIFIED generic engine under the plain ILL config.
 *
 * Encoding (DeYoung–Pfenning–Pruiksma FSCD 2020, Fig. 6, with SNAX
 * MFPS 2022 §3.2 addressing): destinations are terms, allocated-unwritten
 * cells are LINEAR `hole D` facts, filled cells are PERSISTENT
 * `!cell D V` facts (write-once, read-many), processes are LINEAR
 * `proc D P` facts. The FSCD values embed component ADDRESSES (which
 * needs binders in continuations); this encoding uses SNAX's locally
 * calculable projections instead — a pair's components live at `p1 D` /
 * `p2 D`, so every machine step is first-order and binder-free.
 *
 * Pins:
 *   - the SAX machine runs to quiescence on the forward engine
 *   - write-once synchronization: a reader blocks until its cell fills
 *   - CONFLUENCE, empirically: explore() over every interleaving of a
 *     concurrent configuration reaches ONE quiescent state (the diamond
 *     property, FSCD Thm. 10)
 *   - the discipline is load-bearing: violating write-once (two writers,
 *     one hole) is observably non-confluent — two distinct leaves
 */

import { describe, it, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import mde from '../../calculus/ill/index.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { stateHashStr } from '../../lib/engine/explore.js';

const MACHINE = `
% ── SAX machine: types ──────────────────────────────────────────────
dest: type.
pterm: type.

% SNAX projections: component addresses are calculable from the base
p1: dest -> dest.
p2: dest -> dest.

% values (markers; pair components live at the projections)
vpair: pterm.
vunit: pterm.
vin1: pterm.
vin2: pterm.

% process terms
wpr: pterm.                          % write a pair marker
wun: pterm.                          % write the unit marker
win1: pterm.                         % write left injection
win2: pterm.                         % write right injection
fwd: dest -> pterm.                  % identity: copy value from source cell
pcase: dest -> pterm -> pterm -> pterm.  % case on a sum cell

% configuration facts
proc: dest -> pterm -> type.         % ephemeral process (linear)
hole: dest -> type.                  % allocated, unwritten cell (linear)
cell: dest -> pterm -> type.         % filled cell (persistent, write-once)

% ── SAX machine: steps (FSCD Fig. 6 shape) ──────────────────────────
% writes consume the hole (write-once); reads are persistent lookups
sax/write_pair: proc D wpr * hole D -o { !cell D vpair }.
sax/write_unit: proc D wun * hole D -o { !cell D vunit }.
sax/write_in1:  proc D win1 * hole D -o { !cell D vin1 }.
sax/write_in2:  proc D win2 * hole D -o { !cell D vin2 }.
sax/forward:    proc D (fwd S) * !cell S W * hole D -o { !cell D W }.
sax/case_in1:   proc D (pcase S P1 P2) * !cell S vin1 -o { proc D P1 }.
sax/case_in2:   proc D (pcase S P1 P2) * !cell S vin2 -o { proc D P2 }.
`;

const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'sax-encoding-'));
after(() => fs.rmSync(tmp, { recursive: true, force: true }));

/** Load the machine as a fresh program; build an initial state from facts. */
function loadConfig(name, initialFacts) {
  const file = path.join(tmp, `${name}.ill`);
  fs.writeFileSync(file, MACHINE);
  const calc = mde.load(file, { cache: false });
  const initial = mde.decomposeQuery(mde.parseExpr(initialFacts));
  return { calc, initial };
}

const fact = (s) => mde.parseExpr(s);

/** Explore all interleavings; return deduped quiescent-leaf state strings. */
function leafStates(calc, initial, maxDepth = 64) {
  const tree = calc.explore(initial, { maxDepth });
  const leaves = getAllLeaves(tree);
  assert.ok(!leaves.some(l => l.type === 'bound'), 'no bound nodes (raise maxDepth)');
  const quiescent = leaves.filter(l => l.type === 'leaf');
  assert.ok(quiescent.length > 0, 'at least one quiescent leaf');
  return {
    distinct: new Set(quiescent.map(l => stateHashStr(toObject(l.state)))),
    count: quiescent.length,
  };
}

describe('SAX-as-program (TODO_0309 P0): forward encoding + empirical confluence', () => {
  it('negation: case selects the correct branch and writes through', () => {
    const { calc, initial } = loadConfig('neg',
      '!cell c vin1 * hole d * proc d (pcase c win2 win1)');
    const res = calc.exec(initial, { maxSteps: 100 });
    assert.ok(res.quiescent);
    assert.ok(res.state.persistent[fact('cell d vin2')], 'output cell d holds vin2');
    assert.deepEqual(res.state.linear, {}, 'no linear residue: hole consumed, proc consumed');
  });

  it('pipeline: a reader blocks until its input cell is written', () => {
    const { calc, initial } = loadConfig('pipe',
      '!cell c vin1 * hole m * proc m (pcase c win2 win1) * hole d * proc d (pcase m win2 win1)');
    const res = calc.exec(initial, { maxSteps: 100 });
    assert.ok(res.quiescent);
    assert.ok(res.state.persistent[fact('cell m vin2')], 'stage 1: m = ¬c = vin2');
    assert.ok(res.state.persistent[fact('cell d vin1')], 'stage 2: d = ¬m = vin1');
    assert.deepEqual(res.state.linear, {}, 'both stages ran to completion');
  });

  it('swap: 3 concurrent processes — every interleaving reaches ONE state', () => {
    const { calc, initial } = loadConfig('swap',
      '!cell (p1 c) vin1 * !cell (p2 c) vin2 * !cell c vpair * ' +
      'hole d * hole (p1 d) * hole (p2 d) * ' +
      'proc d wpr * proc (p1 d) (fwd (p2 c)) * proc (p2 d) (fwd (p1 c))');
    const { distinct, count } = leafStates(calc, initial);
    assert.equal(distinct.size, 1, `confluent: one quiescent state (got ${distinct.size})`);
    assert.ok(count > 1, `explore visited multiple interleavings (got ${count})`);
    // and the one state is the swapped pair
    const res = calc.exec(initial, { maxSteps: 100 });
    assert.ok(res.state.persistent[fact('cell d vpair')]);
    assert.ok(res.state.persistent[fact('cell (p1 d) vin2')], 'p1 d = old p2 c');
    assert.ok(res.state.persistent[fact('cell (p2 d) vin1')], 'p2 d = old p1 c');
  });

  it('swap ∥ pipeline: independent programs interleave confluently', () => {
    const { calc, initial } = loadConfig('par',
      '!cell (p1 c) vin1 * !cell (p2 c) vin2 * !cell c vpair * ' +
      'hole d * hole (p1 d) * hole (p2 d) * ' +
      'proc d wpr * proc (p1 d) (fwd (p2 c)) * proc (p2 d) (fwd (p1 c)) * ' +
      'hole m * proc m (pcase (p1 c) win2 win1) * hole e * proc e (pcase m win2 win1)');
    const { distinct } = leafStates(calc, initial, 128);
    assert.equal(distinct.size, 1, 'confluent across both programs');
  });

  it('write-once violated (two writers, one hole) is NOT confluent — the control', () => {
    const { calc, initial } = loadConfig('race',
      'hole d * proc d win1 * proc d win2');
    const { distinct } = leafStates(calc, initial);
    assert.equal(distinct.size, 2, 'the race is observable: two distinct final states');
  });
});
