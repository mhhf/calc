/**
 * G2 tell-consistency (THY_0039 §4, task #80).
 *
 * A forward rule's consequent may TELL a persistent theory-atom. When that
 * tell is a GROUND constraint atom the theory REFUTES — e.g. `!eq 1 0` — the
 * resulting leaf's denotation is ∅ (an infeasible path). Before this fix the
 * single-alt production path fed the atom into the accumulated constraint
 * solver but never consulted it, so exploration returned the leaf as a
 * reachable world (a "zombie"), and downstream `!eq 1 0` asks succeeded via
 * state-lookup of the false fact.
 *
 * The multi-alt (⊕) path already SAT-filtered its guards (satFilter tests each
 * alternative against the accumulated solver); only the single-alt tell path
 * skipped the check. The fix consults the already-fed solver after a single-alt
 * step and prunes the branch to a `dead` node when it is UNSAT — a sound
 * refinement of the denotation (never loss), gated so unflagged steps (the
 * whole hot path) pay nothing.
 *
 * SCOPE. The decidable fragment is the calculus's declared constraint
 * predicates (`cc.domain.constraintPreds` for ILL). Predicates the calculus
 * does NOT declare decidable are opaque assertions and are NEVER pruned
 * (soundness: no completeness loss).
 *
 * ORDER GUARDS (task #84, THY_0039 §4 residual (i)). The fragment extends
 * beyond eq/neq to the declared order guards (`constraintPreds.order`, lt/le
 * for ILL) INTERSECTED with the certified total decision procedures
 * (`calc.decidablePreds`, §6.1′). A ground order tell is decided by the SAME
 * evalNumeric ground short-circuit eq/neq use — direct value evaluation, NOT
 * clause resolution (a deep ground query false-fails under the backchainer's
 * depth cap, which would be unsound FFI-off). So the behaviour is identical
 * under FFI-off and FFI-on, and a symbolic order atom is opaque (survives).
 */
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { getAllLeaves } from '../../lib/engine/tree-utils.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { show } from '../../lib/engine/show.js';
import { EqNeqSolver } from '../../lib/engine/constraint.js';
import { binToInt, intToBin, isGround as _binIsGround } from '../../calculus/ill/lib/ffi/convert.js';

let tmpDir;
before(() => { tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'g2-')); });
after(() => {
  for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
  fs.rmdirSync(tmpDir);
});

const DECLS = `e : bin.
i : bin -> bin.
o : bin -> bin.
eq : (a: bin) -> (b: bin) -> type.
neq : (a: bin) -> (b: bin) -> type.
lt : (a: bin) -> (b: bin) -> type.
le : (a: bin) -> (b: bin) -> type.
`;

// Explore an inline program; return {live, dead} node counts and live-leaf
// linear facts, under a given FFI mode.
function classify(name, body, ffi) {
  const f = path.join(tmpDir, `${name}.ill`);
  fs.writeFileSync(f, DECLS + body);
  Store.clear();
  const calc = mde.load(f, { cache: false });
  const st = mde.normalizeQuery(calc.queries.get('symex'));
  const nodes = getAllLeaves(calc.explore(st, { maxDepth: 50, dangerouslyUseFFI: ffi }));
  const live = nodes.filter(n => n.type === 'leaf');
  const dead = nodes.filter(n => n.type === 'dead');
  const facts = live.map(n =>
    Object.keys((n.state.linear && n.state.linear.group ? toObject(n.state) : n.state).linear || {})
      .map(h => show(Number(h))).sort());
  return { live: live.length, dead: dead.length, facts };
}

// Run each case under both FFI-off (clause) and FFI-on — the tell path is
// resolver-independent, so behaviour must be identical.
const both = (name, body) => [false, true].map(ffi => classify(name, body, ffi));

describe('G2 tell-consistency — ground constraint tells are checked (THY_0039 §4)', () => {
  it('a false ground eq tell (!eq 1 0) is pruned to a dead node, not a live leaf', () => {
    for (const r of both('false_eq', `go:type.\nmid:type.\nbad: go -o { !eq (i e) e * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 0, 'no reachable world — the leaf denotes ∅');
      assert.equal(r.dead, 1, 'the infeasible branch is a pruned dead node');
    }
  });

  it('a false ground neq tell (!neq 1 1) is pruned', () => {
    for (const r of both('false_neq', `go:type.\nmid:type.\nbad: go -o { !neq (i e) (i e) * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 0);
      assert.equal(r.dead, 1);
    }
  });

  it('a TRUE ground tell (!neq 1 0, !eq 1 1) is NOT pruned — no over-pruning', () => {
    for (const r of both('true_neq', `go:type.\nmid:type.\nok: go -o { !neq (i e) e * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 1);
      assert.deepEqual(r.facts, [['mid']]);
    }
    for (const r of both('true_eq', `go:type.\nmid:type.\nok: go -o { !eq (i e) (i e) * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 1);
      assert.deepEqual(r.facts, [['mid']]);
    }
  });

  it('an opaque proposition told with contradictory-looking args is NEVER pruned (soundness boundary)', () => {
    // `foo` is not a declared constraint predicate — it carries no decidable
    // semantics, so telling `foo 1 0` is DEFINING it. Pruning it would be a
    // completeness failure. Only cc.domain.constraintPreds (eq/neq) are checked.
    for (const r of both('opaque', `go:type.\nmid:type.\nfoo:(a:bin)->(b:bin)->type.\nr: go -o { !foo (i e) e * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 1, 'undeclared predicate tell survives — never checked');
      assert.deepEqual(r.facts, [['mid']]);
    }
  });

  it('downstream corruption is eliminated: a zombie tell cannot feed a later false ask', () => {
    // bad tells the false `eq 1 0`; exploit ASKS `!eq 1 0` (unprovable — 1≠0).
    // Pre-fix, state-lookup of the zombie fact let exploit fire, fabricating
    // `exploited`. Post-fix the poisoning branch is pruned before exploit runs.
    const prog = `go:type.\nmid:type.\nexploited:type.\n` +
      `bad: go -o { !eq (i e) e * mid }.\n` +
      `exploit: mid * !eq (i e) e -o { exploited }.\n#symex go .\n`;
    for (const r of both('downstream', prog)) {
      assert.equal(r.live, 0, 'exploited is never a reachable world');
      assert.equal(r.dead, 1);
    }
  });

  it('multi-alt (⊕) guard pruning is preserved: a concrete guard resolves the branch', () => {
    // The pre-existing satFilter behaviour must be intact: with C = 1 the
    // `!eq 1 0` alternative is infeasible and only the `!neq 1 0` branch lives.
    const prog = `go:type.\na:type.\nb:type.\n` +
      `choose: go -o { (!eq (i e) e * a) + (!neq (i e) e * b) }.\n#symex go .\n`;
    for (const r of both('choose', prog)) {
      assert.equal(r.live, 1, 'only the feasible branch is a live world');
      assert.deepEqual(r.facts, [['b']]);
    }
  });
});

describe('G2 order-guard tells — certified decidable lt/le (task #84, §4 residual (i))', () => {
  it('a false ground lt tell (!lt 2 1) is pruned to a dead node', () => {
    for (const r of both('false_lt', `go:type.\nmid:type.\nbad: go -o { !lt (o (i e)) (i e) * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 0, 'no reachable world — 2 < 1 is false');
      assert.equal(r.dead, 1);
    }
  });

  it('a false ground le tell (!le 2 1) is pruned', () => {
    for (const r of both('false_le', `go:type.\nmid:type.\nbad: go -o { !le (o (i e)) (i e) * mid }.\n#symex go .\n`)) {
      assert.equal(r.live, 0);
      assert.equal(r.dead, 1);
    }
  });

  it('TRUE ground order tells (!lt 1 2, !le 1 1, !le 1 2) are NOT pruned', () => {
    for (const [nm, body] of [
      ['true_lt', `go:type.\nmid:type.\nok: go -o { !lt (i e) (o (i e)) * mid }.\n#symex go .\n`],
      ['true_le_eq', `go:type.\nmid:type.\nok: go -o { !le (i e) (i e) * mid }.\n#symex go .\n`],
      ['true_le_lt', `go:type.\nmid:type.\nok: go -o { !le (i e) (o (i e)) * mid }.\n#symex go .\n`],
    ]) {
      for (const r of both(nm, body)) {
        assert.equal(r.live, 1, `${nm}: the true order tell survives`);
        assert.deepEqual(r.facts, [['mid']]);
      }
    }
  });

  it('multi-alt (⊕): the false-lt alternative is filtered, only the feasible branch lives', () => {
    const prog = `go:type.\na:type.\nb:type.\n` +
      `choose: go -o { (!lt (o (i e)) (i e) * a) + (!lt (i e) (o (i e)) * b) }.\n#symex go .\n`;
    for (const r of both('choose_lt', prog)) {
      assert.equal(r.live, 1, 'only the 1 < 2 branch is a live world');
      assert.deepEqual(r.facts, [['b']]);
    }
  });
});

// ── Unit: the solver decides order guards by direct evaluation only ────
describe('EqNeqSolver — order guards are ground-decided, symbolic ones opaque', () => {
  const evalNumeric = (h) => (_binIsGround(h) ? binToInt(h) : null);
  const B = (n) => intToBin(BigInt(n));
  const order = { lt: '<', le: '<=' };
  const base = () => new EqNeqSolver({ evalNumeric, predNames: { eq: 'eq', neq: 'neq' }, order });

  it('a false ground order tell is UNSAT; a true one and a symbolic one are SAT', () => {
    let s = base(); // false: lt 2 1
    assert.equal(s.addConstraint(Store.put('lt', [B(2), B(1)])), true, 'ground order recognized');
    assert.equal(s.checkSAT(), false, '2 < 1 refutes the branch');

    s = base(); // true: lt 1 2
    assert.equal(s.addConstraint(Store.put('lt', [B(1), B(2)])), true);
    assert.equal(s.checkSAT(), true, '1 < 2 holds');

    s = base(); // symbolic: lt X 1 — a free metavar decodes to null → opaque
    const X = Store.put('metavar', ['X']);
    assert.equal(s.addConstraint(Store.put('lt', [X, B(1)])), false, 'symbolic order adds no constraint');
    assert.equal(s.checkSAT(), true, 'never pruned on a symbolic order atom');
  });

  it('an order predicate absent from the order map is unrecognized (opaque)', () => {
    const s = new EqNeqSolver({ evalNumeric, predNames: { eq: 'eq', neq: 'neq' }, order: { lt: '<' } });
    assert.equal(s.addConstraint(Store.put('le', [B(2), B(1)])), false, 'le not in the map → opaque');
    assert.equal(s.checkSAT(), true);
  });
});

// ── Corpus regression guard: real paths are never pruned ──────────────
const PROGRAMS = path.join(import.meta.dirname, '../../calculus/ill/programs');
describe('G2 — the real corpus carries only satisfiable guards (no false prune)', () => {
  it('deterministic multisig symex is unchanged: exactly one live leaf, zero dead', () => {
    for (const ffi of [false, true]) {
      Store.clear();
      const calc = mde.load(path.join(PROGRAMS, 'multisig_nocall_solc.ill'), { cache: false });
      const st = mde.normalizeQuery(calc.queries.get('symex'));
      const nodes = getAllLeaves(calc.explore(st, { maxDepth: 100000, dangerouslyUseFFI: ffi }));
      assert.equal(nodes.filter(n => n.type === 'leaf').length, 1, `one reachable state (ffi=${ffi})`);
      assert.equal(nodes.filter(n => n.type === 'dead').length, 0, `no branch pruned (ffi=${ffi})`);
    }
  });
});
