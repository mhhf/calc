/**
 * Forward execution-tree checker (TODO_0045, THY_0035).
 *
 * The forward twin of the backward kernel: explore() builds an execution
 * tree T for Σ; Δ ⊢_fwd T, and lib/prover/forward-check.js re-derives every
 * firing from the PROGRAM rule data (θ the only witness) while threading the
 * linear multiset Δ and the persistent set Φ. These pins establish the
 * checker has teeth — a sound tree certifies, a tampered one is rejected —
 * and that certification is resolver-independent (FFI-off ≡ FFI-on).
 */
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { toObject } from '../../lib/engine/fact-set.js';
import { programFromCalc } from '../../lib/prover/timed/elaborate-trace.js';
import { checkForwardTree } from '../../lib/prover/forward-check.js';

let tmpDir;
before(() => { tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'fwdcheck-')); });
after(() => {
  for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
  fs.rmdirSync(tmpDir);
});

const DECLS = `e : bin.
i : bin -> bin.
o : bin -> bin.
eq : (a: bin) -> (b: bin) -> type.
neq : (a: bin) -> (b: bin) -> type.
`;

// Load an inline program, explore from #symex with evidence, and return the
// pieces the pure checker needs: the normalized tree + program record.
function setup(name, body, { ffi = false } = {}) {
  const f = path.join(tmpDir, `${name}.ill`);
  fs.writeFileSync(f, DECLS + body);
  Store.clear();
  const calc = mde.load(f, { cache: false });
  const st = mde.normalizeQuery(calc.queries.get('symex'));
  const initial = st.linear && st.linear.group ? toObject(st) : st;
  const tree = calc.explore(st, { maxDepth: 50, evidence: true, dangerouslyUseFFI: ffi });
  // normalize terminal engine States → plain objects (the checker is fenced)
  const norm = (node) => {
    if (!node) return;
    if (node.type === 'branch') { (node.children || []).forEach(e => norm(e.child)); return; }
    if (node.state && node.state.linear && node.state.linear.group) node.state = toObject(node.state);
  };
  norm(tree);
  const program = programFromCalc(calc);
  return { calc, tree, program, roles: calc.roles, initial };
}

const check = ({ tree, program, roles, initial, calc }) =>
  checkForwardTree(tree, { program, roles, initial, canonicalize: calc.canonicalize });

describe('forward-check — sound trees certify (TODO_0045)', () => {
  it('a deterministic linear chain a→b→c certifies with one leaf', () => {
    const s = setup('chain', `go:type.\nb:type.\nc:type.\n` +
      `r1: go -o { b }.\nr2: b -o { c }.\n#symex go .\n`);
    const r = check(s);
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.leaves, 1);
    assert.equal(r.unsupported, undefined);
  });

  it('a ⊕ fork explores both alternatives — two certified leaves', () => {
    const s = setup('fork', `go:type.\na:type.\nb:type.\n` +
      `r: go -o { a + b }.\n#symex go .\n`);
    const r = check(s);
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.leaves, 2);
  });

  it('rule nondeterminism (two rules fire) certifies every branch', () => {
    const s = setup('branch', `go:type.\na:type.\nb:type.\n` +
      `r1: go -o { a }.\nr2: go -o { b }.\n#symex go .\n`);
    const r = check(s);
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.leaves, 2);
  });

  it('persistent production then a Φ-membership guard certifies', () => {
    // r1 produces the persistent fact !k (grows Φ); r2 guards on it. Threads
    // both persistent production and the membership check.
    const s = setup('guard', `go:type.\nmid:type.\ndone:type.\nk:type.\n` +
      `r1: go -o { !k * mid }.\nr2: mid * !k -o { done }.\n#symex go .\n`);
    const r = check(s);
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.leaves, 1);
  });
});

describe('forward-check — the checker has teeth (soundness)', () => {
  // Build a valid tree, then tamper it and assert rejection.
  const clone = (t) => structuredClone(t);
  const firstEdge = (tree) => tree.children[0];

  it('a step whose θ consumes an absent fact is rejected', () => {
    const s = setup('t_consume', `go:type.\nb:type.\n` +
      `r: go -o { b }.\n#symex go .\n`);
    assert.equal(check(s).valid, true);
    const tree = clone(s.tree);
    // corrupt θ: point the (empty-θ here) — instead corrupt by injecting a
    // bogus consume via a fake loli token the state does not hold.
    firstEdge(tree).step.loliHash = 999999999;
    const r = checkForwardTree(tree, { program: s.program, roles: s.roles, initial: s.initial });
    // a non-ground / unknown loli token is unsupported OR errors — never valid
    assert.equal(r.valid && !r.unsupported, false);
  });

  it('a leaf recording a fabricated state is rejected', () => {
    const s = setup('t_leaf', `go:type.\nb:type.\n` +
      `r: go -o { b }.\n#symex go .\n`);
    const tree = clone(s.tree);
    // find the leaf and inject a bogus linear fact
    const leaf = firstEdge(tree).child;
    assert.equal(leaf.type, 'leaf');
    leaf.state.linear[123456] = 1;
    const r = checkForwardTree(tree, { program: s.program, roles: s.roles, initial: s.initial });
    assert.equal(r.valid, false);
    assert.ok(r.errors.some(e => /linear state mismatch/.test(e)), r.errors.join('; '));
  });

  it('an edge missing its step witness is rejected (evidence required)', () => {
    const s = setup('t_nostep', `go:type.\nb:type.\n` +
      `r: go -o { b }.\n#symex go .\n`);
    const tree = clone(s.tree);
    delete firstEdge(tree).step;
    const r = checkForwardTree(tree, { program: s.program, roles: s.roles, initial: s.initial });
    assert.equal(r.valid, false);
    assert.ok(r.errors.some(e => /no step witness/.test(e)), r.errors.join('; '));
  });

  it('a fork edge naming a non-existent ⊕ alternative is rejected', () => {
    const s = setup('t_alt', `go:type.\na:type.\nb:type.\n` +
      `r: go -o { a + b }.\n#symex go .\n`);
    const tree = clone(s.tree);
    firstEdge(tree).step.alt = 7;      // rule has alternatives 0,1 only
    const r = checkForwardTree(tree, { program: s.program, roles: s.roles, initial: s.initial });
    assert.equal(r.valid, false);
    assert.ok(r.errors.some(e => /alternative 7/.test(e)), r.errors.join('; '));
  });

  it('an unknown rule name on an edge is rejected', () => {
    const s = setup('t_rule', `go:type.\nb:type.\n` +
      `r: go -o { b }.\n#symex go .\n`);
    const tree = clone(s.tree);
    firstEdge(tree).rule = 'nonexistent';
    const r = checkForwardTree(tree, { program: s.program, roles: s.roles, initial: s.initial });
    assert.equal(r.valid, false);
    assert.ok(r.errors.some(e => /unknown program rule/.test(e)), r.errors.join('; '));
  });
});

describe('forward-check — resolver independence & orchestrator', () => {
  it('certifies identically under FFI-off and FFI-on', () => {
    const prog = `go:type.\na:type.\nb:type.\nr: go -o { a + b }.\n#symex go .\n`;
    const off = check(setup('ri_off', prog, { ffi: false }));
    const on = check(setup('ri_on', prog, { ffi: true }));
    assert.equal(off.valid, true, JSON.stringify(off.errors));
    assert.equal(on.valid, true, JSON.stringify(on.errors));
    assert.equal(off.leaves, on.leaves);
  });

  it('certifies a real corpus explore (toy-branch, theory-canonicalized ⊕)', () => {
    Store.clear();
    const calc = mde.load('calculus/ill/programs/toy-branch.ill', { cache: false });
    const st = mde.normalizeQuery(calc.queries.get('symex'));
    const r = calc.certifyExplore(st, { maxDepth: 200 });
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.unsupported, undefined, 'plain ILL rules are fully re-derivable');
    assert.equal(r.leaves, 2, 'the symbolic branch yields two reachable leaves');
  });

  it('grade-0-fused rules are reported unsupported, never a false rejection', () => {
    // The multisig corpus specializes bytecode at compile time (grade-0):
    // fused rules bind antecedent positions outside the runtime θ, so the
    // checker cannot re-derive them. It must report unsupported (not
    // certified) — NEVER error (which would brand a valid run unsound).
    Store.clear();
    const calc = mde.load('calculus/ill/programs/multisig.ill', { cache: false });
    const st = mde.normalizeQuery(calc.queries.get('symex'));
    const r = calc.certifyExplore(st, { maxDepth: 400 });
    assert.equal(r.errors.length, 0, 'no false soundness rejection');
    assert.ok(r.unsupported && r.unsupported.length > 0, 'fused rules flagged unsupported');
    // full certification is `valid && !unsupported` — here it is NOT certified
    assert.equal(r.valid && !r.unsupported, false);
  });

  it('api.certifyExplore runs explore + check end-to-end', () => {
    const f = path.join(tmpDir, 'orch.ill');
    fs.writeFileSync(f, DECLS + `go:type.\nb:type.\nc:type.\n` +
      `r1: go -o { b }.\nr2: b -o { c }.\n#symex go .\n`);
    Store.clear();
    const calc = mde.load(f, { cache: false });
    const st = mde.normalizeQuery(calc.queries.get('symex'));
    const r = calc.certifyExplore(st, { maxDepth: 50 });
    assert.equal(r.valid, true, JSON.stringify(r.errors));
    assert.equal(r.leaves, 1);
    assert.ok(r.tree);
  });
});
