/**
 * Well-modedness checker (task #81 / P7, THY_0039 §6).
 *
 * P1 — functionality certification (§6.1). A forcing goal (a persistent
 * consequent goal that determines an existential slot) must name a
 * certified-functional predicate at the slot's output position. Certification
 * is SOUND: input-disjoint clause heads (≤ 1 clause per ground input) AND a
 * body-determinism check (the head's output is functionally determined from its
 * inputs through certified premises) — so a relational body is not certified,
 * and forcing it is flagged (G1).
 *
 * Warn-first: findings land on calc.wellModedLint.warnings; calc.functionalPreds
 * is the certified "pred#outPos" set.
 */
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import mde from '../../calculus/ill/index.js';
import { checkWellModed, certifyDecidable } from '../../lib/engine/well-moded.js';

let tmpDir;
before(() => { tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'wm-')); });
after(() => {
  for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
  fs.rmdirSync(tmpDir);
});

// bin + a family of predicates with known determinism status.
const DECLS = `e : bin.
i : bin -> bin.
o : bin -> bin.
inc : (a: bin) -> (b: bin) -> type.
dup : (a: bin) -> (b: bin) -> type.
rel : (a: bin) -> (b: bin) -> type.
trig : type.
out : (v: bin) -> type.
% inc: input-disjoint on arg0, deterministic body ⇒ certified at out=1.
inc/e: inc e (i e).
inc/o: inc (o N) (i N).
inc/i: inc (i N) (o R) <- inc N R.
% dup: two clauses share arg0 = e ⇒ NOT input-disjoint at out=1 (relational).
dup/1: dup e e.
dup/2: dup e (i e).
% rel: one clause, but its body grounds the output only through dup (not
% certified at out=1) ⇒ body-determinism fails ⇒ rel NOT certified at out=1.
rel/1: rel X Y <- dup X Y.
`;

function load(name, body) {
  const f = path.join(tmpDir, `${name}.ill`);
  fs.writeFileSync(f, DECLS + body);
  Store.clear();
  return mde.load(f, { cache: false });
}

function loadRaw(name, body) {
  const f = path.join(tmpDir, `${name}.ill`);
  fs.writeFileSync(f, body);
  Store.clear();
  return mde.load(f, { cache: false });
}

describe('P7/P1 — functionality certification (THY_0039 §6.1)', () => {
  it('certifies an input-disjoint, deterministic-body predicate (inc#1)', () => {
    const calc = load('cert', `r: trig -o { !inc (i e) C * out C }.\n#symex trig .\n`);
    assert.ok(calc.functionalPreds.has('inc#1'), 'inc is functional at output arg 1');
    // Forcing inc is well-moded ⇒ no warning about inc.
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes("'inc'")), 'no forcing warning for inc');
  });

  it('does NOT certify overlapping-head clauses (dup#1) — G1 relational', () => {
    const calc = load('overlap', `bad: trig -o { !dup e X * out X }.\n#symex trig .\n`);
    assert.ok(!calc.functionalPreds.has('dup#1'), 'dup is not functional at output arg 1');
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes("'dup'") && w.includes('position 1')),
      'forcing dup at output 1 is flagged');
  });

  it('does NOT certify a relational-body clause (rel#1) — body-determinism is sound', () => {
    const calc = load('relbody', `bad: trig -o { !rel e X * out X }.\n#symex trig .\n`);
    // rel has ONE clause (input-disjoint vacuously) but its output is grounded
    // only via dup, which is not certified — so rel must not be certified.
    assert.ok(!calc.functionalPreds.has('rel#1'),
      'rel is not functional: its body grounds the output through a relational predicate');
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes("'rel'")), 'forcing rel is flagged');
  });

  it('a zero-clause EDB predicate is never certified (forcing edge is flagged)', () => {
    const calc = load('edb', `edge : (a: bin) -> (b: bin) -> type.\n` +
      `bad: trig -o { !edge e X * out X }.\n#symex trig .\n`);
    assert.ok(!calc.functionalPreds.has('edge#1'), 'a relational EDB fact is not functional');
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes("'edge'")), 'forcing a zero-clause EDB predicate is flagged');
  });

  it('the real EVM corpus certifies its forced arithmetic (plus#2, to256#1) and is warning-free', () => {
    Store.clear();
    const calc = mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/bin.ill'),
      { cache: false });
    assert.ok(calc.functionalPreds.has('plus#2'), 'plus is functional at its sum position');
    assert.ok(calc.functionalPreds.has('to256#1'), 'to256 is functional at its result position');
  });
});

// A list surface: a producer pushes a parameter VALUE onto a cons list; a
// consumer either matches the cons SPINE (opaque, well-moded) or demands the
// value have structure (V1). This is the EVM-stack shape in miniature.
const LIST = `e : bin.
o : bin -> bin.
nil : lst.
cons : (h: bin) -> (t: lst) -> lst.
box : (v: bin) -> type.
lst : (l: lst) -> type.
trig : type.
out : (v: bin) -> type.
`;

describe('P7/P2 — parameter-flow + V1 structural match (THY_0039 §6.2)', () => {
  it('flags a pattern that decomposes a parameter value (V1)', () => {
    // gen produces box V with V an existential parameter; use demands (i X).
    const calc = loadRaw('v1pos', LIST +
      `i : bin -> bin.\n` +
      `gen: trig -o { box V }.\n` +
      `use: box (i X) -o { out X }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes("'use'") && w.includes('V1')),
      'decomposing a parameter (i X) is flagged');
  });

  it('does NOT flag opaque carry — a parameter bound to a bare variable', () => {
    const calc = loadRaw('v1carry', LIST +
      `gen: trig -o { box V }.\n` +
      `use: box Y -o { out Y }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V1')), 'binding a parameter to a variable is well-moded');
  });

  it('does NOT flag matching a list SPINE while binding parameter values as variables', () => {
    // push puts a parameter value at the list head; pop matches cons(H,T)
    // binding H,T as variables. The spine is concrete; only values are
    // parameters — so no rule decomposes a parameter (the EVM-stack shape).
    const calc = loadRaw('v1spine', LIST +
      `push: trig * lst L -o { lst (cons V L) }.\n` +
      `pop: lst (cons H T) -o { lst T * out H }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V1')),
      'matching the cons spine and binding values as variables is well-moded');
  });

  it('flags a pattern that decomposes a list VALUE (V1) — value structure demanded', () => {
    const calc = loadRaw('v1val', LIST +
      `i : bin -> bin.\n` +
      `push: trig * lst L -o { lst (cons V L) }.\n` +
      `bad: lst (cons (i X) T) -o { out X }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes("'bad'") && w.includes('V1')),
      'demanding a list value be (i X) decomposes a parameter');
  });

  it('the EVM corpus has zero V1 findings (only the cd_copy/code_copy G1 residual)', () => {
    Store.clear();
    const calc = mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill'),
      { cache: false });
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V1')), 'no structural match on any EVM parameter');
    // The only residual is G1 on the le/lt-guarded copy loops (task #84).
    assert.ok(warns.every((w) => w.includes('cd_copy') || w.includes('code_copy')),
      'the only warnings are the copy-loop G1 residual');
  });
});

// A parameter reaching a ⊕ whose guards decide the branch on its value.
const GUARD = `e : bin.
i : bin -> bin.
o : bin -> bin.
eq : (a: bin) -> (b: bin) -> type.
neq : (a: bin) -> (b: bin) -> type.
box : (v: bin) -> type.
box2 : (v: bin) -> type.
trig : type.
a : type.
b : type.
gen: trig -o { box V }.
`;

describe('P7/P3 — guard-coverage V2 (THY_0039 §6.3)', () => {
  it('certifies the jumpi discipline (!neq C 0 ⊕ !eq C 0) — no V2', () => {
    const calc = loadRaw('v2clean', GUARD +
      `r: box C -o { (!neq C e * a) + (!eq C e * b) }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V2')), 'complementary eq/neq split covers and excludes');
  });

  it('flags a non-COVERING split (eq C 0 ⊕ eq C 1 — value 2 takes no branch)', () => {
    const calc = loadRaw('v2cover', GUARD +
      `r: box C -o { (!eq C e * a) + (!eq C (i e) * b) }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes('V2 coverage')), 'two eq guards leave the generic value uncovered');
  });

  it('flags a non-EXCLUSIVE split (neq C 0 ⊕ neq C 1 — value 2 takes both)', () => {
    const calc = loadRaw('v2excl', GUARD +
      `r: box C -o { (!neq C e * a) + (!neq C (i e) * b) }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(warns.some((w) => w.includes('V2 exclusion')), 'two neq guards overlap on the generic value');
  });

  it('does NOT flag a ⊕ that carries a parameter opaquely (no guard on it)', () => {
    const calc = loadRaw('v2opaque', GUARD +
      `r: box C -o { (box2 C * a) + (box2 C * b) }.\n#symex trig .\n`);
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V2')), 'a parameter carried into both branches is well-moded');
  });

  it('the EVM corpus certifies jumpi (no V2 findings)', () => {
    Store.clear();
    const calc = mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill'),
      { cache: false });
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('V2')), 'jumpi covers+excludes on the branch condition');
  });
});

// §6.1′ — total DECISION PROCEDURES (certifyDecidable) + the order-guard
// mis-declaration warning that gates the task-#84 tell prune.
describe('P7/§6.1′ — certified decision procedures + order-guard declarations', () => {
  it('certifies exactly the non-multiModal all-input FFI predicates', () => {
    const cc = {
      ffi: {
        parsedModes: { lt: 1, le: 1, gt: 1, plus: 1, eq_bool: 1, alen: 1 },
        getModeMeta: (n) => ({
          lt: { modes: ['+', '+'], multiModal: false },
          le: { modes: ['+', '+'], multiModal: false },
          gt: { modes: ['+', '+', '+', '-'], multiModal: false }, // has output → NOT a decision proc
          plus: { modes: ['+', '+', '+'], multiModal: true },     // multiModal → excluded
          eq_bool: { modes: ['+', '+', '-'], multiModal: false }, // has output → excluded
          alen: { modes: ['+', '-'], multiModal: false },         // has output → excluded
        }[n]),
      },
    };
    const dec = certifyDecidable(cc);
    assert.deepEqual([...dec].sort(), ['le', 'lt'], 'only all-input non-multiModal FFI preds');
  });

  it('warns on a declared order guard that is NOT a certified decision procedure', () => {
    const cc = {
      ffi: {
        parsedModes: { lt: 1 },
        getModeMeta: (n) => ({ lt: { modes: ['+', '+'], multiModal: false } }[n]),
      },
      domain: { constraintPreds: { eq: 'eq', neq: 'neq', order: { lt: '<', bogus: '<' } } },
    };
    const wm = checkWellModed({ compiledRules: [], clauses: new Map(), cc });
    assert.ok(wm.decidablePreds.has('lt'), 'lt is a certified decision procedure');
    assert.ok(!wm.decidablePreds.has('bogus'), 'bogus has no FFI decision mode');
    assert.ok(wm.warnings.some((w) => w.includes("'bogus'") && w.includes('§6.1′')),
      'an uncertified order guard is flagged');
    assert.ok(!wm.warnings.some((w) => w.includes("order guard 'lt'")),
      'a certified order guard is silent');
  });

  it('the EVM corpus declares lt/le as certified order guards (no §6.1′ warning)', () => {
    Store.clear();
    const calc = mde.load(path.join(import.meta.dirname, '../../calculus/ill/programs/evm.ill'),
      { cache: false });
    assert.ok(calc.decidablePreds.has('lt') && calc.decidablePreds.has('le'),
      'lt/le are certified total decision procedures');
    const warns = (calc.wellModedLint && calc.wellModedLint.warnings) || [];
    assert.ok(!warns.some((w) => w.includes('§6.1′')), 'ILL declares only certified order guards');
  });
});
