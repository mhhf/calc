/**
 * State-canonicity invariant (theory-eq sweep): every fact hash in a
 * live engine state is a fixpoint of the composed theory canonicalizer,
 * so hash identity inside the engine (FactSet rows, dedup sets, memo
 * keys) IS value identity.
 *
 * The invariant is enforced at the fact-entry boundaries:
 *   - forward/timed production (compile-time canonPatterns gate — a
 *     consequent applying a theory class constructor over a variable
 *     rebuilds the structural form: `tok (i X)` with X ↦ binlit 1 used
 *     to insert i(binlit 1), hash-distinct from binlit 3)
 *   - plain-object state entry (Store-level API callers)
 *   - dynamic-rule (loli) materialization
 *   - clause-resolution outputs (pre-existing: resolve-all, compiled
 *     tiers, tabling)
 *
 * Certifiers deliberately do NOT trust this invariant — they compare
 * modulo the theories (certify-confluence _thEq pins).
 */
import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import os from 'os';
import path from 'path';
import Store from '../../lib/kernel/store.js';
import illmde from '../../calculus/ill/index.js';

let tmpDir;
before(() => { tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), 'canon-')); });
after(() => {
  for (const f of fs.readdirSync(tmpDir)) fs.unlinkSync(path.join(tmpDir, f));
  fs.rmdirSync(tmpDir);
});

const loadProg = (name, src) => {
  const file = path.join(tmpDir, name);
  fs.writeFileSync(file, src);
  return illmde.load(file, { cache: false });
};
const stateOf = (text) =>
  illmde.decomposeQuery(illmde.parseExpr(text, illmde.illConfig.loader));

const DECLS = `
e : bin.
i : bin -> bin.
o : bin -> bin.
tok : bin -> type.
`;

describe('state-canonicity invariant', () => {
  it('forward production canonicalizes class constructors over variables', () => {
    const calc = loadProg('prod.ill', DECLS + 'r1: tok X -o { tok (i X) }.\n');
    const res = calc.exec(stateOf('tok 1'), { maxSteps: 1 });
    const facts = Object.keys(res.state.linear).map(Number);
    assert.equal(facts.length, 1);
    const arg = Store.child(facts[0], 0);
    assert.equal(Store.tagId(arg), Store.TAG.binlit, 'produced arg is compact binlit');
    assert.equal(Store.child(arg, 0), 3n);
  });

  it('the compile-time gate is precise: ground-canonical consequents are unflagged', () => {
    const calc = loadProg('gate.ill', DECLS +
      'flat: tok X -o { tok 100 }.\n' +
      'deep: tok X -o { tok (o X) }.\n');
    const byName = new Map(calc.forwardRules.map(r => [r.name, r]));
    assert.equal(byName.get('flat').canonPatterns, null,
      'ground binlit consequent pays nothing');
    assert.ok(Array.isArray(byName.get('deep').canonPatterns) &&
      byName.get('deep').canonPatterns.length === 1,
      'class constructor over a variable is flagged');
  });

  it('two representation routes to one value share one FactSet row', () => {
    const calc = loadProg('row.ill', DECLS +
      'a : bin -> type.\nb : bin -> type.\n' +
      'ra: a X -o { tok (i X) }.\n' +
      'rb: b Y -o { tok Y }.\n');
    const res = calc.exec(stateOf('a 1 * b 3'), { maxSteps: 10 });
    const entries = Object.entries(res.state.linear);
    assert.equal(entries.length, 1, 'one row, not two theory-equal rows');
    assert.equal(entries[0][1], 2, 'multiset count merged');
  });

  it('plain-object state entry canonicalizes Store-level facts (exec + explore)', () => {
    const calc = loadProg('entry.ill', DECLS + 'r1: tok X * tok X -o { tok X }.\n');
    // Store-level non-canonical fact: tok (i (binlit 1)) ≡ tok 3
    const bad = Store.put('tok', [Store.put('i', [Store.put1('binlit', 1n)])]);
    const good = Store.put('tok', [Store.put1('binlit', 3n)]);
    assert.notEqual(bad, good, 'representations are hash-distinct');
    const res = calc.exec({ linear: { [bad]: 1, [good]: 1 }, persistent: {} }, { maxSteps: 10 });
    // the rule needs TWO tok X at ONE hash — only fires if entry merged the row
    const entries = Object.entries(res.state.linear);
    assert.equal(entries.length, 1);
    assert.equal(entries[0][1], 1, 'rule consumed both copies of the merged row');
    // …and the survivor is the CANONICAL representation (pre-fix, theory-
    // aware matching still fired but X carried the structural form through)
    assert.equal(Number(entries[0][0]), good, 'surviving fact is canonical');

    const tree = calc.explore({ linear: { [bad]: 1, [good]: 1 }, persistent: {} }, { maxDepth: 4 });
    assert.ok(tree.children && tree.children.length > 0,
      'explore sees the merged row and can fire');
  });

  it('timed fire canonicalizes flagged consequents (till settle path)', async () => {
    const mde = (await import('../../lib/engine/index.js')).default;
    const tillConfig = (await import('../../calculus/till/calculus-config.js')).default;
    const file = path.join(tmpDir, 'p.till');
    fs.writeFileSync(file,
      'i : (a: bin) -> bin.\n' +
      't_tok: (v: bin) -> type.\n' +
      'r1: t_tok X -o { t_tok (i X) }@(1).\n');
    const calc = mde.load(file, { calculusConfig: tillConfig, cache: false });
    const one = Store.put1('binlit', 1n);
    const res = calc.settle({ linear: { [Store.put('t_tok', [one])]: 1 }, persistent: {} }, '0');
    const rows = Object.keys(res.state.linear).map(Number);
    // boundary rendering: at(inner, stamp) or bare inner — find the t_tok
    const inner = rows.map(h => (Store.tag(h) === 'at' ? Store.child(h, 0) : h))
      .filter(h => Store.tag(h) === 't_tok');
    assert.equal(inner.length, 1);
    assert.equal(Store.tagId(Store.child(inner[0], 0)), Store.TAG.binlit,
      'timed-produced fact is canonical (i(binlit 1) folded to binlit 3)');
    assert.equal(Store.child(Store.child(inner[0], 0), 0), 3n);
  });

  it('dynamic-rule (loli) materialization canonicalizes the instantiated body', () => {
    const calc = loadProg('loli.ill', DECLS +
      'seed : bin -> type.\ntrig : type.\n' +
      'mk: seed X * trig -o { (trig -o { tok (i X) }) * trig }.\n');
    const res = calc.exec(stateOf('seed 1 * trig'), { maxSteps: 5 });
    const toks = Object.keys(res.state.linear).map(Number)
      .filter(h => Store.tag(h) === 'tok');
    assert.equal(toks.length, 1);
    assert.equal(Store.tagId(Store.child(toks[0], 0)), Store.TAG.binlit,
      'loli-produced fact is canonical');
    assert.equal(Store.child(Store.child(toks[0], 0), 0), 3n);
  });
});
