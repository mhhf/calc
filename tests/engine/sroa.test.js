/**
 * Tests for SROA (Scalar Replacement of Aggregates) — stack decomposition.
 *
 * After basic block fusion, mega-rules accumulate arr_get/arr_set persistent
 * goals. SROA expands the stack cons pattern to expose individual slots,
 * replacing arr_get/arr_set goals with direct structural matching.
 *
 * SROA replaces the original: if the SROA'd pattern can't match (stack too
 * shallow), the original would also stall (arr_get OOB), so the fallback is
 * unreachable. Only fused rules (name contains '+') are SROA'd.
 */
const { describe, it, beforeEach } = require('node:test');
const assert = require('node:assert/strict');
const Store = require('../../lib/kernel/store');
const { GRADE_W } = require('../../lib/engine/grades');
const { ILL_CONNECTIVES } = require('../../lib/engine/ill/connectives');
const { resolveConnectives, flattenAntecedent, unwrapComputation } = require('../../lib/engine/compile');
const { getPredicateHead } = require('../../lib/kernel/ast');
const { _sroaStackDecomposition } = require('../../lib/engine/compose');
const { getModeMeta: _illGetModeMeta } = require('../../lib/engine/opt/ffi');

const rc = resolveConnectives(ILL_CONNECTIVES);

function makeRule(name, anteHash, conseqBodyHash) {
  const conseqHash = Store.put('monad', [conseqBodyHash]);
  const hash = Store.put('loli', [anteHash, conseqHash]);
  return { name, hash, antecedent: anteHash, consequent: conseqHash };
}

function tensor(...hashes) {
  if (hashes.length === 0) return Store.put('one', []);
  if (hashes.length === 1) return hashes[0];
  let acc = hashes[hashes.length - 1];
  for (let i = hashes.length - 2; i >= 0; i--) {
    acc = Store.put('tensor', [hashes[i], acc]);
  }
  return acc;
}

function bang(h) { return Store.put('bang', [GRADE_W, h]); }
function mv(name) { return Store.put('metavar', [name]); }
function binlit(n) { return Store.put('binlit', [BigInt(n)]); }
function cons(head, tail) { return Store.put('acons', [head, tail]); }

function stackFact(arrExpr) {
  Store.registerTag('stack');
  return Store.put('stack', [arrExpr]);
}

function flattenRule(rule) {
  const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
  const conseqBody = unwrapComputation(Store.child(rule.hash, 1), rc);
  const conseq = flattenAntecedent(conseqBody, rc);
  return { anteLinear: ante.linear, antePersistent: ante.persistent, conseqLinear: conseq.linear };
}

function countPred(persistents, pred) {
  return persistents.filter(p => getPredicateHead(p) === pred).length;
}

/** Get the SROA'd rule from the result (the one with [sroa:] in name) */
function getSroaRule(result) {
  return result.rules.find(r => r.name.includes('[sroa:'));
}

describe('SROA — stack decomposition', () => {
  beforeEach(() => { Store.clear(); });

  it('passes through non-fused rules (no + in name)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    const TOP = mv('TOP'), REST = mv('REST'), X = mv('X');
    const stk = stackFact(cons(TOP, REST));
    const arrGet = Store.put('arr_get', [REST, binlit(0), X]);
    const ante = tensor(stk, bang(arrGet));
    Store.registerTag('out');
    const conseq = Store.put('out', [X]);
    const rule = makeRule('individual_rule', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.rules.length, 1, 'no SROA copy for non-fused rule');
    assert.equal(result.sroaCount, 0);
    assert.equal(result.rules[0].hash, rule.hash, 'rule unchanged');
  });

  it('passes through fused rules without arr_get/arr_set', () => {
    Store.registerTag('stack');
    Store.registerTag('pc');
    Store.registerTag('inc');
    const TOP = mv('TOP'), REST = mv('REST'), Y = mv('Y');
    const pcFact = Store.put('pc', [binlit(1)]);
    const stk = stackFact(cons(TOP, REST));
    const incGoal = Store.put('inc', [binlit(1), Y]);
    const ante = tensor(pcFact, stk, bang(incGoal));
    const conseq = tensor(Store.put('pc', [Y]), stackFact(cons(TOP, REST)));
    const rule = makeRule('a+b', ante, conseq); // fused name

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.rules.length, 1, 'no SROA copy (no arr goals)');
    assert.equal(result.sroaCount, 0);
  });

  it('replaces original with SROA version (single arr_get)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    const TOP = mv('TOP'), REST = mv('REST'), X = mv('X');

    const stk = stackFact(cons(TOP, REST));
    const arrGet = Store.put('arr_get', [REST, binlit(0), X]);
    const ante = tensor(stk, bang(arrGet));
    Store.registerTag('out');
    const conseq = Store.put('out', [X]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.rules.length, 1, 'original replaced by SROA');
    assert.equal(result.sroaCount, 1);
    assert.notEqual(result.rules[0].hash, rule.hash, 'SROA version differs from original');

    const sroa = getSroaRule(result);
    assert(sroa, 'SROA copy exists');
    const f = flattenRule(sroa);
    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'no arr_get left');

    // Antecedent stack should have at least 2 slots: stack([TOP, S0 | TAIL])
    const stackHash = f.anteLinear.find(h => getPredicateHead(h) === 'stack');
    assert(stackHash, 'stack still present');
    const arrExpr = Store.child(stackHash, 0);
    assert.equal(Store.tag(arrExpr), 'acons', 'outer is cons');
    const innerArr = Store.child(arrExpr, 1);
    assert.equal(Store.tag(innerArr), 'acons', 'inner is cons (expanded slot)');

    // The consequent's X should refer to the slot metavar (S0)
    const slot0 = Store.child(innerArr, 0);
    const outHash = f.conseqLinear.find(h => getPredicateHead(h) === 'out');
    assert(outHash, 'out still present');
    assert.equal(Store.child(outHash, 0), slot0, 'X replaced by S0');
  });

  it('eliminates arr_set + arr_get chain (SWAP pattern)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('arr_set');

    const X = mv('X'), REST = mv('REST'), Y = mv('Y'), REST2 = mv('REST2');

    const stk = stackFact(cons(X, REST));
    const arrGet = Store.put('arr_get', [REST, binlit(0), Y]);
    const arrSet = Store.put('arr_set', [REST, binlit(0), X, REST2]);
    const ante = tensor(stk, bang(arrGet), bang(arrSet));
    const conseq = stackFact(cons(Y, REST2));
    const rule = makeRule('swap+next', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    const sroa = getSroaRule(result);
    assert(sroa, 'SROA copy exists');
    const f = flattenRule(sroa);

    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'no arr_get');
    assert.equal(countPred(f.antePersistent, 'arr_set'), 0, 'no arr_set');
    assert.equal(result.sroaCount, 1);

    const stkAnte = f.anteLinear.find(h => getPredicateHead(h) === 'stack');
    const stkConseq = f.conseqLinear.find(h => getPredicateHead(h) === 'stack');
    assert(stkAnte, 'antecedent stack');
    assert(stkConseq, 'consequent stack');

    // ante: stack([X, S0 | TAIL])
    const anteArr = Store.child(stkAnte, 0);
    assert.equal(Store.tag(anteArr), 'acons');
    const anteSlot0 = Store.child(Store.child(anteArr, 1), 0);

    // conseq: stack([S0, X | TAIL]) — Y=S0, REST2=[X|TAIL]
    const conseqArr = Store.child(stkConseq, 0);
    assert.equal(Store.tag(conseqArr), 'acons');
    const conseqHead = Store.child(conseqArr, 0);
    assert.equal(conseqHead, anteSlot0, 'conseq head = S0');
  });

  it('handles deeper access (index 2)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    const TOP = mv('TOP'), REST = mv('REST'), X = mv('X');

    const stk = stackFact(cons(TOP, REST));
    const arrGet = Store.put('arr_get', [REST, binlit(2), X]);
    const ante = tensor(stk, bang(arrGet));
    Store.registerTag('out');
    const conseq = Store.put('out', [X]);
    const rule = makeRule('a+b+c', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    const sroa = getSroaRule(result);
    const f = flattenRule(sroa);

    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');

    // Stack should expand to depth 3: stack([TOP, S0, S1, S2 | TAIL])
    let cur = Store.child(f.anteLinear.find(h => getPredicateHead(h) === 'stack'), 0);
    let depth = 0;
    while (Store.tag(cur) === 'acons') { depth++; cur = Store.child(cur, 1); }
    assert(depth >= 4, `expected depth >= 4, got ${depth}`);
  });

  it('skips rules with non-ground index', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    const TOP = mv('TOP'), REST = mv('REST'), N = mv('N'), X = mv('X');

    const stk = stackFact(cons(TOP, REST));
    const arrGet = Store.put('arr_get', [REST, N, X]);
    const ante = tensor(stk, bang(arrGet));
    Store.registerTag('out');
    const conseq = Store.put('out', [X]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.rules.length, 1, 'no SROA copy');
    assert.equal(result.sroaCount, 0);
  });

  it('preserves non-stack persistent goals', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('plus');
    const TOP = mv('TOP'), REST = mv('REST'), X = mv('X');
    const A = mv('A'), B = mv('B'), C = mv('C');

    const stk = stackFact(cons(TOP, REST));
    const arrGet = Store.put('arr_get', [REST, binlit(0), X]);
    const plusGoal = Store.put('plus', [A, B, C]);
    const ante = tensor(stk, bang(arrGet), bang(plusGoal));
    Store.registerTag('out');
    const conseq = Store.put('out', [X]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    const sroa = getSroaRule(result);
    const f = flattenRule(sroa);

    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');
    assert.equal(countPred(f.antePersistent, 'plus'), 1, 'plus preserved');
    assert.equal(result.sroaCount, 1);
  });

  it('handles full stack (no cons pattern, arr_get on S directly)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    const S = mv('S'), V = mv('V');

    const stk = stackFact(S);
    const arrGet = Store.put('arr_get', [S, binlit(1), V]);
    const ante = tensor(stk, bang(arrGet));
    Store.registerTag('out');
    const conseq = Store.put('out', [V]);
    const rule = makeRule('dup+next', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    const sroa = getSroaRule(result);
    const f = flattenRule(sroa);

    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');
    assert.equal(result.sroaCount, 1);

    const stkAnte = f.anteLinear.find(h => getPredicateHead(h) === 'stack');
    const arrExpr = Store.child(stkAnte, 0);
    assert.equal(Store.tag(arrExpr), 'acons', 'expanded to cons pattern');
  });
});

// ─── McCarthy array axiom tests ──────────────────────────────────────────────

describe('McCarthy array normalization', () => {
  beforeEach(() => { Store.clear(); });

  it('resolves arr_get(acons, 0) directly — head access', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('out');
    const H = mv('H'), T = mv('T'), V = mv('V');

    // stack([H | T]) * !arr_get([H|T], 0, V) -o {out(V)}
    // McCarthy: V = H, arr_get eliminated
    const arr = cons(H, T);
    const stk = stackFact(arr);
    const arrGet = Store.put('arr_get', [arr, binlit(0), V]);
    const ante = tensor(stk, bang(arrGet));
    const conseq = Store.put('out', [V]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.rules.length, 1);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');

    // The consequent out(V) should now reference H directly
    const outHash = f.conseqLinear.find(h => getPredicateHead(h) === 'out');
    assert(outHash, 'out still present');
    // H should appear in the antecedent stack
    const stkHash = f.anteLinear.find(h => getPredicateHead(h) === 'stack');
    const stkArr = Store.child(stkHash, 0);
    const stkHead = Store.child(stkArr, 0);
    assert.equal(Store.child(outHash, 0), stkHead, 'out references stack head');
  });

  it('reduces arr_get(acons, N) to arr_get(tail, N-1) for SROA', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('out');
    const TOP = mv('TOP'), H = mv('H'), REST = mv('REST'), V = mv('V');

    // stack([TOP | [H | REST]]) * !arr_get([H|REST], 1, V) -o {out(V)}
    // McCarthy: arr_get([H|REST], 1, V) → arr_get(REST, 0, V)
    // Then SROA: REST expanded, V = S0
    const inner = cons(H, REST);
    const stk = stackFact(cons(TOP, inner));
    const arrGet = Store.put('arr_get', [inner, binlit(1), V]);
    const ante = tensor(stk, bang(arrGet));
    const conseq = Store.put('out', [V]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied');
    assert.equal(result.sroaCount, 1, 'SROA also applied');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');
  });

  it('resolves arr_set(acons, 0) — head replacement', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_set');
    const H = mv('H'), T = mv('T'), NEWVAL = mv('NEWVAL'), OUT = mv('OUT');

    // stack([H | T]) * !arr_set([H|T], 0, NEWVAL, OUT) -o {stack(OUT)}
    // McCarthy: OUT = [NEWVAL | T], arr_set eliminated
    const arr = cons(H, T);
    const stk = stackFact(arr);
    const arrSet = Store.put('arr_set', [arr, binlit(0), NEWVAL, OUT]);
    const ante = tensor(stk, bang(arrSet));
    const conseq = stackFact(OUT);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_set'), 0, 'arr_set eliminated');

    // Consequent stack should have [NEWVAL | T] structure
    const stkConseq = f.conseqLinear.find(h => getPredicateHead(h) === 'stack');
    assert(stkConseq, 'stack in consequent');
    const conseqArr = Store.child(stkConseq, 0);
    assert.equal(Store.tag(conseqArr), 'acons', 'consequent is acons');
  });

  it('reduces arr_set(acons, N>=depth) to arr_set(base, N-depth)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_set');
    Store.registerTag('arr_get');
    const TOP = mv('TOP'), H = mv('H'), REST = mv('REST');
    const VAL = mv('VAL'), OUT = mv('OUT');

    // stack([TOP | [H | REST]]) * !arr_set([H|REST], 1, VAL, OUT) -o {stack([TOP | OUT])}
    // McCarthy: arr_set([H|REST], 1, VAL, OUT) → arr_set(REST, 0, VAL, INNER), OUT = [H|INNER]
    // Then SROA handles the reduced goal
    const inner = cons(H, REST);
    const stk = stackFact(cons(TOP, inner));
    const arrSet = Store.put('arr_set', [inner, binlit(1), VAL, OUT]);
    const ante = tensor(stk, bang(arrSet));
    const conseq = stackFact(cons(TOP, OUT));
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_set'), 0, 'arr_set eliminated');
  });

  it('handles deeper acons chains — arr_get([H0|[H1|T]], 1)', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('out');
    const TOP = mv('TOP'), H0 = mv('H0'), H1 = mv('H1'), T = mv('T'), V = mv('V');

    // arr_get([H0 | [H1 | T]], 1, V) → V = H1 (direct, depth=2, idx=1)
    const inner = cons(H1, T);
    const arr = cons(H0, inner);
    const stk = stackFact(cons(TOP, arr));
    const arrGet = Store.put('arr_get', [arr, binlit(1), V]);
    const ante = tensor(stk, bang(arrGet));
    const conseq = Store.put('out', [V]);
    const rule = makeRule('a+b+c', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'arr_get eliminated');
  });

  it('skips goals with non-ground index', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('out');
    const H = mv('H'), T = mv('T'), N = mv('N'), V = mv('V');

    const arr = cons(H, T);
    const stk = stackFact(arr);
    const arrGet = Store.put('arr_get', [arr, N, V]);
    const ante = tensor(stk, bang(arrGet));
    const conseq = Store.put('out', [V]);
    const rule = makeRule('a+b', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    // Non-ground index → no McCarthy, no SROA (arrVar is acons not metavar)
    assert.equal(result.mccarthyCount, 0, 'no McCarthy');
    assert.equal(result.sroaCount, 0, 'no SROA');
  });

  it('mixed: McCarthy reduces acons goal, SROA handles the base metavar', () => {
    Store.registerTag('stack');
    Store.registerTag('arr_get');
    Store.registerTag('out');
    const TOP = mv('TOP'), REST = mv('REST'), V1 = mv('V1'), V2 = mv('V2');

    // stack([TOP | REST])
    // !arr_get(REST, 0, V1)          ← SROA: metavar arrVar
    // !arr_get([V1|REST], 1, V2)     ← McCarthy: acons, idx=1 → arr_get(REST, 0, V2)
    //                                   Then SROA handles arr_get(REST, 0, V2)
    // This pattern arises from fusion: rule A reads slot 0 into V1, rule B
    // uses [V1|REST] (arr_set output shape) and reads slot 1.
    const aconsArr = cons(V1, REST);
    const stk = stackFact(cons(TOP, REST));
    const arrGet1 = Store.put('arr_get', [REST, binlit(0), V1]);
    const arrGet2 = Store.put('arr_get', [aconsArr, binlit(1), V2]);
    const ante = tensor(stk, bang(arrGet1), bang(arrGet2));
    const conseq = Store.put('out', [V2]);
    const rule = makeRule('a+b+c', ante, conseq);

    const result = _sroaStackDecomposition([rule], rc, _illGetModeMeta);
    assert.equal(result.mccarthyCount, 1, 'McCarthy applied to acons goal');
    assert.equal(result.sroaCount, 1, 'SROA handles the reduced goal');

    const f = flattenRule(result.rules[0]);
    assert.equal(countPred(f.antePersistent, 'arr_get'), 0, 'all arr_get eliminated');
  });
});
