/**
 * Parser negative-case fuzzer (TODO_0272 M7).
 *
 * parser-fold-fuzz samples strings INSIDE the grammar (all valid). This fuzzes
 * the complement: take valid strings and MUTATE them (char delete/insert/swap,
 * truncation, bracket removal, operator corruption) — almost all mutants are
 * ill-formed. The invariant is robustness: parsing a mutant must EITHER return
 * a well-formed hash OR throw a LOUD, deliberate parse error. It must NEVER
 * throw an unhandled internal JS crash (TypeError "cannot read properties of
 * undefined", RangeError, stack overflow, …) — that class is exactly the
 * rules2 `succedent.trim()` bug (TODO_0272 MINOR 3) and the `a@3/0` RangeError.
 */

import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import path from 'path';
import calculus from '../lib/calculus/index.js';
import { buildParser } from '../lib/calculus/builders.js';
import Store from '../lib/kernel/store.js';

const TILL_CALC = path.join(import.meta.dirname, '../calculus/till/till.calc');

function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6D2B79F5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

// An unhandled internal crash — the bug class this fuzzer exists to catch.
// A deliberate parse rejection never looks like these.
const INTERNAL_CRASH =
  /cannot read propert|cannot access|is not a function|is not iterable|undefined \(reading|reading '|maximum call stack|invalid array length|is not defined|NaN|\[object/i;

const MUTATORS = [
  // delete one char
  (s, r) => { const i = Math.floor(r() * s.length); return s.slice(0, i) + s.slice(i + 1); },
  // duplicate one char
  (s, r) => { const i = Math.floor(r() * s.length); return s.slice(0, i) + s[i] + s.slice(i); },
  // substitute one char from a punchy alphabet
  (s, r) => { const i = Math.floor(r() * s.length); const c = '(){}[]*+-o!@&$#.,/\\ 0123456789Xabc'[Math.floor(r() * 34)]; return s.slice(0, i) + c + s.slice(i + 1); },
  // truncate
  (s, r) => s.slice(0, Math.max(1, Math.floor(r() * s.length))),
  // drop the first bracket-ish char (imbalance)
  (s) => { const i = s.search(/[(){}\[\]]/); return i < 0 ? s + '(' : s.slice(0, i) + s.slice(i + 1); },
  // insert a stray operator
  (s, r) => { const i = Math.floor(r() * (s.length + 1)); return s.slice(0, i) + ' -o ' + s.slice(i); },
];

function fuzz(label, parse, corpus, seed) {
  it(`${label}: mutants parse or reject loudly — never crash (2400 mutations)`, () => {
    const r = rng(seed);
    let parsed = 0, rejected = 0;
    for (let i = 0; i < 2400; i++) {
      const base = corpus[Math.floor(r() * corpus.length)];
      let s = base;
      const nMut = 1 + Math.floor(r() * 3);
      for (let m = 0; m < nMut; m++) s = MUTATORS[Math.floor(r() * MUTATORS.length)](s, r);
      if (s.length === 0) continue;
      try {
        const h = parse(s);
        // Success is fine, but it must be a real Store hash, not junk.
        assert.ok(typeof h === 'number' && Store.tag(h) !== undefined,
          `${label}: '${s}' parsed to a non-hash ${h}`);
        parsed++;
      } catch (e) {
        assert.ok(!INTERNAL_CRASH.test(e.message),
          `${label}: mutant '${s}' (from '${base}') threw an INTERNAL crash, not a loud parse error:\n  ${e.message}`);
        rejected++;
      }
    }
    // Sanity: mutation actually produces a healthy mix (mostly rejections).
    assert.ok(rejected > 200, `${label}: too few rejections (${rejected}) — mutators too weak`);
  });
}

describe('TODO_0272 M7 — parser negative-case fuzz', () => {
  let illParse, tillParse;
  before(() => {
    const ill = calculus.loadILL();
    illParse = buildParser(ill.constructors, {
      binders: { exists: 'exists', forall: 'forall' },
      multiCharFreevars: true, numbers: true, application: true,
      arrows: true, forwardRules: true, binaryNormalization: true,
    });
    tillParse = buildParser(calculus.load(TILL_CALC).constructors, {
      binders: { exists: 'exists', forall: 'forall' },
      multiCharFreevars: true, numbers: true, application: true,
      arrows: true, forwardRules: true, binaryNormalization: true,
      gradeUnit: () => Store.put('binlit', [0n]),
    });
  });

  const ILL_CORPUS = [
    'a * b', 'a -o b', '!a', 'a + b', 'a & b', '{ a }', 'a * (b -o c)',
    '!a * b -o { c + d }', 'exists X. a * X', 'forall X. a -o b',
    'a * b * c & d', '(a + b) -o (c * d)', '!(a -o b) * c',
  ];
  const TILL_CORPUS = [
    'a@3', '{ a }@2', '!_2 a', 'after 5', 'before 10', 'a +[1/2] b',
    '4wood', '{ a }@0.5', 'a@3 * b@4', '!_W a', 'read a', 'a@(Q+2)',
    '{ a * b }@5', '!_2 a@4',
  ];

  fuzz('ill', (s) => illParse(s), ILL_CORPUS, 0xBADF00D);
  fuzz('till', (s) => tillParse(s), TILL_CORPUS, 0xBADCAFE);
});
