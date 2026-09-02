/**
 * Parser acceptance harness (TODO_0268 §5b) — guards the sorted-template
 * grammar fold with two instruments:
 *
 *  1. Corpus sweep: every .ill/.till under calculus/ and tests/ loads with
 *     STRICT ambiguity detection on (lib/parser/earley.js §5a). Baseline
 *     (pre-fold, 2026-08-20): 70/85 files load fully, zero ambiguity; the
 *     remainder fail for non-parse reasons (import fragments, deliberately
 *     broken fixtures) and are tolerated — but an `Ambiguous parse` from
 *     ANY file, loading or not, is a hard failure.
 *
 *  2. Generative fuzz: strings sampled from the grammar's own productions
 *     (depth-bounded random expansion, terminals realized with a
 *     keyword-safe token pool) must parse under strict ambiguity. This
 *     reaches shapes the corpus doesn't. Both real rule-body grammars are
 *     covered: the ILL expression grammar (with convert.js's structural-
 *     operator filter replicated — the unfiltered tables are legitimately
 *     ambiguous: `(x : y)` parses as named-arg AND as the lnl colon
 *     operator) and the till grammar (templates, grades, rationals).
 *
 * During the fold itself, the same generator fed a legacy-vs-folded
 * hash-parity comparison (scaffolding, deleted with the legacy path).
 */

import { describe, it, before, after } from 'node:test';
import assert from 'node:assert/strict';
import fs from 'fs';
import path from 'path';
import mde from '../lib/engine/index.js';
import calculus from '../lib/calculus/index.js';
import { parserTables, parserFromTables } from '../lib/calculus/builders.js';
import { earleyGrammarFromTables, parserFromGrammar } from '../lib/parser/earley-grammar.js';
import { setStrictAmbiguity } from '../lib/parser/earley.js';
import tillConfig from '../calculus/till/calculus-config.js';
import illConfig from '../calculus/ill/calculus-config.js';
import { putRat } from '../lib/kernel/rat-term.js';
import { loadILL } from '../calculus/ill/index.js';

const ROOT = path.join(import.meta.dirname, '..');
const TILL_CALC = path.join(ROOT, 'calculus/till/till.calc');

before(() => setStrictAmbiguity(true));
after(() => setStrictAmbiguity(false));

// Deterministic PRNG (mulberry32).
function rng(seed) {
  let a = seed >>> 0;
  return () => {
    a |= 0; a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function listCorpus() {
  const out = [];
  const walk = (dir) => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (/\.(ill|till)$/.test(e.name)) out.push(p);
    }
  };
  walk(path.join(ROOT, 'calculus'));
  walk(path.join(ROOT, 'tests'));
  return out.sort();
}

describe('corpus sweep: strict ambiguity across every .ill/.till (§5b)', () => {
  it('zero ambiguous parses in the whole corpus', () => {
    const files = listCorpus();
    let ok = 0;
    const skipped = [];
    for (const p of files) {
      const isTill = p.includes('till');
      try {
        mde.load(p, { cache: false, calculusConfig: isTill ? tillConfig : illConfig });
        ok++;
      } catch (e) {
        assert.ok(!/Ambiguous parse/.test(e.message),
          `${path.relative(ROOT, p)}: ${e.message}`);
        skipped.push(path.relative(ROOT, p));
      }
    }
    // Tolerated skips are fragments/broken fixtures — surfaced, not silent.
    assert.ok(ok >= 60, `only ${ok}/${files.length} files loaded (skipped: ${skipped.join(', ')})`);
  });
});

// ─── Generative fuzz ─────────────────────────────────────────────────────────

/** Realize a terminal token as source text. */
function tokenText(type, rand, kwSet) {
  if (type === 'IDENT') {
    const pool = ['foo', 'bar', 'qux', 'v1', 'X', 'Addr'].filter(w => !kwSet.has(w));
    return pool[Math.floor(rand() * pool.length)];
  }
  if (type === 'NUMBER') return ['0', '3', '12'][Math.floor(rand() * 3)];
  if (type === 'RATNUM') return ['1/2', '3/4', '0.5'][Math.floor(rand() * 3)];
  return type; // keywords and operator tokens are their own text
}

/** Depth-bounded random sampler over the grammar's productions. */
function makeSampler(spec) {
  const { rules, start, lexerConfig } = spec;
  const kwSet = new Set(lexerConfig.keywords || []);
  // Minimum expansion depth per nonterminal (fixed point).
  const minD = new Map();
  let changed = true;
  while (changed) {
    changed = false;
    for (const r of rules) {
      let d = 0, known = true;
      for (const s of r.rhs) {
        if (s.sym === 1) {
          const md = minD.get(s.v);
          if (md === undefined) { known = false; break; }
          if (md > d) d = md;
        }
      }
      if (known && (!minD.has(r.lhs) || d + 1 < minD.get(r.lhs))) {
        minD.set(r.lhs, d + 1);
        changed = true;
      }
    }
  }
  const byLhs = new Map();
  for (const r of rules) {
    if (!byLhs.has(r.lhs)) byLhs.set(r.lhs, []);
    byLhs.get(r.lhs).push(r);
  }
  function expand(nt, budget, rand, out) {
    let candidates = byLhs.get(nt).filter(r =>
      r.rhs.every(s => s.sym === 0 || (minD.get(s.v) ?? Infinity) <= budget - 1));
    if (candidates.length === 0) {
      // Budget underrun: take the cheapest rule — its children have
      // strictly smaller minD than this NT, so expansion terminates.
      let best = null, bestD = Infinity;
      for (const r of byLhs.get(nt)) {
        const d = Math.max(0, ...r.rhs.filter(s => s.sym === 1).map(s => minD.get(s.v) ?? Infinity));
        if (d < bestD) { bestD = d; best = r; }
      }
      candidates = [best];
    }
    const r = candidates[Math.floor(rand() * candidates.length)];
    for (const s of r.rhs) {
      if (s.sym === 0) out.push(tokenText(s.v, rand, kwSet));
      else expand(s.v, budget - 1, rand, out);
    }
  }
  return (seed, budget = 8) => {
    const rand = rng(seed);
    const out = [];
    expand(start, budget, rand, out);
    return out.join(' ');
  };
}

/** The real rule-body grammar tables, per calculus (mirrors convert.js /
 *  till calculus-config: structural-op filter for ILL, gradeUnit for till). */
function grammarConfigs() {
  const ill = loadILL();
  const illTables = parserTables(ill.constructors);
  illTables.operators = illTables.operators
    .filter(o => ill.constructors[o.name]?.returnType === 'formula' && o.name !== 'loli');
  illTables.operators.push({ name: 'concat', op: '++', precedence: 55, assoc: 'left' });
  const shared = {
    binders: { exists: 'exists', forall: 'forall' },
    multiCharFreevars: true, numbers: true, application: true,
    arrows: true, forwardRules: true, binaryNormalization: true,
  };
  const tillTables = parserTables(calculus.load(TILL_CALC).constructors);
  return [
    { label: 'ill-expr', tables: { ...illTables, ...shared } },
    { label: 'till', tables: { ...tillTables, ...shared, gradeUnit: () => putRat(0n, 1n) } },
  ];
}

describe('generative fuzz: grammar-sampled strings parse unambiguously (§5b)', () => {
  for (const { label, tables } of grammarConfigs()) {
    it(`${label}: 300 sampled strings, strict ambiguity on`, () => {
      const spec = earleyGrammarFromTables(tables);
      const sample = makeSampler(spec);
      const parse = parserFromGrammar(spec);
      for (let i = 0; i < 300; i++) {
        const src = sample(0xF01D + i);
        let hash;
        try {
          hash = parse(src);
        } catch (e) {
          // Ambiguity is THE failure; semantic parse rejections (double
          // stamp, count-grade validation, ...) are legitimate — templates
          // reject some grammatical strings loudly by design.
          assert.ok(!/Ambiguous parse/.test(e.message), `${label} seed ${i}: '${src}' → ${e.message}`);
          continue;
        }
        assert.equal(typeof hash, 'number', `${label} seed ${i}: '${src}' parsed to non-hash`);
      }
    });
  }
});
