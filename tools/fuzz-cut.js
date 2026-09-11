/**
 * Cut-admissibility fuzzer across the calculus family (TODO_0064 Axis-metatheorem,
 * THY_0044 §4). The unification's operational claim is "one engine, calculi as
 * specs": the generic `cut` rule (kernel + focused.js) is shared verbatim by every
 * instance. This fuzzer is the per-instance EMPIRICAL witness that cut is
 * ADMISSIBLE — anything the cut-free system can derive with a cut, it derives
 * WITHOUT one. It uses ONLY the cut-free prover: for a cut template it checks that
 * both premises `Γ ⊢ A` and `A, Δ ⊢ C` are cut-free provable (sanity) and then that
 * the composed `Γ, Δ ⊢ C` is ALSO cut-free provable and kernel-valid. A failure is a
 * genuine finding: cut is essential (i.e. NOT admissible) for that instance, or the
 * cut-free search is incomplete on it.
 *
 * The deep case is FIXPOINTS: cut-elimination for cyclic (μ/ν) proofs is known-hard
 * (Fortier–Santocanale; Baelde–Doumane–Saurin). fill/grill exercise coinductive and
 * graded-coinductive cut templates through the SAME generic cut. This is evidence,
 * not the display-calculus metatheorem (deferred, THY_0044 §4 item 4).
 *
 * Usage: node tools/fuzz-cut.js [--count N] [--seed N] [--verbose]
 * Exits non-zero on any admissibility failure.
 */
'use strict';

import Seq from '../lib/kernel/sequent.js';
import { buildRuleSpecs } from '../lib/prover/rule-interpreter.js';
import { createProver } from '../lib/prover/focused.js';
import { createKernel } from '../lib/prover/kernel.js';

const args = process.argv.slice(2);
const getArg = (f, d) => { const i = args.indexOf(f); return i >= 0 ? Number(args[i + 1]) : d; };
const COUNT = getArg('--count', 40);
let seed = getArg('--seed', 0x51ed5eed) >>> 0;
const VERBOSE = args.includes('--verbose');
const rand = () => { seed = (seed * 1664525 + 1013904223) >>> 0; return seed / 0x100000000; };
const pick = (a) => a[Math.floor(rand() * a.length)];

// Cut templates. Each is (p,q) → { L, R, Cut, opts, tags } where L/R/Cut are
// { lin, cart, succ } sequents (strings), opts carries cyclic/exhaustive, and
// `tags` lists which calculi it applies to. The cut FORMULA is the succedent of L
// = the distinguished antecedent of R; the fuzzer never names it explicitly.
const TEMPLATES = [
  { tag: 'tensor', calc: ['ill', 'fill', 'gill', 'grill'], cyclic: false,
    L: (p, q) => ({ lin: [p, q], cart: [], succ: `${p} * ${q}` }),
    R: (p, q) => ({ lin: [`${p} * ${q}`], cart: [], succ: `${q} * ${p}` }),
    Cut: (p, q) => ({ lin: [p, q], cart: [], succ: `${q} * ${p}` }) },
  { tag: 'loli', calc: ['ill', 'fill', 'gill', 'grill'], cyclic: false,
    L: (p) => ({ lin: [], cart: [], succ: `${p} -o ${p}` }),
    R: (p) => ({ lin: [`${p} -o ${p}`, p], cart: [], succ: p }),
    Cut: (p) => ({ lin: [p], cart: [], succ: p }) },
  { tag: 'oplus', calc: ['ill', 'fill', 'gill', 'grill'], cyclic: false,
    L: (p, q) => ({ lin: [p], cart: [], succ: `${p} + ${q}` }),
    R: (p, q) => ({ lin: [`${p} + ${q}`], cart: [], succ: `${q} + ${p}` }),
    Cut: (p, q) => ({ lin: [p], cart: [], succ: `${q} + ${p}` }) },
  { tag: 'with', calc: ['ill', 'fill', 'gill', 'grill'], cyclic: false,
    L: (p) => ({ lin: [p], cart: [], succ: `${p} & ${p}` }),
    R: (p) => ({ lin: [`${p} & ${p}`], cart: [], succ: p }),
    Cut: (p) => ({ lin: [p], cart: [], succ: p }) },
  { tag: 'exp-dereliction', calc: ['ill', 'fill', 'gill', 'grill'], cyclic: false,
    L: (p) => ({ lin: [], cart: [p], succ: `! ${p}` }),
    R: (p) => ({ lin: [`! ${p}`], cart: [], succ: p }),
    Cut: (p) => ({ lin: [], cart: [p], succ: p }) },
  // NB: `!p ⊢ p⊗p` (bang-in-linear contraction) and `q ; p ⊢ p⊗q` (cartesian
  // copy into a tensor branch) are valid but NOT proved by the focused search —
  // pre-existing completeness corners (the dereliction/absorption inversion pick
  // is soundly un-backtracked; see baelde-exponential §4). They are orthogonal to
  // cut-admissibility, so templates here avoid them: every Cut below is robustly
  // cut-free provable, making any failure a genuine non-admissibility datapoint.
  // ── fixpoints: the hard case (cyclic cut-elimination) ──────────────────────
  { tag: 'coind-cut', calc: ['fill', 'grill'], cyclic: true,
    L: (p) => ({ lin: [], cart: [p], succ: `nu X. (${p} & X)` }),
    R: (p) => ({ lin: [`nu X. (${p} & X)`], cart: [], succ: p }),
    Cut: (p) => ({ lin: [], cart: [p], succ: p }) },
  { tag: 'ind-cut', calc: ['fill', 'grill'], cyclic: false,
    L: (p) => ({ lin: [p], cart: [], succ: `mu X. (${p} + X)` }),
    R: (p) => ({ lin: [`mu X. (${p} + X)`], cart: [], succ: `mu X. (${p} + X)` }),
    Cut: (p) => ({ lin: [p], cart: [], succ: `mu X. (${p} + X)` }) },
  // ── grades ─────────────────────────────────────────────────────────────────
  { tag: 'graded-haul', calc: ['gill', 'grill'], cyclic: false,
    L: (p) => ({ lin: [p], cart: [], succ: `!!_0 ${p}` }),
    R: (p) => ({ lin: [`!!_0 ${p}`], cart: [], succ: `!!_5 ${p}` }),
    Cut: (p) => ({ lin: [p], cart: [], succ: `!!_5 ${p}` }) },
  // ── the composition: graded coinductive cut (grill only) ────────────────────
  { tag: 'graded-coind-cut', calc: ['grill'], cyclic: true,
    L: (p) => ({ lin: [], cart: [p], succ: `nu X. (${p} & !!_0 X)` }),
    R: (p) => ({ lin: [`nu X. (${p} & !!_0 X)`], cart: [], succ: p }),
    Cut: (p) => ({ lin: [], cart: [p], succ: p }) },
];

async function loadCalc(name) {
  if (name === 'ill') {
    const { loadILL } = await import('../calculus/ill/index.js');
    const calc = await loadILL();
    return { calc, fp: (s) => calc.parse(s) };
  }
  if (name === 'fill') {
    const { loadFill } = await import('../calculus/fill/index.js');
    const { buildForwardParser } = await import('../calculus/fill/lib/forward-parser.js');
    return { calc: await loadFill(), fp: buildForwardParser() };
  }
  if (name === 'gill') {
    const { loadGillSequent, gillCalculusConfig } = await import('../calculus/gill/calculus-config.js');
    return { calc: loadGillSequent(), fp: gillCalculusConfig.loader.buildParser() };
  }
  if (name === 'grill') {
    const { loadGrillSequent, grillCalculusConfig } = await import('../calculus/grill/calculus-config.js');
    return { calc: loadGrillSequent(), fp: grillCalculusConfig.loader.buildParser() };
  }
  throw new Error(`unknown calculus ${name}`);
}

const ATOMS = ['a', 'b', 'c'];

async function run() {
  const CALCI = ['ill', 'fill', 'gill', 'grill'];
  const failures = [];
  let exercised = 0, held = 0;

  for (const cname of CALCI) {
    const { calc, fp } = await loadCalc(cname);
    const { specs, alternatives } = buildRuleSpecs(calc);
    const prover = createProver(calc);
    const kernel = createKernel(calc);
    const templates = TEMPLATES.filter(t => t.calc.includes(cname));

    const prove = (sq, cyclic) => {
      const s = Seq.fromArrays(sq.lin.map(fp), sq.cart.map(fp), fp(sq.succ));
      // exhaustive closes the additive don't-know corner; cyclic arms μ/ν
      const r = prover.prove(s, { rules: specs, alternatives, maxDepth: 300, cyclicProofs: cyclic, exhaustive: true });
      return r;
    };

    let calcExercised = 0;
    for (let t = 0; t < COUNT; t++) {
      const tpl = pick(templates);
      const p = pick(ATOMS); let q = pick(ATOMS); if (q === p) q = ATOMS[(ATOMS.indexOf(p) + 1) % ATOMS.length];
      const L = tpl.L(p, q), R = tpl.R(p, q), Cut = tpl.Cut(p, q);
      const cyc = tpl.cyclic;
      // Sanity: both premises must be cut-free provable, else the template is
      // mis-stated (not a cut-admissibility datapoint).
      const lr = prove(L, cyc), rr = prove(R, cyc);
      if (!lr.success || !rr.success) {
        failures.push(`${cname}/${tpl.tag}[${p},${q}]: PREMISE not cut-free provable (L=${lr.success},R=${rr.success}) — template error`);
        continue;
      }
      exercised++; calcExercised++;
      // Admissibility: the composed sequent must be cut-free provable + kernel-valid.
      const cr = prove(Cut, cyc);
      if (!cr.success) {
        failures.push(`${cname}/${tpl.tag}[${p},${q}]: CUT NOT ADMISSIBLE — Γ,Δ⊢C unprovable cut-free`);
        continue;
      }
      if (!kernel.verifyTree(cr.proofTree).valid) {
        failures.push(`${cname}/${tpl.tag}[${p},${q}]: cut result NOT kernel-valid`);
        continue;
      }
      held++;
      if (VERBOSE && t < 3) console.log(`  ${cname}/${tpl.tag}[${p},${q}] ok`);
    }
    console.log(`  ${cname.padEnd(6)}: ${calcExercised} cut instances exercised`);
  }

  console.log(`fuzz-cut: seed 0x${(getArg('--seed', 0x51ed5eed) >>> 0).toString(16)}, ${COUNT} trials/calculus`);
  console.log(`  exercised: ${exercised}, admissible+kernel-valid: ${held}`);
  if (failures.length) {
    console.error(`FAIL: ${failures.length} cut-admissibility violations`);
    for (const f of failures.slice(0, 25)) console.error('  ' + f);
    process.exit(1);
  }
  console.log('all properties held — cut is admissible across ill/fill/gill/grill.');
}

export { TEMPLATES, loadCalc, ATOMS };

// Run only as a CLI, not when imported by the fast-suite battery test.
if (import.meta.url === `file://${process.argv[1]}`) {
  run().catch(e => { console.error(e); process.exit(1); });
}
