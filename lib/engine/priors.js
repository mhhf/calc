/**
 * Constructor priors — `name: sort @w Q.` (TODO_0292 D5/M6, will P1).
 *
 * Generic machinery, presence-gated: a program without @w annotations has
 * no priors (absent, not disabled), and no sort name or weight appears in
 * engine JS. Priors are DATA (D5): they enter the logic only through
 * collapse — the decimation driver (P2) and the ∃_ρ existential (P3) —
 * never as facts; the in-logic evidence surface is bias facts (M8).
 * Weights are unnormalized ratios in ℚ≥0 (M6): renormalization over the
 * live domain happens at collapse, an unannotated member weighs 1, and 0
 * is legal (dead unless nothing else remains).
 *
 * This module validates the parsed table against the sort system and
 * computes the Chi–Geman subcriticality advisory (THY_0026 T2): per
 * classifier, m = Σ_c share(c)·arity_rec(c) ≤ 1 ⟺ the branching process
 * of lazy collapse is (sub)critical ⟺ generation terminates almost
 * surely. At rung 1 classifier members are atomic (arity 0, m = 0); the
 * check arms itself the day datasort members with recursive arguments
 * land (P3). Advisory at load (M7) — the decimation driver, not the
 * loader, hard-errors on supercritical priors without a depth bound.
 */

'use strict';

import { _parseSignature } from './type-check.js';
import { add as ratAdd, sub as ratSub, mul as ratMul, div as ratDiv } from '../rat.js';

/**
 * Validate a priors table and compute per-classifier subcriticality.
 * @param {Map<string,[bigint,bigint]>} priorsTable  member → weight [n,d]
 * @param {Object|null} sortSystem  buildSortSystem result (null = sortless)
 * @param {Map<string,number>} definitions  name → signature hash
 * @returns {{errors: string[], advice: Array}}
 */
function checkPriors(priorsTable, sortSystem, definitions) {
  const errors = [];
  const advice = [];
  if (!priorsTable || priorsTable.size === 0) return { errors, advice };
  if (!sortSystem) {
    errors.push(`@w priors need the sorts machinery — import your calculus's sorts prelude (priors annotate classifier members)`);
    return { errors, advice };
  }
  const touched = new Set();
  for (const [name] of priorsTable) {
    const s = sortSystem.leastSortOfName(name);
    if (!s || !sortSystem.isClassifier(s)) {
      errors.push(`'${name}': @w prior on a non-member — priors annotate members of a classifier sort ('${name}: <sort> @w Q.')`);
      continue;
    }
    touched.add(s);
  }

  // Chi–Geman (T2) per touched classifier, over ALL its members (default
  // weight 1). Floats suffice: the check is an advisory threshold, never
  // a semantic input.
  for (const s of touched) {
    let total = 0;
    let msum = 0;
    for (const member of sortSystem.membersOf(s)) {
      const w = priorsTable.get(member) || [1n, 1n];
      const wf = Number(w[0]) / Number(w[1]);
      total += wf;
      const sigHash = definitions.get(member);
      const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
      const rec = sig
        ? sig.argSorts.filter((a) => a === s || sortSystem.subsort(a, s)).length
        : 0;
      msum += wf * rec;
    }
    const m = total > 0 ? msum / total : 0;
    if (m > 1) {
      advice.push({ kind: 'supercritical-prior', sort: s, m });
    }
  }
  return { errors, advice };
}

// ── Inside masses (fence B slice 2, TODO_0011 round-2 spec B3) ──
//
// The mass of a STATE (a classifier ⊤ or a datasort) is the total prior
// mass of its language: m(finite classifier) = Σ ρ(members);
// m(structured state) = Σ_heads ρ(head)·Π m(child states). Restricted to
// states REACHABLE from structured datasorts (presence-gated — programs
// without recursive datasorts never enter here), solved bottom-up over
// the SCC DAG. The linearity fence f4 (each head has at most ONE child
// state inside its own SCC) keeps every SCC's system LINEAR over ℚ≥0:
// m = b + A·m, solved exactly by Gaussian elimination. Subcriticality ⟺
// (I−A) nonsingular with nonnegative solution (Perron–Frobenius: a
// supercritical SCC yields a singular system or a negative entry) —
// divergence is a load error, since a diverging inside mass makes the
// conditioned sampler meaningless.

const R0 = [0n, 1n];
const R1 = [1n, 1n];

function solveMasses(sortSystem, priorsTable, definitions) {
  const errors = [];
  const ds = sortSystem.datasorts;
  if (!ds || ds.size === 0) return { masses: null, errors };
  const seeds = [...ds.entries()].filter(([, d]) => d.trans.size > 0).map(([n]) => n);
  if (seeds.length === 0) return { masses: null, errors };

  const prior = (m) => (priorsTable && priorsTable.get(m)) || R1;
  const sigOf = (m) => {
    const h = definitions && definitions.get(m);
    const sig = h !== undefined ? _parseSignature(h) : null;
    return sig || { argSorts: [], returnSort: null };
  };
  // heads(state) → [{ name, children: [stateName] }]
  const heads = (s) => {
    if (ds.has(s)) {
      const d = ds.get(s);
      return [
        ...[...d.members].map((m) => ({ name: m, children: [] })),
        ...[...d.trans.entries()].map(([m, cs]) => ({ name: m, children: cs })),
      ];
    }
    if (sortSystem.isClassifier(s)) {
      return [...sortSystem.membersOf(s)].map((m) => ({ name: m, children: sigOf(m).argSorts }));
    }
    return null;
  };

  // Reachable states from the structured seeds
  const reach = new Set();
  const stack = [...seeds];
  while (stack.length > 0) {
    const s = stack.pop();
    if (reach.has(s)) continue;
    reach.add(s);
    const hs = heads(s);
    if (hs === null) {
      errors.push(`inside mass of '${s}' is not computable — not a classifier or datasort`);
      continue;
    }
    for (const h of hs) for (const c of h.children) stack.push(c);
  }
  if (errors.length > 0) return { masses: null, errors };

  // Tarjan SCCs over the reachable dependency graph
  const idx = new Map(); const low = new Map(); const onStk = new Set();
  const stk = []; const sccOf = new Map(); const sccs = [];
  let counter = 0;
  const strong = (v) => {
    idx.set(v, counter); low.set(v, counter); counter++;
    stk.push(v); onStk.add(v);
    for (const h of heads(v)) for (const w of h.children) {
      if (!idx.has(w)) { strong(w); low.set(v, Math.min(low.get(v), low.get(w))); }
      else if (onStk.has(w)) low.set(v, Math.min(low.get(v), idx.get(w)));
    }
    if (low.get(v) === idx.get(v)) {
      const comp = [];
      for (;;) { const w = stk.pop(); onStk.delete(w); comp.push(w); sccOf.set(w, sccs.length); if (w === v) break; }
      sccs.push(comp);
    }
  };
  for (const s of reach) if (!idx.has(s)) strong(s);

  // f4 (linearity): within an SCC, every head has ≤ 1 child in the SCC
  for (const comp of sccs) {
    const inC = new Set(comp);
    for (const s of comp) {
      for (const h of heads(s)) {
        const k = h.children.filter((c) => inC.has(c)).length;
        if (k > 1) {
          errors.push(`'${s}': head '${h.name}' has ${k} recursive arguments in its own SCC — nonlinear mass system (fence B″: tree-shaped inside masses are algebraic, not yet landed); restructure or drop the datasort`);
        }
      }
    }
  }
  if (errors.length > 0) return { masses: null, errors };

  // Solve bottom-up: Tarjan emits SCCs in reverse topological order of
  // the condensation — dependencies of a component are emitted BEFORE it.
  const masses = new Map();
  for (const comp of sccs) {
    const inC = new Set(comp);
    const selfRef = comp.length > 1 ||
      heads(comp[0]).some((h) => h.children.includes(comp[0]));
    if (!selfRef) {
      const s = comp[0];
      let total = R0;
      for (const h of heads(s)) {
        let w = prior(h.name);
        for (const c of h.children) w = ratMul(w, masses.get(c));
        total = ratAdd(total, w);
      }
      masses.set(s, total);
      continue;
    }
    // linear system (I − A) m = b over the component
    const n = comp.length;
    const pos = new Map(comp.map((s, i) => [s, i]));
    const A = Array.from({ length: n }, () => Array.from({ length: n }, () => R0));
    const b = Array.from({ length: n }, () => R0);
    for (const s of comp) {
      const i = pos.get(s);
      for (const h of heads(s)) {
        let coeff = prior(h.name);
        let internal = -1;
        for (const c of h.children) {
          if (inC.has(c)) internal = pos.get(c);           // ≤1 by f4
          else coeff = ratMul(coeff, masses.get(c));
        }
        if (internal < 0) b[i] = ratAdd(b[i], coeff);
        else A[i][internal] = ratAdd(A[i][internal], coeff);
      }
    }
    // Gaussian elimination on M = I − A, rhs = b
    const M = Array.from({ length: n }, (_, i) =>
      Array.from({ length: n }, (_, j) => ratSub(i === j ? R1 : R0, A[i][j])));
    const rhs = b.map((x) => x);
    let singular = false;
    for (let col = 0; col < n && !singular; col++) {
      let piv = -1;
      for (let r = col; r < n; r++) if (M[r][col][0] !== 0n) { piv = r; break; }
      if (piv < 0) { singular = true; break; }
      [M[col], M[piv]] = [M[piv], M[col]];
      [rhs[col], rhs[piv]] = [rhs[piv], rhs[col]];
      for (let r = 0; r < n; r++) {
        if (r === col || M[r][col][0] === 0n) continue;
        const f = ratDiv(M[r][col], M[col][col]);
        for (let c2 = col; c2 < n; c2++) M[r][c2] = ratSub(M[r][c2], ratMul(f, M[col][c2]));
        rhs[r] = ratSub(rhs[r], ratMul(f, rhs[col]));
      }
    }
    if (!singular) {
      for (let i = 0; i < n; i++) {
        const m = ratDiv(rhs[i], M[i][i]);
        if (m === null || m[0] < 0n) { singular = true; break; }
        masses.set(comp[i], m);
      }
    }
    if (singular) {
      errors.push(`inside masses of {${comp.join(', ')}} diverge — the recursion is critical or supercritical (Chi–Geman); rebalance @w so the branching mass falls below 1`);
      return { masses: null, errors };
    }
  }
  return { masses, errors };
}

export { checkPriors, solveMasses };
export default { checkPriors, solveMasses };
