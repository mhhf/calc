/**
 * Inside-mass solver for datasort states (fence B slices 2+3, TODO_0011
 * round-2 spec B3) — ORACLE MACHINERY, not core semantics.
 *
 * This module is NOT imported by the generic engine: it is bound by a
 * CALCULUS CONFIG (will's `datasortMasses` layer entry) and reaches the
 * driver through the calc object — a plugin alongside the configuration.
 * A calculus that binds no solver structurally lacks the concept; a
 * program declaring recursive datasorts under such a calculus is a load
 * error naming the missing binding. The SEMANTICS stays in logic: the
 * mass equations are derivable statements over the declared membership
 * clauses and priors, the solved values materialize as ground `mass s m`
 * facts when the program declares the predicate (index.js, the
 * subsort/prior discipline), and certificates re-verify claimed masses
 * by substitution — the solver only FINDS the solution.
 *
 * m(finite classifier) = Σ ρ(members); m(structured state) =
 * Σ_heads ρ(head)·Π m(child states), restricted to states REACHABLE
 * from structured datasorts, solved bottom-up over the SCC DAG. The
 * linearity fence f4 (≤1 child state per head inside its own SCC) keeps
 * every SCC's system LINEAR over ℚ≥0: m = b + A·m, solved exactly by
 * rational Gaussian elimination. Subcriticality ⟺ (I−A) nonsingular
 * with a nonnegative solution (Perron–Frobenius: a supercritical SCC
 * yields a singular system or a negative entry) — divergence is an
 * error, since a diverging inside mass makes the conditioned sampler
 * meaningless. States are names or canonical product keys (`d1&d2`),
 * resolved uniformly through sortSystem.stateInfo (slice 3).
 */

'use strict';

import { _parseSignature } from '../../../lib/engine/type-check.js';
import { add as ratAdd, sub as ratSub, mul as ratMul, div as ratDiv } from '../../../lib/rat.js';

const R0 = [0n, 1n];
const R1 = [1n, 1n];

function _solveCore(sortSystem, priorsTable, definitions, seeds, masses, errors) {
  const prior = (m) => (priorsTable && priorsTable.get(m)) || R1;
  const sigOf = (m) => {
    const h = definitions && definitions.get(m);
    const sig = h !== undefined ? _parseSignature(h) : null;
    return sig || { argSorts: [], returnSort: null };
  };
  // heads(state) → [{ name, children: [stateName] }] — stateInfo covers
  // declared datasorts AND product keys (slice 3); classifiers fall back
  // to their member signatures.
  const heads = (s) => {
    const info = sortSystem.stateInfo ? sortSystem.stateInfo(s) : null;
    if (info) {
      return [
        ...[...info.members].map((m) => ({ name: m, children: [] })),
        ...[...info.trans.entries()].map(([m, cs]) => ({ name: m, children: cs })),
      ];
    }
    if (sortSystem.isClassifier(s)) {
      return [...sortSystem.membersOf(s)].map((m) => ({ name: m, children: sigOf(m).argSorts }));
    }
    return null;
  };

  // Reachable UNSOLVED states from the seeds (already-solved states are
  // constants of the extension — the lazy product path re-enters here)
  const reach = new Set();
  const stack = seeds.filter((s) => !masses.has(s));
  while (stack.length > 0) {
    const s = stack.pop();
    if (reach.has(s) || masses.has(s)) continue;
    reach.add(s);
    const hs = heads(s);
    if (hs === null) {
      errors.push(`inside mass of '${s}' is not computable — not a classifier or datasort`);
      continue;
    }
    for (const h of hs) for (const c of h.children) if (!masses.has(c)) stack.push(c);
  }
  if (errors.length > 0) return;

  // Tarjan SCCs over the reachable dependency graph
  const idx = new Map(); const low = new Map(); const onStk = new Set();
  const stk = []; const sccOf = new Map(); const sccs = [];
  let counter = 0;
  const strong = (v) => {
    idx.set(v, counter); low.set(v, counter); counter++;
    stk.push(v); onStk.add(v);
    for (const h of heads(v)) for (const w of h.children) {
      if (masses.has(w)) continue;   // already-solved constant
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
  if (errors.length > 0) return;

  // Solve bottom-up: Tarjan emits SCCs in reverse topological order of
  // the condensation — dependencies of a component are emitted BEFORE it.
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
      return;
    }
  }
}

function solveMasses(sortSystem, priorsTable, definitions) {
  const errors = [];
  const ds = sortSystem.datasorts;
  if (!ds || ds.size === 0) return { masses: null, errors };
  const seeds = [...ds.entries()].filter(([, d]) => d.trans.size > 0).map(([n]) => n);
  if (seeds.length === 0) return { masses: null, errors };
  const masses = new Map();
  _solveCore(sortSystem, priorsTable, definitions, seeds, masses, errors);
  return errors.length > 0 ? { masses: null, errors } : { masses, errors };
}

/**
 * Lazy extension (slice 3): solve a PRODUCT state's mass on first use,
 * against the already-solved load-time masses (mutated into calc.masses
 * — deterministic cache semantics). Throws on divergence, like load.
 */
function ensureMass(calc, key) {
  if (!calc.masses) calc.masses = new Map();
  if (calc.masses.has(key)) return calc.masses.get(key);
  const errors = [];
  _solveCore(calc.sorts, calc.priors, calc.definitions, [key], calc.masses, errors);
  if (errors.length > 0) throw new Error(`Datasort masses: ${errors.join('; ')}`);
  return calc.masses.get(key);
}


export { solveMasses, ensureMass };
export default { solveMasses, ensureMass };
