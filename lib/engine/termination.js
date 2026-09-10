/**
 * Termination analysis for forward multiset-rewriting programs
 * (TODO_0009 §6, Inc-6). SOUND, not complete: `terminating` is a PROOF that no
 * infinite rule sequence exists; everything unproven is `unknown`, never a false
 * certificate.
 *
 * Two sound witnesses (Frühwirth CHR ranking / Dershowitz–Manna multiset order):
 *  (a) ACYCLIC — the predicate dependency graph (edge p → q when a rule consumes
 *      p and produces q) has no cycle: no rule can re-enable itself, so firing
 *      chains are finite.
 *  (b) RANKING — a weight w : Pred → ℕ≥0 such that EVERY rule strictly decreases
 *      the weighted total Σ_p w[p]·count(p). A rule contributes w·δ where
 *      δ[p] = (produced p) − (consumed p); strict means w·δ ≤ −1. The total is
 *      bounded below by 0 and strictly decreases each firing, so by
 *      well-foundedness of ℕ no infinite firing sequence exists. Candidate
 *      weights tried: each single predicate (w = e_p — captures "some resource
 *      count strictly depletes", e.g. one request consumed per fire) and the
 *      uniform sum (w = 1). This candidate set is INCOMPLETE (it misses rankings
 *      needing genuinely mixed weights); a miss yields `unknown`, never a wrong
 *      answer.
 *
 * Value-based termination (EVM gas: gas(N) → gas(N−k), same predicate, count
 * unchanged) is out of scope — the count abstraction cannot see the argument —
 * and is reported `unknown`.
 */

/** Tarjan strongly-connected components over an adjacency map (node → [nodes]). */
function tarjanSCC(nodes, adj) {
  let idx = 0;
  const index = new Map(), low = new Map(), onStack = new Set(), stack = [];
  const sccs = [];
  const strongconnect = (v) => {
    index.set(v, idx); low.set(v, idx); idx++;
    stack.push(v); onStack.add(v);
    for (const w of adj.get(v) || []) {
      if (!index.has(w)) { strongconnect(w); low.set(v, Math.min(low.get(v), low.get(w))); }
      else if (onStack.has(w)) { low.set(v, Math.min(low.get(v), index.get(w))); }
    }
    if (low.get(v) === index.get(v)) {
      const comp = []; let w;
      do { w = stack.pop(); onStack.delete(w); comp.push(w); } while (w !== v);
      sccs.push(comp);
    }
  };
  for (const v of nodes) if (!index.has(v)) strongconnect(v);
  return sccs;
}

function multiplicity(arr, x) { let n = 0; for (const e of arr) if (e === x) n++; return n; }

/**
 * @param {Array} rules - [{ name, consume: [predHead], produce: [predHead] }]
 *   (predHead any comparable key). read/persistent facts, being neither consumed
 *   nor produced, are irrelevant to termination and omitted.
 * @returns {{ result: 'terminating'|'unknown', witness, sccs }}
 *   witness: { kind: 'acyclic' } | { kind: 'ranking', ranking: {kind:'single',pred}|{kind:'sum'} } | null
 *   sccs: [{ preds, cyclic }] — the dependency structure, for reporting.
 */
function analyzeTermination(rules) {
  const preds = new Set();
  for (const r of rules) { for (const p of r.consume) preds.add(p); for (const q of r.produce) preds.add(q); }
  const predList = [...preds];

  // dependency graph: p → q when some rule consumes p and produces q
  const adj = new Map();
  for (const p of predList) adj.set(p, []);
  for (const r of rules) {
    for (const p of r.consume) { const o = adj.get(p); for (const q of r.produce) if (!o.includes(q)) o.push(q); }
  }
  const rawSccs = tarjanSCC(predList, adj);
  const sccs = rawSccs.map(comp => ({
    preds: comp,
    cyclic: comp.length > 1 || (comp.length === 1 && adj.get(comp[0]).includes(comp[0])),
  }));
  const anyCyclic = sccs.some(s => s.cyclic);

  // (a) acyclic ⇒ terminating outright
  if (rules.length === 0 || !anyCyclic) {
    return { result: 'terminating', witness: { kind: 'acyclic' }, sccs };
  }

  // (b) global ranking: some weight makes every rule strictly decrease
  const deltas = rules.map(r => {
    const d = new Map();
    for (const p of predList) d.set(p, multiplicity(r.produce, p) - multiplicity(r.consume, p));
    return d;
  });
  const weighted = (w, d) => { let s = 0; for (const p of predList) s += w(p) * d.get(p); return s; };
  const candidates = [
    ...predList.map(p => ({ kind: 'single', pred: p, w: (q) => (q === p ? 1 : 0) })),
    { kind: 'sum', w: () => 1 },
  ];
  for (const c of candidates) {
    if (deltas.every(d => weighted(c.w, d) <= -1)) {
      const ranking = c.kind === 'single' ? { kind: 'single', pred: c.pred } : { kind: 'sum' };
      return { result: 'terminating', witness: { kind: 'ranking', ranking }, sccs };
    }
  }
  return { result: 'unknown', witness: null, sccs };
}

export { analyzeTermination, tarjanSCC };
export default { analyzeTermination, tarjanSCC };
