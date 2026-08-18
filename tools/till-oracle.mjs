// till-oracle.mjs — executable reference semantics for till (timed graded rewriting).
//
// This is the GROUND TRUTH the engine implementation (todo 0265, Phases 3-4) is
// differentially tested against. It implements, directly from the spec:
//   - timed multiset states: cohorts (atom, stamp) -> count, stamps exact rationals
//   - per-rule MIN-ACTIVATION matching with FIFO tie-break (spec Pseudocode P1):
//     branch-and-bound over stamp-sorted cohorts; NOT lexicographic-first
//   - activation a(m) = max(selected stamps, after-bounds); validity a(m) < min(before)
//   - settle(state, T): fire matches in nondecreasing activation while a(m) <= T (P2)
//   - count grades: `count: k` splits k off one cohort, `countVar` binds the whole
//     cohort's size at firing time (D4); `mode: 'read'` = test arc, original stamp (E7.2)
//   - conflict chooser: stateless content-derived PRF (D17 / P5); Zeno guard (D16)
//
// Deliberately NOT here: term/argument matching (the engine's existing matcher owns
// that); atoms are plain strings. Guards/delays/outputs are host functions of the
// binding th = { stamps: {var: Rat}, counts: {var: int} }.
//
// Rationals are exact (BigInt pairs). Inputs accept: integer Number, "a/b", "1.5"
// (parsed digit-wise — never through a float), or a Rat. NEVER pass non-integer
// Numbers: rat(0.1) throws.

// ── exact rationals ─────────────────────────────────────────────────
const bgcd = (a, b) => { a = a < 0n ? -a : a; b = b < 0n ? -b : b; while (b) [a, b] = [b, a % b]; return a; };

function rat(x) {
  if (x && typeof x === 'object' && 'n' in x) return x;
  if (typeof x === 'number') {
    if (!Number.isInteger(x)) throw new Error(`rat(${x}): non-integer Number; pass a string`);
    return { n: BigInt(x), d: 1n };
  }
  const s = String(x).trim();
  let m;
  if ((m = s.match(/^(-?\d+)\/(\d+)$/))) return norm(BigInt(m[1]), BigInt(m[2]));
  if ((m = s.match(/^(-?)(\d+)\.(\d+)$/)))
    return norm(BigInt(m[1] + m[2] + m[3]), 10n ** BigInt(m[3].length));
  if ((m = s.match(/^-?\d+$/))) return { n: BigInt(s), d: 1n };
  throw new Error(`rat: cannot parse ${s}`);
}
function norm(n, d) {
  if (d === 0n) throw new Error('rat: zero denominator');
  if (d < 0n) { n = -n; d = -d; }
  const g = bgcd(n, d) || 1n;
  return { n: n / g, d: d / g };
}
const radd = (a, b) => norm(a.n * b.d + b.n * a.d, a.d * b.d);
const rcmp = (a, b) => { const l = a.n * b.d, r = b.n * a.d; return l < r ? -1 : l > r ? 1 : 0; };
const rmax = (a, b) => (rcmp(a, b) >= 0 ? a : b);
const rstr = (a) => (a.d === 1n ? `${a.n}` : `${a.n}/${a.d}`);
const R0 = rat(0);

// ── timed multiset state ────────────────────────────────────────────
// state: Map key `atom@stamp` -> { atom, stamp: Rat, count }
const key = (atom, stamp) => `${atom}@${rstr(stamp)}`;

function makeState(init) {
  // init: [ [atom, stamp, count?] ... ]  (unstamped initial atoms: pass stamp 0 — D11)
  const st = new Map();
  for (const [atom, stamp, count = 1] of init) addFact(st, atom, rat(stamp), count);
  return st;
}
function addFact(st, atom, stamp, count) {
  const k = key(atom, stamp);
  const c = st.get(k);
  if (c) c.count += count; else st.set(k, { atom, stamp, count });
}
function removeFact(st, atom, stamp, count) {
  const k = key(atom, stamp);
  const c = st.get(k);
  if (!c || c.count < count) throw new Error(`consume underflow: ${k}`);
  c.count -= count;
  if (c.count === 0) st.delete(k);
}
// cohorts of one atom, oldest stamp first (the FIFO index order — spec D5/D12)
const cohorts = (st, atom) => [...st.values()].filter(c => c.atom === atom).sort((a, b) => rcmp(a.stamp, b.stamp));

const cloneState = (st) => { const m = new Map(); for (const [k, c] of st) m.set(k, { ...c }); return m; };
const stateEq = (a, b) => a.size === b.size && [...a].every(([k, c]) => b.get(k)?.count === c.count);

// ── P1: per-rule minimal-activation match (branch & bound, FIFO tie-break) ──
// rule: { name, inputs: [{ atom, count?, countVar?, stampVar?, stamp?, mode? }],
//         guards?: [th=>bool], after?: [th=>Rat], before?: [th=>Rat],
//         delay?: Rat|string|th=>Rat, outputs?: th=>[[atom,count?]] | [[atom,count?]] }
function bestMatch(rule, st) {
  const ins = rule.inputs;
  let best = null;
  const taken = new Map(); // key -> reserved count within this candidate (consume AND read)

  const search = (i, sel, partialA) => {
    if (best && rcmp(partialA, best.a) >= 0) return;               // prune: max only grows
    if (i === ins.length) {
      const th = { stamps: {}, counts: {} };
      for (let j = 0; j < ins.length; j++) {
        if (ins[j].stampVar) th.stamps[ins[j].stampVar] = sel[j].stamp;
        if (ins[j].countVar) th.counts[ins[j].countVar] = sel[j].take;
      }
      for (const g of rule.guards ?? []) if (!g(th)) return;
      let a = partialA;
      for (const f of rule.after ?? []) a = rmax(a, rat(f(th)));   // after: lower bounds join
      for (const f of rule.before ?? [])
        if (rcmp(a, rat(f(th))) >= 0) return;                      // deadline: a < before
      if (!best || rcmp(a, best.a) < 0)                            // strict < : first-found
        best = { rule, a, sel: sel.slice(), th };                  //   at equal a wins = FIFO
      return;
    }
    const spec = ins[i];
    for (const c of cohorts(st, spec.atom)) {                      // oldest first
      if (spec.stamp !== undefined && rcmp(c.stamp, rat(spec.stamp)) !== 0) continue;
      const avail = c.count - (taken.get(key(c.atom, c.stamp)) ?? 0);
      const need = spec.countVar ? avail : (spec.count ?? 1);      // countVar: whole cohort
      if (need < 1 || avail < need) continue;
      const k = key(c.atom, c.stamp);
      taken.set(k, (taken.get(k) ?? 0) + need);
      sel.push({ atom: c.atom, stamp: c.stamp, take: need, mode: spec.mode ?? 'consume' });
      search(i + 1, sel, rmax(partialA, c.stamp));                 // read stamps join too (E7.2)
      sel.pop();
      taken.set(k, taken.get(k) - need);
    }
  };
  search(0, [], R0);
  return best;
}

// ── P5: content-derived PRF chooser (stateless, D17) ────────────────
const mix32 = (x) => {
  x = Math.imul(x ^ (x >>> 16), 0x45d9f3b);
  x = Math.imul(x ^ (x >>> 13), 0x45d9f3b);
  return (x ^ (x >>> 16)) >>> 0;
};
const strHash = (s) => { let h = 2166136261; for (let i = 0; i < s.length; i++) h = Math.imul(h ^ s.charCodeAt(i), 16777619); return h >>> 0; };
const stateHash = (st) => [...st.keys()].reduce((h, k) => (h ^ mix32(strHash(k) ^ st.get(k).count)) >>> 0, 0);
const matchKey = (m) => `${m.rule.name}|${m.sel.map(s => `${s.atom}@${rstr(s.stamp)}x${s.take}`).join(',')}`;

function choose(tied, st, seed) {
  if (tied.length === 1) return tied[0];
  const sorted = tied.slice().sort((x, y) => matchKey(x) < matchKey(y) ? -1 : 1);
  const candHash = sorted.reduce((h, m) => (h ^ mix32(strHash(matchKey(m)))) >>> 0, 0);
  const r = mix32((seed >>> 0) ^ stateHash(st) ^ candHash);
  return sorted[r % sorted.length];
}

// ── P2: settle ──────────────────────────────────────────────────────
function settle(state, T, opts = {}) {
  const st = cloneState(state);
  const horizon = rat(T);
  const maxSteps = opts.maxSteps ?? 100000;                        // Zeno guard (D16)
  const seed = opts.seed ?? 0;
  const log = opts.log ?? [];
  for (let step = 0; step < maxSteps; step++) {
    const cands = opts.rules.map(r => bestMatch(r, st)).filter(Boolean);
    if (!cands.length) return { state: st, log };                  // quiescent
    let aMin = cands[0].a;
    for (const m of cands) if (rcmp(m.a, aMin) < 0) aMin = m.a;
    if (rcmp(aMin, horizon) > 0) return { state: st, log };        // horizon: future pending
    const m = choose(cands.filter(c => rcmp(c.a, aMin) === 0), st, seed);
    const d = rat(typeof m.rule.delay === 'function' ? m.rule.delay(m.th) : (m.rule.delay ?? 0));
    for (const s of m.sel) if (s.mode !== 'read') removeFact(st, s.atom, s.stamp, s.take);
    const outs = typeof m.rule.outputs === 'function' ? m.rule.outputs(m.th) : (m.rule.outputs ?? []);
    const done = radd(m.a, d);
    for (const [atom, count = 1] of outs) if (count > 0) addFact(st, atom, done, count);
    log.push({ rule: m.rule.name, a: m.a, d, done, sel: m.sel.map(s => ({ ...s })) });
  }
  throw new Error(`settle: maxSteps=${maxSteps} exceeded (Zeno? — check zero-delay cycles)`);
}

const nextActivation = (state, rules) => {
  let aMin = null;
  for (const r of rules) { const m = bestMatch(r, state); if (m && (!aMin || rcmp(m.a, aMin) < 0)) aMin = m.a; }
  return aMin;
};

// ── views ───────────────────────────────────────────────────────────
const observable = (st, T) => {                                     // stamp <= T slice (E5)
  const t = rat(T), out = {};
  for (const c of st.values()) if (rcmp(c.stamp, t) <= 0) out[c.atom] = (out[c.atom] ?? 0) + c.count;
  return out;
};
const pending = (st, T) => [...st.values()].filter(c => rcmp(c.stamp, rat(T)) > 0)
  .sort((a, b) => rcmp(a.stamp, b.stamp));
const inFlight = (log, T) => {                                      // E7.3: events s <= T < s+d
  const t = rat(T);
  return log.filter(e => rcmp(e.a, t) <= 0 && rcmp(t, e.done) < 0)
    .map(e => ({ rule: e.rule, a: e.a, done: e.done }));
};

export { rat, radd, rcmp, rmax, rstr, makeState, cloneState, stateEq, bestMatch, settle, nextActivation, observable, pending, inFlight };
