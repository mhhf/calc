/**
 * dill governance runtime (TODO_0276 / TODO_0318 — P0, Rep1).
 *
 * A thin library over the dill calculus for running governance programs
 * forward and reading consensus back as a derived VIEW. It bundles:
 *   - loadGovernance: load a dill program with dillCalculusConfig;
 *   - decodeFact / decodeNum: structural read-back of settled facts;
 *   - extractGov: the {shares, votes, candidates, currents, says} view over a
 *     settled state — memhub's O = (A, K, <, share, vote) read off the facts;
 *   - the voting KERNELS (threshold / argmax-oldest / n-of-set / priority /
 *     time-locked): pure functions of the view, `(view, P) -> {decided, winner,
 *     ranking}`. This is memhub's consens read-time interpretation L(S(G))→L(G)
 *     (redisc heritage) — argmax needs no NAF because it is a fold OUTSIDE the
 *     transition system, which is exactly why the no-NAF engine constraint never
 *     bites. Threshold consensus can ALSO run in-logic as forward rules (see
 *     calculus/dill/tests/forward/company_cake.ill); this module is the lazy /
 *     derived-view face, the in-logic rules are the eager / enacted face.
 *
 * The forward/backward split (THY_0045/0046): under settle, `says K A` is an
 * opaque structural wrapper — governance rules consume/produce it freely. The
 * entity-veil (`says 1 a ⊬ says 3 a`) lives in the BACKWARD prover (poss_l),
 * reached via the sequent loader for legitimacy queries.
 */

'use strict';

import mde from '../../ill/index.js';
import dillConfig, { loadDillSequent } from '../calculus-config.js';
import convert from '../../../lib/engine/convert.js';
import Store from '../../../lib/kernel/store.js';
import { ratParts, isRatTerm, binVal } from '../../../lib/kernel/rat-term.js';

// ── Loading ────────────────────────────────────────────────────────────────

/** Load a dill governance program for FORWARD execution (settle/exec/prove). */
export function loadGovernance(file, opts = {}) {
  return mde.load(file, { calculusConfig: dillConfig, cache: false, ...opts });
}

/** The BACKWARD sequent calculus (poss_l entity-veil, legitimacy queries). */
export function governanceSequent() {
  return loadDillSequent();
}

// ── Fact injection (the admin/actor `inject` primitive) ───────────────────────

let _fp = null;
/** Parse a bare fact string (e.g. "says 3 (money 300)", "winner 100 10") to a
 *  content-addressed hash via dill's forward parser. */
export function parseFact(str) {
  if (!_fp) _fp = dillConfig.loader.buildParser();
  return _fp(String(str).trim().replace(/^!/, ''));
}

/** Return a NEW state with `str` added. A leading `!` (or persistent:true) routes
 *  to the persistent zone; otherwise it is a linear fact with multiplicity n. */
export function inject(state, str, { persistent = null, n = 1 } = {}) {
  const isPers = persistent === null ? String(str).trim().startsWith('!') : persistent;
  const h = parseFact(str);
  const s = { linear: { ...(state.linear || {}) }, persistent: { ...(state.persistent || {}) } };
  if (isPers) s.persistent[h] = true;
  else s.linear[h] = (s.linear[h] || 0) + n;
  return s;
}

/** Return a NEW state with one occurrence of `str` removed (linear count-- or
 *  persistent delete). No-op if absent. */
export function retract(state, str, { persistent = null } = {}) {
  const isPers = persistent === null ? String(str).trim().startsWith('!') : persistent;
  const h = parseFact(str);
  const s = { linear: { ...(state.linear || {}) }, persistent: { ...(state.persistent || {}) } };
  if (isPers) { delete s.persistent[h]; }
  else if (s.linear[h] > 1) s.linear[h] -= 1;
  else delete s.linear[h];
  return s;
}

/** Build the initial `{linear, persistent}` state from a program query directive
 *  (`#run ... .` → calc.queries; `#... LHS => RHS .` → calc.splitQueries LHS). */
export function initFrom(calc, name) {
  if (calc.queries && calc.queries.has(name)) {
    return convert.decomposeQuery(calc.queries.get(name));
  }
  const split = calc.splitQueries && calc.splitQueries.get(name);
  if (!split) throw new Error(`initFrom: no query '${name}' in program`);
  return convert.decomposeQuery(split.lhsHash);
}

// ── Fact read-back ───────────────────────────────────────────────────────────

/** A numeric fact argument as a JS number, handling both `rat` rationals and
 *  `bin` naturals. Returns NaN for a non-numeric (compound) child. */
export function decodeNum(h) {
  const n = Number(h);
  if (isRatTerm(n)) { const p = ratParts(n); return p ? Number(p[0]) / Number(p[1]) : NaN; }
  const b = binVal(n);
  return b === null || b === undefined ? NaN : Number(b);
}

/** Exact rational [num, den] for a fact argument (rationals and naturals). */
export function decodeRat(h) {
  const n = Number(h);
  if (isRatTerm(n)) { const p = ratParts(n); return p ? [Number(p[0]), Number(p[1])] : null; }
  const b = binVal(n);
  return b === null || b === undefined ? null : [Number(b), 1];
}

/** Recursively decode a fact hash into { pred, args } where each arg is either a
 *  JS number (numeric leaf) or a nested { pred, args } (e.g. the inner formula
 *  of `says K A`). */
export function decodeFact(h) {
  const g = Store.get(Number(h));
  if (!g) return null;
  const args = g.children.map((c) => {
    const num = decodeNum(c);
    if (!Number.isNaN(num)) return num;
    const sub = decodeFact(c);
    return sub || Number(c);
  });
  return { pred: g.tag, args };
}

/** Unwrap the timed `at(inner, stamp)` label carried by linear facts at a state
 *  boundary (THY_0024). Returns { fact, stamp }; a bare fact gets stamp null. */
function unwrapAt(f) {
  if (f && f.pred === 'at' && f.args.length === 2 && typeof f.args[0] === 'object') {
    return { fact: f.args[0], stamp: f.args[1] };
  }
  return { fact: f, stamp: null };
}

/** Every fact of a settled `{linear, persistent}` state, decoded structurally and
 *  UNWRAPPED of the timed `at` label, each tagged with zone / multiplicity / stamp. */
export function decodeState(state) {
  const out = [];
  for (const [h, c] of Object.entries(state.linear || {})) {
    const raw = decodeFact(h); if (!raw) continue;
    const { fact, stamp } = unwrapAt(raw);
    out.push({ ...fact, zone: 'linear', count: c, hash: Number(h), stamp });
  }
  for (const h of Object.keys(state.persistent || {})) {
    const raw = decodeFact(h); if (!raw) continue;
    const { fact, stamp } = unwrapAt(raw);
    out.push({ ...fact, zone: 'persistent', count: 1, hash: Number(h), stamp });
  }
  return out;
}

/**
 * The governance VIEW over a settled state — memhub's O read off the facts.
 * Expects the governance vocabulary:
 *   !share K S            (voter K has voting weight S)
 *   !vote  K P X W        (voter K scores candidate X of proposal P at W∈[0,1])
 *   !candidate P X SEQ    (candidate X of proposal P, SEQ = age; lower = older)
 *   current N T           (a governed cell)
 * plus everything else, kept in `.other` for display.
 */
export function extractGov(state) {
  const facts = decodeState(state);
  const shares = [], votes = [], candidates = [], currents = [], other = [];
  for (const f of facts) {
    if (f.pred === 'share' && f.args.length >= 2) shares.push({ k: f.args[0], s: f.args[1] });
    else if (f.pred === 'vote' && f.args.length >= 4) votes.push({ k: f.args[0], p: f.args[1], x: f.args[2], w: f.args[3] });
    else if (f.pred === 'candidate' && f.args.length >= 3) candidates.push({ p: f.args[0], x: f.args[1], seq: f.args[2] });
    else if (f.pred === 'current' && f.args.length >= 2) currents.push({ n: f.args[0], t: f.args[1] });
    else other.push(f);
  }
  return { shares, votes, candidates, currents, other, facts };
}

// ── Consensus: the memhub value pairing ──────────────────────────────────────

/** value(P, X) = Σ_K share(K) · vote(K, P, X) — the stake-weighted range-vote
 *  pairing (bilinear; the sybil/split-invariance property rests on this). */
export function value(view, P, X) {
  const shareOf = (k) => { const s = view.shares.find((r) => r.k === k); return s ? s.s : 0; };
  return view.votes
    .filter((v) => v.p === P && v.x === X)
    .reduce((acc, v) => acc + shareOf(v.k) * v.w, 0);
}

/** Distinct approvers (vote > 0) of candidate X. */
export function approvers(view, P, X) {
  return new Set(view.votes.filter((v) => v.p === P && v.x === X && v.w > 0).map((v) => v.k)).size;
}

/** Candidates of proposal P with their {x, seq, val, approvers}, ranked by value
 *  desc then age (seq) asc — the canonical redisc/memhub ordering. */
export function ranking(view, P) {
  return view.candidates
    .filter((c) => c.p === P)
    .map((c) => ({ x: c.x, seq: c.seq, val: value(view, P, c.x), approvers: approvers(view, P, c.x) }))
    .sort((a, b) => (b.val - a.val) || (a.seq - b.seq));
}

// ── Voting kernels ───────────────────────────────────────────────────────────
// Each: (view, P, params) -> { decided:boolean, winner:number|null, ranking:[] }.
// `decided` is the eager/enacted question ("is there a committed winner NOW?");
// `winner` is the lazy/derived-view answer ("who leads right now?").

/** argmax Σ share·vote, oldest-wins tie-break (memhub/redisc default consens). */
export function kernelArgmaxOldest(view, P) {
  const r = ranking(view, P);
  return { decided: r.length > 0, winner: r.length ? r[0].x : null, ranking: r };
}

/** Pass iff the leading candidate's value ≥ threshold (how real DAOs decide). */
export function kernelThreshold(view, P, { threshold = 0.5 } = {}) {
  const r = ranking(view, P);
  const top = r[0];
  const decided = !!top && top.val >= threshold;
  return { decided, winner: decided ? top.x : null, ranking: r, threshold };
}

/** Pass iff the leading candidate has ≥ n distinct approvers (n-of-set). */
export function kernelNofSet(view, P, { n = 1 } = {}) {
  const r = ranking(view, P);
  // re-rank by approver count first for this kernel's decision, keep value order for display
  const top = r.slice().sort((a, b) => (b.approvers - a.approvers) || (a.seq - b.seq))[0];
  const decided = !!top && top.approvers >= n;
  return { decided, winner: decided ? top.x : null, ranking: r, n };
}

/** Fixed priority order over candidate ids: first present candidate with any
 *  support wins (deterministic tie-free kernel; e.g. a chair's agenda). */
export function kernelPriority(view, P, { order = [] } = {}) {
  const r = ranking(view, P);
  for (const x of order) {
    const c = r.find((e) => e.x === x && e.val > 0);
    if (c) return { decided: true, winner: x, ranking: r, order };
  }
  return { decided: false, winner: null, ranking: r, order };
}

/** Time-locked: run an inner kernel, but only `decided` once now ≥ deadline. */
export function kernelTimeLocked(view, P, { deadline = 0, now = 0, inner = kernelArgmaxOldest, innerParams = {} } = {}) {
  const res = inner(view, P, innerParams);
  const open = now >= deadline;
  return { ...res, decided: open && res.decided, winner: open ? res.winner : null, deadline, now, locked: !open };
}

export const KERNELS = {
  'argmax-oldest': kernelArgmaxOldest,
  'threshold': kernelThreshold,
  'n-of-set': kernelNofSet,
  'priority': kernelPriority,
  'time-locked': kernelTimeLocked,
};

/** Run a named kernel. */
export function consensus(view, P, kernelName = 'argmax-oldest', params = {}) {
  const k = KERNELS[kernelName];
  if (!k) throw new Error(`consensus: unknown kernel '${kernelName}' (have: ${Object.keys(KERNELS).join(', ')})`);
  return k(view, P, params);
}

export default {
  loadGovernance, governanceSequent, initFrom,
  parseFact, inject, retract,
  decodeNum, decodeRat, decodeFact, decodeState, extractGov,
  value, approvers, ranking,
  kernelArgmaxOldest, kernelThreshold, kernelNofSet, kernelPriority, kernelTimeLocked,
  KERNELS, consensus,
};
