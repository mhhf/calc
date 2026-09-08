/**
 * Timed debug renderings — TODO_0265 Phase 4c.
 *
 * Three read-only views over the SAME settle records (list reading =
 * temporal, DAG reading = causal — the trace↔term duality in debugging
 * form), plus the dual diagnosis of a rule that did NOT fire:
 *
 *   traceLines(events)                — log view: [a] rule consumed → produced @+d
 *   timelineLines(events, initial, T) — per-predicate lanes: jobs + token lifetimes
 *   whyLines(events, initial, fact)   — provenance: walk producer links backward
 *   whyNotLines(rule, state, opts)    — best failed candidate + what killed it
 *
 * Pure functions over plain data (events from settle(), plain states) —
 * the CLI (tools/debug-till.js) and the golden tests share them verbatim.
 * Processes are trace nodes (E7.3): the rule name IS the process kind; no
 * job tokens exist anywhere in the model.
 */

import Store from '../../kernel/store.js';
import { show } from '../show.js';
import { refInner, refStamp } from '../labels.js';
import { ratParts } from '../../kernel/rat-term.js';
import { tryTimedMatch, isAt as _isAt, innerOf as _inner } from './timed.js';
// ─── Formatting primitives ──────────────────────────────────────────

/** Exact stamp string: "n" for integers, "n/d" otherwise. */
function fmtStamp(h) {
  const p = ratParts(h);
  if (!p) return show(h);
  return p[1] === 1n ? String(p[0]) : `${p[0]}/${p[1]}`;
}

/** Fact string `inner@stamp` (stamp 0 for unstamped). */
function fmtFact(h) {
  return _isAt(h)
    ? `${show(Store.child(h, 0))}@${fmtStamp(Store.child(h, 1))}`
    : `${show(h)}@0`;
}

function _facts(obj, mark = '') {
  const out = [];
  for (const [hStr, c] of Object.entries(obj || {})) {
    const s = mark + fmtFact(Number(hStr));
    out.push(c > 1 ? `${s} x${c}` : s);
  }
  return out;
}

// ─── Log view (#trace) ──────────────────────────────────────────────

/** One line per firing: `[a] rule: consumed [read r] → produced @+d`.
 *  Batched firings (TODO_0278 B1) render as ONE line `rule xk:` with
 *  per-fire facts — the log shows what the engine did; the per-token
 *  views below expand the multiplicity instead. */
function traceLines(events) {
  return events.map(e => {
    const lhs = [..._facts(e.consumed), ..._facts(e.reserved, 'read ')].join(', ');
    const rhs = _facts(e.produced).join(', ') || '·';
    const d = e.delay === null || e.delay === undefined ? '' : ` @+${fmtStamp(e.delay)}`;
    const alt = e.alt !== undefined ? ` (alt ${e.alt})` : '';
    const mul = e.multiplicity > 1 ? ` x${e.multiplicity}` : '';
    return `[${fmtStamp(e.activation)}] ${e.rule}${mul}: ${lhs} → ${rhs}${d}${alt}`;
  });
}

// ─── Timeline view (#timeline) ──────────────────────────────────────

/**
 * Per-predicate lanes over token lifetimes. Each token instance is
 * `born→consumer@a` (consumed by an event at its activation) or `born→…`
 * (alive at the horizon); the jobs lane lists firings `rule [a→done]` —
 * in-flight jobs are exactly those with done beyond the horizon.
 */
function timelineLines(events, initialState, T) {
  const lines = [`timeline (T = ${fmtStamp(T)})`, 'jobs:'];
  // Batched events (B1) expand: k fires = k jobs — the per-token views
  // render the RLE-expanded (sequential) semantics.
  const jobs = [];
  for (const e of events) {
    const mul = e.multiplicity || 1;
    for (let i = 0; i < mul; i++) jobs.push(`${e.rule} [${fmtStamp(e.activation)}→${fmtStamp(e.done)}]`);
  }
  lines.push('  ' + (jobs.join('  ') || '(none)'));

  // Token instances per cohort hash: births (initial + produced), deaths
  // (consumed by events, paired in chronological order — fungible within a
  // cohort, D5). Reads are state no-ops and never end a lifetime (E7.2).
  // Batched events carry PER-FIRE counts — multiply by the multiplicity.
  const births = new Map();   // hash -> [bornStampHash, ...]
  const deaths = new Map();   // hash -> [{by, at}, ...]
  for (const [hStr, c] of Object.entries(initialState.linear || {})) {
    const h = Number(hStr);
    const arr = births.get(h) || [];
    for (let i = 0; i < c; i++) arr.push(h);
    births.set(h, arr);
  }
  for (const e of events) {
    const mul = e.multiplicity || 1;
    for (const [hStr, c] of Object.entries(e.produced || {})) {
      const h = Number(hStr);
      const arr = births.get(h) || [];
      for (let i = 0; i < c * mul; i++) arr.push(h);
      births.set(h, arr);
    }
    for (const [hStr, c] of Object.entries(e.consumed || {})) {
      const h = Number(hStr);
      const arr = deaths.get(h) || [];
      for (let i = 0; i < c * mul; i++) arr.push({ by: e.rule, at: e.activation });
      deaths.set(h, arr);
    }
  }

  const lanes = new Map();    // predicate label -> [{born, fate}, ...]
  for (const [h, borns] of births) {
    const label = show(_inner(h));
    const ds = deaths.get(h) || [];
    borns.forEach((_, i) => {
      const born = _isAt(h) ? fmtStamp(Store.child(h, 1)) : '0';
      const fate = i < ds.length ? `${ds[i].by}@${fmtStamp(ds[i].at)}` : '…';
      if (!lanes.has(label)) lanes.set(label, []);
      lanes.get(label).push(`${born}→${fate}`);
    });
  }
  lines.push('tokens:');
  for (const label of [...lanes.keys()].sort()) {
    lines.push(`  ${label}: ${lanes.get(label).sort().join('  ')}`);
  }
  return lines;
}

// ─── Provenance view (#why) ─────────────────────────────────────────

/**
 * Causal tree of a fact: which event produced it, recursively over that
 * event's consumed (and read — they join the activation max) inputs.
 * Facts with no producing event are initial.
 */
function whyLines(events, initialState, factHash) {
  const lines = [];
  // Producers of a cohort hash strictly before event index `bound`,
  // chronological (one entry per produced INSTANCE). Fungible instances
  // resolve nearest-producer-first: instance k takes the (last − k)-th
  // producer; instances beyond the list are initial tokens.
  // Batched events (B1) produce c PER FIRE at multiplicity m — c·m
  // instances, each of which correctly resolves to the event's PER-FIRE
  // consumed inputs (every fire of the batch consumed the same cohorts).
  const producersOf = (h, bound) => {
    const out = [];
    const n = bound === undefined ? events.length : bound;
    for (let i = 0; i < n; i++) {
      const c = (events[i].produced && events[i].produced[h] || 0) * (events[i].multiplicity || 1);
      for (let k = 0; k < c; k++) out.push(i);
    }
    return out;
  };

  function walk(h, instance, prefix, branch, eventBound) {
    const ps = producersOf(h, eventBound);
    const pi = ps.length - 1 - instance;
    if (pi < 0) {
      const initial = (initialState.linear || {})[h] ? ' (initial)' : '';
      lines.push(`${prefix}${branch}${fmtFact(h)}${initial}`);
      return;
    }
    const e = events[ps[pi]];
    const d = e.delay === null || e.delay === undefined ? '' : ` +${fmtStamp(e.delay)}`;
    lines.push(`${prefix}${branch}${fmtFact(h)} ← ${e.rule} @${fmtStamp(e.activation)}${d}`);
    const inputs = [];
    for (const [hStr, c] of Object.entries(e.consumed || {})) {
      for (let k = 0; k < c; k++) inputs.push({ h: Number(hStr), instance: k, read: false });
    }
    for (const hStr of Object.keys(e.reserved || {})) {
      inputs.push({ h: Number(hStr), instance: 0, read: true });
    }
    const childPrefix = prefix + (branch === '' ? '' : (branch.startsWith('└') ? '   ' : '│  '));
    inputs.forEach((inp, k) => {
      const b = (k === inputs.length - 1 ? '└─ ' : '├─ ') + (inp.read ? 'read ' : '');
      walk(inp.h, inp.instance, childPrefix, b, ps[pi]);
    });
  }

  walk(factHash, 0, '', '', undefined);
  return lines;
}

// ─── Failure diagnosis (#why_not) ───────────────────────────────────

/**
 * Why did `rule` not fire (or when will it)? Runs the timed matcher in
 * diagnostic mode against the given state. Reports, in order of depth:
 * a match pending beyond the horizon, a killing before-window, a failing
 * persistent goal, or the shallowest never-satisfied input pattern.
 */
function whyNotLines(rule, state, opts) {
  const { calc, matchOpts, timedConfig: tcfg, horizon } = opts;
  const diag = { deepest: -1 };
  const m = tryTimedMatch(rule, state, calc, matchOpts, tcfg, diag);
  const lines = [`why not ${rule.name}:`];
  if (m) {
    // Labelled state (THY_0024): activations are stamp ids, consumed maps
    // carry packed refs — reify at this rendering boundary.
    const st = state.linear.stamps;
    const aTerm = st.term(m.activation);
    const consumedAt = {};
    for (const k in m.consumed) {
      const ref = Number(k);
      const h = Store.put(tcfg.stampTag, [refInner(ref), st.term(refStamp(ref))]);
      consumedAt[h] = (consumedAt[h] || 0) + m.consumed[k];
    }
    if (horizon !== undefined && tcfg.availability.cmp(aTerm, horizon) > 0) {
      lines.push(`  pending: fires at activation ${fmtStamp(aTerm)} > horizon ${fmtStamp(horizon)}`);
    } else {
      lines.push(`  it CAN fire — activation ${fmtStamp(aTerm)}, consuming ${_facts(consumedAt).join(', ')}`);
    }
    return lines;
  }
  if (diag.window) {
    lines.push(`  best candidate killed by 'before ${fmtStamp(diag.window.bound)}': activation ${fmtStamp(diag.window.activation)} misses the deadline`);
  } else if (diag.goal !== undefined) {
    lines.push(`  best candidate killed by unprovable goal: !${show(diag.goal)}`);
  } else if (diag.leaf) {
    lines.push('  candidates match but none survives the guards');
  } else if (diag.missing !== undefined) {
    const meta = rule.linearMeta[diag.missing];
    lines.push(`  missing input: no fact matches pattern '${show(meta ? meta.body : diag.missing)}'`);
  } else {
    lines.push('  no candidates');
  }
  return lines;
}

export { fmtStamp, fmtFact, traceLines, timelineLines, whyLines, whyNotLines };
