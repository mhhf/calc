/**
 * forward-trace/v2 — canonical JSON serialization of a forward or
 * symbolic execution trace. Sibling of proof-tree/v1 (serialize-tree.js);
 * shares the formula-pool machinery (`_newContext`, `makeRef`).
 *
 * v2 (TODO_0265 Phase 4c) adds optional per-step timed fields
 * (`activation`, `delay`) as formula-pool refs; it is a backward-compatible
 * superset of v1 (consumers ignore unknown fields).
 *
 * The pipeline is:
 *
 *   .ill file → mde.load() → calc.explore(state, { evidence: true })
 *       → ExploreTree (internal, FactSet-backed)
 *       → serializeExploreTree(...)
 *       → { formula pool, tree skeleton, leaves array }
 *
 * ExploreTree internals are VERY large (1987 nodes / 8733 total trace
 * steps for multisig_nocall_solc_symbolic.ill). We ship a tree
 * SKELETON (just rule names + structural type, no state, no trace)
 * plus a LEAVES array (one per leaf: final state + status + trace
 * step count). Per-leaf traces are NOT embedded by default — the
 * viewer fetches them on demand via a separate entry point
 * (`extractLeafTrace`), so first paint stays in the tens of KB.
 *
 * Top-level shape:
 *   {
 *     format: "forward-trace/v2",
 *     mode: "symex" | "exec",
 *     calculus: string,
 *     profile: string,
 *     formulas: { [key]: FormulaAST },         // shared pool (see serialize-tree.js)
 *     queryVars: string[],                     // user-declared binder names
 *     initial: { linear: [[ref, n], ...], persistent: [ref, ...] },
 *     stats: {
 *       totalNodes, branchCount, leafCount, maxDepth,
 *       totalTraceSteps, maxTraceLen
 *     },
 *     tree: TreeNode,
 *     leaves: Leaf[]
 *   }
 *
 * TreeNode:
 *   | { id, idx, type: "branch", children: [{ rule, choice?, child }] }
 *   | { id, idx, type: "leaf",   leafIndex: N, status: "STOP"|... }
 *   | { id, idx, type: "bound"|"cycle"|"memo"|"dead" }
 *   | { id, idx, type: "branch", elided: true, children: [] }     // lazy stub
 *
 * Leaf (no trace in first payload):
 *   {
 *     leafIndex, id, status, stepCount,
 *     state: { linear: [[ref, n], ...], persistent: [ref, ...] }
 *   }
 *
 * Trace step (extractLeafTrace output):
 *   { step, ruleName, consumed: [[ref, n], ...] }
 *
 * Stability: `idx` is the DFS preorder index of the node inside the
 * serialized tree (0-based). `id` is `"n" + idx` — stable across
 * calls given the same explore output (explore.js traverses rules
 * deterministically). The leaves array is indexed by DFS-leaf-order
 * and carries the same id as its TreeNode counterpart.
 */

'use strict';

import { _newContext, serializeFormula } from './serialize-tree.js';
import { toObject } from '../engine/fact-set.js';
import { classifyLeaf } from '../engine/show.js';
// v2 (TODO_0265 Phase 4c): trace steps optionally carry timed fields —
// `activation` and `delay` as formula-pool refs (settle event records).
// Consumers ignore unknown fields, so v2 is a superset of v1.
const FORMAT_VERSION = 'forward-trace/v2';

function idOf(idx) { return 'n' + idx; }

/**
 * Serialize a state (FactSet or plain object) into pool-referenced form.
 * Returns { linear: [[ref, count], ...], persistent: [ref, ...] }.
 */
function serializeState(state, ctx) {
  if (!state) return { linear: [], persistent: [] };
  // Accept both FactSet (has .linear.group) and plain {linear, persistent} objects.
  let linear, persistent;
  if (state.linear && typeof state.linear.group === 'function') {
    const obj = toObject(state);
    linear = obj.linear;
    persistent = obj.persistent;
  } else {
    linear = state.linear || {};
    persistent = state.persistent || {};
  }
  const linPairs = [];
  for (const h of Object.keys(linear)) {
    const n = Number(h);
    const ref = serializeFormula(n, ctx);
    if (ref !== null) linPairs.push([ref, linear[h]]);
  }
  const perRefs = [];
  for (const h of Object.keys(persistent)) {
    const n = Number(h);
    const ref = serializeFormula(n, ctx);
    if (ref !== null) perRefs.push(ref);
  }
  return { linear: linPairs, persistent: perRefs };
}

/**
 * Serialize a trace stack (from evidence mode) into pool-referenced steps.
 */
function serializeTrace(trace, ctx) {
  if (!Array.isArray(trace)) return [];
  const steps = new Array(trace.length);
  for (let i = 0; i < trace.length; i++) {
    const t = trace[i];
    // Untimed evidence records carry a rule OBJECT; settle event records
    // (timed.js) carry the rule NAME directly.
    const ruleName = (t.rule && t.rule.name)
      || (typeof t.rule === 'string' ? t.rule : null) || '(anonymous)';
    const consumedPairs = [];
    const consumed = t.consumed || {};
    for (const h of Object.keys(consumed)) {
      const ref = serializeFormula(Number(h), ctx);
      if (ref !== null) consumedPairs.push([ref, consumed[h]]);
    }
    steps[i] = { step: i + 1, ruleName, consumed: consumedPairs };
    // Batched firing (TODO_0278 B1): consumed pairs are PER FIRE; the
    // record RLE-expands to `multiplicity` sequential steps.
    if (t.multiplicity > 1) steps[i].multiplicity = t.multiplicity;
    // Timed fields (v2): activation/delay stamps as pool refs.
    if (t.activation !== undefined) {
      steps[i].activation = serializeFormula(t.activation, ctx);
      if (t.delay !== null && t.delay !== undefined) {
        steps[i].delay = serializeFormula(t.delay, ctx);
      }
    }
  }
  return steps;
}

/**
 * Recursive DFS serialization of an explore tree. Collects leaves into
 * `leavesOut` (pushed in DFS order, each carrying the same `id` as its
 * TreeNode). Does NOT inline the trace on leaves — per-leaf trace
 * extraction is done lazily via `extractLeafTrace` to keep first paint
 * small for huge trees.
 *
 * stats: { totalNodes, branchCount, leafCount, maxDepth,
 *          totalTraceSteps, maxTraceLen } — mutated in place.
 */
function walkExploreTree(node, depth, ctx, leavesOut, stats, idxRef) {
  const idx = idxRef.next++;
  const id = idOf(idx);
  stats.totalNodes++;
  if (depth > stats.maxDepth) stats.maxDepth = depth;

  if (node.type === 'leaf') {
    stats.leafCount++;
    const traceLen = node.trace ? node.trace.length : 0;
    stats.totalTraceSteps += traceLen;
    if (traceLen > stats.maxTraceLen) stats.maxTraceLen = traceLen;
    const status = classifyLeaf(node.state, ctx.leafPolicy);
    const serState = serializeState(node.state, ctx);
    const leafIndex = leavesOut.length;
    leavesOut.push({
      leafIndex, id, status,
      stepCount: traceLen,
      state: serState,
    });
    return { id, idx, type: 'leaf', leafIndex, status };
  }

  if (node.type === 'branch') {
    stats.branchCount++;
    const children = new Array(node.children.length);
    for (let i = 0; i < node.children.length; i++) {
      const ch = node.children[i];
      const childNode = walkExploreTree(ch.child, depth + 1, ctx, leavesOut, stats, idxRef);
      const out = { rule: ch.rule, child: childNode };
      if (ch.choice !== undefined) out.choice = ch.choice;
      children[i] = out;
    }
    return { id, idx, type: 'branch', children };
  }

  // 'bound' | 'cycle' | 'memo' | 'dead' — terminal markers
  return { id, idx, type: node.type };
}

/**
 * Public API: serialize an explore() result into a forward-trace/v2
 * payload. `initialState` is the state handed to explore() — we
 * serialize it too so the viewer can render the "starting point" of
 * the execution. `queryVars` is the list of user-supplied binder
 * names from `#symex [V1 V2 ...]` (for display; the engine already
 * freshened them to `_q0`, `_q1`, ...).
 */
function serializeExploreTree(tree, opts = {}) {
  const ctx = _newContext(opts);
  // Leaf classification policy is calculus data (cc.domain.classifyLeafPolicy)
  // threaded by the caller; absent → the neutral policy (RES_0143 L2).
  ctx.leafPolicy = opts.leafPolicy;
  const stats = {
    totalNodes: 0, branchCount: 0, leafCount: 0, maxDepth: 0,
    totalTraceSteps: 0, maxTraceLen: 0,
  };
  const leaves = [];
  const root = walkExploreTree(tree, 0, ctx, leaves, stats, { next: 0 });
  const initial = opts.initialState ? serializeState(opts.initialState, ctx) : { linear: [], persistent: [] };
  const out = {
    format: FORMAT_VERSION,
    mode: opts.mode || 'symex',
    calculus: ctx.calculus,
    profile: ctx.profile,
    queryVars: Array.isArray(opts.queryVars) ? opts.queryVars.slice() : [],
    initial,
    stats,
    formulas: ctx.formulas,
    tree: root,
    leaves,
  };
  return out;
}

/**
 * Serialize a single exec() trace (linear, no branching). Produces a
 * forward-trace/v2 payload with mode: "exec" and a single synthesized
 * leaf whose trace is the step list.
 */
function serializeExecTrace(finalState, trace, opts = {}) {
  const ctx = _newContext(opts);
  const steps = serializeTrace(trace || [], ctx);
  const initial = opts.initialState ? serializeState(opts.initialState, ctx) : { linear: [], persistent: [] };
  const finalSer = serializeState(finalState, ctx);
  const status = classifyLeaf(finalState, opts.leafPolicy);
  const leafId = idOf(1);
  return {
    format: FORMAT_VERSION,
    mode: 'exec',
    calculus: ctx.calculus,
    profile: ctx.profile,
    queryVars: Array.isArray(opts.queryVars) ? opts.queryVars.slice() : [],
    initial,
    stats: {
      totalNodes: 2, branchCount: 0, leafCount: 1,
      maxDepth: 1, totalTraceSteps: steps.length, maxTraceLen: steps.length,
    },
    formulas: ctx.formulas,
    tree: {
      id: idOf(0), idx: 0, type: 'branch',
      children: [{ rule: '(exec)', child: { id: leafId, idx: 1, type: 'leaf', leafIndex: 0, status } }],
    },
    leaves: [{ leafIndex: 0, id: leafId, status, stepCount: steps.length, state: finalSer, trace: steps }],
  };
}

/**
 * Lazily extract the trace for a single leaf of an already-computed
 * explore tree. Used by the subtree/leaf-trace API endpoint so traces
 * are not shipped in the first payload.
 *
 * Returns { leafIndex, id, status, stepCount, trace, state, formulas }
 * — formulas is the minimal pool containing exactly what the trace
 * refers to, to keep the response compact.
 */
function extractLeafTrace(tree, leafIndex, opts = {}) {
  let found = null;
  let seen = -1;
  function walk(node) {
    if (found) return;
    if (node.type === 'leaf') {
      seen++;
      if (seen === leafIndex) { found = node; }
      return;
    }
    if (node.type === 'branch') {
      for (const ch of node.children) walk(ch.child);
    }
  }
  walk(tree);
  if (!found) return null;
  const ctx = _newContext(opts);
  const state = serializeState(found.state, ctx);
  const steps = serializeTrace(found.trace || [], ctx);
  const status = classifyLeaf(found.state, opts.leafPolicy);
  return {
    leafIndex,
    id: idOf(leafIndex), // NOTE: id here is the leaf-order id, not the tree-DFS id
    status,
    stepCount: steps.length,
    state,
    trace: steps,
    formulas: ctx.formulas,
  };
}

export { FORMAT_VERSION, serializeExploreTree, serializeExecTrace, extractLeafTrace, serializeState as _serializeState, serializeTrace as _serializeTrace };
export default { FORMAT_VERSION, serializeExploreTree, serializeExecTrace, extractLeafTrace, _serializeState: serializeState, _serializeTrace: serializeTrace };
