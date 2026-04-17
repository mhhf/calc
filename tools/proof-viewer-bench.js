#!/usr/bin/env node
/**
 * proof-viewer-bench — measure the shape, size and fold behaviour of
 * proof-tree/v1 payloads for a set of fixtures.
 *
 * Captures the "first-paint lower bound" for the viewer: server prove
 * time + serialize time + JSON/gzip bytes + how many nodes Phase A+B's
 * default fold (depth-3) actually makes visible. This is what decides
 * whether Phase C.2 (lazy subtree load) is worth adding or whether
 * Phase A+B already clears the 2 s budget.
 *
 * Usage:  node tools/proof-viewer-bench.js [--json]
 */
'use strict';

const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { proveSource } = require('../lib/prover/prove-source');

const CACHE = path.resolve(__dirname, '..', 'out', 'doc-cache-bench');

const FIXTURES = [
  // Small baselines (sanity)
  { label: 'tensor_assoc',  mode: 'sequent', source: '(A * B) * C |- A * (B * C)' },
  { label: 'loli_curry',    mode: 'sequent', source: 'A * B -o C |- A -o (B -o C)' },

  // Wide tensor — Phase A+B folding target
  { label: 'tensor8',   mode: 'sequent', source: 'A1,A2,A3,A4,A5,A6,A7,A8 |- A1*A2*A3*A4*A5*A6*A7*A8' },
  { label: 'tensor16',  mode: 'sequent', source: Array.from({length:16},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:16},(_,i)=>'A'+(i+1)).join('*') },
  { label: 'tensor32',  mode: 'sequent', source: Array.from({length:32},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:32},(_,i)=>'A'+(i+1)).join('*') },
  { label: 'tensor64',  mode: 'sequent', source: Array.from({length:64},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:64},(_,i)=>'A'+(i+1)).join('*') },
  { label: 'tensor128', mode: 'sequent', source: Array.from({length:128},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:128},(_,i)=>'A'+(i+1)).join('*') },

  // Chain — deep but skinny
  { label: 'chain16', mode: 'sequent', source: 'A, A -o B, B -o C, C -o D, D -o E, E -o F, F -o G, G -o H, H -o I, I -o J, J -o K, K -o L, L -o M, M -o N, N -o O, O -o P |- P' },

  // Backchain mode against bin.ill
  { label: 'plus_1_1',      mode: 'backchain', profile: 'teaching',
    source: '#import(programs/bin.ill)\n\nplus (i e) (i e) R' },
  { label: 'plus_3_3',      mode: 'backchain', profile: 'teaching',
    source: '#import(programs/bin.ill)\n\nplus (i (i e)) (i (i e)) R' },

  // Real-program proofs against bin.ill — large trees (≥500 nodes) that
  // exercise the 500-node acceptance criterion for TODO_0213.
  // bin.ill is the arithmetic layer transitively imported by evm.ill and
  // the multisig / solc-symbolic programs, so these are the same clauses
  // those programs fire at scale.
  // nat(n): LSB-first i/o/e Peano encoding. Expanded inline for readability.
  { label: 'mul_255_255',   mode: 'backchain', profile: 'teaching', maxDepth: 2000,
    source: '#import(programs/bin.ill)\n\nmul (i (i (i (i (i (i (i (i e)))))))) (i (i (i (i (i (i (i (i e)))))))) R' },
  { label: 'mul_65535_65535', mode: 'backchain', profile: 'teaching', maxDepth: 2000,
    source: '#import(programs/bin.ill)\n\nmul (i (i (i (i (i (i (i (i (i (i (i (i (i (i (i (i e)))))))))))))))) (i (i (i (i (i (i (i (i (i (i (i (i (i (i (i (i e)))))))))))))))) R' },
  // exp 3 15 = 14_348_907: real arithmetic, ~627 nodes, depth 43. The
  // canonical "real-program" fixture referenced in large-proof-trees.md.
  { label: 'exp_3_15',      mode: 'backchain', profile: 'teaching', maxDepth: 2000,
    source: '#import(programs/bin.ill)\n\nexp (i (i e)) (i (i (i (i e)))) R' },
];

const FOLD_DEPTH = 3; // DEFAULT_FOLD_DEPTH in ProofBlock.tsx

function count(n) {
  let c = 1;
  if (n.premises) for (const p of n.premises) c += count(p);
  return c;
}
function depth(n) {
  if (!n.premises || !n.premises.length) return 1;
  return 1 + Math.max(...n.premises.map(depth));
}
function maxBranch(n) {
  let m = n.premises ? n.premises.length : 0;
  if (n.premises) for (const p of n.premises) m = Math.max(m, maxBranch(p));
  return m;
}
/**
 * Simulate Phase A+B's default fold: count nodes the viewer actually
 * mounts on first paint. A node at depth >= foldDepth with premises > 0
 * collapses to a single stub button; its subtree isn't rendered.
 */
function visibleAtFold(n, d, fold) {
  if (d >= fold && n.premises && n.premises.length > 0) return 1; // stub
  let c = 1;
  if (n.premises) for (const p of n.premises) c += visibleAtFold(p, d + 1, fold);
  return c;
}

/** Estimate pool bytes referenced only by visible (unfolded) nodes.
 *  Approximates what lazy-subtree-loading could trim from first payload. */
function visiblePoolBytes(tree, fold) {
  const referenced = new Set();
  function walk(n, d) {
    const s = n.sequent;
    for (const name of Object.keys(s.contexts)) {
      for (const r of s.contexts[name]) if (r) referenced.add(r);
    }
    if (s.succedent) referenced.add(s.succedent);
    if (d >= fold && n.premises && n.premises.length > 0) return; // stub — skip subtree refs
    if (n.premises) for (const p of n.premises) walk(p, d + 1);
  }
  walk(tree.root, 0);
  // Transitive formula deps
  const queue = [...referenced];
  while (queue.length) {
    const k = queue.pop();
    const f = tree.formulas[k];
    if (!f) continue;
    const kids = [];
    if (f.args) kids.push(...f.args);
    if (f.elements) kids.push(...f.elements);
    if (f.extras) for (const e of f.extras) if (e.elements) kids.push(...e.elements);
    for (const kk of kids) if (kk !== null && kk !== undefined && !referenced.has(kk)) {
      referenced.add(kk); queue.push(kk);
    }
  }
  const subPool = Object.create(null);
  for (const k of referenced) subPool[k] = tree.formulas[k];
  return JSON.stringify(subPool).length;
}

(async function main() {
  const asJson = process.argv.includes('--json');
  const rows = [];
  if (!asJson) {
    console.log([
      'label'.padEnd(16),
      'mode'.padEnd(10),
      'prove_ms'.padStart(9),
      'nodes'.padStart(6),
      'depth'.padStart(6),
      'branch'.padStart(6),
      'json_kb'.padStart(8),
      'gz_kb'.padStart(6),
      'vis@3'.padStart(6),
      'vis_pool_kb'.padStart(12),
    ].join(' '));
  }
  for (const fx of FIXTURES) {
    const t0 = Date.now();
    let r;
    try {
      r = await proveSource({
        source: fx.source,
        calculus: 'ill',
        profile: fx.profile || 'default',
        mode: fx.mode || 'sequent',
        cacheDir: CACHE,
        maxDepth: fx.maxDepth || 500,
      });
    } catch (e) {
      if (!asJson) console.log(fx.label.padEnd(16), '(error)', e.message.slice(0, 60));
      continue;
    }
    const dt = Date.now() - t0;
    if (!r.ok || !r.tree) {
      if (!asJson) console.log(fx.label.padEnd(16), '(fail)', (r.error || 'no tree').slice(0, 60));
      continue;
    }
    const json = JSON.stringify(r.tree);
    const gz = zlib.gzipSync(json).length;
    const nodes = count(r.tree.root);
    const dp = depth(r.tree.root);
    const br = maxBranch(r.tree.root);
    const vis = visibleAtFold(r.tree.root, 0, FOLD_DEPTH);
    const visPool = visiblePoolBytes(r.tree, FOLD_DEPTH);
    const row = {
      label: fx.label, mode: fx.mode, profile: fx.profile || 'default',
      prove_ms: dt, nodes, depth: dp, branch: br,
      json_bytes: json.length, gz_bytes: gz,
      visible_at_fold_3: vis, visible_pool_bytes: visPool,
    };
    rows.push(row);
    if (!asJson) {
      console.log([
        fx.label.padEnd(16),
        (fx.mode || 'sequent').padEnd(10),
        String(dt).padStart(9),
        String(nodes).padStart(6),
        String(dp).padStart(6),
        String(br).padStart(6),
        (json.length/1024).toFixed(1).padStart(8),
        (gz/1024).toFixed(1).padStart(6),
        String(vis).padStart(6),
        (visPool/1024).toFixed(1).padStart(12),
      ].join(' '));
    }
  }
  if (asJson) console.log(JSON.stringify(rows, null, 2));
})().catch((e) => { console.error(e); process.exit(1); });
