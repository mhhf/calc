#!/usr/bin/env node
/**
 * proof-size-probe — measure serialized proof-tree/v1 size for a set of
 * representative sequents.
 *
 * Used to pick a benchmark target for TODO_0213 (large proof tree display).
 */
'use strict';

const zlib = require('zlib');
const { proveSource } = require('../lib/prover/prove-source');

function countNodes(node) {
  let n = 1;
  let depth = 1;
  for (const p of node.premises || []) {
    const sub = countNodes(p);
    n += sub.n;
    depth = Math.max(depth, sub.depth + 1);
  }
  return { n, depth };
}

// Each candidate: { label, source }
const CANDIDATES = [
  { label: 'id',            source: '|- A -o A' },
  { label: 'tensor',        source: 'A, B |- A * B' },
  { label: 'modus_ponens',  source: 'A, A -o B |- B' },
  { label: 'bang_id',       source: '!A |- A' },
  { label: 'bang_dup',      source: '!A |- A * A' },
  { label: 'with_l',        source: 'A & B |- A' },
  { label: 'oplus_r',       source: 'A |- A + B' },
  { label: 'monad_assoc',   source: '{A} |- {A}' },
  { label: 'tensor_assoc',  source: '(A * B) * C |- A * (B * C)' },
  { label: 'loli_curry',    source: 'A * B -o C |- A -o (B -o C)' },
  { label: 'deep_tensor',   source: 'A, B, C, D, E, F, G, H |- A * B * C * D * E * F * G * H' },
];

(async function main() {
  const rows = [];
  for (const c of CANDIDATES) {
    process.stderr.write(`→ ${c.label.padEnd(18)} `);
    const t0 = Date.now();
    const r = await proveSource({ source: c.source, calculus: 'ill', profile: 'default', maxDepth: 60 });
    const dt = Date.now() - t0;
    if (!r.ok || !r.tree) {
      rows.push({ label: c.label, source: c.source, error: r.error || 'unprovable', ms: dt });
      process.stderr.write(`error (${r.error || 'unprovable'})\n`);
      continue;
    }
    const counts = countNodes(r.tree.root);
    const json = JSON.stringify(r.tree);
    const gz = zlib.gzipSync(json).length;
    rows.push({
      label: c.label,
      source: c.source,
      nodes: counts.n,
      depth: counts.depth,
      uniqueFormulas: Object.keys(r.tree.formulas).length,
      jsonBytes: json.length,
      gzippedBytes: gz,
      proveMs: dt,
    });
    process.stderr.write(`${String(counts.n).padStart(4)} nodes · depth ${String(counts.depth).padStart(3)} · ${String(json.length).padStart(6)}B json · ${dt}ms\n`);
  }
  console.log(JSON.stringify(rows, null, 2));
})().catch((e) => { console.error(e); process.exit(1); });
