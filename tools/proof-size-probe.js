#!/usr/bin/env node
/**
 * proof-size-probe — measure serialized proof-tree/v1 size for a set of
 * representative sequents.
 *
 * Used to pick a benchmark target for TODO_0213 (large proof tree display).
 */
'use strict';

const fs = require('fs');
const path = require('path');
const zlib = require('zlib');
const { proveSource } = require('../lib/prover/prove-source');

const FIXTURE_DIR = path.resolve(__dirname, '../tests/fixtures/proof-trees');
const FIXTURE_LABELS = new Set(['tensor32', 'tensor64', 'tensor128', 'chain32']);

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
  // Baseline — inline teaching examples
  { label: 'id',             source: '|- A -o A' },
  { label: 'tensor',         source: 'A, B |- A * B' },
  { label: 'modus_ponens',   source: 'A, A -o B |- B' },
  { label: 'bang_id',        source: '!A |- A' },
  { label: 'with_l',         source: 'A & B |- A' },
  { label: 'oplus_r',        source: 'A |- A + B' },
  { label: 'tensor_assoc',   source: '(A * B) * C |- A * (B * C)' },
  { label: 'loli_curry',     source: 'A * B -o C |- A -o (B -o C)' },

  // Wider tensors — linear growth
  { label: 'tensor8',        source: 'A1, A2, A3, A4, A5, A6, A7, A8 |- A1*A2*A3*A4*A5*A6*A7*A8' },
  { label: 'tensor16',       source: 'A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16 |- A1*A2*A3*A4*A5*A6*A7*A8*A9*A10*A11*A12*A13*A14*A15*A16' },
  { label: 'tensor32',       source: 'A1,A2,A3,A4,A5,A6,A7,A8,A9,A10,A11,A12,A13,A14,A15,A16,A17,A18,A19,A20,A21,A22,A23,A24,A25,A26,A27,A28,A29,A30,A31,A32 |- A1*A2*A3*A4*A5*A6*A7*A8*A9*A10*A11*A12*A13*A14*A15*A16*A17*A18*A19*A20*A21*A22*A23*A24*A25*A26*A27*A28*A29*A30*A31*A32' },
  { label: 'tensor64',       source: Array.from({length:64},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:64},(_,i)=>'A'+(i+1)).join('*') },
  { label: 'tensor128',      source: Array.from({length:128},(_,i)=>'A'+(i+1)).join(',') + ' |- ' + Array.from({length:128},(_,i)=>'A'+(i+1)).join('*') },

  // Chained implications (loli elimination chain)
  { label: 'chain4',         source: 'A, A -o B, B -o C, C -o D |- D' },
  { label: 'chain8',         source: 'A, A -o B, B -o C, C -o D, D -o E, E -o F, F -o G, G -o H |- H' },
  { label: 'chain16',        source: 'A, A -o B, B -o C, C -o D, D -o E, E -o F, F -o G, G -o H, H -o I, I -o J, J -o K, K -o L, L -o M, M -o N, N -o O, O -o P |- P' },
  { label: 'chain32',        source: (() => {
      const names = Array.from({length:33},(_,i)=>String.fromCharCode(65+i % 26)+'x'+Math.floor(i/26));
      const ctx = [names[0], ...names.slice(0,-1).map((a,i)=>`${a} -o ${names[i+1]}`)];
      return `${ctx.join(', ')} |- ${names[names.length-1]}`;
    })() },

  // Curried implication chain (nested loli_r introductions)
  { label: 'curry8',         source: '|- A -o (B -o (C -o (D -o (E -o (F -o (G -o (H -o (A*B*C*D*E*F*G*H))))))))' },

  // Nested monads (bridge rule iteration)
  { label: 'monad3',         source: '{{{A}}} |- {{{A}}}' },
  { label: 'monad6',         source: '{{{{{{A}}}}}} |- {{{{{{A}}}}}}' },

  // With-elim chains (additive picks)
  { label: 'with_pick_4',    source: '(A & B) & (C & D) |- A' },

  // Bang manipulation
  { label: 'bang_to_pair',   source: '!A |- !A * !A' },

  // Composite: nested tensor under monad after loli chain
  { label: 'mixed_medium',   source: 'A, A -o B, B -o {C}, C -o {D} |- {D}' },
];

(async function main() {
  const rows = [];
  for (const c of CANDIDATES) {
    process.stderr.write(`→ ${c.label.padEnd(18)} `);
    const t0 = Date.now();
    const r = await proveSource({ source: c.source, calculus: 'ill', profile: 'default', maxDepth: 500 });
    const dt = Date.now() - t0;
    if (!r.ok || !r.tree) {
      rows.push({ label: c.label, source: c.source, error: r.error || 'unprovable', ms: dt });
      process.stderr.write(`error (${r.error || 'unprovable'})\n`);
      continue;
    }
    const counts = countNodes(r.tree.root);
    const json = JSON.stringify(r.tree);
    const gz = zlib.gzipSync(json).length;
    if (FIXTURE_LABELS.has(c.label)) {
      fs.mkdirSync(FIXTURE_DIR, { recursive: true });
      fs.writeFileSync(path.join(FIXTURE_DIR, `${c.label}.json`), json);
    }
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
