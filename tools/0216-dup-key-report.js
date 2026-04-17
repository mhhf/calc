#!/usr/bin/env node
/**
 * TODO_0216 Phase 0 H11 — aggregator for duplicate-key-θ JSONL
 *
 * Reads doc/_scratch/0216-dup-key.jsonl (written by 0216-dup-key-probe.js)
 * and produces doc/_scratch/0216-dup-key-report.json with totals + dedup'd
 * examples across every worker.
 *
 * Usage:
 *   rm -f doc/_scratch/0216-dup-key.jsonl
 *   NODE_OPTIONS="--require=$PWD/tools/0216-dup-key-probe.js" npm test
 *   node tools/0216-dup-key-report.js
 */

const fs = require('fs');
const path = require('path');

const ROOT = path.resolve(__dirname, '..');
const IN  = path.join(ROOT, 'doc/_scratch/0216-dup-key.jsonl');
const OUT = path.join(ROOT, 'doc/_scratch/0216-dup-key-report.json');

if (!fs.existsSync(IN)) {
  console.error(`No JSONL input at ${IN}. Run the probe first.`);
  process.exit(1);
}

const lines = fs.readFileSync(IN, 'utf8').split('\n').filter(Boolean);
// H1's apply-fuzz test deliberately constructs duplicate-key θ to lock
// first-wins semantics. Exclude it from the "organic" totals — the real
// question H11 answers is whether production callsites ever produce dups.
const FUZZ_RX = /kernel-apply-fuzz/;
let total = 0, dup = 0, fne = 0, workers = 0;
let realTotal = 0, realDup = 0, realFne = 0;
const examples = [];
const seenSig = new Set();

for (const ln of lines) {
  let rec;
  try { rec = JSON.parse(ln); } catch { continue; }
  workers++;
  total += rec.total_calls || 0;
  dup   += rec.dup_calls || 0;
  fne   += rec.first_ne_last || 0;
  const isFuzz = FUZZ_RX.test(rec.argv || '');
  if (!isFuzz) {
    realTotal += rec.total_calls || 0;
    realDup   += rec.dup_calls || 0;
    realFne   += rec.first_ne_last || 0;
  }
  for (const ex of rec.examples || []) {
    const sig = ex.theta.map(p => `${p[0]}→${p[1]}`).join('|');
    if (!seenSig.has(sig) && examples.length < 50) {
      seenSig.add(sig);
      examples.push({ ...ex, fromFuzz: isFuzz });
    }
  }
}

const payload = {
  schema: '0216-dup-key/v1',
  recorded: new Date().toISOString(),
  workers,
  all: { total_calls: total, dup_calls: dup, first_ne_last: fne },
  excluding_fuzz: {
    total_calls: realTotal,
    dup_calls: realDup,
    first_ne_last: realFne,
  },
  safe_for_map_theta_in_production: realFne === 0,
  examples,
};
fs.writeFileSync(OUT, JSON.stringify(payload, null, 2));
console.log(`Wrote ${OUT}`);
console.log(`workers=${workers}`);
console.log(`  all (incl. H1 fuzz): total=${total} dup=${dup} firstNeLast=${fne}`);
console.log(`  production only    : total=${realTotal} dup=${realDup} firstNeLast=${realFne}`);
console.log(`safe_for_map_theta_in_production: ${payload.safe_for_map_theta_in_production}`);
if (realFne > 0) {
  console.log('\nExamples of production duplicate-key θ where first != last:');
  for (const ex of examples.filter(e => e.firstNeLast && !e.fromFuzz).slice(0, 5)) {
    console.log('  θ =', JSON.stringify(ex.theta));
    console.log('    at:', ex.stack[0]);
  }
}
