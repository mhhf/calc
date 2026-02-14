/**
 * Micro-benchmark: TypedArray scaling and growth strategies
 *
 * Tests:
 * 1. Pre-allocated large TypedArray vs doubling strategy
 * 2. Memory behavior (does OS lazily allocate?)
 * 3. Uint32Array vs BigUint64Array performance
 * 4. Array.set() copy cost for resize
 * 5. Tag-based child type inference cost
 */

const { performance } = require('perf_hooks');

function median(arr) {
  const s = [...arr].sort((a, b) => a - b);
  return s[Math.floor(s.length / 2)];
}

function bench(name, fn, runs = 20) {
  const times = [];
  for (let i = 0; i < runs; i++) {
    const t0 = performance.now();
    fn();
    times.push(performance.now() - t0);
  }
  const med = median(times);
  const min = Math.min(...times);
  console.log(`  ${name}: ${med.toFixed(3)}ms median, ${min.toFixed(3)}ms min`);
  return med;
}

// ==========================================================================
// Test 1: Pre-allocated vs doubling
// ==========================================================================
console.log('\n=== Test 1: Pre-allocated vs Doubling ===');
console.log('Inserting 100K entries into SoA store\n');

const N = 100_000;

// Pre-allocated
bench('Pre-alloc 1M entries, write 100K', () => {
  const tags = new Uint8Array(1_000_000);
  const child0 = new Uint32Array(1_000_000);
  const child1 = new Uint32Array(1_000_000);
  for (let i = 0; i < N; i++) {
    tags[i] = i & 0xFF;
    child0[i] = i > 0 ? i - 1 : 0;
    child1[i] = i > 1 ? i - 2 : 0;
  }
});

// Doubling strategy
bench('Doubling from 1K, write 100K', () => {
  let cap = 1024;
  let tags = new Uint8Array(cap);
  let child0 = new Uint32Array(cap);
  let child1 = new Uint32Array(cap);

  for (let i = 0; i < N; i++) {
    if (i >= cap) {
      const newCap = cap * 2;
      const newTags = new Uint8Array(newCap);
      const newC0 = new Uint32Array(newCap);
      const newC1 = new Uint32Array(newCap);
      newTags.set(tags);
      newC0.set(child0);
      newC1.set(child1);
      tags = newTags;
      child0 = newC0;
      child1 = newC1;
      cap = newCap;
    }
    tags[i] = i & 0xFF;
    child0[i] = i > 0 ? i - 1 : 0;
    child1[i] = i > 1 ? i - 2 : 0;
  }
});

// Doubling from 16K (more realistic start)
bench('Doubling from 16K, write 100K', () => {
  let cap = 16384;
  let tags = new Uint8Array(cap);
  let child0 = new Uint32Array(cap);
  let child1 = new Uint32Array(cap);

  for (let i = 0; i < N; i++) {
    if (i >= cap) {
      const newCap = cap * 2;
      const newTags = new Uint8Array(newCap);
      const newC0 = new Uint32Array(newCap);
      const newC1 = new Uint32Array(newCap);
      newTags.set(tags);
      newC0.set(child0);
      newC1.set(child1);
      tags = newTags;
      child0 = newC0;
      child1 = newC1;
      cap = newCap;
    }
    tags[i] = i & 0xFF;
    child0[i] = i > 0 ? i - 1 : 0;
    child1[i] = i > 1 ? i - 2 : 0;
  }
});

// ==========================================================================
// Test 2: Memory allocation behavior
// ==========================================================================
console.log('\n=== Test 2: Memory Allocation ===');

function memUsedMB() {
  if (global.gc) global.gc();
  return process.memoryUsage().rss / 1024 / 1024;
}

const mem0 = memUsedMB();
const big1 = new Uint32Array(1_000_000);  // 4MB virtual
const mem1 = memUsedMB();
const big2 = new Uint32Array(16_000_000); // 64MB virtual
const mem2 = memUsedMB();

// Touch first and last pages
big2[0] = 1;
big2[15_999_999] = 1;
const mem3 = memUsedMB();

// Touch all pages (force physical allocation)
for (let i = 0; i < 16_000_000; i += 1024) big2[i] = i;
const mem4 = memUsedMB();

console.log(`  Base RSS:           ${mem0.toFixed(1)}MB`);
console.log(`  After 1M Uint32:    ${mem1.toFixed(1)}MB (+${(mem1-mem0).toFixed(1)}MB, expect ~4MB)`);
console.log(`  After 16M Uint32:   ${mem2.toFixed(1)}MB (+${(mem2-mem1).toFixed(1)}MB, expect ~64MB)`);
console.log(`  Touch 2 pages:      ${mem3.toFixed(1)}MB (+${(mem3-mem2).toFixed(1)}MB)`);
console.log(`  Touch all pages:    ${mem4.toFixed(1)}MB (+${(mem4-mem3).toFixed(1)}MB)`);

// ==========================================================================
// Test 3: Uint32Array vs BigUint64Array
// ==========================================================================
console.log('\n=== Test 3: Uint32 vs BigUint64 Read Performance ===');
console.log('1M random reads\n');

const READS = 1_000_000;
const SIZE = 100_000;

const u32arr = new Uint32Array(SIZE);
for (let i = 0; i < SIZE; i++) u32arr[i] = i;

// Random read indices
const indices = new Uint32Array(READS);
for (let i = 0; i < READS; i++) indices[i] = Math.floor(Math.random() * SIZE);

bench('Uint32Array random reads', () => {
  let sum = 0;
  for (let i = 0; i < READS; i++) sum += u32arr[indices[i]];
  return sum; // prevent dead code elimination
});

// BigUint64Array (if available)
if (typeof BigUint64Array !== 'undefined') {
  const u64arr = new BigUint64Array(SIZE);
  for (let i = 0; i < SIZE; i++) u64arr[i] = BigInt(i);

  bench('BigUint64Array random reads', () => {
    let sum = 0n;
    for (let i = 0; i < READS; i++) sum += u64arr[indices[i]];
    return sum;
  });

  // Can we use BigUint64Array values as Map keys?
  const m = new Map();
  m.set(42n, 'hello');
  console.log(`  BigInt as Map key: ${m.get(42n) === 'hello' ? 'YES' : 'NO'}`);
  console.log(`  42n === 42: ${42n === 42}`);
  console.log(`  typeof BigUint64Array[0]: ${typeof u64arr[0]}`);
} else {
  console.log('  BigUint64Array not available');
}

// ==========================================================================
// Test 4: .set() copy cost (for resize)
// ==========================================================================
console.log('\n=== Test 4: TypedArray.set() Copy Cost ===\n');

for (const size of [1_000, 10_000, 100_000, 1_000_000]) {
  const src = new Uint32Array(size);
  for (let i = 0; i < size; i++) src[i] = i;

  bench(`Copy ${(size/1000).toFixed(0)}K Uint32`, () => {
    const dst = new Uint32Array(size * 2);
    dst.set(src);
  });
}

// ==========================================================================
// Test 5: Tag-based type inference vs bitmask
// ==========================================================================
console.log('\n=== Test 5: Tag-based Inference vs Bitmask ===');
console.log('Checking 1M children for isTermChild\n');

// Simulate tags
const TAG = { atom: 0, freevar: 1, binlit: 2, strlit: 3, charlit: 4,
              tensor: 5, loli: 6, with: 7, bang: 8, one: 9, code: 10, pc: 11 };
const LEAF_TAGS = new Uint8Array(256);
LEAF_TAGS[TAG.atom] = 1;
LEAF_TAGS[TAG.freevar] = 1;
LEAF_TAGS[TAG.binlit] = 1;
LEAF_TAGS[TAG.strlit] = 1;
LEAF_TAGS[TAG.charlit] = 1;

const testTags = new Uint8Array(SIZE);
const testChildTypes = new Uint8Array(SIZE); // bitmask approach
for (let i = 0; i < SIZE; i++) {
  testTags[i] = i % 12; // mix of all tags
  testChildTypes[i] = (i % 12 < 5) ? 0x03 : 0x00; // leaf tags have primitive children
}

bench('Tag-based inference (lookup table)', () => {
  let count = 0;
  for (let i = 0; i < READS; i++) {
    const id = indices[i];
    if (!LEAF_TAGS[testTags[id]]) count++; // children are term refs
  }
  return count;
});

bench('Bitmask approach', () => {
  let count = 0;
  for (let i = 0; i < READS; i++) {
    const id = indices[i];
    if (!(testChildTypes[id] & 1)) count++; // child0 is term ref
  }
  return count;
});

// ==========================================================================
// Test 6: Map.get vs direct TypedArray access
// ==========================================================================
console.log('\n=== Test 6: Map.get vs TypedArray Direct Access ===');
console.log('1M lookups (the core Store.get bottleneck)\n');

const mapStore = new Map();
for (let i = 0; i < SIZE; i++) {
  mapStore.set(i, { tag: 'code', children: [i > 0 ? i - 1 : 0, i] });
}

bench('Map.get + .tag', () => {
  let count = 0;
  for (let i = 0; i < READS; i++) {
    const node = mapStore.get(indices[i]);
    if (node.tag === 'code') count++;
  }
  return count;
});

bench('TypedArray tags[id] === TAG.code', () => {
  let count = 0;
  for (let i = 0; i < READS; i++) {
    if (testTags[indices[i]] === TAG.code) count++;
  }
  return count;
});

bench('TypedArray tags[id] + child0[id]', () => {
  let sum = 0;
  for (let i = 0; i < READS; i++) {
    const id = indices[i];
    if (testTags[id] === TAG.code) sum += u32arr[id];
  }
  return sum;
});

// ==========================================================================
// Test 7: Resizable ArrayBuffer (if available)
// ==========================================================================
console.log('\n=== Test 7: Resizable ArrayBuffer ===');

try {
  const rab = new ArrayBuffer(1024 * 4, { maxByteLength: 1024 * 1024 * 4 });
  const view = new Uint32Array(rab);
  console.log(`  Resizable ArrayBuffer: AVAILABLE`);
  console.log(`  Initial size: ${rab.byteLength} bytes`);
  console.log(`  Max size: ${rab.maxByteLength} bytes`);

  // Test resize
  for (let i = 0; i < 1024; i++) view[i] = i;
  rab.resize(2048 * 4);
  const view2 = new Uint32Array(rab);
  console.log(`  After resize: ${rab.byteLength} bytes, view length: ${view2.length}`);
  console.log(`  Data preserved: ${view2[1023] === 1023 ? 'YES' : 'NO'}`);

  // Benchmark resize vs copy
  bench('Resizable ArrayBuffer resize (1K→2K→4K→...→1M)', () => {
    const r = new ArrayBuffer(1024 * 4, { maxByteLength: 4 * 1024 * 1024 });
    let v = new Uint32Array(r);
    let size = 1024;
    while (size < 1_000_000) {
      v[size - 1] = size;
      size *= 2;
      r.resize(size * 4);
      v = new Uint32Array(r);
    }
  });
} catch (e) {
  console.log(`  Resizable ArrayBuffer: NOT AVAILABLE (${e.message})`);
}

// ==========================================================================
// Test 8: ArrayBuffer.transfer (if available)
// ==========================================================================
console.log('\n=== Test 8: ArrayBuffer.transfer ===');

try {
  const buf = new ArrayBuffer(1024);
  const transferred = buf.transfer(2048);
  console.log(`  ArrayBuffer.transfer: AVAILABLE`);
  console.log(`  Original detached: ${buf.detached}`);
  console.log(`  New size: ${transferred.byteLength}`);
} catch (e) {
  console.log(`  ArrayBuffer.transfer: NOT AVAILABLE (${e.message})`);
}

console.log('\n=== Done ===\n');
