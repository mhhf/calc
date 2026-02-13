/**
 * Benchmarks for Primitive Storage (binlit vs recursive)
 *
 * Run with: node tests/mde/primitives-benchmark.js
 */

const Store = require('../../lib/kernel/store');
const { intToBin, intToBinRecursive, binToInt } = require('../../lib/engine/ffi/convert');
const arithmetic = require('../../lib/engine/ffi/arithmetic');

function benchmark(name, fn, iterations = 1000) {
  // Warmup
  for (let i = 0; i < 10; i++) fn();

  const start = performance.now();
  for (let i = 0; i < iterations; i++) fn();
  const elapsed = performance.now() - start;

  return {
    name,
    iterations,
    totalMs: elapsed.toFixed(2),
    perOpUs: ((elapsed / iterations) * 1000).toFixed(2),
  };
}

console.log('=== Primitive Storage Benchmarks ===\n');

// Storage comparison: binlit vs recursive
console.log('--- Storage: binlit vs recursive ---\n');

const sizes = [8, 32, 64, 128, 256];
const storageResults = [];

for (const bits of sizes) {
  const value = (1n << BigInt(bits)) - 1n;

  Store.clear();
  const binlitResult = benchmark(`binlit ${bits}-bit`, () => {
    intToBin(value);
  }, 10000);
  const binlitNodes = Store.size();

  Store.clear();
  const recursiveResult = benchmark(`recursive ${bits}-bit`, () => {
    intToBinRecursive(value);
  }, 10000);
  const recursiveNodes = Store.size();

  // Also measure unique value storage (deduplication benefit)
  Store.clear();
  benchmark(`binlit ${bits}-bit unique`, () => {
    for (let i = 0; i < 100; i++) {
      intToBin(value - BigInt(i));
    }
  }, 100);
  const binlitUniqueNodes = Store.size();

  Store.clear();
  benchmark(`recursive ${bits}-bit unique`, () => {
    for (let i = 0; i < 100; i++) {
      intToBinRecursive(value - BigInt(i));
    }
  }, 100);
  const recursiveUniqueNodes = Store.size();

  storageResults.push({
    bits,
    binlitTime: `${binlitResult.perOpUs}µs`,
    recursiveTime: `${recursiveResult.perOpUs}µs`,
    speedup: (parseFloat(recursiveResult.perOpUs) / parseFloat(binlitResult.perOpUs)).toFixed(1) + 'x',
    binlitNodes: binlitNodes,
    recursiveNodes: recursiveNodes,
    nodeReduction: (((recursiveNodes - binlitNodes) / recursiveNodes) * 100).toFixed(0) + '%',
    binlitUnique: binlitUniqueNodes,
    recursiveUnique: recursiveUniqueNodes,
  });
}

console.table(storageResults);

// Conversion comparison: binToInt on binlit vs recursive
console.log('\n--- Conversion: binToInt on binlit vs recursive ---\n');

const conversionResults = [];

for (const bits of sizes) {
  const value = (1n << BigInt(bits)) - 1n;

  Store.clear();
  const binlitHash = intToBin(value);
  const binlitConvert = benchmark(`binToInt binlit ${bits}-bit`, () => {
    binToInt(binlitHash);
  }, 10000);

  Store.clear();
  const recursiveHash = intToBinRecursive(value);
  const recursiveConvert = benchmark(`binToInt recursive ${bits}-bit`, () => {
    binToInt(recursiveHash);
  }, 10000);

  conversionResults.push({
    bits,
    binlitTime: `${binlitConvert.perOpUs}µs`,
    recursiveTime: `${recursiveConvert.perOpUs}µs`,
    speedup: (parseFloat(recursiveConvert.perOpUs) / parseFloat(binlitConvert.perOpUs)).toFixed(1) + 'x',
  });
}

console.table(conversionResults);

// FFI operations with binlit
console.log('\n--- FFI Operations with binlit ---\n');

Store.clear();
const a = intToBin(1_000_000n);
const b = intToBin(2_000_000n);
const c = Store.put('freevar', ['_C']);

const ffiResults = [
  benchmark('plus', () => arithmetic.plus([a, b, c]), 10000),
  benchmark('mul', () => arithmetic.mul([a, b, c]), 10000),
  benchmark('div', () => arithmetic.div([a, b, c]), 10000),
  benchmark('mod', () => arithmetic.mod([a, b, c]), 10000),
  benchmark('lt', () => arithmetic.lt([a, b]), 10000),
];

console.table(ffiResults.map(r => ({
  operation: r.name,
  perOpUs: r.perOpUs,
})));

// Fixed-point operations
console.log('\n--- Fixed-Point Operations ---\n');

Store.clear();
const d18 = intToBin(18n);
const fp_a = intToBin(1_500_000_000_000_000_000n); // 1.5
const fp_b = intToBin(2_000_000_000_000_000_000n); // 2.0
const fp_c = Store.put('freevar', ['_C']);

const fixedResults = [
  benchmark('fixed_mul (18 decimals)', () => arithmetic.fixed_mul([d18, fp_a, fp_b, fp_c]), 10000),
  benchmark('fixed_div (18 decimals)', () => arithmetic.fixed_div([d18, fp_a, fp_b, fp_c]), 10000),
];

console.table(fixedResults.map(r => ({
  operation: r.name,
  perOpUs: r.perOpUs,
})));

// String operations
console.log('\n--- String Operations ---\n');

const { strToHash, hashToStr } = require('../../lib/engine/ffi/convert');

Store.clear();
const str_a = strToHash('hello');
const str_b = strToHash(' world');
const str_c = Store.put('freevar', ['_C']);
const str_len = Store.put('freevar', ['_Len']);

const stringResults = [
  benchmark('string_concat', () => arithmetic.string_concat([str_a, str_b, str_c]), 10000),
  benchmark('string_length', () => arithmetic.string_length([str_a, str_len]), 10000),
];

console.table(stringResults.map(r => ({
  operation: r.name,
  perOpUs: r.perOpUs,
})));

console.log('\n=== Summary ===\n');
console.log('binlit provides:');
console.log('- O(1) storage vs O(log n) for recursive form');
console.log('- O(1) binToInt vs O(log n) for recursive form');
console.log('- Significant node count reduction (especially for large values)');
console.log('- Same FFI interface - transparent upgrade');
