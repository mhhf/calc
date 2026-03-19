#!/usr/bin/env node
/**
 * Precompile MDE/ILL files to binary cache.
 *
 * Usage:
 *   node tools/precompile.js <file.ill> [<file2.ill>...] [-o <output.bin>]
 *
 * Defaults output to out/cache/<basename>.bin
 */

const path = require('path');
const mde = require('../lib/engine');

async function main() {
  const args = process.argv.slice(2);
  if (args.length === 0) {
    console.error('Usage: node tools/precompile.js <file.ill> [<file2.ill>...] [-o <output.bin>]');
    process.exit(1);
  }

  // Parse args
  const files = [];
  let outputPath = null;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '-o' && i + 1 < args.length) {
      outputPath = args[++i];
    } else {
      files.push(path.resolve(args[i]));
    }
  }

  if (files.length === 0) {
    console.error('No input files specified');
    process.exit(1);
  }

  // Default output path
  if (!outputPath) {
    const basename = path.basename(files[0], path.extname(files[0]));
    outputPath = path.join('out', 'cache', `${basename}.bin`);
  }
  outputPath = path.resolve(outputPath);

  console.log(`Precompiling ${files.length} file(s)...`);
  const t0 = performance.now();
  const result = await mde.precompile(files, outputPath);
  const elapsed = performance.now() - t0;

  console.log(`  Types:        ${result.definitions.size}`);
  console.log(`  Clauses:      ${result.clauses.size}`);
  console.log(`  Forward rules: ${result.forwardRules.length}`);
  console.log(`  Store entries: ${mde.Store.size()}`);
  console.log(`  Output:       ${outputPath} (${(result.byteSize / 1024).toFixed(1)} KB)`);
  console.log(`  Time:         ${elapsed.toFixed(1)}ms`);
}

main().catch(err => {
  console.error(err);
  process.exit(1);
});
