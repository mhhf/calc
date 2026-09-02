/**
 * server.js is CJS run under bun (`npm start`) — nothing in the node
 * suite can require it wholesale (module-level serve()). What CAN break
 * silently is its require graph: a lib/ file moves, tests get updated,
 * server.js doesn't, and the server crashes on startup (audit 2026-09-02:
 * prove-source.js moved to lib/prover/ill/ and took the server down).
 * This pins every relative require/import in server.js to an existing
 * file on disk.
 */

import { test } from 'node:test';
import assert from 'node:assert';
import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');

test('server.js relative requires all resolve', () => {
  const src = fs.readFileSync(path.join(ROOT, 'server.js'), 'utf8');
  const specs = [...src.matchAll(/require\(\s*['"](\.[^'"]+)['"]\s*\)/g)].map((m) => m[1]);
  assert.ok(specs.length > 0, 'expected at least one relative require in server.js');
  for (const spec of specs) {
    const base = path.join(ROOT, spec);
    const candidates = [base, `${base}.js`, `${base}.cjs`, path.join(base, 'index.js')];
    assert.ok(
      candidates.some((p) => fs.existsSync(p) && fs.statSync(p).isFile()),
      `server.js requires '${spec}' but no file matches ${base}{,.js,.cjs,/index.js}`
    );
  }
});
