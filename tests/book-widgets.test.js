/**
 * Book widget spec parsing + inline execution (regression guard).
 *
 * The book's {exec} widgets carry their program either as `file:` + `query:` or
 * inline. Inline forms broke twice: a nested ``` fence truncating the block, and
 * a `source: |` YAML frame reaching the ILL parser ("Parse error … got '|'").
 * These tests pin the parse helpers AND actually run every inline {exec} widget
 * in the book through the real run-api, exactly as the browser does.
 */
import { describe, it, before } from 'node:test';
import assert from 'node:assert';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

// The SAME functions the widgets use (node strips the TS types on import).
import { parseSpecBody, inlineProgram } from '../src/ui/lib/widget-spec.ts';

const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const BOOK = path.join(ROOT, 'doc/book');
const SPEC_KEYS = ['file', 'query', 'maxSteps', 'title', 'source'];
// Variable-length widget fence (mirror of markdown.ts).
const EXEC_RE = /(`{3,})\{exec\s+(\w+)\}\n([\s\S]*?)\1/g;

describe('widget-spec parseSpecBody', () => {
  it('parses a `source: |` block scalar, dedented, and later keys', () => {
    const body = [
      'source: |',
      '  a: type.',
      '  b: type.',
      '  go: a -o { b }.',
      'maxSteps: 5',
      'title: Demo',
    ].join('\n');
    const spec = parseSpecBody(body, SPEC_KEYS);
    assert.strictEqual(spec.source, 'a: type.\nb: type.\ngo: a -o { b }.');
    assert.strictEqual(spec.maxSteps, '5');
    assert.strictEqual(spec.title, 'Demo');
    assert.ok(!spec.source.includes('|'), 'block indicator must not leak into source');
  });

  it('parses single-line key: value pairs', () => {
    const spec = parseSpecBody('file: calculus/ill/x.ill\nquery: symex', SPEC_KEYS);
    assert.strictEqual(spec.file, 'calculus/ill/x.ill');
    assert.strictEqual(spec.query, 'symex');
  });
});

describe('widget-spec inlineProgram', () => {
  it('prefers an explicit source block', () => {
    const body = 'source: |\n  a: type.\ntitle: X';
    const spec = parseSpecBody(body, SPEC_KEYS);
    assert.strictEqual(inlineProgram(body, SPEC_KEYS, spec), 'a: type.');
  });

  it('strips spec-key lines from a pure-inline body so only program is sent', () => {
    const body = 'a: type.\nb: type.\ngo: a -o { b }.\nmaxSteps: 3\ntitle: X';
    const spec = parseSpecBody(body, SPEC_KEYS);
    const prog = inlineProgram(body, SPEC_KEYS, spec);
    assert.strictEqual(prog, 'a: type.\nb: type.\ngo: a -o { b }.');
    assert.ok(!/maxSteps|title/.test(prog), 'spec lines must not reach the parser');
  });
});

describe('every inline {exec} widget in the book runs', () => {
  let handleRun;
  before(async () => {
    ({ handleRun } = await import('../src/server/run-api.js'));
  });

  const files = fs.readdirSync(BOOK).filter((f) => /^\d\d_.*\.md$/.test(f)).sort();
  for (const f of files) {
    const md = fs.readFileSync(path.join(BOOK, f), 'utf8');
    EXEC_RE.lastIndex = 0;
    let m;
    let widgetIdx = 0;
    while ((m = EXEC_RE.exec(md)) !== null) {
      const calculus = m[2];
      const body = m[3];
      const spec = parseSpecBody(body, SPEC_KEYS);
      if (spec.file) continue; // file-based widgets are covered elsewhere
      const label = spec.title || `exec #${widgetIdx}`;
      widgetIdx++;
      it(`${f}: ${label}`, async () => {
        const source = inlineProgram(body, SPEC_KEYS, spec);
        assert.ok(source, 'inline widget must yield program source');
        const r = await handleRun('exec', { calculus, source, maxSteps: Number(spec.maxSteps) || 20 });
        assert.ok(r && r.ok, `run failed: ${r && r.error}`);
      });
    }
  }
});
