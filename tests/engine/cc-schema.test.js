/**
 * cc port-contract validation (RES_0143 F1).
 * All shipped configs must validate; typos and missing requireds fail
 * loudly at the composition root with the schema as the reference.
 */
import { describe, it } from 'node:test';
import assert from 'node:assert/strict';
import { validateCalculusConfig, CC_SCHEMA } from '../../lib/engine/cc-schema.js';
import illcc from '../../calculus/ill/calculus-config.js';
import tillcc from '../../calculus/till/calculus-config.js';
import gillcc from '../../calculus/gill/calculus-config.js';
import willcc from '../../calculus/will/calculus-config.js';
import sillcc from '../../calculus/sill/calculus-config.js';
import saxcc from '../../calculus/sax/calculus-config.js';

describe('cc port contract (RES_0143 F1)', () => {
  it('all six shipped configs validate', () => {
    for (const [name, cc] of Object.entries({ illcc, tillcc, gillcc, willcc, sillcc, saxcc })) {
      assert.doesNotThrow(() => validateCalculusConfig(cc, name), name);
    }
  });
  it('an unknown key is a loud load error (typo defense)', () => {
    assert.throws(() => validateCalculusConfig({ ...saxcc, gradesConfig: {} }, 't'),
      /unknown key 'gradesConfig'/);
  });
  it('a missing required key is a loud load error', () => {
    const { connectives, ...rest } = saxcc;
    assert.throws(() => validateCalculusConfig(rest, 't'), /missing required key 'connectives'/);
  });
  it('a wrong-typed key is a loud load error', () => {
    assert.throws(() => validateCalculusConfig({ ...saxcc, stampTag: 42 }, 't'),
      /key 'stampTag': expected string/);
  });
  it('loader.buildParser is enforced (no default parser)', () => {
    assert.throws(() => validateCalculusConfig({ ...saxcc, loader: { connTags: {} } }, 't'),
      /buildParser must be a function/);
  });
  it('the schema documents every engine-read key (no undocumented sockets)', () => {
    for (const [key, spec] of Object.entries(CC_SCHEMA)) {
      assert.ok(spec.consumer || spec.private, `'${key}' must name its consumer or be private`);
    }
  });
});
