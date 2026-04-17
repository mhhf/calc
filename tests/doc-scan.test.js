/**
 * Tests for wiki-link backlink scanner.
 *
 * Builds a throwaway doc/ tree in a tmp dir with known links and verifies
 * the produced backlink index.
 */

const { describe, it, before, after } = require('node:test');
const assert = require('node:assert');
const fs = require('fs');
const path = require('path');
const os = require('os');

const { scanDocs, resolveTarget, buildBacklinkIndex, getDocManifest } = require('../src/ui/plugins/doc-scan');

let root;

function write(rel, content) {
  const p = path.join(root, rel);
  fs.mkdirSync(path.dirname(p), { recursive: true });
  fs.writeFileSync(p, content);
}

describe('doc-scan', () => {
  before(() => {
    root = fs.mkdtempSync(path.join(os.tmpdir(), 'calc-doc-scan-'));
    // Theory docs
    write('theory/0001_alpha.md', `---\ntitle: Alpha\ntags: [foo]\n---\n\nSee [[beta]] and [[def/0002_gamma]] and [[docs/delta]].`);
    write('theory/0002_beta.md', `---\ntitle: Beta\n---\n\nMentions [[alpha]] twice: [[alpha]]. Also unknown [[missing]] and external [[research/foo]].`);
    // Def docs
    write('def/0002_gamma.md', `---\ntitle: Gamma\n---\n\nRefers to [[theory/alpha|Doc Alpha]] with a label.`);
    // Documentation docs
    write('documentation/delta.md', `---\ntitle: Delta\n---\n\nNothing here, links to [[documentation/delta]] (self-link, should not count).`);
    // Extra doc with no outgoing links
    write('def/0003_epsilon.md', `---\ntitle: Epsilon\n---\n\n# Epsilon\n\nNo links.`);
  });

  after(() => {
    fs.rmSync(root, { recursive: true, force: true });
  });

  describe('scanDocs', () => {
    it('discovers all folders and files', () => {
      const { byRoute } = scanDocs(root);
      assert.deepStrictEqual(Object.keys(byRoute).sort(), ['def', 'docs', 'theory']);
      assert.strictEqual(byRoute.theory.length, 2);
      assert.strictEqual(byRoute.def.length, 2);
      assert.strictEqual(byRoute.docs.length, 1);
    });

    it('reads frontmatter title', () => {
      const { byRoute } = scanDocs(root);
      const alpha = byRoute.theory.find(e => e.slug === '0001_alpha');
      assert.strictEqual(alpha.title, 'Alpha');
    });
  });

  describe('resolveTarget', () => {
    it('resolves exact slug in same folder', () => {
      const { byRoute } = scanDocs(root);
      const r = resolveTarget('0001_alpha', 'theory', byRoute);
      assert.deepStrictEqual(r, { route: 'theory', slug: '0001_alpha' });
    });

    it('resolves numbered-prefix suffix match', () => {
      const { byRoute } = scanDocs(root);
      const r = resolveTarget('beta', 'theory', byRoute);
      assert.deepStrictEqual(r, { route: 'theory', slug: '0002_beta' });
    });

    it('resolves cross-folder with route name', () => {
      const { byRoute } = scanDocs(root);
      const r = resolveTarget('def/0002_gamma', 'theory', byRoute);
      assert.deepStrictEqual(r, { route: 'def', slug: '0002_gamma' });
    });

    it('resolves "docs/..." alias for documentation folder', () => {
      const { byRoute } = scanDocs(root);
      const r = resolveTarget('docs/delta', 'theory', byRoute);
      assert.deepStrictEqual(r, { route: 'docs', slug: 'delta' });
    });

    it('resolves "documentation/..." disk alias', () => {
      const { byRoute } = scanDocs(root);
      const r = resolveTarget('documentation/delta', 'theory', byRoute);
      assert.deepStrictEqual(r, { route: 'docs', slug: 'delta' });
    });

    it('returns null for unknown folder prefix (e.g. research)', () => {
      const { byRoute } = scanDocs(root);
      assert.strictEqual(resolveTarget('research/foo', 'theory', byRoute), null);
    });

    it('returns null for missing target', () => {
      const { byRoute } = scanDocs(root);
      assert.strictEqual(resolveTarget('missing', 'theory', byRoute), null);
    });
  });

  describe('buildBacklinkIndex', () => {
    it('has backlinks to alpha from beta and gamma', () => {
      const idx = buildBacklinkIndex(root);
      const key = 'theory/0001_alpha';
      assert.ok(idx[key], 'alpha should have backlinks');
      const titles = idx[key].map(b => b.title);
      assert.deepStrictEqual(titles.sort(), ['Beta', 'Gamma']);
    });

    it('deduplicates multiple links from same source', () => {
      const idx = buildBacklinkIndex(root);
      const backlinks = idx['theory/0001_alpha'];
      const fromBeta = backlinks.filter(b => b.slug === '0002_beta');
      assert.strictEqual(fromBeta.length, 1, 'beta links to alpha twice but appears once');
    });

    it('skips self-links', () => {
      const idx = buildBacklinkIndex(root);
      const backlinks = idx['docs/delta'] || [];
      assert.ok(!backlinks.some(b => b.slug === 'delta'), 'no self-link');
    });

    it('skips unresolvable targets silently', () => {
      const idx = buildBacklinkIndex(root);
      assert.strictEqual(idx['theory/missing'], undefined);
      assert.strictEqual(idx['research/foo'], undefined);
    });

    it('records cross-folder backlinks', () => {
      const idx = buildBacklinkIndex(root);
      assert.ok(idx['def/0002_gamma'], 'gamma linked from theory/alpha');
      assert.ok(idx['docs/delta'], 'delta linked from theory/alpha');
    });

    it('sorts backlinks alphabetically by title', () => {
      const idx = buildBacklinkIndex(root);
      const titles = idx['theory/0001_alpha'].map(b => b.title);
      const sorted = [...titles].sort();
      assert.deepStrictEqual(titles, sorted);
    });

    it('docs with no incoming links are absent from the index', () => {
      const idx = buildBacklinkIndex(root);
      assert.strictEqual(idx['def/0003_epsilon'], undefined);
    });
  });

  describe('getDocManifest', () => {
    it('produces slug arrays per route, sorted', () => {
      const m = getDocManifest(root);
      assert.deepStrictEqual(m.theory, ['0001_alpha', '0002_beta']);
      assert.deepStrictEqual(m.def, ['0002_gamma', '0003_epsilon']);
      assert.deepStrictEqual(m.docs, ['delta']);
    });
  });
});
