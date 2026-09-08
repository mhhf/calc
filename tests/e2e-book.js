/**
 * E2E test for the interactive book (TODO_0308).
 *
 * Usage: bun tests/e2e-book.js   (or node)
 *
 * Starts the real server (API + static UI build), then drives the book in
 * headless Chromium: index page, chapter render, widget hydration, and one
 * full interactive proof (click sequent → apply rule → proof complete).
 */

import { chromium } from 'playwright';
import fs from 'fs';
import path from 'path';
import { spawn, execFileSync, execSync } from 'child_process';

const PORT = 8093;
const ROOT = path.join(import.meta.dirname, '..');

function findChromiumPath() {
  if (process.env.CHROMIUM_PATH) return process.env.CHROMIUM_PATH;
  for (const name of ['chromium', 'chromium-browser', 'google-chrome', 'google-chrome-stable']) {
    try {
      const p = execFileSync('which', [name], { encoding: 'utf8' }).trim();
      if (p && fs.existsSync(p)) return p;
    } catch { /* try next */ }
  }
  return null;
}

function ensureBuild() {
  if (!fs.existsSync(path.join(ROOT, 'out/ui/index.html'))) {
    console.log('Building UI…');
    execSync('npm run build:ui', { cwd: ROOT, stdio: 'inherit' });
  }
}

async function waitForServer(url, tries = 50) {
  for (let i = 0; i < tries; i++) {
    try {
      const r = await fetch(url);
      if (r.ok) return;
    } catch { /* not up yet */ }
    await new Promise(r => setTimeout(r, 200));
  }
  throw new Error('server did not come up');
}

async function run() {
  ensureBuild();
  const server = spawn('bun', ['server.js', '--port', String(PORT)], { cwd: ROOT, stdio: 'ignore' });
  const results = [];
  const errors = [];
  let browser;
  try {
    await waitForServer(`http://localhost:${PORT}/api/health`);

    const chromiumPath = findChromiumPath();
    browser = await chromium.launch({ headless: true, ...(chromiumPath ? { executablePath: chromiumPath } : {}) });
    const page = await browser.newPage();
    page.on('pageerror', e => errors.push(`PageError: ${e.message}`));
    page.on('console', m => {
      if (m.type() === 'error' && !m.text().includes('favicon')) errors.push(m.text());
    });

    const check = (name, pass, details = '') => {
      results.push({ name, pass, details });
      console.log(`${pass ? '✓' : '✗'} ${name}${details ? ` — ${details}` : ''}`);
    };

    // 1. Book index
    await page.goto(`http://localhost:${PORT}/book`, { waitUntil: 'networkidle', timeout: 30000 });
    const h1 = await page.locator('h1:has-text("CALC Book")').count();
    check('book index loads', h1 >= 1);
    const cardCount = await page.locator('ol a[href^="/book/"]').count();
    check('chapter cards render', cardCount >= 1, `${cardCount} chapters`);

    // 2. First chapter
    const firstHref = await page.locator('ol a[href^="/book/"]').first().getAttribute('href');
    await page.goto(`http://localhost:${PORT}${firstHref}`, { waitUntil: 'networkidle', timeout: 30000 });
    await page.waitForTimeout(2000);
    check('chapter renders', (await page.locator('article').count()) === 1);
    check('sidebar nav renders', (await page.locator('aside a[href^="/book/"]').count()) >= 1);

    // 3. Widget hydration — at least one prove widget on chapter 1
    const proveCount = await page.locator('.embed-prove').count();
    check('prove widget hydrates', proveCount >= 1, `${proveCount} widgets`);

    // 4. Interactive proof: P |- P — click the goal sequent, apply id
    if (proveCount >= 1) {
      // The unproven conclusion carries .clickable-sequent (ClassicalProofTree).
      await page.locator('.embed-prove .clickable-sequent').first().click();
      await page.waitForTimeout(800);
      // Rule selector modal: rows show the rule name + an Apply button.
      // Chapter 1's first exercise is `P |- P` — id is the only applicable
      // rule, so the first Apply closes the proof.
      const apply = page.locator('button:has-text("Apply")').first();
      if (await apply.count()) {
        await apply.click();
        await page.waitForTimeout(800);
      }
      const complete = await page.locator('.embed-prove :text("Proof complete")').count();
      check('interactive proof completes', complete >= 1);
    }

    // 5. Prev/next + mark complete present
    check('mark-complete button', (await page.locator('button:has-text("Mark complete")').count()) >= 1);

    // 6. Full sweep: every chapter renders without console errors or
    //    error blocks ({rule}/{calc}/KaTeX failures render as pre.error).
    const list = await (await fetch(`http://localhost:${PORT}/api/docs/book`)).json();
    const slugs = list
      .filter(d => d.chapter !== undefined)
      .sort((a, b) => (a.part - b.part) || (a.chapter - b.chapter))
      .map(d => d.slug);
    let sweepFailures = 0;
    for (const slug of slugs) {
      const before = errors.length;
      await page.goto(`http://localhost:${PORT}/book/${slug}`, { waitUntil: 'networkidle', timeout: 60000 });
      await page.waitForTimeout(2500);
      const article = await page.locator('article').count();
      const errorBlocks = await page.locator('article pre.error').count();
      const newErrors = errors.length - before;
      const ok = article === 1 && errorBlocks === 0 && newErrors === 0;
      if (!ok) {
        sweepFailures++;
        console.log(`  ✗ ${slug}: article=${article} errorBlocks=${errorBlocks} consoleErrors=${newErrors}`);
        if (errorBlocks > 0) {
          const texts = await page.locator('article pre.error').allTextContents();
          for (const t of texts.slice(0, 3)) console.log(`      ${t.slice(0, 120)}`);
        }
      }
    }
    check(`chapter sweep (${slugs.length} chapters)`, sweepFailures === 0, `${sweepFailures} failing`);

    const failed = results.filter(r => !r.pass);
    if (errors.length) {
      console.log('\nConsole errors:');
      for (const e of errors) console.log('  ' + e);
    }
    console.log(`\n${results.length - failed.length}/${results.length} passed`);
    return failed.length === 0 && errors.length === 0;
  } finally {
    if (browser) await browser.close();
    server.kill();
  }
}

run()
  .then(ok => process.exit(ok ? 0 : 1))
  .catch(e => {
    console.error('e2e-book failed:', e);
    process.exit(1);
  });
