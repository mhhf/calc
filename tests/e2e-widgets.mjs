/**
 * E2E smoke for the v2 execution widgets (exec/game/collapse) against the
 * hidden book page doc/book/99_widget-smoke.md. Requires a UI build.
 *
 * Usage: bun tests/e2e-widgets.mjs
 */
import { chromium } from 'playwright';
import fs from 'fs';
import path from 'path';
import { spawn, execFileSync } from 'child_process';

const PORT = 8094;
const ROOT = path.join(import.meta.dirname, '..');

function findChromiumPath() {
  if (process.env.CHROMIUM_PATH) return process.env.CHROMIUM_PATH;
  for (const name of ['chromium', 'chromium-browser', 'google-chrome', 'google-chrome-stable']) {
    try {
      const p = execFileSync('which', [name], { encoding: 'utf8' }).trim();
      if (p && fs.existsSync(p)) return p;
    } catch { /* next */ }
  }
  return null;
}

async function waitForServer(url, tries = 50) {
  for (let i = 0; i < tries; i++) {
    try { if ((await fetch(url)).ok) return; } catch { /* not yet */ }
    await new Promise(r => setTimeout(r, 200));
  }
  throw new Error('server did not come up');
}

const server = spawn('bun', ['server.js', '--port', String(PORT)], { cwd: ROOT, stdio: 'ignore' });
let browser;
const results = [];
const errors = [];
try {
  await waitForServer(`http://localhost:${PORT}/api/health`);
  const chromiumPath = findChromiumPath();
  browser = await chromium.launch({ headless: true, ...(chromiumPath ? { executablePath: chromiumPath } : {}) });
  const page = await browser.newPage();
  page.on('pageerror', e => errors.push(`PageError: ${e.message}`));
  page.on('console', m => { if (m.type() === 'error' && !m.text().includes('favicon')) errors.push(m.text()); });

  await page.goto(`http://localhost:${PORT}/book/99_widget-smoke`, { waitUntil: 'networkidle', timeout: 60000 });
  // widgets fetch + server loads programs — give them time
  await page.waitForTimeout(12000);

  const check = (name, pass, details = '') => {
    results.push({ name, pass });
    console.log(`${pass ? '✓' : '✗'} ${name}${details ? ` — ${details}` : ''}`);
  };

  // exec: fired-rules pane appears after pressing "Run all"
  const runAll = page.locator('button:has-text("Run all")');
  check('exec widget mounts', (await runAll.count()) >= 1);
  if (await runAll.count()) {
    await runAll.first().click();
    await page.waitForTimeout(500);
    const fired = await page.locator('text=evm/stop').count();
    check('exec steps render', fired >= 1);
  }

  // game: menu button with the costed loli label, click it, farm goes in flight
  const alt = page.locator('button:has-text("spc_s")').first();
  check('game widget mounts', (await alt.count()) >= 1);
  if (await alt.count()) {
    // advance to t>=1 then choose
    await page.locator('button:has-text("+1s")').first().click();
    await page.waitForTimeout(1200);
    await alt.click();
    await page.waitForTimeout(1500);
    const inflight = await page.locator('text=farm_s').count();
    check('game choose puts job in flight', inflight >= 1);
  }

  // collapse: waves render; auto-collapse reaches ground
  const auto = page.locator('button:has-text("Auto-collapse")');
  check('collapse widget mounts', (await auto.count()) >= 1);
  const waveCount = await page.locator('button:has-text("Draw this wave")').count();
  check('collapse waves render', waveCount >= 2, `${waveCount} waves`);
  if (await auto.count()) {
    await auto.first().click();
    await page.waitForTimeout(3000);
    const done = await page.locator('text=Fully collapsed').count();
    check('auto-collapse reaches ground', done >= 1);
  }

  if (errors.length) {
    console.log('\nConsole errors:');
    for (const e of errors) console.log('  ' + e);
  }
  const failed = results.filter(r => !r.pass).length;
  console.log(`\n${results.length - failed}/${results.length} passed`);
  process.exit(failed === 0 && errors.length === 0 ? 0 : 1);
} catch (e) {
  console.error('e2e-widgets failed:', e);
  process.exit(1);
} finally {
  if (browser) await browser.close();
  server.kill();
}
