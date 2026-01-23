/**
 * E2E test for the SolidJS UI
 *
 * Usage: node tests/e2e-solidjs.js
 *
 * This test:
 * 1. Builds the SolidJS UI if needed
 * 2. Starts a static server for the built files
 * 3. Opens the UI in headless browser
 * 4. Tests all three pages (Sandbox, Calculus, Meta)
 * 5. Reports any console errors
 */

const { chromium } = require('playwright');
const http = require('http');
const fs = require('fs');
const path = require('path');
const { execSync } = require('child_process');

const PORT = 8082;
const BUILD_DIR = path.join(__dirname, '../out/ui');

// Simple static file server with SPA support
function createServer() {
  return http.createServer((req, res) => {
    let urlPath = req.url.split('?')[0]; // Remove query string
    let filePath = path.join(BUILD_DIR, urlPath === '/' ? 'index.html' : urlPath);

    // For SPA routing, serve index.html for non-file routes
    if (!fs.existsSync(filePath) || fs.statSync(filePath).isDirectory()) {
      filePath = path.join(BUILD_DIR, 'index.html');
    }

    const extname = path.extname(filePath);
    const contentTypes = {
      '.html': 'text/html',
      '.js': 'text/javascript',
      '.css': 'text/css',
      '.json': 'application/json',
      '.woff': 'font/woff',
      '.woff2': 'font/woff2',
    };
    const contentType = contentTypes[extname] || 'application/octet-stream';

    fs.readFile(filePath, (err, content) => {
      if (err) {
        res.writeHead(404);
        res.end(`Not found: ${urlPath}`);
      } else {
        res.writeHead(200, { 'Content-Type': contentType });
        res.end(content);
      }
    });
  });
}

// Check if build exists, build if not
function ensureBuild() {
  const indexPath = path.join(BUILD_DIR, 'index.html');
  if (!fs.existsSync(indexPath)) {
    console.log('Building SolidJS UI...');
    try {
      execSync('npm run build:ui', {
        cwd: path.join(__dirname, '..'),
        stdio: 'inherit'
      });
    } catch (err) {
      console.error('Build failed:', err.message);
      process.exit(1);
    }
  } else {
    console.log('Using existing build at out/ui/');
  }
}

async function runTests() {
  const errors = [];
  const warnings = [];
  const testResults = [];

  // Ensure build exists
  ensureBuild();

  // Start server
  const server = createServer();
  await new Promise(resolve => server.listen(PORT, resolve));
  console.log(`\nServer started on http://localhost:${PORT}\n`);

  let browser;
  try {
    // Launch headless browser
    browser = await chromium.launch({
      headless: true,
      executablePath: process.env.CHROMIUM_PATH || '/etc/profiles/per-user/mhhf/bin/chromium'
    });

    const page = await browser.newPage();

    // Capture console messages
    page.on('console', msg => {
      const type = msg.type();
      const text = msg.text();

      // Ignore certain messages
      if (text.includes('favicon') || text.includes('404')) return;
      if (text.includes('Download the React DevTools')) return;

      if (type === 'error') {
        errors.push(text);
      } else if (type === 'warning') {
        warnings.push(text);
      }
    });

    // Capture page errors
    page.on('pageerror', err => {
      errors.push(`PageError: ${err.message}`);
    });

    // Capture failed requests (ignore favicon)
    page.on('requestfailed', request => {
      const url = request.url();
      if (!url.includes('favicon')) {
        errors.push(`Failed request: ${url}`);
      }
    });

    // ============================================
    // TEST 1: Sandbox Page - Initial Load
    // ============================================
    console.log('TEST 1: Sandbox Page - Initial Load');
    await page.goto(`http://localhost:${PORT}/`, {
      waitUntil: 'networkidle',
      timeout: 30000
    });

    // Wait for app to hydrate
    await page.waitForSelector('h2', { timeout: 5000 });

    const sandboxTitle = await page.textContent('h2');
    const test1Pass = sandboxTitle && sandboxTitle.includes('Sandbox');
    testResults.push({
      name: 'Sandbox page loads',
      pass: test1Pass,
      details: `Title: "${sandboxTitle}"`
    });

    // ============================================
    // TEST 2: Sandbox - Formula Parsing
    // ============================================
    console.log('TEST 2: Sandbox - Formula Parsing');

    // Find the formula input
    const input = await page.$('input[type="text"]');
    if (input) {
      await input.fill('A -o B');
      await page.waitForTimeout(500);

      // Check if LaTeX output appears
      const hasKatex = await page.$('.katex');
      const test2Pass = !!hasKatex;
      testResults.push({
        name: 'Formula parsing works',
        pass: test2Pass,
        details: hasKatex ? 'KaTeX rendered' : 'No KaTeX output'
      });

      // Check for AST tree
      const hasAST = await page.$('text=Abstract Syntax Tree');
      testResults.push({
        name: 'AST view renders',
        pass: !!hasAST,
        details: hasAST ? 'AST section found' : 'No AST section'
      });
    } else {
      testResults.push({
        name: 'Formula input exists',
        pass: false,
        details: 'Input not found'
      });
    }

    // ============================================
    // TEST 3: Sandbox - Parse Error Handling
    // ============================================
    console.log('TEST 3: Sandbox - Parse Error Handling');

    // Re-get input to avoid stale reference
    const inputForError = await page.$('input[type="text"]');
    if (inputForError) {
      await inputForError.fill(')))invalid((');
      await page.waitForTimeout(500);

      // Should show error message
      const errorDiv = await page.$('.text-red-600, .text-red-400');
      testResults.push({
        name: 'Parse errors displayed',
        pass: !!errorDiv,
        details: errorDiv ? 'Error message shown' : 'No error display'
      });
    }

    // ============================================
    // TEST 4: Navigate to Calculus Overview
    // ============================================
    console.log('TEST 4: Calculus Overview Page');

    // Click on Calculus tab
    await page.click('text=Calculus');
    await page.waitForTimeout(500);

    const calculusTitle = await page.textContent('h2');
    const test4Pass = calculusTitle && calculusTitle.includes('Calculus');
    testResults.push({
      name: 'Calculus page loads',
      pass: test4Pass,
      details: `Title: "${calculusTitle}"`
    });

    // Check for rule cards
    const ruleCards = await page.$$('.rule-card');
    testResults.push({
      name: 'Rule cards render',
      pass: ruleCards.length > 0,
      details: `${ruleCards.length} rule cards found`
    });

    // ============================================
    // TEST 5: Calculus - Filter Rules
    // ============================================
    console.log('TEST 5: Calculus - Filter Rules');

    const filterInput = await page.$('input[placeholder*="Filter"]');
    if (filterInput) {
      const initialCount = ruleCards.length;
      await filterInput.fill('Tensor');
      await page.waitForTimeout(300);

      const filteredCards = await page.$$('.rule-card');
      testResults.push({
        name: 'Rule filtering works',
        pass: filteredCards.length < initialCount && filteredCards.length > 0,
        details: `${initialCount} -> ${filteredCards.length} rules after filter`
      });

      // Clear filter
      await filterInput.fill('');
      await page.waitForTimeout(300);
    }

    // ============================================
    // TEST 6: Navigate to Meta Overview
    // ============================================
    console.log('TEST 6: Meta Overview Page');

    await page.click('text=Meta');
    await page.waitForTimeout(500);

    const metaTitle = await page.textContent('h2');
    const test6Pass = metaTitle && (metaTitle.includes('Meta') || metaTitle.includes('Framework'));
    testResults.push({
      name: 'Meta page loads',
      pass: test6Pass,
      details: `Title: "${metaTitle}"`
    });

    // Check for framework documentation section (ll.json format)
    const hasFrameworkDocs = await page.$('text=ll.json Specification');
    testResults.push({
      name: 'Framework docs render',
      pass: !!hasFrameworkDocs,
      details: hasFrameworkDocs ? 'Framework docs section found' : 'Not found'
    });

    // Check for metavariables table
    const hasMetavars = await page.$('text=Metavariable Conventions');
    testResults.push({
      name: 'Metavariables table renders',
      pass: !!hasMetavars,
      details: hasMetavars ? 'Metavariables section found' : 'Not found'
    });

    // ============================================
    // TEST 7: Prove Page - Interactive Proof
    // ============================================
    console.log('TEST 7: Prove Page - Interactive Proof');

    await page.click('text=Prove');
    await page.waitForTimeout(500);

    const proveTitle = await page.textContent('h2');
    const test7Pass = proveTitle && proveTitle.includes('Proof');
    testResults.push({
      name: 'Prove page loads',
      pass: test7Pass,
      details: `Title: "${proveTitle}"`
    });

    // Check for example buttons
    const proveExamples = await page.$('button:has-text("Identity")');
    testResults.push({
      name: 'Prove examples available',
      pass: !!proveExamples,
      details: proveExamples ? 'Example buttons found' : 'Not found'
    });

    // Click an example and start proof
    if (proveExamples) {
      await proveExamples.click();
      await page.waitForTimeout(300);

      const startBtn = await page.$('button:has-text("Start Proof")');
      if (startBtn) {
        await startBtn.click();
        await page.waitForTimeout(500);

        // Check if proof tree appears
        const proofNode = await page.$('.proof-node');
        testResults.push({
          name: 'Proof tree renders',
          pass: !!proofNode,
          details: proofNode ? 'Proof node found' : 'Not found'
        });

        // Check for auto-complete button
        const autoBtn = await page.$('button:has-text("Auto-complete")');
        testResults.push({
          name: 'Auto-complete available',
          pass: !!autoBtn,
          details: autoBtn ? 'Auto-complete button found' : 'Not found'
        });
      }
    }

    // ============================================
    // TEST 8: Dark Mode Toggle
    // ============================================
    console.log('TEST 8: Dark Mode Toggle');

    // Navigate back to home for a clean test
    await page.click('text=Sandbox');
    await page.waitForTimeout(300);

    // Find dark mode toggle button
    const darkModeBtn = await page.$('button[title="Toggle dark mode"]');
    if (darkModeBtn) {
      // Check initial state
      const initialDark = await page.$('div.dark');

      await darkModeBtn.click();
      await page.waitForTimeout(200);

      const afterToggle = await page.$('div.dark');
      testResults.push({
        name: 'Dark mode toggles',
        pass: !!initialDark !== !!afterToggle,
        details: `Before: ${!!initialDark}, After: ${!!afterToggle}`
      });
    } else {
      testResults.push({
        name: 'Dark mode button exists',
        pass: false,
        details: 'Button not found'
      });
    }

    // ============================================
    // TEST 8: Example Buttons
    // ============================================
    console.log('TEST 8: Example Buttons');

    // Make sure we're on the Sandbox page and wait for it to load
    try {
      await page.waitForSelector('input[type="text"]', { timeout: 5000 });

      const exampleBtn = await page.$('button:has-text("A -o B")');
      if (exampleBtn) {
        await exampleBtn.click();
        await page.waitForTimeout(500);

        // Use locator for more stable element access
        const input = page.locator('input[type="text"]');
        const inputValue = await input.inputValue();
        testResults.push({
          name: 'Example buttons work',
          pass: inputValue === 'A -o B',
          details: `Input value: "${inputValue}"`
        });
      } else {
        testResults.push({
          name: 'Example buttons work',
          pass: false,
          details: 'Example button not found'
        });
      }
    } catch (e) {
      testResults.push({
        name: 'Example buttons work',
        pass: false,
        details: `Error: ${e.message}`
      });
    }

    // ============================================
    // REPORT RESULTS
    // ============================================
    console.log('\n' + '='.repeat(50));
    console.log('E2E TEST RESULTS - SolidJS UI');
    console.log('='.repeat(50) + '\n');

    let passCount = 0;
    let failCount = 0;

    for (const result of testResults) {
      const icon = result.pass ? '✓' : '✗';
      const status = result.pass ? 'PASS' : 'FAIL';
      console.log(`${icon} [${status}] ${result.name}`);
      if (result.details) {
        console.log(`    ${result.details}`);
      }
      if (result.pass) passCount++;
      else failCount++;
    }

    console.log('\n' + '-'.repeat(50));
    console.log(`Total: ${passCount} passed, ${failCount} failed`);
    console.log('-'.repeat(50));

    if (errors.length > 0) {
      console.log('\nCONSOLE ERRORS:');
      errors.forEach((e, i) => console.log(`  ${i + 1}. ${e}`));
    }

    if (warnings.length > 0) {
      console.log('\nWARNINGS:');
      warnings.forEach((w, i) => console.log(`  ${i + 1}. ${w}`));
    }

    const success = failCount === 0 && errors.length === 0;
    console.log(`\n${success ? '✓ All tests passed!' : '✗ Some tests failed'}\n`);

    return success;

  } finally {
    if (browser) await browser.close();
    server.close();
  }
}

// Run the tests
runTests()
  .then(success => {
    process.exit(success ? 0 : 1);
  })
  .catch(err => {
    console.error('Test failed with exception:', err);
    process.exit(1);
  });
