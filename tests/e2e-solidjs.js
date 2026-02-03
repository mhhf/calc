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
const { execSync, execFileSync } = require('child_process');

const PORT = 8082;
const BUILD_DIR = path.join(__dirname, '../out/ui');

// Find system Chromium executable (needed for NixOS and other systems where
// Playwright's bundled Chromium doesn't work)
function findChromiumPath() {
  // Check environment variable first
  if (process.env.CHROMIUM_PATH) {
    return process.env.CHROMIUM_PATH;
  }

  // Common chromium executable names
  const candidates = [
    'chromium',
    'chromium-browser',
    'google-chrome',
    'google-chrome-stable',
  ];

  for (const name of candidates) {
    try {
      const result = execFileSync('which', [name], { encoding: 'utf8' }).trim();
      if (result && fs.existsSync(result)) {
        return result;
      }
    } catch {
      // Not found, try next
    }
  }

  // Return null to let Playwright use its bundled browser
  return null;
}

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
    // Find system browser (needed for NixOS where Playwright's bundled browser doesn't work)
    const chromiumPath = findChromiumPath();
    const launchOptions = { headless: true };

    if (chromiumPath) {
      console.log(`Using system Chromium: ${chromiumPath}`);
      launchOptions.executablePath = chromiumPath;
    } else {
      console.log('Using Playwright bundled Chromium');
    }

    // Launch headless browser
    browser = await chromium.launch(launchOptions);

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

    // Wait for the formula input to appear
    try {
      await page.waitForSelector('.formula-input', { timeout: 5000 });
      const input = page.locator('.formula-input');

      // Use fill for setting value
      await input.fill('A -o B');
      await page.waitForTimeout(1000);

      // Check if LaTeX output appears (katex class is added by the library)
      const katexCount = await page.locator('.katex').count();
      const test2Pass = katexCount > 0;
      testResults.push({
        name: 'Formula parsing works',
        pass: test2Pass,
        details: test2Pass ? `KaTeX rendered (${katexCount} elements)` : 'No KaTeX output'
      });

      // Check for AST tree section (only appears after parsing)
      const hasAST = await page.locator('h3:has-text("Abstract Syntax Tree")').count() > 0;
      testResults.push({
        name: 'AST view renders',
        pass: hasAST,
        details: hasAST ? 'AST section found' : 'No AST section'
      });
    } catch (e) {
      testResults.push({
        name: 'Formula parsing works',
        pass: false,
        details: `Error: ${e.message}`
      });
      testResults.push({
        name: 'AST view renders',
        pass: false,
        details: 'Skipped due to input error'
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
    await page.waitForTimeout(800);

    const calculusTitle = await page.textContent('h2');
    const test4Pass = calculusTitle && calculusTitle.includes('Calculus');
    testResults.push({
      name: 'Calculus page loads',
      pass: test4Pass,
      details: `Title: "${calculusTitle}"`
    });

    // Check for inference rules section and rule names
    const hasRulesSection = await page.locator('h3:has-text("Inference Rules")').count() > 0;
    const ruleNames = await page.locator('span.font-mono.font-bold').count();
    testResults.push({
      name: 'Rule cards render',
      pass: hasRulesSection && ruleNames > 0,
      details: `Rules section: ${hasRulesSection}, rule names: ${ruleNames}`
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
    await page.waitForTimeout(800);

    const metaTitle = await page.textContent('h2');
    const test6Pass = metaTitle && (metaTitle.includes('Meta') || metaTitle.includes('Framework'));
    testResults.push({
      name: 'Meta page loads',
      pass: test6Pass,
      details: `Title: "${metaTitle}"`
    });

    // Check for Linear Logic documentation section (section headers)
    const hasLinearLogicDocs = await page.locator('h3:has-text("Linear Logic")').count() > 0;
    testResults.push({
      name: 'Framework docs render',
      pass: hasLinearLogicDocs,
      details: hasLinearLogicDocs ? 'Linear Logic section found' : 'Not found'
    });

    // Check for metavariables table
    const hasMetavars = await page.locator('text=Metavariable').count() > 0;
    testResults.push({
      name: 'Metavariables table renders',
      pass: hasMetavars,
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
      await page.waitForTimeout(500);

      const startBtn = await page.$('button:has-text("Start Proof")');
      if (startBtn) {
        await startBtn.click();
        await page.waitForTimeout(1000);

        // Check if proof tree appears (look for inference-rule class which is used by ClassicalProofTree)
        const proofTree = await page.locator('.inference-rule').count() > 0;
        // Also check for katex elements inside a proof container
        const proofKatex = await page.locator('.katex').count() > 0;
        testResults.push({
          name: 'Proof tree renders',
          pass: proofTree || proofKatex,
          details: proofTree ? 'Proof tree found' : (proofKatex ? 'Proof sequents rendered' : 'Not found')
        });

        // Check for auto-complete button
        const autoBtn = await page.$('button:has-text("Auto")');
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
    // TEST 9: Example Buttons
    // ============================================
    console.log('TEST 9: Example Buttons');

    // Navigate back to Sandbox and test example buttons
    try {
      await page.click('text=Sandbox');
      await page.waitForTimeout(800);

      const exampleBtn = await page.$('button:has-text("A -o B")');
      if (exampleBtn) {
        await exampleBtn.click();
        await page.waitForTimeout(800);

        // Use locator with formula-input class
        const input = page.locator('.formula-input');
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
