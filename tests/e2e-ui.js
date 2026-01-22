/**
 * E2E test for the UI - runs in headless browser and captures console errors
 *
 * Usage: node tests/e2e-ui.js
 *
 * This test:
 * 1. Starts an HTTP server on port 8081
 * 2. Opens the UI in headless browser (system chromium)
 * 3. Captures any console errors/warnings
 * 4. Reports success or failure
 */

const { chromium } = require('playwright');
const http = require('http');
const fs = require('fs');
const path = require('path');

const PORT = 8081;
const HTML_DIR = path.join(__dirname, '../src/html');

// Simple static file server
function createServer() {
  return http.createServer((req, res) => {
    let filePath = path.join(HTML_DIR, req.url === '/' ? 'index.html' : req.url);

    const extname = path.extname(filePath);
    const contentTypes = {
      '.html': 'text/html',
      '.js': 'text/javascript',
      '.css': 'text/css',
    };
    const contentType = contentTypes[extname] || 'application/octet-stream';

    fs.readFile(filePath, (err, content) => {
      if (err) {
        res.writeHead(404);
        res.end('Not found');
      } else {
        res.writeHead(200, { 'Content-Type': contentType });
        res.end(content);
      }
    });
  });
}

async function runTest() {
  const errors = [];
  const warnings = [];
  const logs = [];

  // Start server
  const server = createServer();
  await new Promise(resolve => server.listen(PORT, resolve));
  console.log(`Server started on http://localhost:${PORT}`);

  let browser;
  try {
    // Launch headless browser using system chromium
    browser = await chromium.launch({
      headless: true,
      executablePath: '/etc/profiles/per-user/mhhf/bin/chromium'
    });

    const page = await browser.newPage();

    // Capture console messages
    page.on('console', msg => {
      const type = msg.type();
      const text = msg.text();

      // Ignore favicon 404 errors and generic 404s for non-critical resources
      if (text.includes('favicon') || text.includes('404')) return;

      if (type === 'error') {
        errors.push(text);
      } else if (type === 'warning') {
        warnings.push(text);
      } else {
        logs.push(`[${type}] ${text}`);
      }
    });

    // Capture page errors (uncaught exceptions)
    page.on('pageerror', err => {
      errors.push(`PageError: ${err.message}`);
    });

    // Capture failed requests (but ignore favicon)
    page.on('requestfailed', request => {
      const url = request.url();
      if (!url.includes('favicon')) {
        errors.push(`Failed request: ${url}`);
      }
    });

    // Navigate to the page
    console.log('Loading page...');
    await page.goto(`http://localhost:${PORT}/`, {
      waitUntil: 'networkidle',
      timeout: 30000
    });

    // Wait a bit for any async operations
    await new Promise(resolve => setTimeout(resolve, 1000));

    // Test entering a formula
    console.log('Testing formula input...');
    await page.fill('.field', '-- : P -o Q');
    await page.click('#render');
    await new Promise(resolve => setTimeout(resolve, 1000));

    // Check if the app container has content
    const appContent = await page.$eval('#app-container', el => el.innerHTML.length);
    console.log(`App container has ${appContent} characters of content`);

    // Report results
    console.log('\n=== E2E Test Results ===\n');

    if (errors.length > 0) {
      console.log('ERRORS:');
      errors.forEach((e, i) => console.log(`  ${i + 1}. ${e}`));
      console.log('');
    }

    if (warnings.length > 0) {
      console.log('WARNINGS:');
      warnings.forEach((w, i) => console.log(`  ${i + 1}. ${w}`));
      console.log('');
    }

    if (logs.length > 0) {
      console.log('LOGS:');
      logs.forEach(l => console.log(`  ${l}`));
      console.log('');
    }

    if (errors.length === 0) {
      console.log('✓ No errors detected!');
      return true;
    } else {
      console.log(`✗ ${errors.length} error(s) detected`);
      return false;
    }

  } finally {
    if (browser) await browser.close();
    server.close();
  }
}

// Run the test
runTest()
  .then(success => {
    process.exit(success ? 0 : 1);
  })
  .catch(err => {
    console.error('Test failed with exception:', err);
    process.exit(1);
  });
