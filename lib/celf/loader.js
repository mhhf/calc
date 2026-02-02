/**
 * Calculus Loader
 *
 * Runtime loader for .family/.calc/.rules files.
 * Replaces static ll.json loading with dynamic generation.
 *
 * Provides both async and sync APIs:
 * - Async: await loader.load() or await loader.loadILL()
 * - Sync: loader.getCalc() (after init) or loader.loadILLSync()
 *
 * Usage (async):
 *   const loader = require('./celf/loader');
 *   const calc = await loader.loadILL();
 *   Calc.init(calc);
 *
 * Usage (sync, for backwards compatibility):
 *   const loader = require('./celf/loader');
 *   loader.loadILLSync();  // Blocks until loaded
 *   const calc = loader.getCalc();
 *   Calc.init(calc);
 */

const generator = require('./generator');
const path = require('path');
const fs = require('fs');

// Cache for loaded calculus definitions
const cache = new Map();

// Default ILL calc cache (for sync access)
let defaultCalc = null;
let initPromise = null;

/**
 * Load calculus from .calc and .rules files (async)
 *
 * @param {string} calcPath - Path to .calc file
 * @param {string} rulesPath - Path to .rules file
 * @param {Object} [options] - Options
 * @param {boolean} [options.useCache=true] - Use cached result if available
 * @returns {Promise<Object>} Calc database in ll.json format
 */
async function load(calcPath, rulesPath, options = {}) {
  const { useCache = true } = options;

  const cacheKey = `${calcPath}:${rulesPath}`;
  if (useCache && cache.has(cacheKey)) {
    return cache.get(cacheKey);
  }

  const calc = await generator.generate({ calcPath, rulesPath });

  if (useCache) {
    cache.set(cacheKey, calc);
  }

  return calc;
}

/**
 * Load the default ILL calculus (async)
 *
 * @param {Object} [options] - Options
 * @returns {Promise<Object>} Calc database
 */
async function loadILL(options = {}) {
  const baseDir = path.join(__dirname, '../../calculus');
  const calc = await load(
    path.join(baseDir, 'ill.calc'),
    path.join(baseDir, 'ill.rules'),
    options
  );
  defaultCalc = calc;
  return calc;
}

/**
 * Initialize the default ILL calculus (returns promise, can be awaited)
 * Multiple calls return the same promise.
 */
function init() {
  if (defaultCalc) return Promise.resolve(defaultCalc);
  if (initPromise) return initPromise;
  initPromise = loadILL();
  return initPromise;
}

/**
 * Load the default ILL calculus synchronously
 * Blocks the event loop until loaded.
 * Use sparingly - prefer async API.
 */
function loadILLSync() {
  if (defaultCalc) return defaultCalc;

  // Use synchronous file reading and parsing
  const tsParser = require('./ts-parser');
  const baseDir = path.join(__dirname, '../../calculus');
  const calcPath = path.join(baseDir, 'ill.calc');
  const rulesPath = path.join(baseDir, 'ill.rules');

  // Block until parser is initialized
  // This is a hack but needed for sync compatibility
  const { execSync } = require('child_process');

  // Generate calc using a subprocess to avoid async issues
  const script = `
    const generator = require('${require.resolve('./generator').replace(/\\/g, '\\\\')}');
    const path = require('path');

    (async () => {
      const calc = await generator.generate({
        calcPath: '${calcPath.replace(/\\/g, '\\\\')}',
        rulesPath: '${rulesPath.replace(/\\/g, '\\\\')}'
      });
      console.log(JSON.stringify(calc));
    })();
  `;

  try {
    const result = execSync(`node -e "${script.replace(/"/g, '\\"').replace(/\n/g, '')}"`, {
      encoding: 'utf8',
      cwd: __dirname
    });
    defaultCalc = JSON.parse(result);
    return defaultCalc;
  } catch (err) {
    throw new Error(`Failed to load ILL calculus synchronously: ${err.message}`);
  }
}

/**
 * Get the cached default ILL calc
 * Must call init() or loadILLSync() first.
 *
 * @returns {Object|null} Calc database or null if not loaded
 */
function getCalc() {
  return defaultCalc;
}

/**
 * Get the cached default ILL calc, throwing if not loaded
 *
 * @returns {Object} Calc database
 * @throws {Error} If calc not loaded
 */
function requireCalc() {
  if (!defaultCalc) {
    throw new Error('Calculus not loaded. Call loader.init() or loader.loadILLSync() first.');
  }
  return defaultCalc;
}

/**
 * Clear the loader cache
 */
function clearCache() {
  cache.clear();
  defaultCalc = null;
  initPromise = null;
}

/**
 * Get default calculus paths
 */
function getDefaultPaths() {
  const baseDir = path.join(__dirname, '../../calculus');
  return {
    calcPath: path.join(baseDir, 'ill.calc'),
    rulesPath: path.join(baseDir, 'ill.rules'),
    familyPath: path.join(baseDir, 'lnl.family')
  };
}

module.exports = {
  load,
  loadILL,
  init,
  loadILLSync,
  getCalc,
  requireCalc,
  clearCache,
  getDefaultPaths
};
