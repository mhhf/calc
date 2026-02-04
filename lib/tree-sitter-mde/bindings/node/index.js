/**
 * Tree-sitter MDE bindings using web-tree-sitter (WASM)
 */
const path = require('path');
const TreeSitter = require('web-tree-sitter');

let _parserReady = null;
let _parser = null;

/**
 * Initialize parser (async, cached)
 * @returns {Promise<TreeSitter.Parser>}
 */
async function getParser() {
  if (_parser) return _parser;
  if (_parserReady) return _parserReady;

  _parserReady = (async () => {
    await TreeSitter.Parser.init();
    const wasmPath = path.join(__dirname, '../../tree-sitter-mde.wasm');
    const Lang = await TreeSitter.Language.load(wasmPath);
    _parser = new TreeSitter.Parser();
    _parser.setLanguage(Lang);
    return _parser;
  })();

  return _parserReady;
}

/**
 * Parse MDE source code
 * @param {string} source
 * @returns {Promise<TreeSitter.Tree>}
 */
async function parse(source) {
  const parser = await getParser();
  return parser.parse(source);
}

module.exports = { getParser, parse };
