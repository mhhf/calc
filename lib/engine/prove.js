/**
 * Backward compatibility shim — redirects to backchain.js
 *
 * All backward chaining logic now lives in backchain.js.
 * This file exists so that require('./prove') continues to work
 * for callers that haven't been updated yet.
 */
module.exports = require('./backchain');
