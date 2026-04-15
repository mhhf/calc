/**
 * Optimizer — profile-driven engine configuration.
 *
 * Profiles are plain objects with boolean flags controlling which
 * optimizations are active. Function pointers are resolved once at
 * engine creation time (V8 monomorphic IC, no runtime branching).
 *
 * Built-in profiles:
 *   bare  — no optimizations (correctness baseline)
 *   fast  — FFI + compiled sub + preserved (default)
 *   evm   — all optimizations enabled
 */

const { buildStack } = require('./strategy');
const { makeDiscTreeLayer } = require('./disc-tree');

// ─── Profile Schema ──────────────────────────────────────────────────

const PROFILE_DEFAULTS = {
  ffi: false,
  discTree: false,
  deltaBypass: false,
  preserved: false,
  compiledSub: false,
  fingerprint: false,

  loliDrain: false,
  structuralMemo: false,
  prediction: false,
  solver: false,
};

const PROFILES = {
  bare: { ...PROFILE_DEFAULTS },
  fast: {
    ...PROFILE_DEFAULTS,
    ffi: true,
    compiledSub: true,
    preserved: true,
  },
  evm: {
    ...PROFILE_DEFAULTS,
    ffi: true,
    discTree: true,
    deltaBypass: true,
    preserved: true,
    compiledSub: true,
    fingerprint: true,

    loliDrain: true,
    structuralMemo: true,
    prediction: true,
    solver: true,
  },
};

/**
 * Resolve profile input to a profile object.
 * Accepts: string name, plain object, or undefined (defaults to 'evm').
 * CALC_PROFILE env var takes priority over argument.
 */
function profile(input) {
  const envProfile = typeof process !== 'undefined' ? process.env.CALC_PROFILE : undefined;
  const key = envProfile || input || 'evm';

  if (typeof key === 'string') {
    const profile = PROFILES[key];
    if (!profile) throw new Error(`Unknown profile: '${key}'. Available: ${Object.keys(PROFILES).join(', ')}`);
    return { ...profile, name: key };
  }

  if (typeof key === 'object' && key !== null) {
    return { ...PROFILE_DEFAULTS, ...key, name: key.name || 'custom' };
  }

  return { ...PROFILES.evm, name: 'evm' };
}

/**
 * Create an engine context with resolved function pointers.
 *
 * Fingerprint functions are injected via opts (from composition root)
 * rather than imported directly — keeps optimizer in the generic layer.
 *
 * @param {Object} profile - Resolved profile object
 * @param {Object[]} rules - Compiled forward rules
 * @param {Object} [opts] - { fpDetect, fpLayer, attachPred }
 * @returns {Object} Frozen engine context
 */
function engine(profile, rules, opts = {}) {
  const strategyStack = _buildStrategy(profile, rules, opts);

  return Object.freeze({
    profile,
    strategyStack,
  });
}

/**
 * Build strategy stack from profile and rules.
 * Conditionally includes layers based on profile flags.
 * @private
 */
function _buildStrategy(profile, rules, opts) {
  const layers = [];

  // Fingerprint layer: O(1) lookup by discriminator value
  const { fpDetect, fpLayer, attachPred } = opts;
  const fpConfig = (profile.fingerprint && fpDetect) ? fpDetect(rules) : null;
  if (fpConfig) {
    layers.push(fpLayer(fpConfig));
    if (profile.prediction && attachPred) attachPred(rules, fpConfig);
  }

  // Disc-tree layer: O(pattern_depth) lookup
  if (profile.discTree) {
    layers.push(makeDiscTreeLayer());
  }

  const stack = buildStack(rules, layers);
  stack.fpConfig = fpConfig;
  return stack;
}

module.exports = {
  profile,
  engine,
};
