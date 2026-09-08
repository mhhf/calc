// @ts-check
/**
 * Optimizer — profile-driven engine configuration.
 *
 * Profiles are plain objects with boolean flags controlling which
 * optimizations are active. Function pointers are resolved once at
 * engine creation time (V8 monomorphic IC, no runtime branching).
 *
 * Built-in profiles:
 *   bare  — no optimizations (correctness baseline)
 *   fast  — FFI + compiled sub + preserved
 *   full  — all optimizations enabled (default)
 *
 * Profile names are generic — a calculus that wants a different default
 * declares it as `cc.compile.profile` (read by the composition root);
 * per-load `opts.profile` overrides both. (RES_0143 L1: the all-on
 * profile was historically named after its first client, 'evm'.)
 */

import { buildStack } from './strategy.js';
import { makeDiscTreeLayer } from './opt/disc-tree.js';
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
  full: {
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
 * Accepts: string name, plain object, or undefined (defaults to 'full').
 * CALC_PROFILE env var takes priority over argument.
 */
function profile(input) {
  const envProfile = typeof process !== 'undefined' ? process.env.CALC_PROFILE : undefined;
  const key = envProfile || input || 'full';

  if (typeof key === 'string') {
    const profile = PROFILES[key];
    if (!profile) throw new Error(`Unknown profile: '${key}'. Available: ${Object.keys(PROFILES).join(', ')}`);
    return { ...profile, name: key };
  }

  if (typeof key === 'object' && key !== null) {
    return { ...PROFILE_DEFAULTS, ...key, name: key.name || 'custom' };
  }

  return { ...PROFILES.full, name: 'full' };
}

/**
 * Create an engine context: the ONE channel through which rule-selection
 * strategy reaches the run loops (RES_0143 F2 — this replaces both the
 * dead pre-built strategyStack and the per-run detectStrategy ambient
 * hook; forward/explore call engine.buildStrategy(ruleList)).
 *
 * Fingerprint functions are injected via opts (from composition root)
 * rather than imported directly — keeps optimizer in the generic layer.
 *
 * buildStrategy honors the PROFILE flags (fingerprint/prediction/
 * discTree) — historically the run path ignored them (the flags gated a
 * stack nobody consumed). Memoized per rule-list identity: the common
 * no-filter list is stable (index.js _allRuntimeRules), so settle-tick
 * and repeated-exec callers reuse one stack.
 *
 * @param {Object} profile - Resolved profile object
 * @param {Object[]} rules - Compiled forward rules (full list; unused
 *   beyond documentation — stacks build per CALL list)
 * @param {Object} [opts] - { fpDetect, fpLayer, attachPred }
 * @returns {Object} Frozen engine context { profile, buildStrategy }
 */
function engine(profile, rules, opts = {}) {
  const { fpDetect, fpLayer, attachPred } = opts;
  const memo = new WeakMap();

  function buildStrategy(ruleList) {
    let stack = memo.get(ruleList);
    if (stack) return stack;

    const layers = [];
    // Fingerprint layer: O(1) lookup by discriminator value
    const fpConfig = (profile.fingerprint && fpDetect) ? fpDetect(ruleList) : null;
    if (fpConfig) {
      layers.push(fpLayer(fpConfig));
      if (profile.prediction && attachPred) attachPred(ruleList, fpConfig);
    }
    // Disc-tree layer: O(pattern_depth) lookup
    if (profile.discTree) {
      layers.push(makeDiscTreeLayer());
    }
    stack = buildStack(ruleList, layers);
    stack.fpConfig = fpConfig;
    memo.set(ruleList, stack);
    return stack;
  }

  return Object.freeze({
    profile,
    buildStrategy,
  });
}

export { profile, engine };
export default { profile, engine };
