/**
 * ZK Witness Generator — converts proof terms to STARK trace data.
 *
 * Takes a GenericTerm + Sequent + Store (global) and produces per-chip
 * trace rows + formula ROM + gamma ROM + rule specs as JSON. The Rust
 * bridge deserializes this into RowMajorMatrix per chip and runs the prover.
 *
 * The witness is fully self-describing: tags and rule_specs are derived
 * from the calculus definition, so the same Rust binary verifies proofs
 * from any calculus defined in CALC.
 *
 * Each proof term node maps to exactly one chip row (DFS pre-order).
 * Context-only left rules pass the obligation through to their continuation.
 * Right/left-focus/axiom rules consume/produce obligations via nonces.
 *
 * The architecture is purely local at the constraint level — each row's
 * constraints only reference that row's columns. Global balance is
 * enforced by the framework's LogUp bus accumulators.
 */

const Store = require('../kernel/store');
const Seq = require('../kernel/sequent');
const { buildRightTensor } = require('../kernel/ast');
const { binToInt } = require('../engine/ill/ffi/convert');

// --- Phase 6-6b: 256-bit arithmetic helpers (module-level for testability) ---

const BABY_BEAR_P = 2013265921n;
const NUM_LIMBS = 32;
const MAX_UINT256 = (1n << 256n) - 1n;

/**
 * Decompose a BigInt into 32 × 8-bit limbs (little-endian).
 * @param {bigint} val - Non-negative integer, must fit in 256 bits
 * @returns {number[]} 32-element array of limb values [0..255]
 */
function bigintToLimbs(val) {
  const limbs = new Array(NUM_LIMBS);
  let v = val;
  for (let i = 0; i < NUM_LIMBS; i++) {
    limbs[i] = Number(v & 0xFFn);
    v >>= 8n;
  }
  return limbs;
}

/**
 * Compute carry chain for addition: a + b = c (mod 2^256).
 * @param {number[]} aLimbs - 32 limbs of operand a
 * @param {number[]} bLimbs - 32 limbs of operand b
 * @returns {number[]} 32 carry bits
 */
function computeAdditionCarries(aLimbs, bLimbs) {
  const carries = new Array(NUM_LIMBS);
  let carry = 0;
  for (let i = 0; i < NUM_LIMBS; i++) {
    const sum = aLimbs[i] + bLimbs[i] + carry;
    carries[i] = Math.floor(sum / 256);
    carry = carries[i];
  }
  return carries;
}

/**
 * Compute carry chain for increment: a + 1 = c (mod 2^256).
 * @param {number[]} aLimbs - 32 limbs of operand a
 * @returns {number[]} 32 carry bits
 */
function computeIncrementCarries(aLimbs) {
  const carries = new Array(NUM_LIMBS);
  const sum0 = aLimbs[0] + 1;
  carries[0] = Math.floor(sum0 / 256);
  let carry = carries[0];
  for (let i = 1; i < NUM_LIMBS; i++) {
    const sum = aLimbs[i] + carry;
    carries[i] = Math.floor(sum / 256);
    carry = carries[i];
  }
  return carries;
}

/**
 * Compute carry chain for multiplication: a * b = c (mod 2^256).
 * Returns { carries_lo, carries_hi } where full_carry[k] = carries_lo[k] + carries_hi[k] * 256.
 * Max carry ≈ 8160, fits in two bytes.
 * @param {number[]} aLimbs - 32 limbs of operand a
 * @param {number[]} bLimbs - 32 limbs of operand b
 * @returns {{ carries_lo: number[], carries_hi: number[] }}
 */
function computeMultiplicationCarries(aLimbs, bLimbs) {
  const carries_lo = new Array(NUM_LIMBS);
  const carries_hi = new Array(NUM_LIMBS);
  let carry = 0;
  for (let k = 0; k < NUM_LIMBS; k++) {
    let sum = carry;
    for (let i = 0; i <= k; i++) {
      sum += aLimbs[i] * bLimbs[k - i];
    }
    const carry_out = Math.floor(sum / 256);
    carries_lo[k] = carry_out & 0xFF;
    carries_hi[k] = carry_out >> 8;
    carry = carry_out;
  }
  return { carries_lo, carries_hi };
}

/**
 * Extract 256-bit predicate metadata from a ground predicate hash.
 * Handles plus, inc, and mul with values >= BabyBear prime (deferred from extractPredMeta).
 *
 * Returns { is_plus_256, is_inc_256, is_mul_256, a_limbs, b_limbs, c_limbs,
 *           carries_lo, carries_hi } or null.
 * Values must be non-negative. For mul, the product may exceed 2^256 — we verify mod 2^256.
 *
 * @param {number} predHash - Store hash of the predicate term
 * @returns {Object|null}
 */
function extractUint256PredMeta(predHash) {
  if (!Store.isTerm(predHash)) return null;
  const tag = Store.tag(predHash);
  const arity = Store.arity(predHash);

  function argBigVal(idx) {
    if (idx >= arity) return null;
    const argH = Store.child(predHash, idx);
    const val = binToInt(argH);
    if (val === null || val < 0n || val > MAX_UINT256) return null;
    return val;
  }

  // For mul, the product C = A*B may exceed 2^256. Truncate to lower 256 bits.
  function argBigValTruncated(idx) {
    if (idx >= arity) return null;
    const argH = Store.child(predHash, idx);
    const val = binToInt(argH);
    if (val === null || val < 0n) return null;
    return val & MAX_UINT256;
  }

  const zero_hi = new Array(NUM_LIMBS).fill(0);

  if (tag === 'plus' && arity === 3) {
    const a = argBigVal(0), b = argBigVal(1), c = argBigVal(2);
    if (a === null || b === null || c === null) return null;
    // Must use Uint256 if a+b could wrap in BabyBear
    if (a < BABY_BEAR_P && b < BABY_BEAR_P && c < BABY_BEAR_P && a + b < BABY_BEAR_P) return null;
    const aL = bigintToLimbs(a), bL = bigintToLimbs(b), cL = bigintToLimbs(c);
    return { is_plus_256: 1, is_inc_256: 0, is_mul_256: 0, a_limbs: aL, b_limbs: bL, c_limbs: cL,
             carries_lo: computeAdditionCarries(aL, bL), carries_hi: zero_hi };
  } else if (tag === 'inc' && arity === 2) {
    const a = argBigVal(0), b = argBigVal(1);
    if (a === null || b === null) return null;
    if (a < BABY_BEAR_P && b < BABY_BEAR_P) return null;
    const aL = bigintToLimbs(a), bL = new Array(NUM_LIMBS).fill(0), cL = bigintToLimbs(b);
    return { is_plus_256: 0, is_inc_256: 1, is_mul_256: 0, a_limbs: aL, b_limbs: bL, c_limbs: cL,
             carries_lo: computeIncrementCarries(aL), carries_hi: zero_hi };
  } else if (tag === 'mul' && arity === 3) {
    const a = argBigVal(0), b = argBigVal(1);
    if (a === null || b === null) return null;
    const c = argBigValTruncated(2); // product may exceed 2^256
    if (c === null) return null;
    // Must use Uint256 if a*b could wrap in BabyBear (even if individual args fit)
    if (a < BABY_BEAR_P && b < BABY_BEAR_P && c < BABY_BEAR_P && a * b < BABY_BEAR_P) return null;
    const aL = bigintToLimbs(a), bL = bigintToLimbs(b), cL = bigintToLimbs(c);
    const { carries_lo, carries_hi } = computeMultiplicationCarries(aL, bL);
    return { is_plus_256: 0, is_inc_256: 0, is_mul_256: 1, a_limbs: aL, b_limbs: bL, c_limbs: cL,
             carries_lo, carries_hi };
  }
  return null;
}

/**
 * Derive ZK tag mapping from a calculus object.
 *
 * Assigns a unique 1-indexed integer to each formula connective
 * (excluding 'atom') in definition order. The mapping is deterministic
 * and derived from the .calc connective definitions.
 *
 * @param {Object} calculus - Loaded calculus (from loadILL() or browser hydration)
 * @returns {Object} name → integer tag mapping
 */
function deriveZkTags(calculus) {
  const tags = {};
  calculus.connectivesFor('formula')
    .filter(c => c.name !== 'atom')
    .forEach((c, i) => { tags[c.name] = i + 1; });
  // freevar is a Store built-in, not a calculus connective, but SubstChip
  // needs it for freevar-leaf FORMULA_BUS lookups
  if (tags.freevar == null) {
    const maxTag = Object.values(tags).reduce((a, b) => Math.max(a, b), 0);
    tags.freevar = maxTag + 1;
  }
  return tags;
}

/**
 * Derive ZK RuleSpec structures from a calculus object.
 *
 * Maps each rule descriptor to a RuleSpec that the Rust bridge uses to
 * construct generic RuleChip AIR instances. The mapping is mechanical:
 * rule descriptor fields → RuleSpec fields.
 *
 * @param {Object} calculus - Loaded calculus
 * @param {Object} zkTags - ZK tag mapping (from deriveZkTags)
 * @returns {Object} chipName → RuleSpec object (matching Rust serde format)
 */
function deriveZkRuleSpecs(calculus, zkTags) {
  const specs = {};

  // Special rules: id and copy (not in rule descriptor map)
  specs.id = {
    name: 'id', tag: null, arity: 0,
    oblig_receive: true, premises: [],
    ctx_receive: true, ctx_sends: [],
    formula_lookup: false, gamma_lookup: false, is_identity: true,
  };
  specs.copy = {
    name: 'copy', tag: null, arity: 0,
    oblig_receive: false, premises: [],
    ctx_receive: false, ctx_sends: ['Hash'],
    formula_lookup: false, gamma_lookup: true, is_identity: false,
  };
  // FFI axiom: absorbing axiom that consumes an obligation without proof.
  // Used only when dangerouslyUseFFI is enabled (benchmarking).
  // ZK-unsound — the verifier trusts these. With noFFI (default), all
  // persistent goals are proved via clause resolution and this chip is unused.
  specs.ffi = {
    name: 'ffi', tag: null, arity: 0,
    oblig_receive: true, premises: [],
    ctx_receive: false, ctx_sends: [],
    formula_lookup: false, gamma_lookup: false, is_identity: false,
  };
  // Phase 6-4: fact_axiom — ROM-backed axiom for custom chip predicates.
  // Like ffi but sound: discharges obligation via FACT_BUS ROM lookup
  // instead of blind trust. Used for arr_get, arr_set, mem_read, mem_expand, inc, plus, mul.
  specs.fact_axiom = {
    name: 'fact_axiom', tag: null, arity: 0,
    oblig_receive: true, premises: [],
    ctx_receive: false, ctx_sends: [],
    formula_lookup: false, gamma_lookup: false, fact_lookup: true, is_identity: false,
  };

  // Map each rule to a ZK RuleSpec
  for (const [ruleName, rule] of Object.entries(calculus.rules)) {
    const d = rule.descriptor;
    if (!d || !d.connective) continue; // skip structural (copy) and id
    const zkName = ruleToZkName(ruleName);
    if (!zkName) continue; // skip unmappable rules
    if (zkName === 'zero_l') continue; // specialized chip

    const tag = zkTags[d.connective];
    if (tag == null) continue;
    const arity = d.arity || 0;
    const isRight = d.side === 'r';
    const numPremises = (d.premises || []).length;
    const isLeftFocus = !isRight && numPremises > 1;

    // oblig_receive: right rules and left-focus rules consume an obligation
    const oblig_receive = isRight || isLeftFocus;

    // premises: child obligations to produce on OBLIG_BUS
    const premises = [];
    if (d.modeShift) {
      // monad_r: mode shift → 1 premise with lax=1
      premises.push({ succedent: { Child: 0 }, lax: 1 });
    } else if (oblig_receive) {
      for (let i = 0; i < numPremises; i++) {
        const pd = d.premises[i];
        let succedent;
        if (pd.succedent !== undefined) {
          succedent = { Child: pd.succedent };
        } else if (isRight) {
          // Default for right rules: premise i gets child i
          succedent = { Child: i };
        } else {
          // Left-focus without explicit succedent: inherited
          succedent = 'Inherited';
        }
        premises.push({ succedent, lax: null });
      }
    }

    // ctx_receive: left rules consume principal from context
    const ctx_receive = !isRight && d.side === 'l';

    // ctx_sends: children sent to CONTEXT_BUS
    const ctx_sends = [];
    if (!d.emptyLinear) {
      for (const pd of (d.premises || [])) {
        for (const j of (pd.linear || [])) {
          const send = { Child: j };
          // Avoid duplicates (shouldn't happen, but defensive)
          if (!ctx_sends.some(s => s.Child === j)) {
            ctx_sends.push(send);
          }
        }
        // cartesian children go to gamma, NOT to ctx_sends
      }
    }

    // formula_lookup: any rule with a connective does a formula bus lookup
    const formula_lookup = d.connective != null;

    specs[zkName] = {
      name: zkName, tag, arity,
      oblig_receive, premises,
      ctx_receive, ctx_sends,
      formula_lookup, gamma_lookup: false, is_identity: false,
    };
  }

  // Invertible loli_l: context-only decomposition (1-subterm).
  // Same structure as tensor_l (consume compound, add both children to context)
  // but with loli tag. Used when backward prover applies loli_l in invertible phase.
  if (zkTags.loli) {
    specs['loli_l_inv'] = {
      name: 'loli_l_inv', tag: zkTags.loli, arity: 2,
      oblig_receive: false, premises: [],
      ctx_receive: true, ctx_sends: [{ Child: 0 }, { Child: 1 }],
      formula_lookup: true, gamma_lookup: false, is_identity: false,
    };
  }

  return specs;
}

/**
 * Map calculus rule name to ZK chip name.
 */
function ruleToZkName(name) {
  switch (name) {
    case 'promotion': return 'bang_r';
    case 'dereliction': return 'bang_l';
    default: return name; // tensor_r, tensor_l, loli_r, etc.
  }
}

/**
 * Generate ZK witness data from a proof term and sequent.
 *
 * @param {Object} term - GenericTerm (from extractTerm or buildGuidedTerm)
 * @param {Object} sequent - The sequent being proved (Store hashes)
 * @param {Object} [opts] - Options
 * @param {Object} opts.calculus - Loaded calculus (required, used to derive ZK tags)
 * @param {Object} [opts.tags] - Override ZK tag mapping (default: derived from calculus)
 * @param {Set<string>} [opts.customChips] - Predicate names for custom chip optimization
 *   (e.g., new Set(['inc', 'arr_get', 'plus'])). Clause proof subtrees for these
 *   predicates emit one fact_axiom row instead of the full proof tree.
 * @returns {{ tags: Object, chips: Object, formula_rom: number[][], gamma_rom: number[][], fact_rom: number[][] }}
 */
function generateWitness(term, sequent, opts = {}) {
  if (!opts.calculus && !opts.tags) {
    throw new Error('generateWitness requires opts.calculus or opts.tags');
  }
  const ZK_TAGS = opts.tags || deriveZkTags(opts.calculus);
  let _maxZkTag = Object.values(ZK_TAGS).reduce((a, b) => Math.max(a, b), 0);
  const customChips = opts.customChips || new Set();
  let nonceCtr = 0;
  let substIdCtr = 0;
  const formulaLookups = new Map(); // hash → { tag, c0, c1, count }
  const gammaEntries = new Map();   // hash → lookup count
  const freevarRomEntries = new Map(); // `${substId}:${freevarHash}` → { substId, freevarHash, groundValue, count }
  const factRomEntries = new Map(); // goalHash → lookup count (Phase 6-4 custom chips)
  const predRomEntries = new Map(); // predHash → { is_plus, is_mul, is_inc, arg0, arg1, arg2, count } (Phase 6-6a)
  const uint256ArithEntries = new Map(); // predHash → { meta, count } (Phase 6-6b)
  const byteCheckCounts = new Array(256).fill(0); // byte value → lookup count (Phase 6-6b)

  // Per-chip trace rows
  const chips = {
    init: [],
    dup: [],
    zero_l: [],
    discard: [],
  };

  // Segment tracking for chunk assignment (Phase 6-7).
  // _faSegment increments after each fact_axiom row push.
  // Non-fa chip rows get tagged with the current _faSegment,
  // so generateChunkedTreeWitness can assign them to the correct chunk.
  let _faSegment = 0;
  const _chipSegments = {};
  const _boundaryDeltas = [];

  // Dynamic chip names (one array per RuleSpec name encountered)
  function chipRows(name) {
    if (!chips[name]) chips[name] = [];
    if (!_chipSegments[name]) _chipSegments[name] = [];
    return {
      push(row) { chips[name].push(row); _chipSegments[name].push(_faSegment); }
    };
  }

  function addFormulaLookup(hash) {
    if (!Store.isTerm(hash)) return;
    const tag = Store.tag(hash);
    let zkTag = ZK_TAGS[tag];
    if (zkTag == null) {
      // Dynamically assign ZK tags for predicate/atom nodes encountered
      // during SubstChip tree verification
      _maxZkTag += 1;
      ZK_TAGS[tag] = _maxZkTag;
      zkTag = ZK_TAGS[tag];
    }
    const existing = formulaLookups.get(hash);
    if (existing) {
      existing.count++;
    } else {
      const arity = Store.arity(hash);
      // For freevar/atom/strlit: child0 is a string table index (raw u32),
      // not a term reference. Use rawChild to get the numeric value.
      const c0 = arity >= 1 ? Store.rawChild(hash, 0) : 0;
      const c1 = arity >= 2 ? Store.rawChild(hash, 1) : 0;
      formulaLookups.set(hash, { tag: zkTag, c0, c1, count: 1 });
    }
  }

  function addGammaLookup(hash) {
    gammaEntries.set(hash, (gammaEntries.get(hash) || 0) + 1);
  }

  function addFreevarLookup(substId, freevarHash, groundValue) {
    const key = `${substId}:${freevarHash}`;
    const existing = freevarRomEntries.get(key);
    if (existing) {
      existing.count++;
    } else {
      freevarRomEntries.set(key, { substId, freevarHash, groundValue, count: 1 });
    }
  }

  /**
   * Emit SubstChip rows for a substitution tree walk.
   * Recursively decomposes old/new hash pairs, emitting one row per node.
   *
   * At the root (loli node), only the antecedent child (c0) is recursively
   * verified. The body child (c1) may have different structure (pattern body
   * vs ground tensor chain) and is separately verified by loli_l/monad_l/tensor_l.
   *
   * @param {number} oldHash - original formula hash (may contain freevars)
   * @param {number} newHash - ground formula hash (freevars resolved)
   * @param {number} substId - substitution instance ID
   * @param {boolean} isRoot - true for the root node (CONTEXT_BUS swap)
   */
  function emitSubstTree(oldHash, newHash, substId, isRoot) {
    if (oldHash === newHash) {
      // Identical hashes — no row needed, parent's c_eq=1 handles this
      return;
    }

    const oldTag = Store.tag(oldHash);

    // Freevar leaf: old is a freevar, new is the ground value
    if (oldTag === 'freevar') {
      const freevarZkTag = ZK_TAGS['freevar'] || 0;
      const nameId = Store.arity(oldHash) >= 1 ? Store.rawChild(oldHash, 0) : 0;
      // Width 16: [active, hash_old, hash_new, is_root, is_freevar, subst_id, tag,
      //            c0_old, c1_old, c0_new, c1_new, c0_eq, c1_eq, is_internal, non_root_int, is_unwrap]
      chipRows('subst').push([1, oldHash, newHash, isRoot ? 1 : 0, 1, substId,
        freevarZkTag, nameId, 0, 0, 0, 0, 0, 0, 0, 0]);
      addFreevarLookup(substId, oldHash, newHash);
      addFormulaLookup(oldHash);
      return;
    }

    // Internal node: same tag, recurse on children
    const oldArity = Store.arity(oldHash);
    const c0Old = oldArity >= 1 ? Store.rawChild(oldHash, 0) : 0;
    const c1Old = oldArity >= 2 ? Store.rawChild(oldHash, 1) : 0;
    const newArity = Store.arity(newHash);
    const c0New = newArity >= 1 ? Store.rawChild(newHash, 0) : 0;
    const c1New = newArity >= 2 ? Store.rawChild(newHash, 1) : 0;
    const c0Eq = c0Old === c0New ? 1 : 0;

    // Ensure ZK tag exists (addFormulaLookup assigns dynamic tags for predicates)
    addFormulaLookup(oldHash);
    addFormulaLookup(newHash);
    const resolvedTag = ZK_TAGS[oldTag] || 0;

    if (isRoot) {
      // Root loli node: verify c0 (antecedent) recursively, skip c1 (body).
      // Body has different structure (pattern vs ground tensor chain) and is
      // separately verified by loli_l/monad_l/tensor_l chips.
      // Set c1_eq=1 to suppress SUBST_TREE_BUS send for body.
      // is_internal=1, non_root_int=0, is_unwrap=0
      chipRows('subst').push([1, oldHash, newHash, 1, 0, substId, resolvedTag,
        c0Old, c1Old, c0New, c1New, c0Eq, 1, 1, 0, 0]);
      // Only recurse into antecedent
      if (!c0Eq) emitSubstTree(c0Old, c0New, substId, false);
    } else {
      // Non-root internal: verify both children
      const c1Eq = c1Old === c1New ? 1 : 0;
      // is_internal=1, non_root_int=1, is_unwrap=0
      chipRows('subst').push([1, oldHash, newHash, 0, 0, substId, resolvedTag,
        c0Old, c1Old, c0New, c1New, c0Eq, c1Eq, 1, 1, 0]);
      if (!c0Eq) emitSubstTree(c0Old, c0New, substId, false);
      if (!c1Eq) emitSubstTree(c1Old, c1New, substId, false);
    }
  }

  // --- Emit InitChip rows ---
  const linear = Seq.getContext(sequent, 'linear');
  const succedent = sequent.succedent;

  // First row: first context element + obligation
  // Format: [ctx_hash, ctx_active, oblig_hash, oblig_active, nonce, lax, is_active]
  if (linear.length > 0) {
    chipRows('init').push([linear[0], 1, succedent, 1, 0, 0, 1]);
  } else {
    chipRows('init').push([0, 0, succedent, 1, 0, 0, 1]);
  }
  // Additional context rows
  for (let i = 1; i < linear.length; i++) {
    chipRows('init').push([linear[i], 1, 0, 0, 0, 0, 1]);
  }

  // Build initial live delta (linear context as a Map: hash → count)
  const liveDelta = new Map();
  for (const h of linear) {
    liveDelta.set(h, (liveDelta.get(h) || 0) + 1);
  }

  // --- Ground body decomposition (used by loli_match) ---

  /** Emit tensor_l / absorption / one_l chip rows for a ground body tensor chain. */
  function emitGroundDecomp(bodyHash) {
    const tag = Store.tag(bodyHash);
    if (tag === 'tensor') {
      const bc0 = Store.child(bodyHash, 0);
      const bc1 = Store.child(bodyHash, 1);
      chipRows('tensor_l').push([1, bodyHash, bc0, bc1]);
      addFormulaLookup(bodyHash);
      emitGroundDecomp(bc0);
      emitGroundDecomp(bc1);
    } else if (tag === 'bang') {
      const bc0 = Store.child(bodyHash, 0);
      chipRows('absorption').push([1, bodyHash, bc0]);
      addFormulaLookup(bodyHash);
    } else if (tag === 'one') {
      chipRows('one_l').push([1, bodyHash]);
      addFormulaLookup(bodyHash);
    }
    // Leaf atoms: added to delta by caller
  }

  // --- Predicate metadata extraction (Phase 6-6a) ---

  /**
   * Extract predicate metadata from a ground predicate hash.
   * Returns { is_plus, is_mul, is_inc, is_arr_get, is_arr_set, is_mem_read,
   *           is_mem_expand, arg0, arg1, arg2, arg3 } or null if unverifiable.
   *
   * Arithmetic predicates (plus, mul, inc): args are binToInt values (BabyBear range).
   * ROM-based predicates (arr_get, arr_set, mem_read, mem_expand): args are Store IDs
   *   (u32 sequential indices, always < BabyBear). No algebraic constraint needed —
   *   VK-committed ROM membership IS the verification (per-proof VK).
   */
  function extractPredMeta(predHash) {
    if (!Store.isTerm(predHash)) return null;
    const tag = Store.tag(predHash);
    const arity = Store.arity(predHash);

    // Extract numeric argument values from binlit children
    function argVal(idx) {
      if (idx >= arity) return 0;
      const argH = Store.child(predHash, idx);
      const val = binToInt(argH);
      if (val === null || val >= BABY_BEAR_P) return null; // exceeds BabyBear range
      return Number(val);
    }

    // Extract raw child hash (Store ID) — always fits in BabyBear
    function childHash(idx) {
      if (idx >= arity) return 0;
      return Store.rawChild(predHash, idx);
    }

    const result = {
      is_plus: 0, is_mul: 0, is_inc: 0,
      is_arr_get: 0, is_arr_set: 0, is_mem_read: 0, is_mem_expand: 0,
      arg0: 0, arg1: 0, arg2: 0, arg3: 0,
    };

    if (tag === 'plus' && arity === 3) {
      const a = argVal(0), b = argVal(1), c = argVal(2);
      if (a === null || b === null || c === null) return null;
      // Reject if a+b wraps in BabyBear — falls through to Uint256ArithChip
      if (BigInt(a) + BigInt(b) >= BABY_BEAR_P) return null;
      result.is_plus = 1; result.arg0 = a; result.arg1 = b; result.arg2 = c;
    } else if (tag === 'mul' && arity === 3) {
      const a = argVal(0), b = argVal(1), c = argVal(2);
      if (a === null || b === null || c === null) return null;
      // Reject if a*b wraps in BabyBear — falls through to Uint256ArithChip
      if (BigInt(a) * BigInt(b) >= BABY_BEAR_P) return null;
      result.is_mul = 1; result.arg0 = a; result.arg1 = b; result.arg2 = c;
    } else if (tag === 'inc' && arity === 2) {
      const a = argVal(0), b = argVal(1);
      if (a === null || b === null) return null;
      result.is_inc = 1; result.arg0 = a; result.arg1 = b;
    } else if (tag === 'arr_get' && arity === 3) {
      result.is_arr_get = 1;
      result.arg0 = childHash(0); result.arg1 = childHash(1); result.arg2 = childHash(2);
    } else if (tag === 'arr_set' && arity === 4) {
      result.is_arr_set = 1;
      result.arg0 = childHash(0); result.arg1 = childHash(1);
      result.arg2 = childHash(2); result.arg3 = childHash(3);
    } else if (tag === 'mem_read' && arity === 3) {
      result.is_mem_read = 1;
      result.arg0 = childHash(0); result.arg1 = childHash(1); result.arg2 = childHash(2);
    } else if (tag === 'mem_expand' && arity === 4) {
      result.is_mem_expand = 1;
      result.arg0 = childHash(0); result.arg1 = childHash(1);
      result.arg2 = childHash(2); result.arg3 = childHash(3);
    } else {
      return null;
    }
    return result;
  }

  /**
   * Register a predicate hash in the pred_rom.
   * Called once per fact_axiom row to track predicate verification entries.
   */
  function addPredRomEntry(predHash) {
    // Check pred_rom (BabyBear range) first
    const existing = predRomEntries.get(predHash);
    if (existing) { existing.count++; return; }

    // Check uint256_arith (large values) second
    const existingU256 = uint256ArithEntries.get(predHash);
    if (existingU256) { existingU256.count++; return; }

    const meta = extractPredMeta(predHash);
    if (meta) {
      predRomEntries.set(predHash, { ...meta, count: 1 });
      return;
    }

    // Phase 6-6b: try 256-bit arithmetic for large values
    const u256meta = extractUint256PredMeta(predHash);
    if (u256meta) {
      uint256ArithEntries.set(predHash, { ...u256meta, count: 1 });
      // Accumulate byte lookup counts for all limbs + carries
      for (let i = 0; i < NUM_LIMBS; i++) {
        byteCheckCounts[u256meta.a_limbs[i]]++;
        byteCheckCounts[u256meta.b_limbs[i]]++;
        byteCheckCounts[u256meta.c_limbs[i]]++;
        byteCheckCounts[u256meta.carries_lo[i]]++;
        byteCheckCounts[u256meta.carries_hi[i]]++;
      }
    }
    // Unrecognized predicates (not handled by either extractor) are NOT added.
  }

  // --- Walk proof term ---

  /**
   * Iterative DFS walk. Emits chip rows for each proof term node.
   *
   * @param {Object} t - GenericTerm node
   * @param {number} nonceIn - obligation nonce this node consumes
   * @param {number} lax - lax flag (0 or 1)
   * @param {number} goal - succedent hash (obligation type)
   * @param {Map<number,number>} delta - live linear context (hash → count), modified in place
   */
  function walk(_t, _nonceIn, _lax, _goal, _delta) {
    // Fully iterative: explicit continuation stack replaces all recursion.
    // Each frame records the next subtree to process + any pre-action (delta
    // mutation or chip row emission) to run before processing it.
    // Zig-portable: bounded heap allocation, no call-stack growth.
    const contStack = [];
    let t = _t, nonceIn = _nonceIn, lax = _lax, goal = _goal, delta = _delta;
    for (;;) {
    processNode: {
    if (!t || !t.rule) break processNode;
    const rule = resolveRule(t);

    switch (rule) {
      case 'id': {
        // IdentityChip: [active, hash, nonce_in, lax]
        chipRows('id').push([1, t.principal, nonceIn, lax]);
        deltaRemove(delta, t.principal);
        break processNode;
      }

      // --- Right rules (consume obligation, produce child obligations) ---

      case 'tensor_r': {
        // Iterative right-spine traversal: collect all left children and the
        // final leaf, push them as continuation frames, trampoline to first.
        let cur = t, curGoal = goal, curNonceIn = nonceIn;
        const leftChildren = [];
        while (resolveRule(cur) === 'tensor_r') {
          const hash = curGoal;
          const c0 = Store.child(hash, 0);
          const c1 = Store.child(hash, 1);
          const n0 = ++nonceCtr;
          const n1 = ++nonceCtr;
          chipRows('tensor_r').push([1, hash, c0, c1, curNonceIn, lax, n0, n1]);
          addFormulaLookup(hash);
          leftChildren.push({ t: cur.subterms[0], nonceIn: n0, goal: c0 });
          curNonceIn = n1;
          curGoal = c1;
          cur = cur.subterms[1];
        }
        // Push leaf (rightmost non-tensor_r), then left children in reverse
        contStack.push({ t: cur, nonceIn: curNonceIn, lax, goal: curGoal, delta });
        for (let i = leftChildren.length - 1; i >= 1; i--) {
          contStack.push({ t: leftChildren[i].t, nonceIn: leftChildren[i].nonceIn, lax, goal: leftChildren[i].goal, delta });
        }
        // Trampoline to first left child
        t = leftChildren[0].t;
        nonceIn = leftChildren[0].nonceIn;
        goal = leftChildren[0].goal;
        continue;
      }

      case 'with_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;

        // Emit DupChip rows for each live element (additive context copy)
        for (const [h, cnt] of delta) {
          for (let i = 0; i < cnt; i++) {
            chipRows('dup').push([h, 1]);
          }
        }

        chipRows('with_r').push([1, hash, c0, c1, nonceIn, lax, n0, n1]);
        addFormulaLookup(hash);

        const delta0 = new Map(delta);
        const delta1 = new Map(delta);
        // Push sub1 continuation, trampoline to sub0
        contStack.push({ t: t.subterms[1], nonceIn: n1, lax, goal: c1, delta: delta1 });
        t = t.subterms[0]; nonceIn = n0; goal = c0; delta = delta0;
        continue;
      }

      case 'loli_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0); // antecedent A
        const c1 = Store.child(hash, 1); // consequent B
        const n0 = ++nonceCtr;
        chipRows('loli_r').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        deltaAdd(delta, c0); // loli_r introduces A into context
        t = t.subterms[0]; nonceIn = n0; goal = c1;
        continue;
      }

      case 'oplus_r1': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        chipRows('oplus_r1').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      case 'oplus_r2': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        chipRows('oplus_r2').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        t = t.subterms[0]; nonceIn = n0; goal = c1;
        continue;
      }

      case 'one_r': {
        chipRows('one_r').push([1, goal, nonceIn, lax]);
        addFormulaLookup(goal);
        break processNode;
      }

      case 'bang_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('bang_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      case 'monad_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('monad_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        // monad_r forces lax=1 for inner proof
        const inner = t.evidence || t.subterms[0];
        t = inner; nonceIn = n0; lax = 1; goal = c0;
        continue;
      }

      case 'exists_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('exists_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      case 'forall_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('forall_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      // --- Context-only left rules (no obligation interaction) ---

      case 'tensor_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        chipRows('tensor_l').push([1, hash, c0, c1]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        deltaAdd(delta, c1);
        t = t.subterms[0]; continue;
      }

      case 'with_l1': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        chipRows('with_l1').push([1, hash, c0, c1]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0); // send child0
        t = t.subterms[0]; continue;
      }

      case 'with_l2': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        chipRows('with_l2').push([1, hash, c0, c1]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c1); // send child1
        t = t.subterms[0]; continue;
      }

      case 'one_l': {
        const hash = t.principal;
        chipRows('one_l').push([1, hash]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        t = t.subterms[0]; continue;
      }

      case 'dereliction': {
        // bang_l (dereliction): !A → A in linear
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('bang_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        t = t.subterms[0]; continue;
      }

      case 'absorption': {
        // bang_l (absorption): !A consumed from linear context, inner A
        // moves to gamma zone (handled by the chip's CONTEXT_BUS receive).
        // The chip does NOT send A to CONTEXT_BUS — gamma membership is
        // tracked externally via GAMMA_BUS.
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('absorption').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        t = t.subterms[0]; continue;
      }

      case 'monad_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('monad_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        t = t.subterms[0]; continue;
      }

      case 'exists_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('exists_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        t = t.subterms[0]; continue;
      }

      case 'forall_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('forall_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        t = t.subterms[0]; continue;
      }

      case 'copy': {
        const hash = t.principal;

        // Phase 6-4: custom chip short-circuit for clause proof copies.
        // Clause proof subtrees have principal = loli(ant, monad(Q)).
        // When customChips is non-empty, intercept ALL clause proof copies
        // and replace the entire subtree with a single fact_axiom row.
        //
        // The copy node is annotated (by buildStepTerm) with:
        //   consumed: ground linear facts consumed from CONTEXT_BUS
        //   produced: ground linear facts produced to CONTEXT_BUS
        //   continuation: next step (skipping the clause proof internals)
        //
        // fact_axiom handles: OBLIG_BUS.receive/send + FACT_BUS lookup +
        // CONTEXT_BUS.receive(consumed) + CONTEXT_BUS.send(produced).
        if (customChips.size > 0 && Store.isTerm(hash) && Store.tag(hash) === 'loli') {
          const monadH = Store.child(hash, 1);
          if (Store.isTerm(monadH) && Store.tag(monadH) === 'monad') {
            const consumed = t.consumed || [];
            const produced = t.produced || [];
            // Apply CONTEXT_BUS effects to live delta FIRST so we can
            // compute goalOut from the full state (not just produced).
            for (const h of consumed) deltaRemove(delta, h);
            for (const h of produced) deltaAdd(delta, h);
            // Continuation obligation: goal_out = tensor of ALL facts
            // currently in delta.  Steps may only consume/produce a
            // subset of the state, so produced alone is insufficient.
            const allDeltaFacts = [];
            for (const [h, cnt] of delta) {
              for (let k = 0; k < cnt; k++) allDeltaFacts.push(h);
            }
            // Sort numerically to match buildSuccedentFromState ordering
            // (Object.entries sorts integer keys), ensuring the last
            // step's goalOut matches the monad body hash from monad_r.
            allDeltaFacts.sort((a, b) => a - b);
            const goalOut = buildRightTensor(allDeltaFacts);
            const nonceOut = ++nonceCtr;
            // Phase 6-6a: extract predicate hash from persistent goals.
            // persistentGoals contains the ground predicate applications (e.g., inc(2,3))
            // annotated by buildStepTerm from the trace's persistentEvidence.
            const persistentGoals = t.persistentGoals || [];
            // Phase 6-6c/d: set pred_hash/pred_active for ALL recognized predicates
            // (plus, mul, inc, arr_get, arr_set, mem_read, mem_expand).
            let predHash = 0;
            let predActive = 0;
            for (const pg of persistentGoals) {
              if (extractPredMeta(pg)) {
                predHash = pg;
                predActive = 1;
                break;
              }
            }
            // fact_axiom row: [active, goal, nonce_in, lax, goal_out, nonce_out,
            //   c0..c5, ca0..ca5, p0..p5, pa0..pa5, pred_hash, pred_active]
            const row = [1, goal, nonceIn, lax, goalOut, nonceOut];
            for (let i = 0; i < 6; i++) row.push(i < consumed.length ? consumed[i] : 0);
            for (let i = 0; i < 6; i++) row.push(i < consumed.length ? 1 : 0);
            for (let i = 0; i < 6; i++) row.push(i < produced.length ? produced[i] : 0);
            for (let i = 0; i < 6; i++) row.push(i < produced.length ? 1 : 0);
            row.push(predHash); // col 30: pred_hash for PRED_BUS
            row.push(predActive); // col 31: pred_active
            chipRows('fact_axiom').push(row);
            _faSegment++;
            _boundaryDeltas.push(new Map(delta));
            factRomEntries.set(goal, (factRomEntries.get(goal) || 0) + 1);
            if (predActive) addPredRomEntry(predHash);
            // Note: additional persistent goals beyond predHash are NOT added
            // to pred_rom. Each fact_axiom row does exactly one PRED_BUS lookup.
            // Multi-predicate steps verify only the first recognized goal;
            // additional goals require multi-slot pred_hash (future phase).
            // Continue with next step using the continuation obligation
            if (t.continuation) {
              nonceIn = nonceOut;
              goal = goalOut;
              t = t.continuation;
              continue;
            }
            break processNode;
          }
        }

        chipRows('copy').push([1, hash]);
        addGammaLookup(hash);
        deltaAdd(delta, hash);
        t = t.subterms[0]; continue;
      }

      case 'loli_match': {
        // Loli match with freevars: the original loli body contains unresolved
        // freevars (e.g., sha3's _Bytes). The forward engine resolves these via
        // subApplyIdx, producing ground facts. We bridge the hash mismatch with
        // a SubstChip: swap original loli → ground loli on CONTEXT_BUS, then
        // decompose the ground version normally.
        const hash = t.principal;
        const c0 = t.groundAntecedent; // ground antecedent (freevars resolved)

        // Construct ground body: right-nested tensor chain from ground facts
        const groundFacts = t.groundFacts || [];
        const groundBody = buildRightTensor(groundFacts);
        const groundMonad = Store.put('monad', [groundBody]);
        const groundLoli = Store.put('loli', [c0, groundMonad]);

        // SubstChip: recursive tree walk verifying old→new substitution
        const sid = ++substIdCtr;
        emitSubstTree(hash, groundLoli, sid, true);
        deltaRemove(delta, hash);

        // Now decompose the ground loli exactly like a normal loli_l
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;
        chipRows('loli_l').push([1, groundLoli, c0, groundMonad, nonceIn, lax, n0, n1, goal]);
        addFormulaLookup(groundLoli);

        // Emit monad_l + ground body decomposition chip rows now (order-independent)
        chipRows('monad_l').push([1, groundMonad, groundBody]);
        addFormulaLookup(groundMonad);
        emitGroundDecomp(groundBody);

        // Push continuation: add ground facts to delta, then process sub1
        const _groundFacts = groundFacts;
        const _delta = delta;
        contStack.push({
          t: t.subterms[1], nonceIn: n1, lax, goal, delta,
          before() { for (let i = 0; i < _groundFacts.length; i++) deltaAdd(_delta, _groundFacts[i]); }
        });
        // Trampoline to sub0 (antecedent proof)
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      case 'ffi': {
        // FFI axiom: absorbs obligation without proof (trusted).
        // Width 4: [active, hash, nonce_in, lax] — same layout as one_r.
        chipRows('ffi').push([1, goal, nonceIn, lax]);
        break processNode;
      }

      // --- Left-focus rules (consume obligation + context) ---

      case 'loli_l': {
        if (t.subterms.length === 1) {
          // Invertible variant: context-only decomposition (like tensor_l).
          // Backward prover applies this in the invertible phase — no obligation
          // split. Consume A⊸B, add both A (antecedent) and B (body) to context.
          const hash = t.principal;
          const c0 = Store.child(hash, 0); // A
          const c1 = Store.child(hash, 1); // B
          chipRows('loli_l_inv').push([1, hash, c0, c1]);
          addFormulaLookup(hash);
          deltaRemove(delta, hash);
          deltaAdd(delta, c0);
          deltaAdd(delta, c1);
          t = t.subterms[0]; continue;
        }
        const hash = t.principal;
        const c0 = Store.child(hash, 0); // A
        const c1 = Store.child(hash, 1); // B
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;

        chipRows('loli_l').push([1, hash, c0, c1, nonceIn, lax, n0, n1, goal]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);

        // Push continuation: after sub0, add B to delta, then process sub1
        contStack.push({ t: t.subterms[1], nonceIn: n1, lax, goal, delta, deltaAddHash: c1 });
        // Trampoline to sub0
        t = t.subterms[0]; nonceIn = n0; goal = c0;
        continue;
      }

      case 'oplus_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;

        deltaRemove(delta, hash);

        // Emit DupChip rows for remaining live elements (context copy)
        for (const [h, cnt] of delta) {
          for (let i = 0; i < cnt; i++) {
            chipRows('dup').push([h, 1]);
          }
        }

        chipRows('oplus_l').push([1, hash, c0, c1, nonceIn, lax, n0, n1, goal]);
        addFormulaLookup(hash);

        const delta0 = new Map(delta);
        deltaAdd(delta0, c0);
        const delta1 = new Map(delta);
        deltaAdd(delta1, c1);

        // Push sub1 continuation, trampoline to sub0
        contStack.push({ t: t.subterms[1], nonceIn: n1, lax, goal, delta: delta1 });
        t = t.subterms[0]; nonceIn = n0; delta = delta0;
        continue;
      }

      // --- Zero (specialized) ---

      case 'zero_l': {
        const hash = t.principal;
        deltaRemove(delta, hash);
        const numDiscards = mapTotal(delta);

        chipRows('zero_l').push([hash, 1, nonceIn, lax, goal, numDiscards]);
        addFormulaLookup(hash);

        // Emit DiscardChip rows for each remaining element
        for (const [h, cnt] of delta) {
          for (let i = 0; i < cnt; i++) {
            chipRows('discard').push([h, 1, nonceIn]);
          }
        }
        delta.clear();
        break processNode;
      }

      default:
        throw new Error(`unsupported rule in ZK witness: ${rule}`);
    }
    } // end processNode

    // Pop next continuation frame or return
    if (contStack.length === 0) return;
    const frame = contStack.pop();
    if (frame.before) frame.before();
    if (frame.deltaAddHash !== undefined) deltaAdd(frame.delta, frame.deltaAddHash);
    t = frame.t; nonceIn = frame.nonceIn; lax = frame.lax; goal = frame.goal; delta = frame.delta;
    } // end for
  }

  _boundaryDeltas.push(new Map(liveDelta)); // boundaryDeltas[0] = initial delta
  walk(term, 0, 0, succedent, liveDelta);

  // --- Build formula ROM ---
  const formula_rom = [];
  for (const [hash, info] of formulaLookups) {
    formula_rom.push([hash, info.tag, info.c0, info.c1, 1, info.count]);
  }

  // --- Build gamma ROM ---
  const gamma_rom = [];
  for (const [hash, count] of gammaEntries) {
    gamma_rom.push([hash, 1, count]);
  }

  // --- Build freevar ROM ---
  // [subst_id, freevar_hash, ground_value, is_active, num_lookups]
  const freevar_rom = [];
  for (const entry of freevarRomEntries.values()) {
    freevar_rom.push([entry.substId, entry.freevarHash, entry.groundValue, 1, entry.count]);
  }

  // --- Build fact ROM (Phase 6-4: custom chip verified facts) ---
  // [goal_hash, is_active, num_lookups]
  const fact_rom = [];
  for (const [hash, count] of factRomEntries) {
    fact_rom.push([hash, 1, count]);
  }

  // --- Build pred ROM (Phase 6-6a/c/d: in-circuit predicate verification) ---
  // [pred_hash, is_active, num_lookups, is_plus, is_mul, is_inc,
  //  is_arr_get, is_arr_set, is_mem_read, is_mem_expand, arg0, arg1, arg2, arg3]
  const pred_rom = [];
  for (const [hash, entry] of predRomEntries) {
    pred_rom.push([hash, 1, entry.count,
      entry.is_plus, entry.is_mul, entry.is_inc,
      entry.is_arr_get, entry.is_arr_set, entry.is_mem_read, entry.is_mem_expand,
      entry.arg0, entry.arg1, entry.arg2, entry.arg3]);
  }

  // --- Build uint256_arith (Phase 6-6b: 256-bit arithmetic verification) ---
  // Preprocessed (101 cols): [pred_hash, is_active, is_plus_256, is_inc_256, is_mul_256,
  //                           a_0..31, b_0..31, c_0..31]
  // Main (65 cols): [num_lookups, carry_lo_0..31, carry_hi_0..31]
  // JSON format: all 166 cols concatenated
  const uint256_arith = [];
  for (const [hash, entry] of uint256ArithEntries) {
    const row = [hash, 1, entry.is_plus_256, entry.is_inc_256, entry.is_mul_256];
    row.push(...entry.a_limbs);    // 32 limbs
    row.push(...entry.b_limbs);    // 32 limbs
    row.push(...entry.c_limbs);    // 32 limbs
    row.push(entry.count);         // num_lookups
    row.push(...entry.carries_lo); // 32 carry_lo
    row.push(...entry.carries_hi); // 32 carry_hi
    uint256_arith.push(row);
  }

  // --- Build byte_check_rom (Phase 6-6b: byte range check table) ---
  // 256 entries: [num_lookups] per byte value 0..255
  // Only included when uint256_arith has entries.
  const byte_check_rom = uint256_arith.length > 0 ? [...byteCheckCounts] : [];

  // Derive rule specs from calculus (or use provided ones)
  const ruleSpecs = opts.ruleSpecs || deriveZkRuleSpecs(opts.calculus, ZK_TAGS);

  // --- Bus balance pre-flight check ---
  // Catches supply/demand imbalances before they reach the STARK prover.
  verifyBusBalance(chips, fact_rom, pred_rom, uint256_arith);

  return {
    tags: ZK_TAGS, rule_specs: ruleSpecs, chips, formula_rom, gamma_rom, freevar_rom,
    fact_rom, pred_rom, uint256_arith, byte_check_rom,
    chipSegments: _chipSegments, boundaryDeltas: _boundaryDeltas, faCount: _faSegment,
  };
}

/**
 * Verify bus balance: FACT_BUS and PRED_BUS supply/demand must match.
 * Throws on imbalance — catches witness generation bugs before STARK proving.
 */
function verifyBusBalance(chips, fact_rom, pred_rom, uint256_arith) {
  // FACT_BUS: fact_rom supply count must equal fact_axiom demand count
  const factRomSupply = fact_rom.reduce((sum, entry) => sum + entry[2], 0); // sum of num_lookups
  const factAxiomRows = (chips.fact_axiom || []).filter(r => r[0] === 1);
  const factDemand = factAxiomRows.length;
  if (factRomSupply !== factDemand) {
    throw new Error(
      `FACT_BUS imbalance: fact_rom supply=${factRomSupply} but fact_axiom demand=${factDemand}`
    );
  }

  // PRED_BUS: (pred_rom + uint256_arith) supply must equal fact_axiom pred_active demand
  const predRomSupply = pred_rom.reduce((sum, entry) => sum + entry[2], 0); // sum of num_lookups
  // uint256_arith: num_lookups is at index 101 (after 101 preprocessed cols)
  const uint256Supply = (uint256_arith || []).reduce((sum, entry) => sum + entry[101], 0);
  const totalPredSupply = predRomSupply + uint256Supply;
  const predDemand = factAxiomRows.filter(r => r[31] === 1).length; // pred_active=1
  if (totalPredSupply !== predDemand) {
    throw new Error(
      `PRED_BUS imbalance: pred_rom+uint256 supply=${totalPredSupply} but fact_axiom pred_active demand=${predDemand}`
    );
  }
}

// --- Delta helpers (multiset: hash → count) ---

function deltaAdd(delta, hash) {
  delta.set(hash, (delta.get(hash) || 0) + 1);
}

function deltaRemove(delta, hash) {
  const cnt = delta.get(hash);
  if (cnt == null || cnt <= 0) {
    throw new Error(`deltaRemove: hash ${hash} not in live delta`);
  }
  if (cnt === 1) delta.delete(hash);
  else delta.set(hash, cnt - 1);
}

function mapTotal(m) {
  let total = 0;
  for (const v of m.values()) total += v;
  return total;
}

// --- Rule name resolution ---

/**
 * Resolve proof term rule name to canonical ZK chip name.
 *
 * The backward prover uses spec keys (e.g., 'bang_l' for both dereliction
 * and absorption). This function disambiguates using structural heuristics.
 */
function resolveRule(term) {
  const rule = term.rule;

  // Direct mappings
  if (rule === 'id' || rule === 'id_+' || rule === 'id_-') return 'id';
  if (rule === 'promotion') return 'bang_r';

  // bang_l disambiguation: dereliction vs absorption
  if (rule === 'bang_l') {
    // Check if the continuation immediately copies the inner formula from gamma.
    // If so, it's absorption (inner went to gamma). Otherwise dereliction.
    if (term.subterms.length === 1 && term.principal != null) {
      const inner = Store.child(term.principal, 0);
      const cont = term.subterms[0];
      if (cont && cont.rule === 'copy' && cont.principal === inner) {
        return 'absorption';
      }
    }
    return 'dereliction';
  }

  return rule;
}

/**
 * Generate chunked tree witness from a full tree witness.
 *
 * Phase 6-7: splits a tree witness into chunks by fact_axiom row count.
 * Uses segment-based assignment: each chip row is tagged with the
 * fact_axiom index at the time of emission. Structural rules (loli_l,
 * tensor_r, id, etc.) go to the chunk containing their nonce range.
 *
 * @param {Object} fullWitness - Full tree witness from generateWitness()
 * @param {Object} opts - Options
 * @param {number} [opts.maxFactAxiomPerChunk=128] - Max fact_axiom rows per chunk
 * @returns {Object[]} Array of chunk witnesses (each is a WitnessJson)
 */
function generateChunkedTreeWitness(fullWitness, opts = {}) {
  const maxPerChunk = opts.maxFactAxiomPerChunk || 128;
  const faCount = fullWitness.faCount || (fullWitness.chips.fact_axiom || []).filter(r => r[0] === 1).length;

  if (faCount <= maxPerChunk) return [fullWitness];

  const numChunks = Math.ceil(faCount / maxPerChunk);
  const chipSegments = fullWitness.chipSegments;
  const boundaryDeltas = fullWitness.boundaryDeltas;

  // Segment-to-chunk mapping.
  // fa row K (0-indexed) gets segment K → chunk floor(K / maxPerChunk).
  // Non-fa chips between fa K-1 and fa K get segment K → same chunk as fa K.
  // Non-fa chips after last fa get segment faCount → last chunk.
  function segmentToChunk(segment) {
    if (segment >= faCount) return numChunks - 1;
    return Math.min(Math.floor(segment / maxPerChunk), numChunks - 1);
  }

  // Initialize per-chunk chip arrays
  const chunkChips = [];
  for (let ci = 0; ci < numChunks; ci++) chunkChips.push({});

  // Distribute chip rows to chunks based on segment
  for (const [chipName, rows] of Object.entries(fullWitness.chips)) {
    const segments = (chipSegments && chipSegments[chipName]) || [];
    for (let ci = 0; ci < numChunks; ci++) {
      if (!chunkChips[ci][chipName]) chunkChips[ci][chipName] = [];
    }
    for (let r = 0; r < rows.length; r++) {
      const segment = segments[r] != null ? segments[r] : 0;
      const chunk = segmentToChunk(segment);
      chunkChips[chunk][chipName].push(rows[r]);
    }
  }

  // Boundary states from recorded deltas.
  // boundaryDeltas[K] = delta after fa row K-1 (1-indexed).
  // Boundary between chunk I and I+1: after fa row (I+1)*maxPerChunk - 1
  // = boundaryDeltas[(I+1)*maxPerChunk].
  const boundaryStates = [];
  for (let i = 0; i < numChunks - 1; i++) {
    const bdIdx = (i + 1) * maxPerChunk;
    const delta = boundaryDeltas[bdIdx];
    const faRows = chunkChips[i].fact_axiom || [];
    const lastFaRow = faRows[faRows.length - 1];
    boundaryStates.push({
      goalOut: lastFaRow[4],
      nonceOut: lastFaRow[5],
      lax: lastFaRow[3],
      delta: delta,
    });
  }

  // Compute normalization sizes
  let maxObligCount = 1;
  let maxBoundaryCtxSize = 0;
  for (const bs of boundaryStates) {
    let total = 0;
    for (const cnt of bs.delta.values()) total += cnt;
    if (total > maxBoundaryCtxSize) maxBoundaryCtxSize = total;
  }
  {
    let initTotal = 0;
    for (const cnt of boundaryDeltas[0].values()) initTotal += cnt;
    if (initTotal > maxBoundaryCtxSize) maxBoundaryCtxSize = initTotal;
  }

  // Build chunk witnesses
  const chunks = [];
  for (let i = 0; i < numChunks; i++) {
    const chunk = { ...fullWitness };
    chunk.chips = { ...chunkChips[i] };

    // Build boundary chip rows
    const obligBoundaryRows = [];
    const ctxBoundaryRows = [];

    if (i > 0) {
      const bs = boundaryStates[i - 1];
      obligBoundaryRows.push([1, 1, bs.nonceOut, bs.goalOut, bs.lax]);
      for (const [h, cnt] of bs.delta) {
        for (let k = 0; k < cnt; k++) {
          ctxBoundaryRows.push([1, 1, h]);
        }
      }
      // Constant VK: keep same preprocessed init data, deactivate main trace
      chunk.chips.init = fullWitness.chips.init.map(row => {
        const r = [...row];
        r[4] = 0; // nonce = 0
        r[6] = 0; // is_active = 0
        return r;
      });
    }

    if (i < numChunks - 1) {
      const faRows = chunkChips[i].fact_axiom || [];
      const lastRow = faRows[faRows.length - 1];
      obligBoundaryRows.push([1, 0, lastRow[5], lastRow[4], lastRow[3]]);
      const bs = boundaryStates[i];
      for (const [h, cnt] of bs.delta) {
        for (let k = 0; k < cnt; k++) {
          ctxBoundaryRows.push([1, 0, h]);
        }
      }
    }

    chunk.chips.oblig_boundary = obligBoundaryRows;
    chunk.chips.ctx_boundary = ctxBoundaryRows;
    chunk.max_oblig_count = maxObligCount;
    chunk.max_boundary_ctx_size = maxBoundaryCtxSize;

    // Per-chunk ROM lookups (counts only — normalization unifies entries below)
    chunk.fact_rom = recomputeFactRom(chunkChips[i].fact_axiom || [], fullWitness.fact_rom);
    chunk.pred_rom = recomputePredRom(chunkChips[i].fact_axiom || [], fullWitness.pred_rom);
    chunk.formula_rom = recomputeFormulaRom(chunkChips[i], fullWitness.formula_rom);
    chunk.gamma_rom = recomputeGammaRom(chunkChips[i], fullWitness.gamma_rom);
    chunk.freevar_rom = recomputeFreevarRom(chunkChips[i], fullWitness.freevar_rom);
    // Phase 6-6b: recompute uint256_arith + byte_check_rom per chunk
    const u256Recomputed = recomputeUint256Arith(chunkChips[i].fact_axiom || [], fullWitness.uint256_arith);
    chunk.uint256_arith = u256Recomputed;
    chunk.byte_check_rom = recomputeByteCheckRom(u256Recomputed, fullWitness.byte_check_rom);

    chunks.push(chunk);
  }

  // Constant VK: normalize ROMs across chunks (union with per-chunk lookups)
  normalizeTreeRoms(chunks);

  return chunks;
}

/**
 * Recompute fact_rom for a subset of fact_axiom rows.
 * Returns fact_rom entries with corrected num_lookups for this chunk.
 */
function recomputeFactRom(faRows, fullFactRom) {
  // Count goal_hash occurrences in this chunk
  const goalCounts = new Map();
  for (const row of faRows) {
    if (row[0] === 1) { // active
      const goal = row[1];
      goalCounts.set(goal, (goalCounts.get(goal) || 0) + 1);
    }
  }
  // Rebuild fact_rom with per-chunk counts
  const result = [];
  for (const entry of fullFactRom) {
    const hash = entry[0];
    const count = goalCounts.get(hash);
    if (count) {
      result.push([hash, 1, count]);
    }
  }
  return result;
}

/**
 * Recompute pred_rom for a subset of fact_axiom rows.
 * Returns pred_rom entries with corrected num_lookups for this chunk.
 */
function recomputePredRom(faRows, fullPredRom) {
  // Count pred_hash occurrences in this chunk (only pred_active=1 rows)
  const predCounts = new Map();
  for (const row of faRows) {
    if (row[0] === 1 && row[31] === 1) { // active && pred_active
      const predHash = row[30];
      predCounts.set(predHash, (predCounts.get(predHash) || 0) + 1);
    }
  }
  // Rebuild pred_rom with per-chunk counts
  const result = [];
  for (const entry of fullPredRom) {
    const hash = entry[0];
    const count = predCounts.get(hash);
    if (count) {
      // Copy full entry, update num_lookups (index 2)
      const newEntry = [...entry];
      newEntry[2] = count;
      result.push(newEntry);
    }
  }
  return result;
}

/**
 * Recompute uint256_arith for a chunk's fact_axiom rows.
 * Returns uint256_arith entries with per-chunk num_lookups (index 101).
 */
function recomputeUint256Arith(faRows, fullUint256Arith) {
  if (!fullUint256Arith || fullUint256Arith.length === 0) return [];
  // Build set of uint256 pred_hashes for O(1) lookup
  const u256Hashes = new Set(fullUint256Arith.map(e => e[0]));
  // Count pred_hash occurrences referencing uint256 entries
  const predCounts = new Map();
  for (const row of faRows) {
    if (row[0] === 1 && row[31] === 1) { // active && pred_active
      const predHash = row[30];
      if (u256Hashes.has(predHash)) {
        predCounts.set(predHash, (predCounts.get(predHash) || 0) + 1);
      }
    }
  }
  const result = [];
  for (const entry of fullUint256Arith) {
    const hash = entry[0];
    const count = predCounts.get(hash);
    if (count) {
      const newEntry = [...entry];
      newEntry[101] = count; // num_lookups
      result.push(newEntry);
    }
  }
  return result;
}

/**
 * Recompute byte_check_rom for a chunk's uint256_arith entries.
 * Counts byte lookups from limbs and carries in this chunk's uint256 entries.
 */
function recomputeByteCheckRom(chunkUint256, fullByteCheckRom) {
  if (!fullByteCheckRom || fullByteCheckRom.length === 0) return [];
  if (!chunkUint256 || chunkUint256.length === 0) {
    // No uint256 entries in this chunk — all counts zero
    return new Array(256).fill(0);
  }
  const counts = new Array(256).fill(0);
  for (const entry of chunkUint256) {
    const numLookups = entry[101];
    // Each active entry contributes numLookups * (limb + carry lookups) per byte value
    // Limbs: a[5..36], b[37..68], c[69..100]; carries_lo[102..133], carries_hi[134..165]
    for (let i = 0; i < NUM_LIMBS; i++) {
      counts[entry[5 + i]] += numLookups;   // a_limb
      counts[entry[37 + i]] += numLookups;  // b_limb
      counts[entry[69 + i]] += numLookups;  // c_limb
      counts[entry[102 + i]] += numLookups; // carry_lo
      counts[entry[134 + i]] += numLookups; // carry_hi
    }
  }
  return counts;
}

// Chips that do NOT look up formula_rom
const NO_FORMULA_LOOKUP = new Set([
  'id', 'copy', 'fact_axiom', 'init', 'dup', 'zero_l', 'discard',
  'oblig_boundary', 'ctx_boundary', 'ffi',
  'subst', // handled separately below (needs both oldHash and newHash)
]);

/**
 * Recompute formula_rom for a chunk's chips.
 * Counts formula hash lookups from rule chips (col 1 = formula hash).
 * SubstChip is special: looks up both oldHash (col 1) and newHash (col 2),
 * except freevar rows (is_freevar=1, col 4) which only look up oldHash.
 */
function recomputeFormulaRom(chunkChips, fullFormulaRom) {
  const lookupCounts = new Map();
  for (const [chipName, rows] of Object.entries(chunkChips)) {
    if (NO_FORMULA_LOOKUP.has(chipName)) continue;
    for (const row of rows) {
      const hash = row[1]; // formula hash is always col 1 for rule chips
      lookupCounts.set(hash, (lookupCounts.get(hash) || 0) + 1);
    }
  }
  // SubstChip: oldHash (col 1) always looked up;
  // newHash (col 2) also looked up for non-freevar rows
  for (const row of (chunkChips.subst || [])) {
    lookupCounts.set(row[1], (lookupCounts.get(row[1]) || 0) + 1);
    if (row[4] !== 1) { // not freevar → also count newHash
      lookupCounts.set(row[2], (lookupCounts.get(row[2]) || 0) + 1);
    }
  }
  const result = [];
  for (const entry of fullFormulaRom) {
    const hash = entry[0];
    const count = lookupCounts.get(hash);
    if (count) {
      result.push([hash, entry[1], entry[2], entry[3], 1, count]);
    }
  }
  return result;
}

/**
 * Recompute gamma_rom for a chunk's chips.
 * Only 'copy' chip rows look up gamma_rom (col 1 = hash).
 */
function recomputeGammaRom(chunkChips, fullGammaRom) {
  const lookupCounts = new Map();
  for (const row of (chunkChips.copy || [])) {
    const hash = row[1];
    lookupCounts.set(hash, (lookupCounts.get(hash) || 0) + 1);
  }
  const result = [];
  for (const entry of fullGammaRom) {
    const hash = entry[0];
    const count = lookupCounts.get(hash);
    if (count) {
      result.push([hash, 1, count]);
    }
  }
  return result;
}

/**
 * Recompute freevar_rom for a chunk's chips.
 * SubstChip rows with is_freevar=1 (col 4) look up freevar_rom.
 */
function recomputeFreevarRom(chunkChips, fullFreevarRom) {
  const lookupCounts = new Map();
  for (const row of (chunkChips.subst || [])) {
    if (row[4] === 1) { // is_freevar
      const key = `${row[5]}:${row[1]}`; // substId:freevarHash(oldHash)
      lookupCounts.set(key, (lookupCounts.get(key) || 0) + 1);
    }
  }
  const result = [];
  for (const entry of fullFreevarRom) {
    const key = `${entry[0]}:${entry[1]}`;
    const count = lookupCounts.get(key);
    if (count) {
      result.push([entry[0], entry[1], entry[2], 1, count]);
    }
  }
  return result;
}

/**
 * Normalize ROM entries across tree chunks so preprocessed data is program-static.
 * Same pattern as flat path's normalizeRoms, extended for fact_rom and pred_rom.
 */
function normalizeTreeRoms(chunks) {
  // FormulaRom: [hash, tag, c0, c1, is_active, num_lookups]
  const formulaUnion = new Map();
  const formulaLookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of chunk.formula_rom) {
      if (!formulaUnion.has(row[0])) {
        formulaUnion.set(row[0], [row[0], row[1], row[2], row[3], row[4]]);
      }
      cl.set(row[0], row[5]);
    }
    formulaLookups.push(cl);
  }
  const formulaKeys = [...formulaUnion.keys()].sort((a, b) => a - b);
  for (let i = 0; i < chunks.length; i++) {
    chunks[i].formula_rom = formulaKeys.map(h => [
      ...formulaUnion.get(h), formulaLookups[i].get(h) || 0,
    ]);
  }

  // GammaRom: [hash, is_active, num_lookups]
  const gammaUnion = new Map();
  const gammaLookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of chunk.gamma_rom) {
      if (!gammaUnion.has(row[0])) {
        gammaUnion.set(row[0], [row[0], row[1]]);
      }
      cl.set(row[0], row[2]);
    }
    gammaLookups.push(cl);
  }
  const gammaKeys = [...gammaUnion.keys()].sort((a, b) => a - b);
  for (let i = 0; i < chunks.length; i++) {
    chunks[i].gamma_rom = gammaKeys.map(h => [
      ...gammaUnion.get(h), gammaLookups[i].get(h) || 0,
    ]);
  }

  // FreevarRom: [substId, freevarHash, groundValue, is_active, num_lookups]
  const freevarUnion = new Map();
  const freevarLookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of (chunk.freevar_rom || [])) {
      const key = `${row[0]}:${row[1]}:${row[2]}`;
      if (!freevarUnion.has(key)) {
        freevarUnion.set(key, [row[0], row[1], row[2], row[3]]);
      }
      cl.set(key, row[4]);
    }
    freevarLookups.push(cl);
  }
  const freevarKeys = [...freevarUnion.keys()].sort();
  for (let i = 0; i < chunks.length; i++) {
    chunks[i].freevar_rom = freevarKeys.map(k => [
      ...freevarUnion.get(k), freevarLookups[i].get(k) || 0,
    ]);
  }

  // FactRom: [hash, is_active, num_lookups]
  const factUnion = new Map();
  const factLookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of (chunk.fact_rom || [])) {
      if (!factUnion.has(row[0])) {
        factUnion.set(row[0], [row[0], row[1]]);
      }
      cl.set(row[0], row[2]);
    }
    factLookups.push(cl);
  }
  const factKeys = [...factUnion.keys()].sort((a, b) => a - b);
  for (let i = 0; i < chunks.length; i++) {
    chunks[i].fact_rom = factKeys.map(h => [
      ...factUnion.get(h), factLookups[i].get(h) || 0,
    ]);
  }

  // PredRom: [pred_hash, is_active, num_lookups, is_plus, is_mul, is_inc,
  //           is_arr_get, is_arr_set, is_mem_read, is_mem_expand, arg0, arg1, arg2, arg3]
  const predUnion = new Map();
  const predLookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of (chunk.pred_rom || [])) {
      if (!predUnion.has(row[0])) {
        // Everything except num_lookups (index 2)
        const entry = [...row];
        entry.splice(2, 1); // remove num_lookups
        predUnion.set(row[0], entry);
      }
      cl.set(row[0], row[2]);
    }
    predLookups.push(cl);
  }
  const predKeys = [...predUnion.keys()].sort((a, b) => a - b);
  for (let i = 0; i < chunks.length; i++) {
    chunks[i].pred_rom = predKeys.map(h => {
      const entry = [...predUnion.get(h)];
      // Re-insert num_lookups at index 2
      entry.splice(2, 0, predLookups[i].get(h) || 0);
      return entry;
    });
  }

  // Uint256Arith: [pred_hash, is_active, ...(99 prep cols), num_lookups, ...(64 main cols)]
  // Total 166 cols. num_lookups at index 101.
  const u256Union = new Map();
  const u256Lookups = [];
  for (const chunk of chunks) {
    const cl = new Map();
    for (const row of (chunk.uint256_arith || [])) {
      if (!u256Union.has(row[0])) {
        const entry = [...row];
        entry[101] = 0; // zero out num_lookups (will be set per-chunk)
        u256Union.set(row[0], entry);
      }
      cl.set(row[0], row[101]);
    }
    u256Lookups.push(cl);
  }
  if (u256Union.size > 0) {
    const u256Keys = [...u256Union.keys()].sort((a, b) => a - b);
    for (let i = 0; i < chunks.length; i++) {
      chunks[i].uint256_arith = u256Keys.map(h => {
        const entry = [...u256Union.get(h)];
        entry[101] = u256Lookups[i].get(h) || 0;
        return entry;
      });
      // Recompute byte_check_rom for normalized uint256_arith
      chunks[i].byte_check_rom = recomputeByteCheckRom(chunks[i].uint256_arith, chunks[i].byte_check_rom);
    }
  }
}

module.exports = {
  generateWitness, generateChunkedTreeWitness, deriveZkTags, deriveZkRuleSpecs,
  // Phase 6-6b: exported for testing
  extractUint256PredMeta, bigintToLimbs, computeAdditionCarries, computeIncrementCarries, computeMultiplicationCarries,
};
