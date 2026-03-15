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
  // instead of blind trust. Used for arr_get, inc, plus, mul, neq.
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
  const customChips = opts.customChips || new Set();
  let nonceCtr = 0;
  let substIdCtr = 0;
  const formulaLookups = new Map(); // hash → { tag, c0, c1, count }
  const gammaEntries = new Map();   // hash → lookup count
  const freevarRomEntries = new Map(); // `${substId}:${freevarHash}` → { substId, freevarHash, groundValue, count }
  const factRomEntries = new Map(); // goalHash → lookup count (Phase 6-4 custom chips)

  // Per-chip trace rows
  const chips = {
    init: [],
    dup: [],
    zero_l: [],
    discard: [],
  };
  // Dynamic chip names (one array per RuleSpec name encountered)
  function chipRows(name) {
    if (!chips[name]) chips[name] = [];
    return chips[name];
  }

  function addFormulaLookup(hash) {
    if (!Store.isTerm(hash)) return;
    const tag = Store.tag(hash);
    let zkTag = ZK_TAGS[tag];
    if (zkTag == null) {
      // Dynamically assign ZK tags for predicate/atom nodes encountered
      // during SubstChip tree verification
      const maxTag = Object.values(ZK_TAGS).reduce((a, b) => Math.max(a, b), 0);
      ZK_TAGS[tag] = maxTag + 1;
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
  if (linear.length > 0) {
    chips.init.push([linear[0], 1, succedent, 1, 0, 0]);
  } else {
    chips.init.push([0, 0, succedent, 1, 0, 0]);
  }
  // Additional context rows
  for (let i = 1; i < linear.length; i++) {
    chips.init.push([linear[i], 1, 0, 0, 0, 0]);
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
            chips.dup.push([h, 1]);
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
            // fact_axiom row: [active, goal, nonce_in, lax, goal_out, nonce_out,
            //   c0..c5, ca0..ca5, p0..p5, pa0..pa5]
            const row = [1, goal, nonceIn, lax, goalOut, nonceOut];
            for (let i = 0; i < 6; i++) row.push(i < consumed.length ? consumed[i] : 0);
            for (let i = 0; i < 6; i++) row.push(i < consumed.length ? 1 : 0);
            for (let i = 0; i < 6; i++) row.push(i < produced.length ? produced[i] : 0);
            for (let i = 0; i < 6; i++) row.push(i < produced.length ? 1 : 0);
            chipRows('fact_axiom').push(row);
            factRomEntries.set(goal, (factRomEntries.get(goal) || 0) + 1);
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
            chips.dup.push([h, 1]);
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

        chips.zero_l.push([hash, 1, nonceIn, lax, goal, numDiscards]);
        addFormulaLookup(hash);

        // Emit DiscardChip rows for each remaining element
        for (const [h, cnt] of delta) {
          for (let i = 0; i < cnt; i++) {
            chips.discard.push([h, 1, nonceIn]);
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

  // Derive rule specs from calculus (or use provided ones)
  const ruleSpecs = opts.ruleSpecs || deriveZkRuleSpecs(opts.calculus, ZK_TAGS);

  return { tags: ZK_TAGS, rule_specs: ruleSpecs, chips, formula_rom, gamma_rom, freevar_rom, fact_rom };
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

module.exports = { generateWitness, deriveZkTags, deriveZkRuleSpecs };
