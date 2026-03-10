/**
 * ZK Witness Generator — converts ILL proof terms to STARK trace data.
 *
 * Takes a GenericTerm + Sequent + Store (global) and produces per-chip
 * trace rows + formula ROM + gamma ROM as JSON. The Rust bridge
 * deserializes this into RowMajorMatrix per chip and runs the prover.
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

// ZK tag constants — must match zk/ill-checker/src/tags.rs
const ZK_TAGS = {
  tensor: 1, loli: 2, with: 3, bang: 4, oplus: 5,
  monad: 6, one: 7, zero: 8, exists: 9, forall: 10,
};

/**
 * Generate ZK witness data from a proof term and sequent.
 *
 * @param {Object} term - GenericTerm (from extractTerm or buildGuidedTerm)
 * @param {Object} sequent - The sequent being proved (Store hashes)
 * @param {Object} [opts] - Options
 * @param {Object} [opts.ruleMap] - Override rule name → ZK rule key mapping
 * @returns {{ chips: Object, formula_rom: number[][], gamma_rom: number[][] }}
 */
function generateWitness(term, sequent, opts = {}) {
  let nonceCtr = 0;
  const formulaLookups = new Map(); // hash → { tag, c0, c1, count }
  const gammaEntries = new Map();   // hash → lookup count

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
    const zkTag = ZK_TAGS[tag];
    if (zkTag == null) return;
    const arity = Store.arity(hash);
    const c0 = arity >= 1 ? Store.child(hash, 0) : 0;
    const c1 = arity >= 2 ? Store.child(hash, 1) : 0;
    const existing = formulaLookups.get(hash);
    if (existing) {
      existing.count++;
    } else {
      formulaLookups.set(hash, { tag: zkTag, c0, c1, count: 1 });
    }
  }

  function addGammaLookup(hash) {
    gammaEntries.set(hash, (gammaEntries.get(hash) || 0) + 1);
  }

  // --- Emit InitChip rows ---
  const linear = Seq.getContext(sequent, 'linear');
  const cartesian = Seq.getContext(sequent, 'cartesian');
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

  // Gamma set (cartesian context)
  // Note: cartesian context elements are NOT put on CONTEXT_BUS by init.
  // They are available via GAMMA_BUS (copy rule). For Phase 1f, we track
  // gamma membership separately.
  const gammaSet = new Set(cartesian);

  // --- Walk proof term ---

  /**
   * Recursive DFS walk. Emits chip rows for each proof term node.
   *
   * @param {Object} t - GenericTerm node
   * @param {number} nonceIn - obligation nonce this node consumes
   * @param {number} lax - lax flag (0 or 1)
   * @param {number} goal - succedent hash (obligation type)
   * @param {Map<number,number>} delta - live linear context (hash → count), modified in place
   */
  function walk(t, nonceIn, lax, goal, delta) {
    if (!t || !t.rule) return;
    const rule = resolveRule(t);

    switch (rule) {
      case 'id': {
        // IdentityChip: [active, hash, nonce_in, lax]
        chipRows('id').push([1, t.principal, nonceIn, lax]);
        deltaRemove(delta, t.principal);
        break;
      }

      // --- Right rules (consume obligation, produce child obligations) ---

      case 'tensor_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;
        chipRows('tensor_r').push([1, hash, c0, c1, nonceIn, lax, n0, n1]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c0, delta);
        walk(t.subterms[1], n1, lax, c1, delta);
        break;
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
        walk(t.subterms[0], n0, lax, c0, delta0);
        walk(t.subterms[1], n1, lax, c1, delta1);
        break;
      }

      case 'loli_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0); // antecedent A
        const c1 = Store.child(hash, 1); // consequent B
        const n0 = ++nonceCtr;
        chipRows('loli_r').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        deltaAdd(delta, c0); // loli_r introduces A into context
        walk(t.subterms[0], n0, lax, c1, delta);
        break;
      }

      case 'oplus_r1': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        chipRows('oplus_r1').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c0, delta); // prove child0
        break;
      }

      case 'oplus_r2': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        const n0 = ++nonceCtr;
        chipRows('oplus_r2').push([1, hash, c0, c1, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c1, delta); // prove child1
        break;
      }

      case 'one_r': {
        chipRows('one_r').push([1, goal, nonceIn, lax]);
        addFormulaLookup(goal);
        break;
      }

      case 'bang_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('bang_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c0, delta);
        break;
      }

      case 'monad_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('monad_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        // monad_r forces lax=1 for inner proof
        const inner = t.evidence || t.subterms[0];
        walk(inner, n0, 1, c0, delta);
        break;
      }

      case 'exists_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('exists_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c0, delta);
        break;
      }

      case 'forall_r': {
        const hash = goal;
        const c0 = Store.child(hash, 0);
        const n0 = ++nonceCtr;
        chipRows('forall_r').push([1, hash, c0, nonceIn, lax, n0]);
        addFormulaLookup(hash);
        walk(t.subterms[0], n0, lax, c0, delta);
        break;
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
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'with_l1': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        chipRows('with_l1').push([1, hash, c0, c1]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0); // send child0
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'with_l2': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        const c1 = Store.child(hash, 1);
        chipRows('with_l2').push([1, hash, c0, c1]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c1); // send child1
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'one_l': {
        const hash = t.principal;
        chipRows('one_l').push([1, hash]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'dereliction': {
        // bang_l (dereliction): !A → A in linear
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('bang_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'absorption': {
        // bang_l (absorption): !A → A to gamma zone
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('absorption').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        gammaSet.add(c0);
        // absorption doesn't send to context — child goes to gamma externally
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'monad_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('monad_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'exists_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('exists_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'forall_l': {
        const hash = t.principal;
        const c0 = Store.child(hash, 0);
        chipRows('forall_l').push([1, hash, c0]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);
        deltaAdd(delta, c0);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      case 'copy': {
        const hash = t.principal;
        chipRows('copy').push([1, hash]);
        addGammaLookup(hash);
        deltaAdd(delta, hash);
        walk(t.subterms[0], nonceIn, lax, goal, delta);
        break;
      }

      // --- Left-focus rules (consume obligation + context) ---

      case 'loli_l': {
        if (t.subterms.length === 1) {
          // Invertible variant: both A and B added to delta
          // Map to context-only decomposition (no obligation interaction)
          // TODO: needs a LOLI_L_INV RuleSpec for proper ZK support
          throw new Error('loli_l invertible (1-subterm) not yet supported in ZK');
        }
        const hash = t.principal;
        const c0 = Store.child(hash, 0); // A
        const c1 = Store.child(hash, 1); // B
        const n0 = ++nonceCtr;
        const n1 = ++nonceCtr;

        chipRows('loli_l').push([1, hash, c0, c1, nonceIn, lax, n0, n1, goal]);
        addFormulaLookup(hash);
        deltaRemove(delta, hash);

        // Sequential context split: sub0 gets remaining, sub1 gets remaining + B
        walk(t.subterms[0], n0, lax, c0, delta);
        deltaAdd(delta, c1); // B added for premise 1
        walk(t.subterms[1], n1, lax, goal, delta);
        break;
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

        walk(t.subterms[0], n0, lax, goal, delta0);
        walk(t.subterms[1], n1, lax, goal, delta1);
        break;
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
        break;
      }

      default:
        throw new Error(`unsupported rule in ZK witness: ${rule}`);
    }
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

  return { chips, formula_rom, gamma_rom };
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

  // oplus_r disambiguation: the backward prover may use 'oplus_r'
  if (rule === 'oplus_r') {
    // Need to determine if it's r1 or r2 based on which child matches
    // For now, default to oplus_r1
    return 'oplus_r1';
  }

  return rule;
}

module.exports = { generateWitness, ZK_TAGS };
