/**
 * Grade-0 Cut Elimination — compose rules through !_0 intermediate types.
 *
 * Three-layer API:
 *   L1: composePair        — atomic cut elimination (grade-agnostic)
 *   L2: buildPredicateMap   — analysis (producers/consumers/bridges)
 *   L3: composeGrade0       — multi-pass scheduler → ComposeResult
 *
 * All domain-specific knowledge (predicate names, number representation) is
 * injected via configuration objects. See lib/engine/ill/compose-config.js
 * for the ILL-specific defaults.
 *
 * Theory: stratified cut elimination (THY_0015). SELL cut admissibility
 * (Nigam-Miller PPDP 2009) ensures each composePair call preserves
 * derivability. Grade-0 erasure (Atkey 2018, Choudhury et al. POPL 2021)
 * justifies that grade-0 intermediates are compile-time scaffolding.
 */

'use strict';

const Store = require('../kernel/store');
const { unify } = require('../kernel/unify');
const { apply, debruijnSubst } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');
const { flattenAntecedent, unwrapComputation, resolveConnectives, expandConsequentChoices } = require('./compile');
const { getPredicateHead, buildRightTensor } = require('../kernel/ast');
const { collectMetavars, isGround } = require('./pattern-utils');
const { GRADE_0, GRADE_W } = require('./grades');

// ─── Tabling cache ──────────────────────────────────────────────────────────
// In-memory cache for resolveAll results. Survives across composeGrade0 calls
// within the same process (helps when multiple test files load the same program).
// Invalidated on Store.clear() via the onClear hook.

const _tablingCache = new Map();
const _composeCache = new Map();
Store.onClear(() => { _tablingCache.clear(); _composeCache.clear(); });

/** Canonical string key for tabling cache — no collision risk (C22). */
function _tablingCacheKey(clauses, definitions) {
  const cParts = [];
  const dParts = [];
  if (clauses) for (const [, cl] of clauses) cParts.push(cl.hash);
  if (definitions) for (const [, dh] of definitions) dParts.push(dh);
  return cParts.join(',') + '|' + dParts.join(',');
}

/** Canonical string key for full compose cache — no collision risk (C22). */
function _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts, hasResolver) {
  const parts = [_tablingCacheKey(clauses, definitions)];
  const rParts = [];
  for (let i = 0; i < compiledRules.length; i++) rParts.push(compiledRules[i].hash);
  parts.push(rParts.join(','));
  if (extraGrade0Facts) {
    const fParts = [];
    for (const [, facts] of extraGrade0Facts) {
      for (const f of facts) fParts.push(f.hash);
    }
    parts.push(fParts.join(','));
  }
  if (hasResolver) parts.push('R');
  return parts.join(';');
}

// ─── Helpers ────────────────────────────────────────────────────────────────

/**
 * Alpha-rename all metavars in a formula hash.
 * Returns { hash: freshHash, theta: [[oldMV, newMV], ...] }.
 */
function alphaRename(hash) {
  const mvs = new Set();
  collectMetavars(hash, mvs);
  if (mvs.size === 0) return { hash, theta: [] };
  const theta = [];
  for (const mv of mvs) {
    theta.push([mv, freshMetavar()]);
  }
  return { hash: apply(hash, theta), theta };
}

/**
 * Find the first element in arr whose predicate head matches predHead.
 * Returns { index, hash } or null.
 */
function findByPredHead(arr, predHead) {
  for (let i = 0; i < arr.length; i++) {
    if (getPredicateHead(arr[i]) === predHead) {
      return { index: i, hash: arr[i] };
    }
  }
  return null;
}

/**
 * Remove element at index from array, return new array.
 */
function removeAt(arr, idx) {
  const out = new Array(arr.length - 1);
  for (let i = 0, j = 0; i < arr.length; i++) {
    if (i !== idx) out[j++] = arr[i];
  }
  return out;
}

// ─── Rule reassembly ─────────────────────────────────────────────────────────
// Every compose pass (cut elimination, specialization, fusion, SROA) produces
// a new rule from flat antecedent/consequent parts. This helper wraps the
// shared reassembly: bang-wrap persistent/grade-0, tensor-fold, monad-wrap.
//
// Note: the connective shape (bang/tensor/monad/loli) is fixed to SELL-like
// logics. The compose pipeline is generic in predicate names and number
// representations, but assumes this formula structure throughout.

/**
 * Build a loli rule hash from flat antecedent and consequent parts.
 * @param {{ linear: number[], persistent: number[], grade0?: number[] }} ante
 * @param {{ linear: number[], persistent: number[], grade0?: number[] }} conseq
 * @returns {{ hash: number, antecedent: number, consequent: number }}
 */
function _buildRuleHash(ante, conseq) {
  const anteParts = [
    ...ante.linear,
    ...ante.persistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...(ante.grade0 || []).map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const anteHash = buildRightTensor(anteParts);
  const conseqParts = [
    ...conseq.linear,
    ...conseq.persistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...(conseq.grade0 || []).map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const conseqBody = buildRightTensor(conseqParts);
  const conseqHash = Store.put('monad', [conseqBody]);
  const hash = Store.put('loli', [anteHash, conseqHash]);
  return { hash, antecedent: anteHash, consequent: conseqHash };
}

/**
 * Convenience: build a raw rule object from flat parts + metadata.
 * @param {Object} [flags] - optional flags to spread onto the rule (e.g. { isFused: true })
 */
function _makeRule(name, ante, conseq, sourceLabel, flags) {
  const { hash, antecedent, consequent } = _buildRuleHash(ante, conseq);
  const rule = { name, hash, antecedent, consequent, sourceLabel: sourceLabel || null };
  if (flags) Object.assign(rule, flags);
  return rule;
}

// ─── Persistent goal ordering ────────────────────────────────────────────────

/**
 * Topologically sort persistent goals so that inputs are grounded before use.
 *
 * After composePair merges producer + consumer persistent goals, the naive
 * concatenation may violate input→output dependencies. The backward prover
 * resolves goals strictly in order, so we must reorder: goals whose inputs
 * depend on another goal's output come after it.
 *
 * Uses mode metadata (+/- per position) to distinguish inputs from outputs.
 * MultiModal predicates allow at most 1 input position to be ungrounded
 * (it becomes the computed output).
 *
 * @param {number[]} goals - persistent goal hashes (post-theta)
 * @param {number[]} linearPatterns - linear patterns (their metavars are grounded at runtime)
 * @param {Function|null} getModeMeta - (predHead) → { modes: string[], multiModal: boolean } | null
 * @returns {number[]} topologically sorted goals
 */
function sortPersistentGoals(goals, linearPatterns, getModeMeta) {
  if (!getModeMeta || goals.length <= 1) return goals;

  // Metavars grounded by linear pattern matching
  const grounded = new Set();
  for (const pat of linearPatterns) collectMetavars(pat, grounded);

  // Analyze each goal: per-position metavars + mode info
  const infos = goals.map((goal, originalIdx) => {
    const pred = getPredicateHead(goal);
    const meta = pred ? getModeMeta(pred) : null;
    const arity = Store.arity(goal);
    const posMVs = [];
    const allMVs = new Set();
    for (let j = 0; j < arity; j++) {
      const s = new Set();
      collectMetavars(Store.child(goal, j), s);
      posMVs.push(s);
      for (const mv of s) allMVs.add(mv);
    }
    return { goal, originalIdx, meta, arity, posMVs, allMVs };
  });

  // Readiness check: can this goal fire given current grounded set?
  function isReady(info) {
    const { meta, arity, posMVs, allMVs } = info;
    if (!meta || arity !== meta.modes.length) {
      // No mode info — conservative: all metavars must already be grounded
      for (const mv of allMVs) if (!grounded.has(mv)) return false;
      return true;
    }
    let ungroundedInputs = 0;
    for (let j = 0; j < arity; j++) {
      if (meta.modes[j] === '+') {
        for (const mv of posMVs[j]) {
          if (!grounded.has(mv)) { ungroundedInputs++; break; }
        }
      }
    }
    return meta.multiModal ? ungroundedInputs <= 1 : ungroundedInputs === 0;
  }

  // Greedy topological sort
  const scheduled = [];
  const remaining = new Set(infos.map((_, i) => i));
  let progress = true;
  while (progress && remaining.size > 0) {
    progress = false;
    for (const idx of remaining) {
      if (isReady(infos[idx])) {
        scheduled.push(infos[idx].goal);
        remaining.delete(idx);
        for (const mv of infos[idx].allMVs) grounded.add(mv);
        progress = true;
        break; // restart scan — earlier goals may now be ready
      }
    }
  }
  // Append any remaining goals in original order (cycle or unknown modes)
  if (remaining.size > 0) {
    const sorted = [...remaining].sort((a, b) => infos[a].originalIdx - infos[b].originalIdx);
    for (const idx of sorted) scheduled.push(infos[idx].goal);
  }
  return scheduled;
}

// ─── L1: Atomic cut elimination ─────────────────────────────────────────────

/**
 * Compose two rules through a shared cut formula. Grade-agnostic.
 *
 * @param {Object} producer - compiled rule whose consequent grade0[] has cutPredHead
 * @param {Object} consumer - compiled rule whose antecedent grade0[] has cutPredHead
 * @param {string} cutPredHead - predicate head string identifying the cut type
 * @param {Object} rc - resolved connectives (from resolveConnectives)
 * @param {Function|null} getModeMeta - mode metadata for persistent goal sorting
 * @returns {Object|null} raw rule { name, hash, antecedent, consequent, sourceLabel } or null
 */
function composePair(producer, consumer, cutPredHead, rc, getModeMeta) {
  // Step 1: Alpha-rename producer to prevent metavar collision.
  // We rename the full loli hash, then re-derive ante/conseq.
  const { hash: freshProdHash } = alphaRename(producer.hash);
  const freshProdAnte = Store.child(freshProdHash, 0);
  const freshProdConseq = Store.child(freshProdHash, 1);

  // Step 2: Flatten both sides.
  // NOTE: compiled.antecedent is the flattened object, not a hash.
  // We derive raw hashes from compiled.hash (the full loli formula).
  const pAnte = flattenAntecedent(freshProdAnte, rc);
  const pConseqBody = unwrapComputation(freshProdConseq, rc);
  const pConseq = flattenAntecedent(pConseqBody, rc);

  const consumerAnteHash = Store.child(consumer.hash, 0);
  const consumerConseqHash = Store.child(consumer.hash, 1);
  const cAnte = flattenAntecedent(consumerAnteHash, rc);
  const cConseqBody = unwrapComputation(consumerConseqHash, rc);
  const cConseq = flattenAntecedent(cConseqBody, rc);

  // Step 3: Locate cut formula in producer's conseq.grade0 and consumer's ante.grade0.
  const pMatch = findByPredHead(pConseq.grade0, cutPredHead);
  const cMatch = findByPredHead(cAnte.grade0, cutPredHead);
  if (!pMatch || !cMatch) return null;

  // Step 4: Unify the cut formulas.
  const theta = unify(pMatch.hash, cMatch.hash);
  if (theta === null) return null;

  // Step 5: Apply θ and merge, removing the cut formula from each side.
  const pConseqGrade0Rest = removeAt(pConseq.grade0, pMatch.index);
  const cAnteGrade0Rest = removeAt(cAnte.grade0, cMatch.index);

  const applyAll = arr => arr.map(h => apply(h, theta));

  const combinedAnteLinear = applyAll([...pAnte.linear, ...cAnte.linear]);
  const combinedAntePersistent = sortPersistentGoals(
    applyAll([...pAnte.persistent, ...cAnte.persistent]),
    combinedAnteLinear,
    getModeMeta
  );
  const combinedAnteGrade0 = applyAll([...pAnte.grade0, ...cAnteGrade0Rest]);

  const combinedConseqLinear = applyAll([...pConseq.linear, ...cConseq.linear]);
  const combinedConseqPersistent = applyAll([...pConseq.persistent, ...cConseq.persistent]);
  const combinedConseqGrade0 = applyAll([...pConseqGrade0Rest, ...cConseq.grade0]);

  // Step 6: Reassemble and return raw rule.
  return _makeRule(
    `${consumer.name}:${producer.name}`,
    { linear: combinedAnteLinear, persistent: combinedAntePersistent, grade0: combinedAnteGrade0 },
    { linear: combinedConseqLinear, persistent: combinedConseqPersistent, grade0: combinedConseqGrade0 },
    consumer.sourceLabel || producer.sourceLabel
  );
}

/**
 * Specialize a rule by resolving a persistent goal against a ground grade-0 clause.
 * Separate from composePair — different semantics (ground fact × rule, not rule × rule).
 *
 * @param {Object} rule - Rule with .hash (loli formula) and .name
 * @param {number} factHash - Ground clause hash
 * @param {string} factName - Clause name
 * @param {string} predHead - Predicate head to resolve
 * @param {Object} rc - Resolved connectives
 * @param {Function|null} getModeMeta - Mode metadata for persistent goal sorting
 * @returns {Object|null} Raw rule { name, hash, antecedent, consequent, sourceLabel } or null
 */
function specializePersistent(rule, factHash, factName, predHead, rc, getModeMeta) {
  // Step 1: Alpha-rename rule to prevent metavar collision with fact
  const { hash: freshRuleHash } = alphaRename(rule.hash);
  const freshAnteHash = Store.child(freshRuleHash, 0);
  const freshConseqHash = Store.child(freshRuleHash, 1);

  // Step 2: Flatten both sides
  const ante = flattenAntecedent(freshAnteHash, rc);
  const conseqBody = unwrapComputation(freshConseqHash, rc);
  const conseq = flattenAntecedent(conseqBody, rc);

  // Step 3: Find persistent goal matching predHead
  const goalMatch = findByPredHead(ante.persistent, predHead);
  if (!goalMatch) return null;

  // Step 4: Unify goal with ground fact
  const theta = unify(goalMatch.hash, factHash);
  if (theta === null) return null;

  // Step 5: Apply θ, remove the resolved goal
  const applyAll = arr => arr.map(h => apply(h, theta));
  const remainingPersistent = removeAt(ante.persistent, goalMatch.index);

  const combinedAnteLinear = applyAll(ante.linear);
  const combinedAntePersistent = sortPersistentGoals(
    applyAll(remainingPersistent),
    combinedAnteLinear,
    getModeMeta
  );
  const combinedAnteGrade0 = applyAll(ante.grade0);

  const combinedConseqLinear = applyAll(conseq.linear);
  const combinedConseqPersistent = applyAll(conseq.persistent);
  const combinedConseqGrade0 = applyAll(conseq.grade0);

  // Step 6: Reassemble.
  return _makeRule(
    `${rule.name}:${factName}`,
    { linear: combinedAnteLinear, persistent: combinedAntePersistent, grade0: combinedAnteGrade0 },
    { linear: combinedConseqLinear, persistent: combinedConseqPersistent, grade0: combinedConseqGrade0 },
    rule.sourceLabel
  );
}

// ─── L2: Analysis ───────────────────────────────────────────────────────────

/**
 * Extract grade-0 predicate heads from a compiled rule's flattened arrays.
 * @param {Object} compiled - compiled rule with antecedent.grade0[] and consequent.grade0[]
 * @returns {{ produced: string[], consumed: string[] }}
 */
function getGrade0Roles(compiled) {
  const produced = new Set();
  const consumed = new Set();

  const anteG0 = compiled.antecedent.grade0 || [];
  for (const h of anteG0) {
    const pred = getPredicateHead(h);
    if (pred) consumed.add(pred);
  }

  // consequent.grade0 comes from the expanded consequent (effectiveConseq)
  const conseqG0 = compiled.consequent.grade0 || [];
  for (const h of conseqG0) {
    const pred = getPredicateHead(h);
    if (pred) produced.add(pred);
  }

  return { produced: [...produced], consumed: [...consumed] };
}

/**
 * Build grade-0 predicate map from compiled rules.
 *
 * @param {Object[]} compiledRules
 * @returns {Map<string, { producers: Object[], consumers: Object[], bridges: Object[] }>}
 */
function buildPredicateMap(compiledRules) {
  const map = new Map();

  function ensure(pred) {
    if (!map.has(pred)) map.set(pred, { producers: [], consumers: [], bridges: [] });
    return map.get(pred);
  }

  // First pass: classify producers and consumers per predicate.
  for (const r of compiledRules) {
    if (!r.hasGrade0) continue;
    const { produced, consumed } = getGrade0Roles(r);
    for (const p of produced) ensure(p).producers.push(r);
    for (const c of consumed) ensure(c).consumers.push(r);
  }

  // Second pass: detect bridges — rules that consume pred A and produce pred B.
  for (const r of compiledRules) {
    if (!r.hasGrade0) continue;
    const { produced, consumed } = getGrade0Roles(r);
    if (produced.length > 0 && consumed.length > 0) {
      // Rule crosses grade-0 predicates — it's a bridge for all involved preds
      const allPreds = new Set([...produced, ...consumed]);
      for (const p of allPreds) ensure(p).bridges.push(r);
    }
  }

  return map;
}

// ─── Fact indexing ──────────────────────────────────────────────────────────
// For predicates with many grade-0 facts, O(N) brute-force specializePersistent
// calls per rule dominate compile time. Index facts by argument values for O(1)
// lookup. Threshold: 8+ facts before indexing (below that, linear scan is faster).

/**
 * Build per-position argument indexes for a set of grade-0 facts.
 * @param {Array} facts - [{name, hash}]
 * @returns {Array|null} posIndexes[pos] = Map<argHash, [fact]> or null if not selective
 */
function _buildFactArgIndexes(facts) {
  if (facts.length < 8) return null;

  const arity = Store.arity(facts[0].hash);
  if (arity === 0) return null;

  const indexes = [];
  let anySelective = false;
  for (let pos = 0; pos < arity; pos++) {
    const idx = new Map();
    for (const f of facts) {
      const key = Store.child(f.hash, pos);
      if (!idx.has(key)) idx.set(key, []);
      idx.get(key).push(f);
    }
    if (idx.size > 1) {
      indexes.push(idx);
      anySelective = true;
    } else {
      indexes.push(null);
    }
  }

  return anySelective ? indexes : null;
}

/**
 * Look up matching facts using the argument index.
 * Finds the most selective indexed position where the goal has a ground arg.
 * @param {Array} posIndexes - from _buildFactArgIndexes
 * @param {number} goalHash - persistent goal hash
 * @returns {Array|null} matching facts, or null to fall back to brute force
 */
function _indexedFactLookup(posIndexes, goalHash) {
  const goalArity = Store.arity(goalHash);
  let best = null;

  for (let pos = 0; pos < goalArity && pos < posIndexes.length; pos++) {
    const idx = posIndexes[pos];
    if (!idx) continue;

    const goalArg = Store.child(goalHash, pos);
    if (typeof goalArg !== 'number' || Store.tag(goalArg) === 'metavar') continue;

    const hits = idx.get(goalArg);
    if (!hits) return []; // Ground arg with no matching fact → empty result
    if (!best || hits.length < best.length) best = hits;
  }

  return best;
}

// ─── Additive chain fusion ───────────────────────────────────────────────────
// When persistent goals form threading chains (output of one feeds input of
// the next), the chain can be collapsed into a single goal with an accumulated
// constant. This is algebraic simplification / strength reduction.
//
// Example (with ILL predicates, but the algorithm is calculus-agnostic):
//   step(X,Y) * step(Y,Z) → fused(X, 2, Z)    (unary step)
//   sub(G,3,G2) * sub(G2,5,G3) → sub(G,8,G3)  (binary accumulate)
//
// Safety: intermediate metavars must not appear elsewhere in the rule.

/**
 * Chain fusion configuration descriptor.
 *
 * Two patterns:
 * - Unary step: pred(input, output). Chain of N → fusedPred(input, N, output).
 * - Binary accumulate: pred(input, constant, output).
 *   Chain → fusedPred(input, sum_of_constants, output).
 *
 * @typedef {Object} ChainConfig
 * @property {string} pred - predicate name to detect
 * @property {number} inputArg - arg index for the threading input
 * @property {number} outputArg - arg index for the threading output
 * @property {number|null} constantArg - arg index for the additive constant (null for unary step)
 * @property {string} fusedPred - predicate name for the fused result
 * @property {number} fusedInputArg - arg index for input in fused predicate
 * @property {number} fusedConstantArg - arg index for accumulated constant in fused predicate
 * @property {number} fusedOutputArg - arg index for output in fused predicate
 * @property {Function} parseConstant - (hash) → bigint|null; decode a constant from Store hash
 * @property {Function} buildConstant - (bigint) → hash; encode a constant as Store hash
 */

/**
 * Fuse additive threading chains in persistent goals.
 *
 * Handles any predicate family where
 * output of one goal feeds into input of the next, with an additive constant that
 * can be summed across the chain.
 *
 * @param {Object[]} pool - raw rules
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @param {ChainConfig[]} chainConfigs - chain descriptors (must be provided by caller)
 * @returns {Object[]} transformed pool
 */
function _fuseAdditiveChains(pool, rc, getModeMeta, chainConfigs) {
  if (!chainConfigs || chainConfigs.length === 0) return pool;
  const configs = chainConfigs;

  const result = [];
  for (const rule of pool) {
    const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
    const conseqBody = unwrapComputation(Store.child(rule.hash, 1), rc);
    const conseq = flattenAntecedent(conseqBody, rc);

    // Collect goals matching any chain config
    // Each goal: { index, hash, input, output, constant (bigint|null), config }
    const chainableGoals = [];
    for (let i = 0; i < ante.persistent.length; i++) {
      const h = ante.persistent[i];
      const pred = getPredicateHead(h);
      for (const cfg of configs) {
        if (pred === cfg.pred && Store.arity(h) === (cfg.constantArg !== null ? 3 : 2)) {
          let constant = null;
          if (cfg.constantArg !== null) {
            const cval = Store.child(h, cfg.constantArg);
            constant = cfg.parseConstant(cval);
            if (constant === null) break; // non-ground constant, skip
          }
          chainableGoals.push({
            index: i, hash: h,
            input: Store.child(h, cfg.inputArg),
            output: Store.child(h, cfg.outputArg),
            constant, // null for unary (implicit step=1), bigint for binary
            config: cfg,
          });
          break; // matched a config, don't try others
        }
      }
    }

    if (chainableGoals.length < 2) {
      result.push(rule);
      continue;
    }

    // Group by config (pred family) — chains only form within the same family
    const byFamily = new Map(); // config → [goal, ...]
    for (const g of chainableGoals) {
      const key = g.config.pred;
      if (!byFamily.has(key)) byFamily.set(key, []);
      byFamily.get(key).push(g);
    }

    const allChains = []; // { chain: [goal,...], config }
    const inChain = new Set(); // goal indices in any chain

    for (const [, familyGoals] of byFamily) {
      if (familyGoals.length < 2) continue;

      // Build maps for this family
      const byOutput = new Map();
      for (const g of familyGoals) {
        if (Store.tag(g.output) === 'metavar') byOutput.set(g.output, g);
      }
      const byInput = new Map();
      for (const g of familyGoals) byInput.set(g.input, g);

      // Find chain heads: goals whose input is not another goal's output
      const heads = familyGoals.filter(g => !byOutput.has(g.input));

      for (const head of heads) {
        const chain = [head];
        let current = head;
        while (true) {
          const next = byInput.get(current.output);
          if (!next || next === head) break;
          chain.push(next);
          current = next;
        }
        if (chain.length >= 2) {
          allChains.push({ chain, config: head.config });
          for (const g of chain) inChain.add(g.index);
        }
      }
    }

    if (allChains.length === 0) {
      result.push(rule);
      continue;
    }

    // Safety: intermediate vars must not appear elsewhere
    const otherMvs = new Set();
    for (const h of ante.linear) collectMetavars(h, otherMvs);
    for (const h of conseq.linear) collectMetavars(h, otherMvs);
    for (const h of conseq.persistent) collectMetavars(h, otherMvs);
    for (let i = 0; i < ante.persistent.length; i++) {
      if (!inChain.has(i)) collectMetavars(ante.persistent[i], otherMvs);
    }

    const safeChains = [];
    for (const { chain, config } of allChains) {
      let safe = true;
      for (let i = 0; i < chain.length - 1; i++) {
        if (otherMvs.has(chain[i].output)) { safe = false; break; }
      }
      if (safe) {
        safeChains.push({ chain, config });
      } else {
        for (const g of chain) inChain.delete(g.index);
      }
    }

    if (safeChains.length === 0) {
      result.push(rule);
      continue;
    }

    // Build replacement persistent goals
    const newPersistent = [];
    for (let i = 0; i < ante.persistent.length; i++) {
      if (!inChain.has(i)) newPersistent.push(ante.persistent[i]);
    }

    const fusedLabels = [];
    for (const { chain, config } of safeChains) {
      const input = chain[0].input;
      const output = chain[chain.length - 1].output;

      // Accumulate constant: sum for binary, count for unary
      let total;
      if (config.constantArg !== null) {
        total = chain.reduce((s, g) => s + g.constant, 0n);
      } else {
        total = BigInt(chain.length); // unary step: each link = 1
      }
      const totalHash = config.buildConstant(total);

      // Build fused goal with correct arity
      const cfg = config;
      const args = [];
      const arity = Math.max(cfg.fusedInputArg, cfg.fusedConstantArg, cfg.fusedOutputArg) + 1;
      for (let i = 0; i < arity; i++) {
        if (i === cfg.fusedInputArg) args.push(input);
        else if (i === cfg.fusedConstantArg) args.push(totalHash);
        else if (i === cfg.fusedOutputArg) args.push(output);
      }
      newPersistent.push(Store.put(cfg.fusedPred, args));
      fusedLabels.push(`${config.pred}-fused:${chain.length}`);
    }

    // Reassemble rule hash
    const sortedPersistent = sortPersistentGoals(newPersistent, ante.linear, getModeMeta);
    result.push(_makeRule(
      `${rule.name}[${fusedLabels.join(',')}]`,
      { linear: ante.linear, persistent: sortedPersistent, grade0: ante.grade0 },
      { linear: conseq.linear, persistent: conseq.persistent, grade0: conseq.grade0 },
      rule.sourceLabel
    ));
  }

  return result;
}

// ─── Residual persistent resolution ─────────────────────────────────────────
// After specialization and fusion, rules may still have persistent goals whose
// inputs are all ground. A residualResolver callback computes their outputs at
// compile time, propagating groundness to dependent goals via running theta.

/**
 * Resolve ALL residual persistent goals on a single rule in one pass.
 *
 * Pre-sorts goals topologically (via sortPersistentGoals) so that each goal's
 * inputs are grounded before it's attempted. A running theta composition
 * propagates bindings: resolving goal A may ground the input of goal B.
 *
 * No alpha-rename needed: resolver returns fully ground facts, so no metavar
 * collision with the rule's own metavars is possible.
 *
 * @param {Object} rule - raw rule {name, hash, ...}
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta - mode metadata for persistent goal sorting
 * @param {Function} resolver - (goalHash) → factHash | null
 * @returns {Object} updated rule (same object if nothing resolved)
 */
function _resolveResidualOnce(rule, rc, getModeMeta, resolver) {
  const anteHash = Store.child(rule.hash, 0);
  const conseqHash = Store.child(rule.hash, 1);
  const ante = flattenAntecedent(anteHash, rc);
  const conseqBody = unwrapComputation(conseqHash, rc);
  const conseq = flattenAntecedent(conseqBody, rc);

  // Sort goals so inputs are grounded before dependent goals are attempted.
  // This ensures the running theta propagates correctly through chains like
  // f(GROUND, ?Y) → g(?Y, ?Z) → h(?Z, ?W).
  const sortedGoals = sortPersistentGoals(ante.persistent, ante.linear, getModeMeta);

  // Build index from original positions → sorted goals (for elimination tracking)
  const goalToOrigIdx = new Map();
  for (let i = 0; i < ante.persistent.length; i++) {
    goalToOrigIdx.set(ante.persistent[i], i);
  }

  const resolvedIndices = new Set();
  const resolvedPreds = [];
  let combinedTheta = [];

  for (const goal of sortedGoals) {
    const applied = apply(goal, combinedTheta);
    const factHash = resolver(applied);
    if (factHash === null) continue;

    const theta_i = unify(applied, factHash);
    if (theta_i === null) continue;

    // Compose theta_i into combinedTheta (idempotent substitution composition)
    for (let j = 0; j < combinedTheta.length; j++) {
      combinedTheta[j][1] = apply(combinedTheta[j][1], theta_i);
    }
    for (const [mv, val] of theta_i) {
      if (!combinedTheta.find(([m]) => m === mv)) combinedTheta.push([mv, val]);
    }
    const origIdx = goalToOrigIdx.get(goal);
    if (origIdx !== undefined) resolvedIndices.add(origIdx);
    resolvedPreds.push(getPredicateHead(goal) || 'unknown');
  }

  if (resolvedIndices.size === 0) return rule;

  // Apply combined theta and reassemble — ONCE
  const applyAll = arr => arr.map(h => apply(h, combinedTheta));

  const resolvedSuffix = resolvedPreds.length > 0
    ? ':resolved:' + resolvedPreds.join(':resolved:')
    : '';

  return _makeRule(
    rule.name + resolvedSuffix,
    {
      linear: applyAll(ante.linear),
      persistent: sortPersistentGoals(
        ante.persistent
          .filter((_, i) => !resolvedIndices.has(i))
          .map(h => apply(h, combinedTheta)),
        applyAll(ante.linear),
        getModeMeta
      ),
      grade0: applyAll(ante.grade0),
    },
    {
      linear: applyAll(conseq.linear),
      persistent: applyAll(conseq.persistent),
      grade0: applyAll(conseq.grade0),
    },
    rule.sourceLabel
  );
}

/**
 * Batch resolve residual persistent goals across a pool of rules.
 * Single pass per rule: flatten once, resolve all goals, apply once, reassemble once.
 */
function _resolveResidualBatch(pool, rc, getModeMeta, resolver) {
  return pool.map(rule => _resolveResidualOnce(rule, rc, getModeMeta, resolver));
}

// ─── Basic block fusion ─────────────────────────────────────────────────────
// When a rule produces a ground linear resource and exactly one other rule
// consumes it, the two can be fused (linear cut elimination). This is the
// forward-chaining analog of basic block merging in compiler CFG optimization.
// The threading predicate (e.g. a program counter) is the cut formula.

/**
 * Fuse two rules through a shared ground linear resource.
 *
 * Producer's consequent contains cutPred(V) in linear.
 * Consumer's antecedent contains cutPred(V) in linear.
 * We unify all of producer's consequent with consumer's antecedent
 * (predicate-by-predicate for unique predicates), then merge the remainder.
 *
 * @param {Object} producer - raw rule whose consequent linear has cutPred(V)
 * @param {Object} consumer - raw rule whose antecedent linear has cutPred(V)
 * @param {string} cutPred - predicate name for the threading resource
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta - mode metadata for persistent goal sorting
 * @returns {Object|null} fused raw rule, or null on failure
 */

/**
 * Open exists binders in a formula, keeping oplus/with as opaque linear elements.
 * Unlike expandConsequentChoices (which expands oplus into alternatives), this
 * only opens exists (via debruijnSubst) so the formula stays as a single path
 * with oplus preserved for runtime resolution.
 */
function _openExists(h, rc) {
  const tag = Store.tag(h);
  if (!tag) return { linear: [h], persistent: [], grade0: [] };
  if (tag === rc.existential) {
    const body = Store.child(h, 0);
    const opened = debruijnSubst(body, 0n, freshMetavar());
    return _openExists(opened, rc);
  }
  if (tag === rc.product) {
    const l = _openExists(Store.child(h, 0), rc);
    const r = _openExists(Store.child(h, 1), rc);
    return {
      linear: [...l.linear, ...r.linear],
      persistent: [...l.persistent, ...r.persistent],
      grade0: [...l.grade0, ...r.grade0]
    };
  }
  if (tag === rc.exponential) {
    const grade = Store.child(h, 0);
    const inner = Store.child(h, 1);
    if (grade === GRADE_0) return { linear: [], persistent: [], grade0: [inner] };
    return { linear: [], persistent: [inner], grade0: [] };
  }
  // oplus/with and everything else: keep as opaque linear element
  return { linear: [h], persistent: [], grade0: [] };
}

/**
 * Open all exists binders in a flattened consequent (from flattenAntecedent).
 * Processes each linear element through _openExists.
 */
function _openConseqExists(conseq, rc) {
  const result = { linear: [], persistent: [...(conseq.persistent || [])], grade0: [...(conseq.grade0 || [])] };
  for (const h of conseq.linear) {
    const opened = _openExists(h, rc);
    result.linear.push(...opened.linear);
    result.persistent.push(...opened.persistent);
    result.grade0.push(...opened.grade0);
  }
  return result;
}

function fuseLinearPair(producer, consumer, cutPred, rc, getModeMeta) {
  // Step 1: Alpha-rename producer
  const { hash: freshProdHash } = alphaRename(producer.hash);
  const freshProdAnte = Store.child(freshProdHash, 0);
  const freshProdConseq = Store.child(freshProdHash, 1);

  // Step 2: Flatten both sides
  const pAnte = flattenAntecedent(freshProdAnte, rc);
  const pConseqBody = unwrapComputation(freshProdConseq, rc);
  const pConseq = flattenAntecedent(pConseqBody, rc);

  const cAnteHash = Store.child(consumer.hash, 0);
  const cConseqHash = Store.child(consumer.hash, 1);
  const cAnte = flattenAntecedent(cAnteHash, rc);
  const cConseqBody = unwrapComputation(cConseqHash, rc);
  const cConseq = flattenAntecedent(cConseqBody, rc);

  // Step 2.5: Open exists in consequents (preserve oplus/with as opaque).
  // flattenAntecedent treats exists as opaque, hiding pc/gas/stack inside.
  // _openConseqExists opens exists binders via debruijnSubst (replacing bound(0)
  // with fresh metavars) while keeping oplus/with intact for runtime resolution.
  // After fusion, compileRule detects existential slots automatically.
  const pConseqFlat = _openConseqExists(pConseq, rc);
  const cConseqFlat = _openConseqExists(cConseq, rc);

  // Step 3: Find and remove the cut predicate from both sides
  const pCutIdx = pConseqFlat.linear.findIndex(h => getPredicateHead(h) === cutPred);
  const cCutIdx = cAnte.linear.findIndex(h => getPredicateHead(h) === cutPred);
  if (pCutIdx < 0 || cCutIdx < 0) return null;

  // Unify the cut formulas
  let theta = unify(pConseqFlat.linear[pCutIdx], cAnte.linear[cCutIdx]);
  if (theta === null) return null;

  const pConseqLinear = removeAt(pConseqFlat.linear, pCutIdx);
  const cAnteLinear = removeAt(cAnte.linear, cCutIdx);

  // Step 4: Match producer consequent linear → consumer antecedent linear (by predicate head)
  // Only match predicates that appear exactly once on each side (unambiguous)
  const pPredCount = {}, cPredCount = {};
  for (const h of pConseqLinear) {
    const p = getPredicateHead(h);
    if (p) pPredCount[p] = (pPredCount[p] || 0) + 1;
  }
  for (const h of cAnteLinear) {
    const p = getPredicateHead(h);
    if (p) cPredCount[p] = (cPredCount[p] || 0) + 1;
  }

  const pUnmatched = [];
  const cMatched = new Set();

  for (let i = 0; i < pConseqLinear.length; i++) {
    const pPred = getPredicateHead(pConseqLinear[i]);
    if (!pPred || pPredCount[pPred] !== 1 || cPredCount[pPred] !== 1) {
      pUnmatched.push(pConseqLinear[i]);
      continue;
    }

    // Find matching consumer antecedent formula
    const cIdx = cAnteLinear.findIndex((h, j) => !cMatched.has(j) && getPredicateHead(h) === pPred);
    if (cIdx < 0) {
      pUnmatched.push(pConseqLinear[i]);
      continue;
    }

    // Unify the pair, extending theta
    const pApplied = apply(pConseqLinear[i], theta);
    const cApplied = apply(cAnteLinear[cIdx], theta);
    const theta2 = unify(pApplied, cApplied);
    if (theta2 === null) {
      // Can't unify — skip fusion for this pair
      return null;
    }
    theta = [...theta, ...theta2];
    cMatched.add(cIdx);
  }

  const cUnmatched = cAnteLinear.filter((_, i) => !cMatched.has(i));

  // Step 5: Assemble fused rule
  const applyAll = arr => arr.map(h => apply(h, theta));

  const fusedAnteLinear = applyAll([...pAnte.linear, ...cUnmatched]);
  const fusedAntePersistent = sortPersistentGoals(
    applyAll([...pAnte.persistent, ...cAnte.persistent]),
    fusedAnteLinear,
    getModeMeta
  );
  const fusedAnteGrade0 = applyAll([...pAnte.grade0, ...cAnte.grade0]);

  const fusedConseqLinear = applyAll([...pUnmatched, ...cConseqFlat.linear]);
  const fusedConseqPersistent = applyAll([...pConseqFlat.persistent, ...cConseqFlat.persistent]);
  const fusedConseqGrade0 = applyAll([...pConseqFlat.grade0, ...cConseqFlat.grade0]);

  // Step 6: Reassemble. Mark as fused so downstream passes (SROA) can identify it.
  return _makeRule(
    `${producer.name}+${consumer.name}`,
    { linear: fusedAnteLinear, persistent: fusedAntePersistent, grade0: fusedAnteGrade0 },
    { linear: fusedConseqLinear, persistent: fusedConseqPersistent, grade0: fusedConseqGrade0 },
    producer.sourceLabel || consumer.sourceLabel,
    { isFused: true }
  );
}

/**
 * Fuse a producer with a consumer, expanding oplus in the producer's consequent.
 *
 * When the producer has oplus (internal/external choice) in its consequent,
 * each branch is projected into a separate rule and fused independently.
 * Returns an array of successfully fused rules (one per oplus branch that fuses).
 *
 * @param {Object} producer - producer rule
 * @param {Object} consumer - consumer rule
 * @param {string} cutPred - the threading predicate
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @returns {Object[]|null} array of fused rules, or null if none fuse
 */
function fuseLinearPairExpanded(producer, consumer, cutPred, rc, getModeMeta) {
  // Check if producer has oplus in consequent
  const prodConseqBody = unwrapComputation(Store.child(producer.hash, 1), rc);
  const prodConseq = flattenAntecedent(prodConseqBody, rc);

  let hasChoice = false;
  for (const h of prodConseq.linear) {
    const tag = Store.tag(h);
    if (tag === rc.internalChoice || tag === rc.externalChoice) {
      hasChoice = true;
      break;
    }
  }

  if (!hasChoice) {
    // No oplus — delegate to fuseLinearPair directly
    const fused = fuseLinearPair(producer, consumer, cutPred, rc, getModeMeta);
    return fused ? [fused] : null;
  }

  // Expand oplus into alternatives
  const alts = expandConsequentChoices(prodConseq, rc);
  if (alts.length <= 1) {
    const fused = fuseLinearPair(producer, consumer, cutPred, rc, getModeMeta);
    return fused ? [fused] : null;
  }

  // Create projected rules (one per alternative) and fuse each.
  // Persistent goals from oplus branches are GUARDS (must be proved before firing),
  // so they go into the projected rule's ANTECEDENT, not CONSEQUENT.
  // This ensures dead branches (contradictory guards like !eq 1 0) never fire.
  const ante = flattenAntecedent(Store.child(producer.hash, 0), rc);
  const results = [];
  for (let ai = 0; ai < alts.length; ai++) {
    const alt = alts[ai];
    const projectedAnte = {
      linear: ante.linear,
      persistent: [...ante.persistent, ...(alt.persistent || [])],
      grade0: [...(ante.grade0 || []), ...(alt.grade0 || [])]
    };
    const projectedConseq = {
      linear: alt.linear,
      persistent: [],
      grade0: []
    };
    const projected = _makeRule(
      `${producer.name}:alt${ai}`,
      projectedAnte,
      projectedConseq,
      producer.sourceLabel,
      producer.isFused ? { isFused: true } : undefined
    );
    const fused = fuseLinearPair(projected, consumer, cutPred, rc, getModeMeta);
    if (fused) results.push(fused);
  }
  return results.length > 0 ? results : null;
}

/**
 * Fuse basic blocks in a pool of rules.
 * Finds 1:1 cutPred(GROUND) producer→consumer pairs and chains them.
 * Supports oplus producers via per-branch projection (fuseLinearPairExpanded).
 *
 * @param {Array} pool - raw rules
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @param {string} linearFusionPredicate - the threading predicate to fuse on (required)
 * @returns {{ rules: Array, fusedCount: number, chainLengths: number[] }}
 */
function _fuseBasicBlocks(pool, rc, getModeMeta, linearFusionPredicate, fusionBarriers) {
  const cutPred = linearFusionPredicate;
  const producers = {}; // value → [ruleIdx]
  const consumers = {}; // value → [ruleIdx]
  const hiddenProducers = new Set(); // values produced inside oplus/with/exists

  /**
   * Recursively collect ground values of the fusion predicate from inside
   * oplus/with/exists nodes. These are "invisible producers" — values that
   * flattenAntecedent can't see. Consumers must NOT be fused away.
   */
  function _collectInvisibleCut(h) {
    const tag = Store.tag(h);
    if (!tag) return;
    if (tag === rc.internalChoice || tag === rc.externalChoice) {
      _collectInvisibleCut(Store.child(h, 0));
      _collectInvisibleCut(Store.child(h, 1));
    } else if (tag === rc.product) {
      _collectInvisibleCut(Store.child(h, 0));
      _collectInvisibleCut(Store.child(h, 1));
    } else if (tag === rc.exponential) {
      _collectInvisibleCut(Store.child(h, 1));
    } else if (tag === rc.existential) {
      _collectInvisibleCut(Store.child(h, 0));
    } else {
      const pred = getPredicateHead(h);
      if (pred === cutPred && Store.arity(h) === 1) {
        const child = Store.child(h, 0);
        if (typeof child === 'number' && isGround(child)) {
          hiddenProducers.add(child);
        }
      }
    }
  }

  // Build producer/consumer maps
  for (let ri = 0; ri < pool.length; ri++) {
    const rule = pool[ri];
    const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
    const conseqBody = unwrapComputation(Store.child(rule.hash, 1), rc);
    const conseq = flattenAntecedent(conseqBody, rc);

    // Consumer: cutPred(GROUND) in antecedent linear
    for (const h of ante.linear) {
      const pred = getPredicateHead(h);
      if (pred === cutPred && Store.arity(h) === 1) {
        const child = Store.child(h, 0);
        if (typeof child === 'number' && isGround(child)) {
          if (!consumers[child]) consumers[child] = [];
          consumers[child].push(ri);
        }
      }
    }

    // Scan for hidden producers inside oplus/with (NOT exists — existentials are
    // deterministic, they just introduce a fresh variable, not a choice point)
    for (const h of conseq.linear) {
      const tag = Store.tag(h);
      if (tag === rc.internalChoice || tag === rc.externalChoice) {
        _collectInvisibleCut(h);
      }
    }

    // Producer: cutPred(GROUND) in consequent linear — at top level or inside exists.
    // Oplus rules ARE allowed as producers: fuseLinearPairExpanded projects each oplus
    // branch into a separate fused rule, so resources inside branches get properly matched.
    // Skip oplus/with nodes themselves; only scan top-level and exists-wrapped items.
    for (const h of conseq.linear) {
      const tag = Store.tag(h);
      // Skip oplus/with nodes — their cutPred values are tracked via _collectInvisibleCut
      if (tag === rc.internalChoice || tag === rc.externalChoice) continue;
      // Walk through exists wrappers
      let candidate = h;
      while (Store.tag(candidate) === rc.existential) {
        candidate = Store.child(candidate, 0);
      }
      // Walk tensor tree for cutPred(GROUND)
      const toCheck = [candidate];
      while (toCheck.length > 0) {
        const cur = toCheck.pop();
        const curTag = Store.tag(cur);
        if (curTag === rc.product) {
          toCheck.push(Store.child(cur, 0));
          toCheck.push(Store.child(cur, 1));
          continue;
        }
        const pred = getPredicateHead(cur);
        if (pred === cutPred && Store.arity(cur) === 1) {
          const child = Store.child(cur, 0);
          if (typeof child === 'number' && isGround(child)) {
            if (!producers[child]) producers[child] = [];
            producers[child].push(ri);
          }
        }
      }
    }
  }

  // Find 1:1 fuseable pairs: cut value with exactly 1 producer and 1 consumer.
  // Exclude values with hidden producers (inside oplus/with/exists) — the consumer
  // rule is still needed at runtime for those hidden paths.
  // Also exclude fusion barriers: pc values that are dynamic jump targets (JUMPDESTs).
  // These have runtime producers (JUMP/JUMPI) invisible to static analysis.
  const fuseableEdges = []; // { cutVal, producerIdx, consumerIdx }
  const allCutVals = new Set([...Object.keys(producers), ...Object.keys(consumers)]);
  for (const cv of allCutVals) {
    if (hiddenProducers.has(Number(cv))) continue; // hidden producer from oplus/choice
    if (fusionBarriers && fusionBarriers.has(Number(cv))) continue; // dynamic jump target
    const p = producers[cv] || [];
    const c = consumers[cv] || [];
    if (p.length === 1 && c.length === 1 && p[0] !== c[0]) {
      fuseableEdges.push({ cutVal: cv, producerIdx: p[0], consumerIdx: c[0] });
    }
  }

  if (fuseableEdges.length === 0) {
    return { rules: pool, fusedCount: 0, chainLengths: [] };
  }

  // Build chains: follow producer→consumer edges
  const producerToEdge = {};
  for (const e of fuseableEdges) producerToEdge[e.producerIdx] = e;
  const consumerToEdge = {};
  for (const e of fuseableEdges) consumerToEdge[e.consumerIdx] = e;

  const visited = new Set();
  const chains = []; // each chain: [ruleIdx1, ruleIdx2, ...]

  for (const edge of fuseableEdges) {
    // Start from chain head: a producer not involved as consumer in any fuseable edge
    if (visited.has(edge.producerIdx)) continue;
    if (consumerToEdge[edge.producerIdx]) continue; // not a chain head

    // Walk forward
    const chain = [edge.producerIdx];
    let currentIdx = edge.producerIdx;
    visited.add(currentIdx);

    while (producerToEdge[currentIdx]) {
      const nextEdge = producerToEdge[currentIdx];
      const nextIdx = nextEdge.consumerIdx;
      if (visited.has(nextIdx)) break;
      chain.push(nextIdx);
      visited.add(nextIdx);
      currentIdx = nextIdx;
    }

    if (chain.length >= 2) chains.push(chain);
  }

  // Fuse each chain (capped at MAX_FUSE_CHAIN to stay within match engine's 64-slot limit)
  const MAX_FUSE_CHAIN = 20; // ~2 metavars per opcode → 40 metavars, comfortably under 64
  const fusedRules = new Set(); // indices of rules that were fused away
  const newRules = [];
  const chainLengths = [];

  for (const chain of chains) {
    // Fuse chain, tracking multiple branches from oplus expansion.
    // `branches` is an array of {rule, fusedUpTo} — starts with one branch,
    // may multiply at oplus producers (fuseLinearPairExpanded returns >1 rule).
    let branches = [{ rule: pool[chain[0]], fusedUpTo: 0 }];
    const limit = Math.min(chain.length, MAX_FUSE_CHAIN);
    for (let i = 1; i < limit; i++) {
      const next = pool[chain[i]];
      const nextBranches = [];
      for (const branch of branches) {
        const fused = fuseLinearPairExpanded(branch.rule, next, cutPred, rc, getModeMeta);
        if (fused) {
          for (const f of fused) nextBranches.push({ rule: f, fusedUpTo: i });
        }
        // If fusion fails for this branch, keep the branch at its current fusedUpTo
        // (it won't extend further but its partial chain is still valid)
      }
      if (nextBranches.length === 0) break; // no branch could extend
      branches = nextBranches;
    }

    // Collect successfully fused results (fusedUpTo >= 1)
    let maxFusedUpTo = 0;
    for (const branch of branches) {
      if (branch.fusedUpTo >= 1) {
        newRules.push(branch.rule);
        if (branch.fusedUpTo > maxFusedUpTo) maxFusedUpTo = branch.fusedUpTo;
      }
    }
    if (maxFusedUpTo >= 1) {
      // Mark rules up to maxFusedUpTo as consumed (all branches cover these)
      for (let i = 0; i <= maxFusedUpTo; i++) fusedRules.add(chain[i]);
      chainLengths.push(maxFusedUpTo + 1);
    }
  }

  // Build result: keep unfused rules + add fused mega-rules
  const result = [];
  for (let i = 0; i < pool.length; i++) {
    if (!fusedRules.has(i)) result.push(pool[i]);
  }
  result.push(...newRules);

  return { rules: result, fusedCount: fusedRules.size - newRules.length, chainLengths };
}

// ─── Pass 6: SROA — scalar replacement of aggregates ─────────────────────────

/**
 * SROA (Scalar Replacement of Aggregates) for array-backed resources.
 *
 * Only applies to rules with `isFused: true` (produced by fuseLinearPair).
 * When such a rule has persistent array-access goals with ground indices on
 * an array held by a linear resource, SROA expands the array pattern into
 * individual slots and eliminates the goals.
 *
 * Example: resource([X | REST]) * !get(REST, 0, Y) * !set(REST, 0, X, REST')
 *   becomes: resource([X, S0 | TAIL]) with Y=S0, REST'=[X | TAIL]
 *
 * Preceded by McCarthy normalization (read-head, write-head axioms) which
 * resolves goals on concrete acons patterns before SROA handles the metavar case.
 *
 * @param {Object[]} pool - raw rules
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @param {Object} sroaConfig - { arrayPreds, resourcePred, parseIndex, buildIndex }
 * @returns {{ rules: Object[], sroaCount: number, mccarthyCount: number }}
 */
function _sroaStackDecomposition(pool, rc, getModeMeta, sroaConfig) {
  if (!sroaConfig) return { rules: pool, sroaCount: 0, mccarthyCount: 0 };
  const cfg = sroaConfig;
  const result = [];
  let sroaCount = 0;
  let mccarthyCount = 0;

  for (const rule of pool) {
    if (!rule.isFused) {
      result.push(rule);
      continue;
    }

    // Phase A: McCarthy normalization — peel acons layers from array-access goals.
    // get([H|T], 0, V) → V=H (direct), get([H|T], N, V) → get(T, N-1, V) (reduced).
    const normalized = _mccarthyNormalize(rule, rc, cfg);
    const effective = normalized || rule;
    if (normalized) mccarthyCount++;

    // Phase B: SROA — expand cons pattern for remaining metavar array goals.
    const transformed = _trySROA(effective, rc, cfg);
    if (transformed) {
      result.push(transformed);
      sroaCount++;
      continue;
    }
    result.push(effective);
  }

  return { rules: result, sroaCount, mccarthyCount };
}

// ─── McCarthy array axiom normalization ──────────────────────────────────────
//
// When array-access goals have an acons (cons cell) as their array argument,
// list-based rewrite rules derived from McCarthy's select/store axioms reduce
// them. McCarthy (1962) and Stump et al. (2001) state the axioms over flat
// arrays: select(store(a,i,v),i)=v, select(store(a,i,v),j)=select(a,j).
// Our acons(H,T) head-tail encoding is semantically equivalent for ground
// non-negative indices, forming a convergent conditional rewrite system:
//   get([H|T], 0, V)  →  V = H                    (read-head)
//   get([H|T], N, V)  →  get(T, N-1, V)           (read-tail, N>0)
//   set([H|T], 0, W, R)  →  R = [W|T]             (write-head)
//   set([H|T], N, W, R)  →  set(T, N-1, W, I), R = [H|I]  (write-tail)
//
// Termination: structural recursion on acons depth. Confluence: ground indices
// mean at most one rule fires per goal (no critical pairs).
// Applied iteratively for deeper acons chains. Goals resolved directly are
// eliminated; goals reduced to metavar base are left for SROA.

/**
 * Peel acons layers from a hash, collecting head elements.
 * @returns {{ base: number, heads: number[], depth: number }}
 */
function _peelAcons(h) {
  const heads = [];
  let cur = h;
  while (Store.tag(cur) === 'acons' && Store.arity(cur) === 2) {
    heads.push(Store.child(cur, 0));
    cur = Store.child(cur, 1);
  }
  return { base: cur, heads, depth: heads.length };
}

/**
 * McCarthy normalization for a single rule.
 * Peels acons layers from array-access goals, resolving or reducing them.
 * Returns transformed rule or null if nothing to normalize.
 */
function _mccarthyNormalize(rule, rc, sroaConfig) {
  const anteHash = Store.child(rule.hash, 0);
  const ante = flattenAntecedent(anteHash, rc);
  const arrGoals = _collectArrGoals(ante.persistent, sroaConfig);

  // Find goals with acons arrVar and ground index
  const aconsGoals = [];
  for (const g of arrGoals) {
    if (Store.tag(g.arrVar) !== 'acons') continue;
    if (!isGround(g.idx) || sroaConfig.parseIndex(g.idx) === null) continue;
    aconsGoals.push(g);
  }
  if (aconsGoals.length === 0) return null;

  const theta = [];
  const eliminatedGoals = new Set();
  const newGoals = []; // replacement goals with reduced index

  for (const g of aconsGoals) {
    const { base, heads, depth } = _peelAcons(g.arrVar);
    const idxNum = Number(sroaConfig.parseIndex(g.idx));

    if (g.type === 'get') {
      if (idxNum < depth) {
        // McCarthy read-head: get([H0..Hk|T], idx, V) with idx < k → V = H[idx]
        theta.push([g.outVar, heads[idxNum]]);
        eliminatedGoals.add(g.hash);
      } else {
        // McCarthy read-tail: reduce index by depth, goal now references base
        const newIdx = sroaConfig.buildIndex(BigInt(idxNum - depth));
        const newGoalHash = Store.put(sroaConfig.arrayPreds[0], [base, newIdx, g.outVar]);
        eliminatedGoals.add(g.hash);
        newGoals.push(newGoalHash);
      }
    } else if (g.type === 'set') {
      if (idxNum < depth) {
        // McCarthy write-head: replace heads[idx], rebuild acons chain
        const newHeads = [...heads];
        newHeads[idxNum] = g.val;
        let rebuilt = base;
        for (let i = newHeads.length - 1; i >= 0; i--) {
          rebuilt = Store.put('acons', [newHeads[i], rebuilt]);
        }
        _decomposePatternIntoTheta(g.outVar, rebuilt, theta);
        eliminatedGoals.add(g.hash);
      } else {
        // McCarthy write-tail: reduce index, wrap output with preserved heads
        const innerOut = freshMetavar();
        const newIdx = sroaConfig.buildIndex(BigInt(idxNum - depth));
        const newGoalHash = Store.put(sroaConfig.arrayPreds[1], [base, newIdx, g.val, innerOut]);
        let rebuilt = innerOut;
        for (let i = heads.length - 1; i >= 0; i--) {
          rebuilt = Store.put('acons', [heads[i], rebuilt]);
        }
        _decomposePatternIntoTheta(g.outVar, rebuilt, theta);
        eliminatedGoals.add(g.hash);
        newGoals.push(newGoalHash);
      }
    }
  }

  if (eliminatedGoals.size === 0) return null;

  // Compose theta: resolve transitive bindings (acyclic → single pass)
  for (let i = 0; i < theta.length; i++) {
    theta[i][1] = apply(theta[i][1], theta);
  }

  // Apply theta to the whole rule
  const thetaApplied = apply(rule.hash, theta);
  const newConseqHash = Store.child(thetaApplied, 1);

  // Reconstruct antecedent: remove eliminated goals, add reduced goals
  const newAnteRaw = Store.child(thetaApplied, 0);
  const newAnte = flattenAntecedent(newAnteRaw, rc);

  const appliedEliminated = new Set();
  for (const h of eliminatedGoals) appliedEliminated.add(apply(h, theta));

  const anteParts = [];
  for (const h of newAnte.linear) anteParts.push(h);
  for (const p of newAnte.persistent) {
    if (!appliedEliminated.has(p)) anteParts.push(Store.put('bang', [GRADE_W, p]));
  }
  for (const ng of newGoals) {
    anteParts.push(Store.put('bang', [GRADE_W, apply(ng, theta)]));
  }
  for (const p of (newAnte.grade0 || [])) anteParts.push(Store.put('bang', [GRADE_0, p]));
  const newAnteHash = buildRightTensor(anteParts);

  const newFullHash = Store.put('loli', [newAnteHash, newConseqHash]);

  return {
    name: rule.name,
    hash: newFullHash,
    antecedent: newAnteHash,
    consequent: newConseqHash,
    sourceLabel: rule.sourceLabel || null,
  };
}

/**
 * Try to apply SROA to a single rule. Returns new rule or null.
 */
function _trySROA(rule, rc, sroaConfig) {
  const anteHash = Store.child(rule.hash, 0);
  const ante = flattenAntecedent(anteHash, rc);

  // Phase 1: Find array get/set persistent goals and the array holder.
  const arrGoals = _collectArrGoals(ante.persistent, sroaConfig);
  if (arrGoals.length === 0) return null;

  const arrBaseVars = new Set();
  for (const g of arrGoals) arrBaseVars.add(g.arrVar);

  // Find a linear fact holding an array var (resource([TOP | REST]) or resource(S))
  // Walk the full acons chain — after McCarthy normalization, the arrVar may be
  // nested several levels deep (e.g., resource([A | [B | REST]]) with arrVar=REST).
  const resourcePred = sroaConfig ? sroaConfig.resourcePred : null;
  let baseVar = null;
  for (const h of ante.linear) {
    const pred = getPredicateHead(h);
    if (!pred || Store.arity(h) !== 1) continue;
    if (resourcePred && pred !== resourcePred) continue;
    const child = Store.child(h, 0);
    let cur = child;
    while (Store.tag(cur) === 'acons' && Store.arity(cur) === 2) {
      const tail = Store.child(cur, 1);
      if (arrBaseVars.has(tail)) { baseVar = tail; break; }
      cur = tail;
    }
    if (baseVar) break;
    if (Store.tag(child) === 'metavar' && arrBaseVars.has(child)) { baseVar = child; break; }
  }
  if (!baseVar) return null;

  // Phase 2: Collect version chain (fixpoint over array-set outputs).
  const chainGoals = [];
  const allVersions = new Set([baseVar]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const g of arrGoals) {
      if (!allVersions.has(g.arrVar) || chainGoals.includes(g)) continue;
      if (!isGround(g.idx) || sroaConfig.parseIndex(g.idx) === null) return null;
      chainGoals.push(g);
      if (g.type === 'set') { allVersions.add(g.outVar); changed = true; }
    }
  }
  if (chainGoals.length === 0) return null;

  // Phase 3: Determine expansion depth = max index + 1.
  let maxIdx = 0n;
  for (const g of chainGoals) { const i = sroaConfig.parseIndex(g.idx); if (i > maxIdx) maxIdx = i; }
  const depth = Number(maxIdx) + 1;

  // Phase 4: Build theta — the core substitution.
  // (a) Expand baseVar: A → [V0, V1, ..., VK | TAIL]
  const slotVars = [];
  for (let i = 0; i < depth; i++) slotVars.push(freshMetavar());
  const tailVar = freshMetavar();

  const theta = [];
  {
    let baseArr = tailVar;
    for (let i = slotVars.length - 1; i >= 0; i--) baseArr = Store.put('acons', [slotVars[i], baseArr]);
    theta.push([baseVar, baseArr]);
  }

  // (b) Trace version chain: get(V, idx, X) → X = V_slots[idx]
  //                           set(V, idx, val, V') → V' = modified slots
  const versionSlots = new Map();
  versionSlots.set(baseVar, [...slotVars]);

  const processQueue = [baseVar];
  const processed = new Set();
  while (processQueue.length > 0) {
    const curVar = processQueue.shift();
    if (processed.has(curVar)) continue;
    processed.add(curVar);
    const curSlots = versionSlots.get(curVar);
    if (!curSlots) continue;

    for (const g of chainGoals) {
      if (g.arrVar !== curVar || g.type !== 'get') continue;
      theta.push([g.outVar, curSlots[Number(sroaConfig.parseIndex(g.idx))]]);
    }
    for (const g of chainGoals) {
      if (g.arrVar !== curVar || g.type !== 'set') continue;
      const idx = Number(sroaConfig.parseIndex(g.idx));
      const newSlots = [...curSlots];
      newSlots[idx] = g.val;
      let newArr = tailVar;
      for (let i = newSlots.length - 1; i >= 0; i--) newArr = Store.put('acons', [newSlots[i], newArr]);
      // Decompose structured output patterns (e.g. [?H | ?T] from fusion)
      _decomposePatternIntoTheta(g.outVar, newArr, theta);
      versionSlots.set(g.outVar, newSlots);
      processQueue.push(g.outVar);
    }
  }

  // Compose theta: apply requires idempotent substitution, but version chains
  // create transitive entries (e.g. [X, Y] + [Y, V0]). Resolve by applying
  // theta to all values. Acyclic chain → single pass suffices.
  for (let i = 0; i < theta.length; i++) {
    theta[i][1] = apply(theta[i][1], theta);
  }

  // Phase 5: Apply theta to the whole rule hash (preserves existentials).
  const thetaApplied = apply(rule.hash, theta);
  const newConseqHash = Store.child(thetaApplied, 1);

  // Only the antecedent needs structural surgery: remove eliminated persistent goals.
  const newAnteRaw = Store.child(thetaApplied, 0);
  const newAnte = flattenAntecedent(newAnteRaw, rc);

  // Build set of theta-applied goal hashes to remove
  const eliminatedGoals = new Set();
  for (const g of chainGoals) eliminatedGoals.add(apply(g.hash, theta));

  const anteParts = [];
  for (const h of newAnte.linear) anteParts.push(h);
  for (const p of newAnte.persistent) {
    if (!eliminatedGoals.has(p)) anteParts.push(Store.put('bang', [GRADE_W, p]));
  }
  for (const p of (newAnte.grade0 || [])) anteParts.push(Store.put('bang', [GRADE_0, p]));
  const newAnteHash = buildRightTensor(anteParts);

  const newFullHash = Store.put('loli', [newAnteHash, newConseqHash]);

  return {
    name: `${rule.name}[sroa:${depth}]`,
    hash: newFullHash,
    antecedent: newAnteHash,
    consequent: newConseqHash,
    sourceLabel: rule.sourceLabel || null,
  };
}

/**
 * Decompose a pattern against a concrete expanded array, adding bindings to theta.
 * Handles structured output patterns from array-set (e.g. [?H | ?T] from fusion).
 * For metavar leaves, adds a direct substitution. For acons patterns, recurses.
 */
function _decomposePatternIntoTheta(pattern, expanded, theta) {
  if (Store.tag(pattern) === 'metavar') {
    theta.push([pattern, expanded]);
    return;
  }
  if (Store.tag(pattern) === 'acons' && Store.arity(pattern) === 2) {
    // Pattern is [head | tail] — decompose against expanded acons chain
    if (Store.tag(expanded) === 'acons' && Store.arity(expanded) === 2) {
      _decomposePatternIntoTheta(Store.child(pattern, 0), Store.child(expanded, 0), theta);
      _decomposePatternIntoTheta(Store.child(pattern, 1), Store.child(expanded, 1), theta);
    } else {
      // Structural mismatch — push whole substitution as fallback
      theta.push([pattern, expanded]);
    }
    return;
  }
  // Ground or other — push whole substitution
  theta.push([pattern, expanded]);
}

/**
 * Collect array-access persistent goals matching the SROA config.
 * @param {number[]} persistent - persistent goal hashes
 * @param {Object} sroaConfig - { arrayPreds: [getPred, setPred], ... }
 * @returns {Array<{ type, hash, arrVar, idx, outVar, val? }>}
 */
function _collectArrGoals(persistent, sroaConfig) {
  const cfg = sroaConfig;
  const getPred = cfg.arrayPreds[0];
  const setPred = cfg.arrayPreds[1];
  const goals = [];
  for (const p of persistent) {
    const pred = getPredicateHead(p);
    if (pred === getPred && Store.arity(p) === 3) {
      goals.push({
        type: 'get',
        hash: p,
        arrVar: Store.child(p, 0),
        idx: Store.child(p, 1),
        outVar: Store.child(p, 2),
      });
    } else if (pred === setPred && Store.arity(p) === 4) {
      goals.push({
        type: 'set',
        hash: p,
        arrVar: Store.child(p, 0),
        idx: Store.child(p, 1),
        val: Store.child(p, 2),
        outVar: Store.child(p, 3),
      });
    }
  }
  return goals;
}

// ─── L2.5: Elimination ordering ─────────────────────────────────────────────

/**
 * Build topological elimination order for grade-0 persistent predicates.
 * Uses Kahn's algorithm for cycle detection + topological sort.
 *
 * Direction: if predicates A and B co-occur as persistent goals in some rule
 * and share a metavar, the one with fewer metavars (more ground/constraining)
 * comes first. Independent predicates are included in arbitrary order.
 *
 * @param {Map} grade0Facts - predHead → [{name, hash}]
 * @param {Object[]} rules - rules with .hash (loli formula)
 * @param {Object} rc - resolved connectives
 * @returns {string[]} elimination order (predicates to specialize, earliest first)
 */
function buildEliminationOrder(grade0Facts, rules, rc) {
  const preds = [...grade0Facts.keys()];
  if (preds.length <= 1) return preds;

  const predSet = new Set(preds);
  const adj = new Map();     // pred → Set<pred> (successors)
  const inDeg = new Map();   // pred → incoming edge count
  for (const p of preds) { adj.set(p, new Set()); inDeg.set(p, 0); }

  // Analyze co-occurring grade-0 persistent goals in each rule
  for (const rule of rules) {
    const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
    const g0Goals = [];
    for (const goal of ante.persistent) {
      const pred = getPredicateHead(goal);
      if (pred && predSet.has(pred)) {
        const mvs = new Set();
        collectMetavars(goal, mvs);
        g0Goals.push({ pred, mvs });
      }
    }
    if (g0Goals.length < 2) continue;

    // For each pair, add edge from more-ground to less-ground
    for (let i = 0; i < g0Goals.length; i++) {
      for (let j = i + 1; j < g0Goals.length; j++) {
        let shared = false;
        for (const mv of g0Goals[i].mvs) {
          if (g0Goals[j].mvs.has(mv)) { shared = true; break; }
        }
        if (!shared) continue;

        const a = g0Goals[i], b = g0Goals[j];
        if (a.mvs.size < b.mvs.size) {
          if (!adj.get(a.pred).has(b.pred)) {
            adj.get(a.pred).add(b.pred);
            inDeg.set(b.pred, inDeg.get(b.pred) + 1);
          }
        } else if (b.mvs.size < a.mvs.size) {
          if (!adj.get(b.pred).has(a.pred)) {
            adj.get(b.pred).add(a.pred);
            inDeg.set(a.pred, inDeg.get(a.pred) + 1);
          }
        }
        // Equal metavar count: no ordering constraint
      }
    }
  }

  // Kahn's algorithm
  const queue = [];
  for (const [p, deg] of inDeg) {
    if (deg === 0) queue.push(p);
  }

  const order = [];
  while (queue.length > 0) {
    const p = queue.shift();
    order.push(p);
    for (const next of adj.get(p)) {
      const newDeg = inDeg.get(next) - 1;
      inDeg.set(next, newDeg);
      if (newDeg === 0) queue.push(next);
    }
  }

  if (order.length < preds.length) {
    const inCycle = preds.filter(p => !order.includes(p));
    throw new Error(
      `Grade-0 persistent predicate cycle: ${inCycle.join(', ')} — ` +
      `cannot determine elimination order`
    );
  }

  return order;
}

// ─── L3: Orchestration ──────────────────────────────────────────────────────

/**
 * Grade-0 cut elimination: multi-stage composition (THY_0015, TODO_0160).
 *
 * Pass 1: Linear composition via composePair (grade-0 types in antecedent/consequent)
 * Pass 2: Multi-stage persistent specialization via specializePersistent.
 *         Builds dependency DAG → Kahn's topological sort → stage-by-stage elimination.
 *         Includes tabling: grade-0 clauses with premises are resolved via
 *         compile-time backward proof search (TODO_0160).
 *
 * @param {Object[]} compiledRules - all compiled rules (some with hasGrade0)
 * @param {Object} connectives - connective table (e.g. ILL_CONNECTIVES)
 * @param {Function|null} getModeMeta - mode metadata for persistent goal ordering
 * @param {Map|null} clauses - backward clause map (some with grade0: true)
 * @param {Map|null} definitions - backward definitions map (zero-premise axioms)
 * @param {Map|null} extraGrade0Facts - externally-provided grade-0 facts (predHead → [{name, hash}])
 * @param {Function|null} scopeGuard - (rule, pred, goalHash, flatAnte) → boolean; false = skip specialization
 * @param {Object} [opts] - Additional options
 * @param {Function|null} [opts.residualResolver] - (goalHash) → factHash | null; resolve persistent goals at compile time
 * @param {boolean} [opts.fuseBasicBlocks] - Enable linear basic block fusion
 * @param {string} [opts.linearFusionPredicate] - threading predicate for block fusion (required if fuseBasicBlocks)
 * @param {ChainConfig[]} [opts.chainFusionPredicates] - chain fusion descriptors
 * @param {Object} [opts.sroaConfig] - SROA configuration { arrayPreds, resourcePred, parseIndex, buildIndex }
 * @returns {{ composedRules: Object[], removedNames: Set, predicateMap: Map, diagnostics: Object }}
 */
function composeGrade0(compiledRules, connectives, getModeMeta, clauses, definitions, extraGrade0Facts, scopeGuard, opts) {
  const residualResolver = opts && opts.residualResolver || null;
  const doFuse = opts && opts.fuseBasicBlocks || false;
  const chainConfigs = opts && opts.chainFusionPredicates || null;
  const linearFusionPredicate = opts && opts.linearFusionPredicate || null;
  const sroaConfig = opts && opts.sroaConfig || null;
  const canonicalize = opts && opts.canonicalize || null;
  const fusionBarriers = opts && opts.fusionBarriers || null;

  // Full-result cache: all compose outputs are deterministic for the same Store content.
  // Key covers clauses + definitions + forwardRules (via compiledRules hashes).
  const fullKey = _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts, !!residualResolver || doFuse);
  const fullCached = _composeCache.get(fullKey);
  if (fullCached) return fullCached;

  const rc = resolveConnectives(connectives);
  const diagnostics = {
    pairsAttempted: 0,
    pairsSucceeded: 0,
    pairsSkipped: 0,
    specializations: 0,
    grade0Predicates: [],
    errors: [],
  };

  // ── Pass 1: Linear composition (grade-0 types) ────────────────────

  const predicateMap = buildPredicateMap(compiledRules);

  let pass1Rules = [];
  if (predicateMap.size > 0) {
    // Validation
    for (const [pred, entry] of predicateMap) {
      diagnostics.grade0Predicates.push(pred);
      if (entry.producers.length === 0) {
        diagnostics.errors.push(
          `Grade-0 type '${pred}' is consumed but never produced`
        );
      }
      if (entry.consumers.length === 0) {
        diagnostics.errors.push(
          `Grade-0 type '${pred}' is produced but never consumed`
        );
      }
      if (entry.bridges.length > 0) {
        const bridgeNames = entry.bridges.map(r => r.name).join(', ');
        diagnostics.errors.push(
          `Grade-0 type '${pred}' has bridge rules (${bridgeNames}) — ` +
          `bridge composition not yet supported`
        );
      }
    }

    if (diagnostics.errors.length === 0) {
      for (const [pred, entry] of predicateMap) {
        for (const producer of entry.producers) {
          for (const consumer of entry.consumers) {
            diagnostics.pairsAttempted++;
            const result = composePair(producer, consumer, pred, rc, getModeMeta);
            if (result) {
              pass1Rules.push(result);
              diagnostics.pairsSucceeded++;
            } else {
              diagnostics.pairsSkipped++;
            }
          }
        }
      }
    }

    // Defense-in-depth: filter pass-1 rules with grade-0 residuals
    const validPass1 = [];
    for (const raw of pass1Rules) {
      const anteFlat = flattenAntecedent(Store.child(raw.hash, 0), rc);
      const conseqBody = unwrapComputation(Store.child(raw.hash, 1), rc);
      const conseqFlat = flattenAntecedent(conseqBody, rc);
      if (anteFlat.grade0.length > 0 || conseqFlat.grade0.length > 0) {
        diagnostics.errors.push(
          `Composed rule '${raw.name}' still has grade-0 residuals — ` +
          `bridge composition required for multi-predicate grade-0`
        );
      } else {
        validPass1.push(raw);
      }
    }
    pass1Rules = validPass1;
  }

  // ── Pass 2: Persistent specialization (grade-0 clause facts) ──────

  // Collect grade-0 clauses grouped by predicate head.
  // Clauses WITH premises are resolved via compile-time tabling (TODO_0160).
  // Uses in-memory cache to skip resolveAll on repeated loads.
  const grade0Facts = new Map(); // predHead → [{name, hash}, ...]
  if (clauses) {
    const tabKey = _tablingCacheKey(clauses, definitions);
    const tabCached = _tablingCache.get(tabKey);

    if (tabCached) {
      // Cache hit — restore grade0Facts
      for (const [pred, facts] of tabCached.facts) {
        grade0Facts.set(pred, [...facts]);
      }
      diagnostics.tablings = tabCached.tablings;
    } else {
      const { resolveAll } = require('./resolve-all');

      for (const [name, clause] of clauses) {
        if (!clause.grade0) continue;
        const predHead = getPredicateHead(clause.hash);
        if (!predHead) continue;
        if (!grade0Facts.has(predHead)) grade0Facts.set(predHead, []);

        if (clause.premises && clause.premises.length > 0) {
          // Tabling: enumerate all ground solutions via backward proof search
          try {
            const solutions = resolveAll(
              clause.premises, clauses, definitions || new Map(),
              { maxSolutions: 10000, canonicalize }
            );
            for (let i = 0; i < solutions.length; i++) {
              let fact = apply(clause.hash, solutions[i]);
              if (canonicalize) fact = canonicalize(fact);
              grade0Facts.get(predHead).push({
                name: `${name}:${i}`,
                hash: fact,
              });
            }
            diagnostics.tablings = (diagnostics.tablings || 0) + solutions.length;
          } catch (e) {
            diagnostics.errors.push(`Tabling '${name}': ${e.message}`);
          }
        } else {
          grade0Facts.get(predHead).push({ name, hash: clause.hash });
        }
      }

      // Cache for subsequent loads
      const toCache = new Map();
      for (const [pred, facts] of grade0Facts) toCache.set(pred, [...facts]);
      _tablingCache.set(tabKey, { facts: toCache, tablings: diagnostics.tablings || 0 });
    }
  }

  // Merge externally-provided grade-0 facts (e.g., from a domain-specific loader)
  if (extraGrade0Facts) {
    for (const [pred, facts] of extraGrade0Facts) {
      if (!grade0Facts.has(pred)) grade0Facts.set(pred, []);
      const existing = grade0Facts.get(pred);
      for (const f of facts) existing.push(f);
    }
  }

  const removedNames = new Set();
  let specializedPool = [];

  if (grade0Facts.size > 0) {
    // ── Pool: collect all rules eligible for persistent specialization ──

    // Separate pass-1 outputs into those needing specialization and those that don't
    const pass1ForSpec = [];
    const pass1Direct = [];
    for (const raw of pass1Rules) {
      const ante = flattenAntecedent(Store.child(raw.hash, 0), rc);
      let hasG0Goal = false;
      for (const goal of ante.persistent) {
        const pred = getPredicateHead(goal);
        if (pred && grade0Facts.has(pred)) { hasG0Goal = true; break; }
      }
      (hasG0Goal ? pass1ForSpec : pass1Direct).push(raw);
    }

    // Add compiledRules with grade-0 persistent goals (not handled in Pass 1)
    const compiledForSpec = [];
    for (const rule of compiledRules) {
      if (rule.hasGrade0) continue;
      if (removedNames.has(rule.name)) continue;
      const persistent = rule.antecedent.persistent || [];
      let hasG0Goal = false;
      for (const goal of persistent) {
        const pred = getPredicateHead(goal);
        if (pred && grade0Facts.has(pred)) { hasG0Goal = true; break; }
      }
      if (hasG0Goal) {
        compiledForSpec.push(rule);
        removedNames.add(rule.name);
      }
    }

    let pool = [...pass1ForSpec, ...compiledForSpec];

    // ── Elimination order: dependency DAG + Kahn's topological sort ──

    const elimOrder = buildEliminationOrder(grade0Facts, pool, rc);
    for (const pred of elimOrder) {
      diagnostics.grade0Predicates.push(pred);
    }

    // ── Multi-stage specialization: one predicate per stage ──

    const MAX_COMPOSED_PER_STAGE = 100000;

    for (const pred of elimOrder) {
      const facts = grade0Facts.get(pred);
      if (!facts || facts.length === 0) continue;

      // Build argument index for O(1) fact lookup (critical for large fact sets)
      const factIndex = _buildFactArgIndexes(facts);

      const nextPool = [];
      for (const rule of pool) {
        const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
        const goalMatch = findByPredHead(ante.persistent, pred);

        if (!goalMatch) {
          nextPool.push(rule); // pass through — no matching goal
          continue;
        }

        // Scoping guard: caller can reject specialization for specific rule/pred combos
        if (scopeGuard && !scopeGuard(rule, pred, goalMatch.hash, ante)) {
          nextPool.push(rule); // pass through — scoping guard rejected
          diagnostics.scopeGuarded = (diagnostics.scopeGuarded || 0) + 1;
          continue;
        }

        // Use indexed lookup when available (O(1) vs O(N) for large fact sets)
        const candidates = factIndex
          ? (_indexedFactLookup(factIndex, goalMatch.hash) || facts)
          : facts;

        for (const fact of candidates) {
          let result = specializePersistent(rule, fact.hash, fact.name, pred, rc, getModeMeta);
          if (result) {
            // Transitive resolution: resolve goals that became ground after specialization
            if (residualResolver) {
              result = _resolveResidualOnce(result, rc, getModeMeta, residualResolver);
            }
            nextPool.push(result);
            diagnostics.specializations++;
          }
        }
      }

      if (nextPool.length > MAX_COMPOSED_PER_STAGE) {
        throw new Error(
          `Multi-stage composition: ${nextPool.length} rules after stage '${pred}' ` +
          `exceeds limit (${MAX_COMPOSED_PER_STAGE})`
        );
      }

      pool = nextPool;
    }

    pass1Rules = pass1Direct;
    specializedPool = pool;
  }

  // ── Pass 3+4: Batch residual resolution ────────────────────────────
  // Most work done during transitive resolution in specialization loop.
  // This pass catches any remaining resolvable goals (safety net).
  if (residualResolver && specializedPool.length > 0) {
    specializedPool = _resolveResidualBatch(specializedPool, rc, getModeMeta, residualResolver);
    diagnostics.residualResolutions = specializedPool.reduce((n, r) => {
      const name = r.name;
      const resCount = (name.match(/resolved:/g) || []).length;
      return n + resCount;
    }, 0);
  }

  // ── Pass 5: Basic block fusion ──────────────────────────────────────
  // Fuse 1:1 producer→consumer pairs into mega-rules via shared linear resource.
  if (doFuse && specializedPool.length > 0) {
    const fuseResult = _fuseBasicBlocks(specializedPool, rc, getModeMeta, linearFusionPredicate, fusionBarriers);
    specializedPool = fuseResult.rules;
    diagnostics.fusedRuleReduction = fuseResult.fusedCount;
    diagnostics.fuseChainLengths = fuseResult.chainLengths;
  }

  // ── Pass 5.5: Additive chain fusion after basic block fusion ────────
  // Fused mega-rules accumulate threading chains. Collapse them algebraically.
  if (doFuse && specializedPool.length > 0) {
    specializedPool = _fuseAdditiveChains(specializedPool, rc, getModeMeta, chainConfigs);
  }

  // ── Pass 5.6: Second residual resolution after fusion ───────────────
  // Fusion may create newly-ground goals. Resolve them before SROA.
  if (residualResolver && doFuse && specializedPool.length > 0) {
    specializedPool = _resolveResidualBatch(specializedPool, rc, getModeMeta, residualResolver);
  }

  // ── Pass 6: McCarthy normalization + SROA ──────────────────────────
  // McCarthy: peel acons layers from array-access goals (read/write-head axioms).
  // SROA: expand cons pattern in linear resource, eliminate remaining array goals.
  // Replacement strategy: SROA'd version replaces original (OOB = stall either way).
  if (doFuse && specializedPool.length > 0) {
    const sroaResult = _sroaStackDecomposition(specializedPool, rc, getModeMeta, sroaConfig);
    specializedPool = sroaResult.rules;
    diagnostics.sroaTransformed = sroaResult.sroaCount;
    diagnostics.mccarthyNormalized = sroaResult.mccarthyCount;
  }

  // ── Pass 6.5: Post-SROA residual resolution ───────────────────────
  // McCarthy + SROA ground variables (array slot bindings), enabling resolution
  // of dependent goals that were previously blocked by non-ground inputs.
  if (residualResolver && doFuse && specializedPool.length > 0) {
    specializedPool = _resolveResidualBatch(specializedPool, rc, getModeMeta, residualResolver);
  }

  // Return all results: pass-1 (unspecialized) + multi-stage specialized
  const composedRules = [...pass1Rules, ...specializedPool];
  const result = { composedRules, removedNames, predicateMap, diagnostics };
  _composeCache.set(fullKey, result);
  return result;
}

module.exports = {
  // L1: atomic operations
  composePair,
  specializePersistent,
  // L2: analysis
  buildPredicateMap,
  buildEliminationOrder,
  // L3: orchestration
  composeGrade0,
  // Pass functions (exported for testing)
  _fuseAdditiveChains,
  _resolveResidualOnce,
  _resolveResidualBatch,
  _sroaStackDecomposition,
  // Cache key functions (exported for testing — C22)
  _tablingCacheKey,
  _composeFullKey,
  // Exported for direct testing (S6)
  sortPersistentGoals,
  fuseLinearPair,
};
