/**
 * Grade-0 Cut Elimination — compose rules through !_0 intermediate types.
 *
 * Three-layer API:
 *   L1: composePair    — atomic cut elimination (grade-agnostic)
 *   L2: buildPredicateMap — analysis (producers/consumers/bridges)
 *   L3: composeGrade0  — v1 scheduler + validation → ComposeResult
 *
 * Theory: stratified cut elimination (THY_0015). Grade-0 non-interference
 * (Choudhury et al. POPL 2021) guarantees composed rules are observationally
 * equivalent. Each composePair call is one cut step on the grade-0 fragment.
 */

'use strict';

const Store = require('../kernel/store');
const { unify } = require('../kernel/unify');
const { apply } = require('../kernel/substitute');
const { freshMetavar } = require('../kernel/fresh');
const { flattenAntecedent, unwrapComputation, resolveConnectives } = require('./compile');
const { getPredicateHead, buildRightTensor } = require('../kernel/ast');
const { collectMetavars } = require('./pattern-utils');
const { GRADE_0, GRADE_W } = require('./grades');

// ─── Tabling cache ──────────────────────────────────────────────────────────
// In-memory cache for resolveAll results. Survives across composeGrade0 calls
// within the same process (helps when multiple test files load the same program).
// Invalidated on Store.clear() via the onClear hook.

const _tablingCache = new Map();
const _composeCache = new Map();
Store.onClear(() => { _tablingCache.clear(); _composeCache.clear(); });

function _tablingCacheKey(clauses, definitions) {
  let h = 0;
  if (clauses) for (const [, cl] of clauses) h = (h * 31 + cl.hash) | 0;
  if (definitions) for (const [, dh] of definitions) h = (h * 31 + dh) | 0;
  return h;
}

function _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts) {
  let h = _tablingCacheKey(clauses, definitions);
  for (let i = 0; i < compiledRules.length; i++) {
    h = (h * 31 + compiledRules[i].hash) | 0;
  }
  if (extraGrade0Facts) {
    for (const [, facts] of extraGrade0Facts) {
      for (const f of facts) h = (h * 31 + f.hash) | 0;
    }
  }
  return h;
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

// ─── Persistent goal ordering ────────────────────────────────────────────────

/**
 * Topologically sort persistent goals so that inputs are grounded before use.
 *
 * After composePair merges producer + consumer persistent goals, the naive
 * concatenation [...producer, ...consumer] can put a producer goal (e.g.
 * !checked_sub GAS COST GAS') before the consumer goal that grounds one of
 * its inputs (e.g. !plus 3 MemGas COST). The backward prover resolves goals
 * strictly in order, so we must reorder.
 *
 * Uses FFI mode metadata (+/- per position) to distinguish inputs from outputs.
 * MultiModal predicates (e.g. plus) allow at most 1 input position to be
 * ungrounded (it becomes the computed output).
 *
 * @param {number[]} goals - persistent goal hashes (after theta application)
 * @param {number[]} linearPatterns - linear antecedent patterns (metavars are grounded at runtime)
 * @param {Function|null} getModeMeta - (predHead) → { modes: string[], multiModal: boolean } | null
 * @returns {number[]} reordered goals
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

  // Step 6: Reassemble.
  // Antecedent: linear * persistent(bang-wrapped) * grade0(bang-wrapped)
  const anteParts = [
    ...combinedAnteLinear,
    ...combinedAntePersistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...combinedAnteGrade0.map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const anteHash = buildRightTensor(anteParts);

  // Consequent: linear * persistent(bang-wrapped) * grade0(bang-wrapped)
  const conseqParts = [
    ...combinedConseqLinear,
    ...combinedConseqPersistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...combinedConseqGrade0.map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const conseqBody = buildRightTensor(conseqParts);
  const conseqHash = Store.put('monad', [conseqBody]);
  const fullHash = Store.put('loli', [anteHash, conseqHash]);

  // Step 7: Return raw rule.
  return {
    name: `${consumer.name}:${producer.name}`,
    hash: fullHash,
    antecedent: anteHash,
    consequent: conseqHash,
    sourceLabel: consumer.sourceLabel || producer.sourceLabel || null,
  };
}

/**
 * Specialize a rule by resolving a persistent goal against a ground grade-0 clause.
 * Separate from composePair — different semantics (ground fact × rule, not rule × rule).
 *
 * @param {Object} rule - Rule with .hash (loli formula) and .name
 * @param {number} factHash - Ground clause hash (e.g., is_push(0x60, 1))
 * @param {string} factName - Clause name (e.g., 'is_push/push1')
 * @param {string} predHead - Predicate head to resolve (e.g., 'is_push')
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

  // Step 6: Reassemble
  const anteParts = [
    ...combinedAnteLinear,
    ...combinedAntePersistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...combinedAnteGrade0.map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const anteHash = buildRightTensor(anteParts);

  const conseqParts = [
    ...combinedConseqLinear,
    ...combinedConseqPersistent.map(p => Store.put('bang', [GRADE_W, p])),
    ...combinedConseqGrade0.map(p => Store.put('bang', [GRADE_0, p])),
  ];
  const conseqBodyHash = buildRightTensor(conseqParts);
  const conseqHash = Store.put('monad', [conseqBodyHash]);
  const fullHash = Store.put('loli', [anteHash, conseqHash]);

  return {
    name: `${rule.name}:${factName}`,
    hash: fullHash,
    antecedent: anteHash,
    consequent: conseqHash,
    sourceLabel: rule.sourceLabel || null,
  };
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
 * @returns {{ composedRules: Object[], removedNames: Set, predicateMap: Map, diagnostics: Object }}
 */
function composeGrade0(compiledRules, connectives, getModeMeta, clauses, definitions, extraGrade0Facts) {
  // Full-result cache: all compose outputs are deterministic for the same Store content.
  // Key covers clauses + definitions + forwardRules (via compiledRules hashes).
  const fullKey = _composeFullKey(compiledRules, clauses, definitions, extraGrade0Facts);
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
          `multi-stage composition not yet supported (see TODO_0158)`
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
          `Composed rule '${raw.name}' still has grade-0 content — ` +
          `multi-stage composition required (see TODO_0158)`
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
      const { binlitTheory } = require('./ill/binlit-theory');

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
              { maxSolutions: 10000 }
            );
            for (let i = 0; i < solutions.length; i++) {
              let fact = apply(clause.hash, solutions[i]);
              fact = binlitTheory.canonicalize(fact);
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

  // Merge externally-provided grade-0 facts (e.g., from bytecode loader)
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

      const nextPool = [];
      for (const rule of pool) {
        const ante = flattenAntecedent(Store.child(rule.hash, 0), rc);
        const goalMatch = findByPredHead(ante.persistent, pred);

        if (!goalMatch) {
          nextPool.push(rule); // pass through — no matching goal
          continue;
        }

        // Specialize against all facts for this predicate
        for (const fact of facts) {
          const result = specializePersistent(rule, fact.hash, fact.name, pred, rc, getModeMeta);
          if (result) {
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

  // Return all results: pass-1 (unspecialized) + multi-stage specialized
  const composedRules = [...pass1Rules, ...specializedPool];
  const result = { composedRules, removedNames, predicateMap, diagnostics };
  _composeCache.set(fullKey, result);
  return result;
}

module.exports = { composePair, specializePersistent, buildPredicateMap, buildEliminationOrder, composeGrade0 };
