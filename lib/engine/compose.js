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

// ─── L3: Orchestration ──────────────────────────────────────────────────────

/**
 * Grade-0 cut elimination: two-pass composition (THY_0015).
 *
 * Pass 1: Linear composition via composePair (grade-0 types in antecedent/consequent)
 * Pass 2: Persistent specialization via specializePersistent (grade-0 clause facts)
 *
 * @param {Object[]} compiledRules - all compiled rules (some with hasGrade0)
 * @param {Object} connectives - connective table (e.g. ILL_CONNECTIVES)
 * @param {Function|null} getModeMeta - mode metadata for persistent goal ordering
 * @param {Map|null} clauses - backward clause map (some with grade0: true)
 * @returns {{ composedRules: Object[], removedNames: Set, predicateMap: Map, diagnostics: Object }}
 */
function composeGrade0(compiledRules, connectives, getModeMeta, clauses) {
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

  // Collect grade-0 clauses grouped by predicate head
  const grade0Facts = new Map(); // predHead → [{name, hash}, ...]
  if (clauses) {
    for (const [name, clause] of clauses) {
      if (!clause.grade0) continue;
      const predHead = getPredicateHead(clause.hash);
      if (!predHead) continue;
      if (!grade0Facts.has(predHead)) grade0Facts.set(predHead, []);
      grade0Facts.get(predHead).push({ name, hash: clause.hash });
    }
  }

  const specializedRules = [];
  const removedNames = new Set();

  if (grade0Facts.size > 0) {
    for (const pred of grade0Facts.keys()) {
      diagnostics.grade0Predicates.push(pred);
    }

    // Helper: check if a raw rule has persistent goals matching grade-0 predicates
    function specializeRule(rule) {
      const anteFlat = flattenAntecedent(Store.child(rule.hash, 0), rc);
      for (const goal of anteFlat.persistent) {
        const predHead = getPredicateHead(goal);
        if (!predHead || !grade0Facts.has(predHead)) continue;
        // Found a persistent goal matching a grade-0 predicate — specialize
        const facts = grade0Facts.get(predHead);
        for (const fact of facts) {
          const result = specializePersistent(rule, fact.hash, fact.name, predHead, rc, getModeMeta);
          if (result) {
            specializedRules.push(result);
            diagnostics.specializations++;
          }
        }
        removedNames.add(rule.name);
        return true; // specialized (one grade-0 persistent predicate per pass)
      }
      return false;
    }

    // Specialize pass-1 outputs
    const remainingPass1 = [];
    for (const raw of pass1Rules) {
      if (!specializeRule(raw)) {
        remainingPass1.push(raw);
      }
    }
    pass1Rules = remainingPass1;

    // Specialize original compiled rules that have matching persistent goals
    // (rules that weren't in pass 1 but consume grade-0 clause predicates)
    for (const rule of compiledRules) {
      if (rule.hasGrade0) continue; // already handled in pass 1
      if (removedNames.has(rule.name)) continue;
      const persistent = rule.antecedent.persistent || [];
      for (const goal of persistent) {
        const predHead = getPredicateHead(goal);
        if (predHead && grade0Facts.has(predHead)) {
          specializeRule(rule);
          break;
        }
      }
    }
  }

  // Return all results: pass-1 (minus specialized) + pass-2 specialized
  const composedRules = [...pass1Rules, ...specializedRules];
  return { composedRules, removedNames, predicateMap, diagnostics };
}

module.exports = { composePair, specializePersistent, buildPredicateMap, composeGrade0 };
