/**
 * Compose optimization passes P5 + P5.5 — basic-block fusion and
 * additive chain fusion (RES_0143 M4; extracted from compose.js).
 *
 * These are ILL/EVM-motivated but calculus-agnostic optimizations over
 * composed rule pools: P5 fuses 1:1 producer→consumer pairs threading a
 * cc-declared linear fusion predicate into mega-rules; P5.5 collapses
 * additive threading chains (cc-declared ChainConfigs) algebraically.
 * Both are semantics-preserving (pinned by compose-equivalence.test.js)
 * and doubly opt-in: the doFuse flag AND injection — compose0 receives
 * { fuseBasicBlocks, fuseChains, sroa } via composeOpts.fusePasses from
 * the composition root; the semantic passes never import this module.
 */

import Store from '../../kernel/store.js';
import { unify } from '../../kernel/unify.js';
import { apply, debruijnSubst } from '../../kernel/substitute.js';
import { freshMetavar } from '../../kernel/fresh.js';
import { flattenAnte, unwrapComp, expandConsqChoices } from '../formula-utils.js';
import { predHead } from '../../kernel/ast.js';
import { collectMetavars, isGround, hasMetavarInDomain } from '../pattern-utils.js';
import { grade0 } from '../grades.js';
import { newPairProf, emitFuseScanDetect, emitFuseProfile } from '../compose-profile.js';
import { _makeRule, _renameForCompose, removeAt, sortGoals } from '../compose.js';
import { performance } from 'perf_hooks';

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
function _fuseChains(pool, rc, getModeMeta, chainConfigs) {
  if (!chainConfigs || chainConfigs.length === 0) return pool;
  const configs = chainConfigs;

  const result = [];
  for (const rule of pool) {
    const ante = flattenAnte(Store.child(rule.hash, 0), rc);
    const conseqBody = unwrapComp(Store.child(rule.hash, 1), rc);
    const conseq = flattenAnte(conseqBody, rc);

    // Collect goals matching any chain config
    // Each goal: { index, hash, input, output, constant (bigint|null), config }
    const chainableGoals = [];
    for (let i = 0; i < ante.persistent.length; i++) {
      const h = ante.persistent[i];
      const pred = predHead(h);
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
    const sortedPersistent = sortGoals(newPersistent, ante.linear, getModeMeta);
    result.push(_makeRule(
      `${rule.name}[${fusedLabels.join(',')}]`,
      { linear: ante.linear, persistent: sortedPersistent, grade0: ante.grade0 },
      { linear: conseq.linear, persistent: conseq.persistent, grade0: conseq.grade0 },
      rule.sourceLabel,
      undefined, rc
    ));
  }

  return result;
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
 * Unlike expandConsqChoices (which expands oplus into alternatives), this
 * only opens exists (via debruijnSubst) so the formula stays as a single path
 * with oplus preserved for runtime resolution.
 */
function _openEx(h, rc) {
  const tag = Store.tag(h);
  if (!tag) return { linear: [h], persistent: [], grade0: [] };
  if (tag === rc.existential) {
    const body = Store.child(h, 0);
    const opened = debruijnSubst(body, 0n, freshMetavar());
    return _openEx(opened, rc);
  }
  if (tag === rc.product) {
    const l = _openEx(Store.child(h, 0), rc);
    const r = _openEx(Store.child(h, 1), rc);
    return {
      linear: [...l.linear, ...r.linear],
      persistent: [...l.persistent, ...r.persistent],
      grade0: [...l.grade0, ...r.grade0]
    };
  }
  if (tag === rc.exponential) {
    const grade = Store.child(h, 0);
    const inner = Store.child(h, 1);
    // grade atom from the resolved record (compose's CONSTRUCTION sites stay
    // {0,1,ω}-hardcoded until 0157 — this read site takes rc for consistency)
    if (grade === (rc.grade0 || grade0)()) return { linear: [], persistent: [], grade0: [inner] };
    return { linear: [], persistent: [inner], grade0: [] };
  }
  // oplus/with and everything else: keep as opaque linear element
  return { linear: [h], persistent: [], grade0: [] };
}

/**
 * Open all exists binders in a flattened consequent (from flattenAnte).
 * Processes each linear element through _openEx.
 */
function _openConseqEx(conseq, rc) {
  const result = { linear: [], persistent: [...(conseq.persistent || [])], grade0: [...(conseq.grade0 || [])] };
  for (const h of conseq.linear) {
    const opened = _openEx(h, rc);
    result.linear.push(...opened.linear);
    result.persistent.push(...opened.persistent);
    result.grade0.push(...opened.grade0);
  }
  return result;
}

function fusePair(producer, consumer, cutPred, rc, getModeMeta, prof) {
  // Step 1: Alpha-rename producer
  const _tRen0 = prof ? performance.now() : 0;
  const { hash: freshProdHash } = _renameForCompose(producer, 'fusePair');
  const freshProdAnte = Store.child(freshProdHash, 0);
  const freshProdConseq = Store.child(freshProdHash, 1);
  if (prof) { prof.renameMs += performance.now() - _tRen0; prof.renameCalls++; }

  // Step 2: Flatten both sides
  const _tFl0 = prof ? performance.now() : 0;
  const pAnte = flattenAnte(freshProdAnte, rc);
  const pConseqBody = unwrapComp(freshProdConseq, rc);
  const pConseq = flattenAnte(pConseqBody, rc);

  const cAnteHash = Store.child(consumer.hash, 0);
  const cConseqHash = Store.child(consumer.hash, 1);
  const cAnte = flattenAnte(cAnteHash, rc);
  const cConseqBody = unwrapComp(cConseqHash, rc);
  const cConseq = flattenAnte(cConseqBody, rc);
  if (prof) { prof.flattenMs += performance.now() - _tFl0; prof.flattenCalls += 4; }

  // Step 2.5: Open exists in consequents (preserve oplus/with as opaque).
  // flattenAnte treats exists as opaque, hiding pc/gas/stack inside.
  // _openConseqEx opens exists binders via debruijnSubst (replacing bound(0)
  // with fresh metavars) while keeping oplus/with intact for runtime resolution.
  // After fusion, compileRule detects existential slots automatically.
  const _tOx0 = prof ? performance.now() : 0;
  const pConseqFlat = _openConseqEx(pConseq, rc);
  const cConseqFlat = _openConseqEx(cConseq, rc);
  if (prof) { prof.openExMs += performance.now() - _tOx0; prof.openExCalls += 2; }

  // Step 3: Find and remove the cut predicate from both sides
  const pCutIdx = pConseqFlat.linear.findIndex(h => predHead(h) === cutPred);
  const cCutIdx = cAnte.linear.findIndex(h => predHead(h) === cutPred);
  if (pCutIdx < 0 || cCutIdx < 0) { if (prof) prof.failCutMissing++; return null; }

  // Unify the cut formulas
  const _tCu0 = prof ? performance.now() : 0;
  let theta = unify(pConseqFlat.linear[pCutIdx], cAnte.linear[cCutIdx]);
  if (prof) { prof.cutUnifyMs += performance.now() - _tCu0; prof.cutUnifyCalls++; }
  if (theta === null) { if (prof) prof.failCutUnify++; return null; }

  const pConseqLinear = removeAt(pConseqFlat.linear, pCutIdx);
  const cAnteLinear = removeAt(cAnte.linear, cCutIdx);

  // Step 4: Match producer consequent linear → consumer antecedent linear (by predicate head)
  // Only match predicates that appear exactly once on each side (unambiguous)
  const _tMa0 = prof ? performance.now() : 0;
  const pPredCount = {}, cPredCount = {};
  for (const h of pConseqLinear) {
    const p = predHead(h);
    if (p) pPredCount[p] = (pPredCount[p] || 0) + 1;
  }
  for (const h of cAnteLinear) {
    const p = predHead(h);
    if (p) cPredCount[p] = (cPredCount[p] || 0) + 1;
  }

  const pUnmatched = [];
  const cMatched = new Set();

  let _matchUnifyAttempts = 0;
  let _matchUnifyFailures = 0;
  for (let i = 0; i < pConseqLinear.length; i++) {
    const pPred = predHead(pConseqLinear[i]);
    if (!pPred || pPredCount[pPred] !== 1 || cPredCount[pPred] !== 1) {
      pUnmatched.push(pConseqLinear[i]);
      continue;
    }

    // Find matching consumer antecedent formula
    const cIdx = cAnteLinear.findIndex((h, j) => !cMatched.has(j) && predHead(h) === pPred);
    if (cIdx < 0) {
      pUnmatched.push(pConseqLinear[i]);
      continue;
    }

    // Unify the pair, extending theta
    const pApplied = apply(pConseqLinear[i], theta);
    const cApplied = apply(cAnteLinear[cIdx], theta);
    _matchUnifyAttempts++;
    const theta2 = unify(pApplied, cApplied);
    if (theta2 === null) {
      // Can't unify — skip fusion for this pair
      _matchUnifyFailures++;
      if (prof) {
        prof.matchMs += performance.now() - _tMa0;
        prof.matchUnifyAttempts += _matchUnifyAttempts;
        prof.matchUnifyFailures += _matchUnifyFailures;
        prof.failMatchUnify++;
      }
      return null;
    }
    theta = [...theta, ...theta2];
    cMatched.add(cIdx);
  }
  if (prof) {
    prof.matchMs += performance.now() - _tMa0;
    prof.matchUnifyAttempts += _matchUnifyAttempts;
    prof.matchUnifyFailures += _matchUnifyFailures;
  }

  const cUnmatched = cAnteLinear.filter((_, i) => !cMatched.has(i));

  // Step 5: Assemble fused rule
  const _tSu0 = prof ? performance.now() : 0;
  let _applyCount = 0;

  // Pair-substitute fast path: build θ's metavar domain once, then skip
  // apply() on terms that are either ground or have no metavar in the domain.
  // Uses memoized metavar sets from pattern-utils (content-addressed cache).
  //
  // Observed on multisig_nocall_solc_symbolic: ~6750 apply() calls across 343
  // fusePair invocations with avg θ size 2.53. Most antecedent resources (memory,
  // gas, stack, persistent constraints) carry metavars disjoint from θ —
  // the pair-match binds only the cut-thread + matched pred pairs' metavars.
  const thetaDomain = new Set();
  for (let i = 0; i < theta.length; i++) thetaDomain.add(theta[i][0]);

  const applyAll = arr => {
    const out = new Array(arr.length);
    for (let i = 0; i < arr.length; i++) {
      const h = arr[i];
      if (isGround(h) || !hasMetavarInDomain(h, thetaDomain)) {
        out[i] = h;
      } else {
        out[i] = apply(h, theta);
        _applyCount++;
      }
    }
    return out;
  };

  const fusedAnteLinear = applyAll([...pAnte.linear, ...cUnmatched]);
  const fusedAntePersistent = sortGoals(
    applyAll([...pAnte.persistent, ...cAnte.persistent]),
    fusedAnteLinear,
    getModeMeta
  );
  const fusedAnteGrade0 = applyAll([...pAnte.grade0, ...cAnte.grade0]);

  const fusedConseqLinear = applyAll([...pUnmatched, ...cConseqFlat.linear]);
  const fusedConseqPersistent = applyAll([...pConseqFlat.persistent, ...cConseqFlat.persistent]);
  const fusedConseqGrade0 = applyAll([...pConseqFlat.grade0, ...cConseqFlat.grade0]);
  if (prof) { prof.substituteMs += performance.now() - _tSu0; prof.applyCalls += _applyCount; prof.thetaSize += theta.length; }

  // Step 6: Reassemble. Mark as fused so downstream passes (SROA) can identify it.
  const _tAs0 = prof ? performance.now() : 0;
  const fused = _makeRule(
    `${producer.name}+${consumer.name}`,
    { linear: fusedAnteLinear, persistent: fusedAntePersistent, grade0: fusedAnteGrade0 },
    { linear: fusedConseqLinear, persistent: fusedConseqPersistent, grade0: fusedConseqGrade0 },
    producer.sourceLabel || consumer.sourceLabel,
    { isFused: true },
    rc
  );
  if (prof) { prof.assembleMs += performance.now() - _tAs0; prof.assembleCalls++; prof.succeeded++; }
  return fused;
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
function fusePairEx(producer, consumer, cutPred, rc, getModeMeta, prof) {
  // Check if producer has oplus in consequent
  const _tCh0 = prof ? performance.now() : 0;
  const prodConseqBody = unwrapComp(Store.child(producer.hash, 1), rc);
  const prodConseq = flattenAnte(prodConseqBody, rc);

  let hasChoice = false;
  for (const h of prodConseq.linear) {
    const tag = Store.tag(h);
    if (tag === rc.internalChoice || tag === rc.externalChoice) {
      hasChoice = true;
      break;
    }
  }
  if (prof) { prof.exChoiceCheckMs += performance.now() - _tCh0; prof.exChoiceCheckCalls++; }

  if (!hasChoice) {
    // No oplus — delegate to fusePair directly
    const fused = fusePair(producer, consumer, cutPred, rc, getModeMeta, prof);
    return fused ? [fused] : null;
  }

  // Expand oplus into alternatives
  const _tEx0 = prof ? performance.now() : 0;
  const alts = expandConsqChoices(prodConseq, rc);
  if (prof) { prof.exExpandMs += performance.now() - _tEx0; prof.exExpandCalls++; }
  if (alts.length <= 1) {
    const fused = fusePair(producer, consumer, cutPred, rc, getModeMeta, prof);
    return fused ? [fused] : null;
  }

  // Create projected rules (one per alternative) and fuse each.
  // Persistent goals from oplus branches are GUARDS (must be proved before firing),
  // so they go into the projected rule's ANTECEDENT, not CONSEQUENT.
  // This ensures dead branches (contradictory guards like !eq 1 0) never fire.
  const _tPr0 = prof ? performance.now() : 0;
  const ante = flattenAnte(Store.child(producer.hash, 0), rc);
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
      producer.isFused ? { isFused: true } : undefined,
      rc
    );
    if (prof) prof.exProjectCalls++;
    const fused = fusePair(projected, consumer, cutPred, rc, getModeMeta, prof);
    if (fused) results.push(fused);
  }
  if (prof) { prof.exProjectMs += performance.now() - _tPr0; prof.exProjectsProduced += alts.length; prof.exBranchesFused += results.length; }
  return results.length > 0 ? results : null;
}

/**
 * Fuse basic blocks in a pool of rules.
 * Finds 1:1 cutPred(GROUND) producer→consumer pairs and chains them.
 * Supports oplus producers via per-branch projection (fusePairEx).
 *
 * @param {Array} pool - raw rules
 * @param {Object} rc - resolved connectives
 * @param {Function|null} getModeMeta
 * @param {string} linearFusionPredicate - the threading predicate to fuse on (required)
 * @returns {{ rules: Array, fusedCount: number, chainLengths: number[] }}
 */
function _fuseBasicBlocks(pool, rc, getModeMeta, linearFusionPredicate, fusionBarriers, onPhase) {
  const _pEmit = (name, ms, meta) => { if (onPhase) onPhase(name, ms, meta); };
  const _tScan = onPhase ? performance.now() : 0;
  const cutPred = linearFusionPredicate;
  const producers = {}; // value → [ruleIdx]
  const consumers = {}; // value → [ruleIdx]
  const hiddenProducers = new Set(); // values produced inside oplus/with/exists

  // ── Fuse-pair profiling accumulator (null when onPhase is off) ──────
  // Shape lives in compose-profile.js; gated entirely behind `onPhase`
  // truthiness via null checks in fusePair.
  const pairProf = onPhase ? newPairProf() : null;
  // Per-chain records for top-K / histogram / distribution.
  const chainRecords = onPhase ? [] : null;

  /**
   * Recursively collect ground values of the fusion predicate from inside
   * oplus/with/exists nodes. These are "invisible producers" — values that
   * flattenAnte can't see. Consumers must NOT be fused away.
   */
  function _invisibleCut(h) {
    const tag = Store.tag(h);
    if (!tag) return;
    if (tag === rc.internalChoice || tag === rc.externalChoice) {
      _invisibleCut(Store.child(h, 0));
      _invisibleCut(Store.child(h, 1));
    } else if (tag === rc.product) {
      _invisibleCut(Store.child(h, 0));
      _invisibleCut(Store.child(h, 1));
    } else if (tag === rc.exponential) {
      _invisibleCut(Store.child(h, 1));
    } else if (tag === rc.existential) {
      _invisibleCut(Store.child(h, 0));
    } else {
      const pred = predHead(h);
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
    const ante = flattenAnte(Store.child(rule.hash, 0), rc);
    const conseqBody = unwrapComp(Store.child(rule.hash, 1), rc);
    const conseq = flattenAnte(conseqBody, rc);

    // Consumer: cutPred(GROUND) in antecedent linear
    for (const h of ante.linear) {
      const pred = predHead(h);
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
        _invisibleCut(h);
      }
    }

    // Producer: cutPred(GROUND) in consequent linear — at top level or inside exists.
    // Oplus rules ARE allowed as producers: fusePairEx projects each oplus
    // branch into a separate fused rule, so resources inside branches get properly matched.
    // Skip oplus/with nodes themselves; only scan top-level and exists-wrapped items.
    for (const h of conseq.linear) {
      const tag = Store.tag(h);
      // Skip oplus/with nodes — their cutPred values are tracked via _invisibleCut
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
        const pred = predHead(cur);
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

  const scanMs = onPhase ? performance.now() - _tScan : 0;
  const _tDetect = onPhase ? performance.now() : 0;

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
    if (onPhase) {
      emitFuseScanDetect(_pEmit, {
        scanMs, detectMs: performance.now() - _tDetect,
        pool, producers, consumers, hiddenProducers,
        fuseableEdges: 0, chains: 0,
      });
    }
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

  const detectMs = onPhase ? performance.now() - _tDetect : 0;
  const _tFuse = onPhase ? performance.now() : 0;

  // Fuse each chain (capped at MAX_FUSE_CHAIN to stay within match engine's 64-slot limit)
  const MAX_FUSE_CHAIN = 20; // ~2 metavars per opcode → 40 metavars, comfortably under 64
  const fusedRules = new Set(); // indices of rules that were fused away
  const newRules = [];
  const chainLengths = [];
  let _branchMultiplications = 0;

  for (const chain of chains) {
    const _tChain = onPhase ? performance.now() : 0;
    const _chainBranchesAtStart = onPhase ? _branchMultiplications : 0;
    const _chainPairsAttempted = { n: 0 };
    const _chainPairsSucceeded = { n: 0 };
    // Fuse chain, tracking multiple branches from oplus expansion.
    // `branches` is an array of {rule, fusedUpTo} — starts with one branch,
    // may multiply at oplus producers (fusePairEx returns >1 rule).
    let branches = [{ rule: pool[chain[0]], fusedUpTo: 0 }];
    const limit = Math.min(chain.length, MAX_FUSE_CHAIN);
    for (let i = 1; i < limit; i++) {
      const next = pool[chain[i]];
      const nextBranches = [];
      for (const branch of branches) {
        if (onPhase) _chainPairsAttempted.n++;
        const fused = fusePairEx(branch.rule, next, cutPred, rc, getModeMeta, pairProf);
        if (fused) {
          for (const f of fused) nextBranches.push({ rule: f, fusedUpTo: i });
          if (fused.length > 1) _branchMultiplications++;
          if (onPhase) _chainPairsSucceeded.n++;
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

    if (onPhase) {
      const headRule = pool[chain[0]];
      const tailRule = pool[chain[chain.length - 1]];
      chainRecords.push({
        head: headRule && headRule.name ? String(headRule.name) : '?',
        tail: tailRule && tailRule.name ? String(tailRule.name) : '?',
        len: chain.length,
        fusedLen: maxFusedUpTo + 1,
        ms: performance.now() - _tChain,
        pairsAttempted: _chainPairsAttempted.n,
        pairsSucceeded: _chainPairsSucceeded.n,
        branchMults: _branchMultiplications - _chainBranchesAtStart,
        branchesOut: branches.length,
      });
    }
  }

  // Build result: keep unfused rules + add fused mega-rules
  const result = [];
  for (let i = 0; i < pool.length; i++) {
    if (!fusedRules.has(i)) result.push(pool[i]);
  }
  result.push(...newRules);

  if (onPhase) {
    emitFuseProfile(_pEmit, {
      fuseMs: performance.now() - _tFuse, scanMs, detectMs,
      pool, producers, consumers, hiddenProducers,
      fuseableEdges, chains, fusedRules, newRules,
      branchMultiplications: _branchMultiplications, chainLengths,
      pairProf, chainRecords,
    });
  }

  return { rules: result, fusedCount: fusedRules.size - newRules.length, chainLengths };
}

export { _fuseChains as fuseChains, fusePair, fusePairEx, _fuseBasicBlocks as fuseBasicBlocks, _openEx, _openConseqEx };
export default { fuseChains: _fuseChains, fusePair, fusePairEx, fuseBasicBlocks: _fuseBasicBlocks };
