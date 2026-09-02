/**
 * Compose profiling emission — extracted verbatim from compose.js (audit
 * 2026-09-02 readability split, zero semantic change).
 *
 * Everything here is pure and only invoked when `onPhase` is truthy, so
 * it never executes on the hot path during normal (non-benchmarking)
 * loads: the fuse-pair accumulator shape, the fuse-blocks scan/detect/
 * fuse rollup + per-step leaves, and the grade-0 tabling rollup +
 * sub-activity leaves.
 */

'use strict';

/**
 * Fixed-bucket histogram: [<1, 1-10, 10-100, 100-1000, ≥1000].
 * Returns [n0, n1, n2, n3, n4]; sum == values.length.
 */
function _histogram(values, bucketEdges) {
  const h = new Array(bucketEdges.length + 1).fill(0);
  for (const v of values) {
    let b = bucketEdges.length;
    for (let i = 0; i < bucketEdges.length; i++) {
      if (v < bucketEdges[i]) { b = i; break; }
    }
    h[b]++;
  }
  return h;
}

/**
 * Descriptive stats from a numeric array. Safe on empty input (returns zeros).
 * Sorting is in-place for performance; pass a copy if the caller needs to
 * preserve order.
 */
function _stats(valuesSortedInPlace) {
  const a = valuesSortedInPlace;
  if (a.length === 0) return { min: 0, p50: 0, p95: 0, max: 0, mean: 0, stddev: 0, count: 0 };
  a.sort((x, y) => x - y);
  const n = a.length;
  const sum = a.reduce((s, v) => s + v, 0);
  const mean = sum / n;
  const v2 = a.reduce((s, v) => s + (v - mean) * (v - mean), 0) / n;
  return {
    min: a[0],
    p50: a[Math.floor(n * 0.5)],
    p95: a[Math.min(n - 1, Math.floor(n * 0.95))],
    max: a[n - 1],
    mean,
    stddev: Math.sqrt(v2),
    count: n,
  };
}

function _round2(x) { return Math.round(x * 100) / 100; }

/**
 * Fuse-pair profiling accumulator (null-pattern lives at the call site).
 * All fields are numeric so field-wise aggregation across calls is trivial.
 * Gated entirely behind `onPhase` truthiness via null checks in fusePair.
 */
function newPairProf() {
  return {
    // fusePairEx outer layer (oplus dispatch)
    exChoiceCheckMs: 0, exChoiceCheckCalls: 0,
    exExpandMs: 0, exExpandCalls: 0,
    exProjectMs: 0, exProjectCalls: 0,
    exProjectsProduced: 0, exBranchesFused: 0,
    // fusePair step 1: alpha-rename
    renameMs: 0, renameCalls: 0,
    // fusePair step 2: flattenAnte + unwrapComp
    flattenMs: 0, flattenCalls: 0,
    // fusePair step 2.5: _openConseqEx
    openExMs: 0, openExCalls: 0,
    // fusePair step 3: cut unify
    cutUnifyMs: 0, cutUnifyCalls: 0,
    // fusePair step 4: pairwise match + unify
    matchMs: 0,
    matchUnifyAttempts: 0, matchUnifyFailures: 0,
    // fusePair step 5: substitute (apply) to assemble merged rule
    substituteMs: 0, applyCalls: 0, thetaSize: 0,
    // fusePair step 6: _makeRule + sortGoals
    assembleMs: 0, assembleCalls: 0,
    // Outcomes
    succeeded: 0,
    failCutMissing: 0, failCutUnify: 0, failMatchUnify: 0,
  };
}

/** Scan + detect leaves (also the early-exit shape when no edges fused). */
function emitFuseScanDetect(emit, { scanMs, detectMs, pool, producers, consumers,
  hiddenProducers, fuseableEdges, chains }) {
  emit('load/compose/fuse-blocks/scan', scanMs, {
    poolSize: pool.length,
    producerValues: Object.keys(producers).length,
    consumerValues: Object.keys(consumers).length,
    hiddenProducers: hiddenProducers.size,
  });
  emit('load/compose/fuse-blocks/detect', detectMs, {
    fuseableEdges,
    chains,
  });
}

/** Full fuse-blocks rollup: scan/detect + fuse meta + per-step leaves + residual. */
function emitFuseProfile(emit, { fuseMs, scanMs, detectMs, pool, producers,
  consumers, hiddenProducers, fuseableEdges, chains, fusedRules, newRules,
  branchMultiplications, chainLengths, pairProf, chainRecords }) {
  emitFuseScanDetect(emit, {
    scanMs, detectMs, pool, producers, consumers, hiddenProducers,
    fuseableEdges: fuseableEdges.length, chains: chains.length,
  });

  // Attributed per-step times (from pairProf accumulator)
  const pp = pairProf;
  const stepMs = {
    'oplus-choice-check': pp.exChoiceCheckMs,
    'oplus-expand':       pp.exExpandMs,
    'oplus-project':      pp.exProjectMs,
    'pair-rename':        pp.renameMs,
    'pair-flatten':       pp.flattenMs,
    'pair-open-ex':       pp.openExMs,
    'pair-cut-unify':     pp.cutUnifyMs,
    'pair-match':         pp.matchMs,
    'pair-substitute':    pp.substituteMs,
    'pair-assemble':      pp.assembleMs,
  };

  // Compute per-chain stats
  const chainMsArr = chainRecords.map(r => r.ms);
  const chainLenArr = chainRecords.map(r => r.len);
  const fusedLenArr = chainRecords.map(r => r.fusedLen);
  const chainMsStats = _stats(chainMsArr.slice());
  const chainLenStats = _stats(chainLenArr.slice());
  const fusedLenStats = _stats(fusedLenArr.slice());

  // Histograms: ms buckets (log-ish), length buckets (linear).
  const chainMsBuckets = [0.01, 0.05, 0.1, 0.5, 1, 2, 5, 10, 25, 50];
  const chainLenBuckets = [2, 3, 5, 8, 12, 16, 20];
  const chainMsHist = _histogram(chainMsArr, chainMsBuckets);
  const chainLenHist = _histogram(chainLenArr, chainLenBuckets);

  // Top-K hottest chains (by ms)
  const TOP_K_CHAINS = 12;
  const topChains = chainRecords.slice()
    .sort((a, b) => b.ms - a.ms)
    .slice(0, TOP_K_CHAINS)
    .map(r => ({
      head: r.head,
      tail: r.tail,
      len: r.len,
      fusedLen: r.fusedLen,
      ms: _round2(r.ms),
      pairsAttempted: r.pairsAttempted,
      pairsSucceeded: r.pairsSucceeded,
      branchMults: r.branchMults,
    }));

  // Attribution: sum of step times + top-K chain wall-clock residual.
  const attributedStepMs = Object.values(stepMs).reduce((s, v) => s + v, 0);
  const attributionRatio = fuseMs > 0 ? attributedStepMs / fuseMs : 0;
  const otherMs = Math.max(0, fuseMs - attributedStepMs);

  emit('load/compose/fuse-blocks/fuse', fuseMs, {
    chainsAttempted: chains.length,
    fusedRulesIn: fusedRules.size,
    fusedRulesOut: newRules.length,
    reduction: fusedRules.size - newRules.length,
    branchMultiplications,
    chainLengths,
    // Pair-level success/failure breakdown
    pairsSucceeded: pp.succeeded,
    pairsFailCutMissing: pp.failCutMissing,
    pairsFailCutUnify: pp.failCutUnify,
    pairsFailMatchUnify: pp.failMatchUnify,
    pairsMatchUnifyAttempts: pp.matchUnifyAttempts,
    pairsMatchUnifyFailures: pp.matchUnifyFailures,
    pairMatchSuccessRate: pp.matchUnifyAttempts > 0
      ? 1 - pp.matchUnifyFailures / pp.matchUnifyAttempts : 1,
    // Oplus stats
    oplusBranchesProjected: pp.exProjectsProduced,
    oplusBranchesFused: pp.exBranchesFused,
    // Chain stats
    perChainTimes: chainMsStats,
    perChainLength: chainLenStats,
    perChainFusedLength: fusedLenStats,
    chainTimeHistogram: chainMsHist,
    chainTimeHistogramEdges: chainMsBuckets,
    chainLengthHistogram: chainLenHist,
    chainLengthHistogramEdges: chainLenBuckets,
    topChains,
    // Attribution
    attributedMs: _round2(attributedStepMs),
    unattributedMs: _round2(otherMs),
    attributionRatio: _round2(attributionRatio),
  });

  // Emit per-step sub-paths (absolute ms). These sum to <= fuseMs.
  for (const [step, ms] of Object.entries(stepMs)) {
    const meta = {};
    if (step === 'pair-rename')     { meta.calls = pp.renameCalls; }
    if (step === 'pair-flatten')    { meta.calls = pp.flattenCalls; }
    if (step === 'pair-open-ex')    { meta.calls = pp.openExCalls; }
    if (step === 'pair-cut-unify')  {
      meta.calls = pp.cutUnifyCalls;
      meta.failMissing = pp.failCutMissing;
      meta.failUnify = pp.failCutUnify;
    }
    if (step === 'pair-match')      {
      meta.unifyAttempts = pp.matchUnifyAttempts;
      meta.unifyFailures = pp.matchUnifyFailures;
    }
    if (step === 'pair-substitute') {
      meta.applyCalls = pp.applyCalls;
      meta.avgThetaSize = pp.assembleCalls > 0 ? pp.thetaSize / pp.assembleCalls : 0;
    }
    if (step === 'pair-assemble')   { meta.calls = pp.assembleCalls; meta.succeeded = pp.succeeded; }
    if (step === 'oplus-choice-check') { meta.calls = pp.exChoiceCheckCalls; }
    if (step === 'oplus-expand')       { meta.calls = pp.exExpandCalls; }
    if (step === 'oplus-project')      {
      meta.calls = pp.exProjectCalls;
      meta.projectsProduced = pp.exProjectsProduced;
      meta.branchesFused = pp.exBranchesFused;
    }
    emit(`load/compose/fuse-blocks/fuse/${step}`, ms, meta);
  }

  // NOTE: top-K hottest chains are available in the rollup's `topChains` meta
  // above; we do NOT emit per-chain leaves because chain wall-clock overlaps
  // with the pair-step wall-clock (a chain's time IS the sum of pair-rename +
  // pair-substitute + etc. for that chain). Emitting both would double-count
  // in any renderer that sums leaves (sunburst, table totals).

  // Residual: fuse wall-clock - attributed step ms. Keeps sunburst total correct.
  emit('load/compose/fuse-blocks/fuse/other', otherMs, {
    note: 'chain-walk + loop overhead + GC',
  });
}

/** Grade-0 tabling rollup + sub-activity leaves (partition wall-clock honestly). */
function emitTablingProfile(emit, { rp, perClause, tTabAcc, premiseClauses,
  tablingSolutions, tablingErrors, producedFacts, applyHeadMs, canonMs,
  canonicalize }) {
  // ── Rich tabling rollup meta: per-clause distribution, top-K, histograms
  const perClauseTimes = perClause.map(c => c.ms);
  const perClauseSols = perClause.map(c => c.solutions);
  const perClauseNodes = perClause.map(c => c.searchNodes);
  const perClauseUnifies = perClause.map(c => c.unifyAttempts);
  const tsBuckets = [1, 10, 100, 1000];      // ms buckets
  const solBuckets = [1, 10, 100, 1000];     // solution-count buckets
  const nodeBuckets = [10, 100, 1000, 10000]; // search-node buckets
  const topN = [...perClause].sort((a, b) => b.ms - a.ms).slice(0, 10).map(c => ({
    name: c.name,
    ms: _round2(c.ms),
    solutions: c.solutions,
    premises: c.premises,
    searchNodes: c.searchNodes,
    unifyAttempts: c.unifyAttempts,
    errored: c.errored || undefined,
  }));
  // Total time precisely attributed to sub-activities. The residual
  // (tTabAcc - attributedMs) goes into tabling/other so the sunburst arc
  // matches the true wall-clock total.
  const attributedMs =
    rp.indexMs + rp.selectGoalMs + rp.mapApplyMs + rp.alphaRenMs +
    rp.unifyMs + rp.composeSubMs + rp.applyPremisesMs + rp.backchainMs +
    rp.ffiMs + rp.nativeMs + applyHeadMs + canonMs;

  emit('load/compose/grade0-facts/tabling', tTabAcc, {
    premiseClauses,
    solutions: tablingSolutions,
    errors: tablingErrors,
    producedFacts,

    // Search shape
    searchNodes: rp.searchNodes,
    maxSearchDepth: rp.maxDepth,
    solutionsFound: rp.solutionsFound,
    avgNodesPerClause: premiseClauses ? _round2(rp.searchNodes / premiseClauses) : 0,

    // Unification
    unifyAttempts: rp.unifyAttempts,
    unifySucceeded: rp.unifySucceeded,
    unifyFailures: rp.unifyFailures,
    unifySuccessRate: rp.unifyAttempts ? _round2(rp.unifySucceeded / rp.unifyAttempts) : 0,

    // Backchain / FFI / native mix
    backchainLookups: rp.backchainLookups,
    avgCandidatesPerLookup: rp.backchainLookups ? _round2(rp.totalCandidates / rp.backchainLookups) : 0,
    maxCandidatesPerLookup: rp.maxCandidates,
    backchainCalls: rp.backchainCalls,
    backchainSuccesses: rp.backchainSuccesses,
    ffiCalls: rp.ffiCalls,
    ffiSuccesses: rp.ffiSuccesses,
    ffiSuccessRate: rp.ffiCalls ? _round2(rp.ffiSuccesses / rp.ffiCalls) : 0,
    nativeCalls: rp.nativeCalls,

    // Call counts
    alphaRenCalls: rp.alphaRenCalls,
    composeSubCalls: rp.composeSubCalls,
    mapApplyCalls: rp.mapApplyCalls,
    applyPremisesCalls: rp.applyPremisesCalls,
    freeCountCalls: rp.freeCountCalls,

    // Per-clause distributional stats
    perClauseTimes: _stats(perClauseTimes.slice()),
    perClauseSolutions: _stats(perClauseSols.slice()),
    perClauseSearchNodes: _stats(perClauseNodes.slice()),
    perClauseUnifies: _stats(perClauseUnifies.slice()),

    // Histograms: [<1ms, 1-10, 10-100, 100-1000, ≥1000]
    timeHistogram: _histogram(perClauseTimes, tsBuckets),
    timeHistogramBuckets: tsBuckets,
    solutionsHistogram: _histogram(perClauseSols, solBuckets),
    solutionsHistogramBuckets: solBuckets,
    searchNodesHistogram: _histogram(perClauseNodes, nodeBuckets),
    searchNodesHistogramBuckets: nodeBuckets,

    // Top hotspots
    topClauses: topN,

    // Coverage / residual
    attributedMs: _round2(attributedMs),
    unattributedMs: _round2(Math.max(0, tTabAcc - attributedMs)),
    attributionRatio: tTabAcc > 0 ? _round2(attributedMs / tTabAcc) : 0,
  });

  // Structural sub-paths (leaves for sunburst/streamgraph).
  // Each measures time in a specific internal activity; together they partition
  // tabling wall-clock with a residual "other" leaf to make the sunburst honest.
  emit('load/compose/grade0-facts/tabling/index-build', rp.indexMs, {
    calls: rp.indexCalls,
  });
  emit('load/compose/grade0-facts/tabling/select-goal', rp.selectGoalMs, {
    searchNodes: rp.searchNodes,
    freeCountCalls: rp.freeCountCalls,
    avgGoalsInspected: rp.searchNodes ? _round2(rp.freeCountCalls / rp.searchNodes) : 0,
  });
  emit('load/compose/grade0-facts/tabling/map-apply', rp.mapApplyMs, {
    calls: rp.mapApplyCalls,
    avgUs: rp.mapApplyCalls ? _round2((rp.mapApplyMs * 1000) / rp.mapApplyCalls) : 0,
  });
  emit('load/compose/grade0-facts/tabling/alpha-rename', rp.alphaRenMs, {
    calls: rp.alphaRenCalls,
    avgUs: rp.alphaRenCalls ? _round2((rp.alphaRenMs * 1000) / rp.alphaRenCalls) : 0,
  });
  emit('load/compose/grade0-facts/tabling/unify', rp.unifyMs, {
    attempts: rp.unifyAttempts,
    succeeded: rp.unifySucceeded,
    failed: rp.unifyFailures,
    successRate: rp.unifyAttempts ? _round2(rp.unifySucceeded / rp.unifyAttempts) : 0,
    avgUs: rp.unifyAttempts ? _round2((rp.unifyMs * 1000) / rp.unifyAttempts) : 0,
  });
  emit('load/compose/grade0-facts/tabling/compose-sub', rp.composeSubMs, {
    calls: rp.composeSubCalls,
    avgUs: rp.composeSubCalls ? _round2((rp.composeSubMs * 1000) / rp.composeSubCalls) : 0,
  });
  emit('load/compose/grade0-facts/tabling/apply-premises', rp.applyPremisesMs, {
    calls: rp.applyPremisesCalls,
  });
  emit('load/compose/grade0-facts/tabling/backchain', rp.backchainMs, {
    calls: rp.backchainCalls,
    successes: rp.backchainSuccesses,
    successRate: rp.backchainCalls ? _round2(rp.backchainSuccesses / rp.backchainCalls) : 0,
  });
  emit('load/compose/grade0-facts/tabling/ffi', rp.ffiMs, {
    calls: rp.ffiCalls,
    successes: rp.ffiSuccesses,
    successRate: rp.ffiCalls ? _round2(rp.ffiSuccesses / rp.ffiCalls) : 0,
  });
  emit('load/compose/grade0-facts/tabling/native', rp.nativeMs, {
    calls: rp.nativeCalls,
  });
  emit('load/compose/grade0-facts/tabling/apply-head', applyHeadMs, {
    facts: producedFacts,
  });
  emit('load/compose/grade0-facts/tabling/canonicalize', canonMs, {
    facts: producedFacts,
    enabled: !!canonicalize,
  });
  emit('load/compose/grade0-facts/tabling/other', Math.max(0, tTabAcc - attributedMs), {
    premiseClauses,
    note: 'search loop overhead + control flow not attributed to a specific sub-activity',
  });

  // NOTE: top-K clauses are available in the rollup's `topClauses` meta;
  // we do NOT emit per-clause leaves because clause wall-clock overlaps
  // with the sub-activity wall-clock (a clause's time IS unify + backchain
  // + compose-sub + etc. for that clause). Emitting both would double-count
  // in any renderer that sums leaves (sunburst, table totals).
}

export { newPairProf, emitFuseScanDetect, emitFuseProfile, emitTablingProfile, _stats, _histogram, _round2 };
export default { newPairProf, emitFuseScanDetect, emitFuseProfile, emitTablingProfile };
