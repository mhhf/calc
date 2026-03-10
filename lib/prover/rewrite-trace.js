/**
 * Flat Rewriting Certificates — compact forward execution certificates.
 *
 * A rewriting certificate records each forward step as a flat record:
 * consumed facts, produced facts, rule identity. This is NOT an ILL
 * proof term — it's a resource-accounting certificate where soundness
 * comes from multiset conservation.
 *
 * Two certificate forms coexist:
 * - ILL proof terms (backward prover, checked by checkTerm)
 * - Rewriting certificates (forward engine, checked by checkRewriteTrace)
 *
 * Inter-derivable for the forward fragment:
 * - flat → ILL: buildGuidedTerm (constructive, already implemented)
 * - ILL → flat: buildRewriteTrace (this module)
 *
 * See TODO_0084 §Theoretical Analysis for soundness proof.
 */

const { applyIndexed } = require('../kernel/substitute');

/**
 * Build a flat rewriting trace from an enriched forward trace.
 *
 * Each step record is self-contained: consumed hashes, produced hashes,
 * rule identity. No tree nesting, no obligations, no nonces.
 *
 * @param {Array} trace - Forward trace with evidence (from forward.run
 *   with { trace: true, evidence: true })
 * @returns {Array<Object>} Flat certificate — array of step records:
 *   { consumed, produced, ruleHash, loliHash, evidence, name }
 */
function buildRewriteTrace(trace) {
  return trace.map(entry => {
    const { rule, theta, slots, persistentEvidence, loliHash } = entry;
    return {
      consumed: Object.keys(entry.consumed).map(Number),
      produced: (rule.consequent.linear || []).map(p => applyIndexed(p, theta, slots)),
      ruleHash: rule.hash || null,
      loliHash: loliHash || null,
      evidence: (persistentEvidence || []).map(e => e.goal),
      name: rule.name,
    };
  });
}

/**
 * Verify a flat rewriting trace: resource accounting check.
 *
 * Walks the trace left-to-right, maintaining a multiset (Map<hash, count>).
 * Each step consumes from and produces into the multiset. If any consumed
 * fact is missing, verification fails.
 *
 * Does NOT verify pattern matching (consumed matches rule antecedent).
 * That verification is done by the full ILL proof term path. This function
 * verifies the weaker property: resource conservation.
 *
 * @param {Map<number, number>} delta0 - Initial linear context (hash → count)
 * @param {Array} trace - Flat certificate from buildRewriteTrace
 * @returns {{ valid: boolean, remaining?: Map, error?: string }}
 */
function checkRewriteTrace(delta0, trace) {
  const ctx = new Map(delta0);
  for (let i = 0; i < trace.length; i++) {
    const step = trace[i];
    for (const h of step.consumed) {
      const c = ctx.get(h);
      if (!c) {
        return { valid: false, error: `step ${i} (${step.name}): consumed ${h} not in context` };
      }
      if (c === 1) ctx.delete(h);
      else ctx.set(h, c - 1);
    }
    for (const h of step.produced) {
      ctx.set(h, (ctx.get(h) || 0) + 1);
    }
  }
  return { valid: true, remaining: ctx };
}

module.exports = { buildRewriteTrace, checkRewriteTrace };
