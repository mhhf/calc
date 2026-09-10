/**
 * Forward execution-tree checker (TODO_0045) — the forward twin of
 * lib/prover/kernel.js.
 *
 * `explore()` (lib/engine/explore.js) builds an execution tree T for the
 * judgment Σ; Δ ⊢_fwd T (THY_0035, the parametric forward-chaining
 * judgment; TODO_0045 §2 the typed term language). This module CHECKS one
 * such tree: it re-derives every firing from the PROGRAM'S declarative
 * rule data under the recorded substitution θ, and threads the linear
 * multiset Δ and persistent set Φ down the tree — the untimed
 * generalization of the timed face's per-run `certifyRun`
 * (elaborate-trace.js) to the WHOLE explore() tree with all eight
 * constructors.
 *
 * Trust boundary (Approach B, TODO_0045 §3.3, generalized to the tree):
 * `explore()`, findAllMatches, tryMatch, the strategy stack, mutation+undo
 * — none are trusted. The witness is only θ (plus the ⊕-alternative index
 * and the fired loli token). Everything else is re-derived here from the
 * rule patterns + the threaded state; a step whose consumed patterns are
 * not present, whose produced facts the rule does not license, or whose
 * persistent guards are unprovable, is REJECTED.
 *
 * SOUNDNESS, not completeness. The tree's soundness claim is "every leaf
 * is reachable from Δ₀ by valid forward steps"; the verified per-edge
 * re-derivation plus the threaded Δ establishes exactly that, and the
 * terminal state-consistency check binds each recorded reachable state to
 * the derivation that reaches it. The tree's COMPLETENESS claims —
 * quiescence at a `leaf`, justified pruning at a `dead`, all-rules-present
 * at a `branch` — are negative/universal assertions a checker cannot
 * witness (TODO_0045 §5.4); they rest on `findAllMatches` and the pruner,
 * and are the subject of TODO_0042. So `leaf`/`cycle`/`bound`/`memo`/`dead`
 * are terminal here: adding any of them introduces NO leaf, hence no
 * unsound reachable state.
 *
 * The step re-derivation shares its rule-record adaptation and clause-only
 * persistent-goal certificates with the timed checker (programFromCalc /
 * checkGoalCert): the SEARCH for a persistent-goal certificate is untrusted
 * (the engine backchainer), the CHECK (checkGoalCert) is trusted — the
 * numeric FFI never enters the verification path.
 */

import Store from '../kernel/store.js';
import { subst, deriveLoliRecord, countOf } from './timed/fire-check.js';
import { checkGoalCert } from './sld-check.js';

const UNBOUND_TAGS = new Set(['metavar', 'freevar']);

/** Does a term still carry an unbound metavar/freevar after grounding? */
function hasUnbound(h) {
  if (!Store.isTerm(h)) return false;
  if (UNBOUND_TAGS.has(Store.tag(h))) return true;
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && hasUnbound(c)) return true;
  }
  return false;
}

// ── plain-state multiset helpers ────────────────────────────────────
// Δ is a Map(hash → count); Φ is a Set(hash). The tree's terminal states
// arrive as plain { linear: {hash:count}, persistent: {hash:true} }
// objects (the orchestrator normalizes engine State via toObject).

// A checker never trusts representation equality: facts are compared MODULO
// THEORY. Every fact the checker reads — initial, produced, consumed,
// recorded terminal — is routed through the composed canonicalizer (a
// fixpoint fold to a canonical representative, in the TCB), so two
// theory-equal facts collapse to one hash and all multiset comparisons are
// exact whether the live state stored a raw or canonical representative.
function linMap(obj, canon) {
  const m = new Map();
  for (const k in obj || {}) {
    const c = obj[k]; if (c <= 0) continue;
    const h = canon(Number(k));
    m.set(h, (m.get(h) || 0) + c);
  }
  return m;
}
function perSet(obj, canon) {
  const s = new Set();
  for (const k in obj || {}) s.add(canon(Number(k)));
  return s;
}
function mapEqDiff(a, b) {
  // returns null if equal, else a short human diff
  if (a.size !== b.size) {
    return `size ${a.size} ≠ ${b.size}`;
  }
  for (const [h, c] of a) if (b.get(h) !== c) return `${h}×${c} ≠ ×${b.get(h) || 0}`;
  return null;
}
function setEqDiff(a, b) {
  if (a.size !== b.size) return `size ${a.size} ≠ ${b.size}`;
  for (const h of a) if (!b.has(h)) return `missing ${h}`;
  return null;
}

/**
 * Re-derive one firing and thread the state.
 *
 * @param {Object} pr - the program rule record (programFromCalc/adaptRule):
 *   { slots, consume, read, produce, producePers, goals, alts, wholeBind }
 * @param {Object} step - the edge witness: { theta:[hash], alt?, loliHash? }
 * @param {Map} lin - the incoming linear multiset (NOT mutated)
 * @param {Set} per - the incoming persistent set (NOT mutated)
 * @param {Object} deps - { program, roles }
 * @returns {{ lin, per } | { error } | { unsupported }}
 */
function stepForward(pr, step, lin, per, deps) {
  const { program, roles, canon } = deps;
  if (pr.unsupported) return { unsupported: pr.unsupported };
  if (pr.wholeBind && pr.wholeBind.length) {
    return { unsupported: 'whole-bind (!_W) premise — timed feature, untimed checker' };
  }

  const slots = pr.slots || [];
  const theta = step.theta || [];
  if (theta.length !== slots.length) {
    return { error: `theta arity mismatch: rule has ${slots.length} slot(s), witness has ${theta.length}` };
  }
  const bind = new Map();
  for (let i = 0; i < slots.length; i++) {
    if (theta[i] !== undefined && theta[i] !== null) bind.set(slots[i], theta[i]);
  }
  const ground = (h) => { const g = subst(h, bind); return hasUnbound(g) ? null : canon(g); };
  const groundAll = (hs, what) => {
    const out = [];
    for (const h of hs || []) {
      const g = ground(h);
      // An antecedent metavar the recorded θ does not bind is NOT a forged
      // tree — matching always binds antecedent metavars. It means the
      // checker cannot model this rule's slot layout: a grade-0-specialized
      // / fused rule binds some positions at COMPILE time (the bytecode
      // specialization), outside the runtime θ. Report unsupported (the
      // firing is not certified), never error (which would falsely brand a
      // valid exploration unsound). The EVM guided profile certifies these
      // per-path via buildGuidedTerm/checkTerm instead.
      if (g === null) return { unsupported: `unbound slot in ${what} pattern (grade-0-specialized / fused rule)` };
      out.push(g);
    }
    return { out };
  };
  const bail = (r) => r.error || r.unsupported;

  // consumed = antecedent linear patterns (minus read) under θ; must all be
  // present in Δ (multiplicity respected), removed on the way down.
  const cg = groundAll(pr.consume, 'consume');
  if (bail(cg)) return cg;
  const nextLin = new Map(lin);
  for (const g of cg.out) {
    const c = nextLin.get(g) || 0;
    if (c < 1) return { error: `consumed fact not available in Δ (${g})` };
    if (c === 1) nextLin.delete(g); else nextLin.set(g, c - 1);
  }
  // reads: present after consumption, NOT removed.
  const rg = groundAll(pr.read, 'read');
  if (bail(rg)) return rg;
  for (const g of rg.out) {
    if ((nextLin.get(g) || 0) < 1) return { error: `read fact not available in Δ (${g})` };
  }

  // persistent goals: Φ-membership, else a clause-only SLD certificate the
  // checker re-derives and verifies (never the engine's FFI/state oracle).
  const gg = groundAll(pr.goals, 'goal');
  if (bail(gg)) return gg;
  for (const g of gg.out) {
    if (per.has(g)) continue;
    const cert = program.certifyGoal ? program.certifyGoal(g) : null;
    if (cert) {
      const r = checkGoalCert(cert, g, program.clauses, program.definitions);
      if (!r.error) continue;
      return { error: `persistent goal certificate: ${r.error}` };
    }
    return { error: `unprovable persistent goal (${g})` };
  }

  // the fired consequent alternative (⊕): the witness names one branch.
  let produce = pr.produce, producePers = pr.producePers;
  if (step.alt != null && pr.alts) {
    if (!pr.alts[step.alt]) return { error: `witness names alternative ${step.alt} but rule has none` };
    produce = pr.alts[step.alt].produce;
    producePers = pr.alts[step.alt].producePers;
  } else if (step.alt != null && step.alt !== 0) {
    return { error: `witness names alternative ${step.alt} but rule has a single consequent` };
  }

  // produced linear facts (counted parcels !_k A expand to k copies — a no-op
  // for ILL, live for graded consequents) added to Δ. The exponential tag
  // comes from roles (never a hardcoded connective name); absent ⇒ the
  // counted-parcel branch is inert and every produce is a plain fact.
  const expTag = roles && roles.exponential;
  const pg = groundAll(produce, 'produce');
  if (bail(pg)) return pg;
  for (const g of pg.out) {
    if (Store.tag(g) === expTag && countOf(Store.child(g, 0)) !== null) {
      const k = countOf(Store.child(g, 0));
      const body = canon(Store.child(g, 1));
      for (let i = 0n; i < k; i++) nextLin.set(body, (nextLin.get(body) || 0) + 1);
    } else {
      nextLin.set(g, (nextLin.get(g) || 0) + 1);
    }
  }
  // persistent conclusions added to Φ.
  const ppg = groundAll(producePers, 'producePers');
  if (bail(ppg)) return ppg;
  const nextPer = new Set(per);
  for (const g of ppg.out) nextPer.add(g);

  return { lin: nextLin, per: nextPer };
}

/** Resolve the rule record an edge fires: a program rule by name, or a
 *  possessed loli token derived from its own structure (Phase 6c / the D
 *  component of THY_0035). */
function resolveRule(edge, deps) {
  const { program, roles } = deps;
  if (edge.step && edge.step.loliHash != null) {
    const rec = deriveLoliRecord(edge.step.loliHash, roles || {});
    if (!rec) return { unsupported: `loli continuation is not a ground rule token` };
    return { pr: rec };
  }
  const pr = program.rules[edge.rule];
  if (!pr) return { error: `unknown program rule '${edge.rule}'` };
  return { pr };
}

/**
 * Check a whole execution tree produced by explore(evidence:true).
 *
 * @param {Object} tree - the explore() return value; terminal `.state`
 *   entries must be PLAIN { linear:{hash:count}, persistent:{hash:true} }
 *   (normalize engine State with toObject before calling).
 * @param {Object} opts - { program, roles, initial }
 *   program: programFromCalc(engineCalc) — { rules, certifyGoal, clauses, definitions }
 *   roles: calculus.roles (connective-tag record)
 *   initial: the initial state, PLAIN { linear, persistent }
 *   canonicalize: the composed theory canonicalizer (hash→hash fixpoint) —
 *     null ⇒ identity; facts are compared modulo theory through it.
 * @returns {{ valid, errors, unsupported? , leaves }}
 *   `leaves` = count of quiescent leaves reached (the reachable-state set size).
 */
function checkForwardTree(tree, { program, roles, initial, canonicalize }) {
  const errors = [];
  const unsupported = new Set();
  let leaves = 0;

  const canon = canonicalize || ((h) => h);
  const deps = { program, roles, canon };
  const path = [];   // rule names, for error context

  // compare a terminal node's recorded state against the threaded Δ/Φ.
  const checkTerminal = (kind, node, lin, per) => {
    if (!node.state) { errors.push(`${here()} ${kind}: no recorded state`); return; }
    const ldiff = mapEqDiff(lin, linMap(node.state.linear, canon));
    if (ldiff) errors.push(`${here()} ${kind}: linear state mismatch (${ldiff})`);
    const pdiff = setEqDiff(per, perSet(node.state.persistent, canon));
    if (pdiff) errors.push(`${here()} ${kind}: persistent state mismatch (${pdiff})`);
  };
  const here = () => (path.length ? `at [${path.join(' → ')}]` : 'at root');

  function walk(node, lin, per) {
    switch (node.type) {
      case 'leaf':
        leaves++;
        checkTerminal('leaf', node, lin, per);
        return;
      case 'cycle': case 'bound': case 'memo':
        // terminal: no leaf claim (soundness vacuous). The recorded state
        // must still equal the threaded state — a back-edge/revisit/bound
        // is taken AT the current state.
        checkTerminal(node.type, node, lin, per);
        return;
      case 'dead':
        // a ⊕/tell alternative the pruner cut as UNSAT — contributes no
        // leaf; vacuously sound. Whether the cut was JUSTIFIED is a
        // completeness concern (TODO_0042), not checked here.
        return;
      case 'branch': {
        for (const edge of node.children || []) {
          const child = edge.child;
          if (!child) { errors.push(`${here()} branch: edge without child`); continue; }
          if (child.type === 'dead') continue;         // pruned alternative
          if (!edge.step) {
            errors.push(`${here()} branch edge '${edge.rule}': no step witness ` +
              `(explore must run with { evidence: true })`);
            continue;
          }
          const rr = resolveRule(edge, deps);
          if (rr.unsupported) { unsupported.add(rr.unsupported); continue; }
          if (rr.error) { errors.push(`${here()} ${rr.error}`); continue; }
          const stepped = stepForward(rr.pr, edge.step, lin, per, deps);
          if (stepped.unsupported) { unsupported.add(stepped.unsupported); continue; }
          if (stepped.error) {
            errors.push(`${here()} step '${edge.rule}': ${stepped.error}`);
            continue;
          }
          path.push(edge.rule);
          walk(child, stepped.lin, stepped.per);
          path.pop();
        }
        return;
      }
      default:
        errors.push(`${here()}: unknown tree node type '${node.type}'`);
    }
  }

  walk(tree, linMap(initial.linear, canon), perSet(initial.persistent, canon));

  const result = { valid: errors.length === 0, errors, leaves };
  if (unsupported.size > 0) result.unsupported = [...unsupported].sort();
  return result;
}

export { checkForwardTree, stepForward, hasUnbound };
export default { checkForwardTree };
