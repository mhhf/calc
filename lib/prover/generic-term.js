/**
 * Generic Proof Terms (Layer 1)
 *
 * Implements the Curry-Howard correspondence for CALC's ILL prover.
 * Two phases, both driven by rule descriptors — no manual term definitions:
 *
 * Phase 1 (signatures): Derives proof term constructor shapes from rule
 *   descriptors at calculus load time. One constructor per inference rule,
 *   following Harper-Honsell-Plotkin (1993, LF) — adequacy by construction.
 *
 * Phase 2 (extraction): Walks completed ProofTrees post-hoc and builds
 *   GenericTerm objects. No changes to the prover search loop required.
 *
 * Phase 3 (forward terms): Builds CLF monadic let-chains from forward
 *   traces and explore trees (see also guided-term.js for ILL-verified terms).
 *
 * Descriptor fields → term shape:
 *   side='l'               → first arg is principal z (consumed from antecedent)
 *   binding='eigenvariable' → fresh variable arg a (forall_r, exists_l)
 *   binding='metavar'       → witness term arg s (forall_l, exists_r)
 *   premises[i].linear     → bound variables x_i scoped over sub-proof (in Delta)
 *   premises[i].cartesian  → bound variables y_i moved to Gamma
 *
 * Other descriptor fields (contextFlow, modeShift, arity, connective,
 * emptyLinear, requiresSuccedentTag) are for rule application/focusing,
 * not term shape — they are consumed by rule-interpreter.js and generic.js.
 *
 * See doc/documentation/proof-terms.md for the full constructor catalog.
 */

const Seq = require('../kernel/sequent');
const Store = require('../kernel/store');

/**
 * Arg types for a generic term signature.
 * @typedef {'principal'|'eigenvariable'|'witness'|'subproof'} ArgKind
 * @typedef {{ kind: ArgKind, name: string, bindings?: string[] }} ArgSpec
 * @typedef {{ constructor: string, args: ArgSpec[] }} TermSignature
 */

/**
 * Compute the generic term signature for a single rule.
 *
 * @param {{ name: string, descriptor: Object, structural?: boolean, numPremises: number }} rule
 * @returns {TermSignature}
 */
function termSig(rule) {
  const d = rule.descriptor;
  const args = [];

  // Left rules: first arg is the principal formula consumed from antecedent
  if (d.side === 'l') {
    args.push({ kind: 'principal', name: 'z' });
  }

  // Quantifier bindings come before premises
  if (d.binding === 'eigenvariable') {
    args.push({ kind: 'eigenvariable', name: 'a' });
  } else if (d.binding === 'metavar') {
    args.push({ kind: 'witness', name: 's' });
  }

  // Each premise contributes bound variables + a sub-proof
  for (let i = 0; i < d.premises.length; i++) {
    const p = d.premises[i];
    const bindings = [
      ...(p.linear || []).map(idx => `x${idx}`),
      ...(p.cartesian || []).map(idx => `y${idx}`)
    ];
    args.push({ kind: 'subproof', name: `u${i}`, bindings });
  }

  return { constructor: rule.name, args };
}

// Hardcoded signatures for structural rules and axioms that live outside
// the descriptor framework (no connective, no .rules file entry).
// copy: structural (contraction from Gamma), ffi: trusted axiom,
// unreachable: dead branch placeholder for oplus case analysis.
const SPECIAL_SIGNATURES = {
  id:          { constructor: 'id', args: [{ kind: 'principal', name: 'x' }] },
  copy:        { constructor: 'copy', args: [
    { kind: 'principal', name: 'u' },
    { kind: 'subproof', name: 'u0', bindings: ['x0'] }
  ]},
  ffi:         { constructor: 'ffi', args: [
    { kind: 'witness', name: 'name' },
    { kind: 'witness', name: 'args' },
    { kind: 'witness', name: 'result' }
  ]},
  unreachable: { constructor: 'unreachable', args: [
    { kind: 'witness', name: 'reason' }
  ]}
};

/**
 * Build a signature map for all rules in a calculus.
 *
 * Registers both canonical names (e.g., "absorption") and spec-key aliases
 * (e.g., "bang_l"). The prover's proof trees use spec keys (connective_side)
 * because ruleName() in generic.js generates them from formula tags — so
 * extractTerm needs both keys to look up signatures.
 *
 * @param {Object} rules - calculus.rules (name → rule)
 * @returns {{ [ruleName: string]: TermSignature }}
 */
function sigMap(rules) {
  const sigs = {};

  for (const [name, rule] of Object.entries(rules)) {
    if (SPECIAL_SIGNATURES[name]) {
      sigs[name] = SPECIAL_SIGNATURES[name];
      continue;
    }

    if (!rule.descriptor) continue;

    const sig = termSig(rule);
    sigs[name] = sig;

    // Register spec-key alias: connective_side (e.g., bang_l for absorption)
    // The prover uses these names in proof trees instead of the rule name
    const d = rule.descriptor;
    if (d.connective && d.side) {
      const specKey = `${d.connective}_${d.side}`;
      if (specKey !== name && !sigs[specKey]) {
        sigs[specKey] = sig;
      }
    }
  }

  return sigs;
}

/**
 * Compute the flattened arity of a signature (total child count in Store node).
 * Bindings are not separate children — they are encoded as de Bruijn indices
 * within the sub-proof. The flattened arity counts: principals, witnesses,
 * eigenvariables, and sub-proofs.
 */
function flattenedArity(sig) {
  return sig.args.length;
}

/**
 * Format a signature as the generic notation string from §2.7.
 * e.g. "tensor_l(z, x0 x1 -> u0)"
 */
function formatSignature(sig) {
  const parts = sig.args.map(a => {
    if (a.kind === 'subproof' && a.bindings && a.bindings.length > 0) {
      return `${a.bindings.join(' ')} -> ${a.name}`;
    }
    return a.name;
  });
  return `${sig.constructor}(${parts.join(', ')})`;
}

// =============================================================================
// Phase 2: Term Extraction from ProofTrees
//
// Post-hoc extraction: the prover builds proof trees as normal, then
// extractTerm walks them to produce GenericTerm objects. This separation
// keeps the search loop clean — no term-building in the hot path.
//
// GenericTerms are plain JS objects (not Store-interned). Content-addressing
// in Store is deferred to when/if terms need sharing or serialization.
// =============================================================================

/**
 * Generic proof term representation.
 *
 * Each node corresponds to exactly one ILL inference rule. The rule name
 * IS the constructor (LF adequacy: bijection between proofs and terms).
 *
 * @typedef {Object} GenericTerm
 * @property {string} rule - Constructor name (= rule name)
 * @property {number|null} principal - Formula hash of principal (left rules, id, copy)
 * @property {GenericTerm[]} subterms - Recursive sub-proof terms (one per premise)
 * @property {number|null} [witness] - Witness term hash (exists_r, forall_l)
 * @property {number|null} [eigenvariable] - Eigenvariable hash (exists_l, forall_r)
 * @property {GenericTerm} [evidence] - For monad_r: the inner proof (guided mode)
 */

/**
 * Find the principal formula for a left rule by scanning the conclusion's
 * linear context for a formula whose tag matches the rule's connective.
 *
 * Content-addressed: if duplicates exist they have the same hash, so any match works.
 */
function findPrincipal(conclusion, connective) {
  const linear = Seq.getContext(conclusion, 'linear');
  for (const h of linear) {
    if (Store.isTerm(h) && Store.tag(h) === connective) return h;
  }
  return null;
}

/**
 * Find the principal for identity: a formula in linear matching the succedent.
 * Content-addressed: equal formulas = equal hashes, so this is O(1) per formula.
 *
 * The focused prover resolves metavars in proof trees (applyThetaToTree),
 * so identity nodes always have hash-equal linear formula and succedent.
 */
function idPrincipal(conclusion) {
  const linear = Seq.getContext(conclusion, 'linear');
  const succ = conclusion.succedent;
  for (const h of linear) {
    if (h === succ) return h;
  }
  return null;
}

/**
 * Find the principal for copy: a cartesian formula that was added to linear.
 * The premise linear contains the copied formula; it also exists in cartesian.
 */
function findCopyPrincipal(conclusion, premise) {
  const cart = Seq.getContext(conclusion, 'cartesian');
  const premiseLinear = Seq.getContext(premise, 'linear');
  const conclLinear = Seq.getContext(conclusion, 'linear');

  // Build multiset of conclusion's linear
  const conclCounts = {};
  for (const h of conclLinear) conclCounts[h] = (conclCounts[h] || 0) + 1;

  // The copied formula is in premise linear, in cartesian, but has extra
  // count vs conclusion linear
  const premCounts = {};
  for (const h of premiseLinear) premCounts[h] = (premCounts[h] || 0) + 1;

  const cartSet = new Set(cart);
  for (const h of Object.keys(premCounts)) {
    const hash = Number(h);
    if (cartSet.has(hash) && (premCounts[h] > (conclCounts[h] || 0))) {
      return hash;
    }
  }

  // Fallback: first cartesian formula
  return cart.length > 0 ? cart[0] : null;
}

/**
 * Extract a generic proof term from a completed ProofTree.
 *
 * Post-hoc extraction: walks the tree built by the prover and produces
 * a GenericTerm for each node. No changes to the prover itself.
 *
 * @param {import('./pt').ProofTree} proofTree - Completed (proven) proof tree
 * @param {Object} calculus - Loaded calculus with rules
 * @returns {GenericTerm|null}
 */
function extractTerm(proofTree, calculus) {
  if (!proofTree || !proofTree.proven) return null;

  const rule = proofTree.rule;
  const concl = proofTree.conclusion;
  const premises = proofTree.premises;

  // Identity (id, id_+, id_- are all the same for term extraction)
  if (rule === 'id' || rule === 'id_+' || rule === 'id_-') {
    return {
      rule: 'id',
      principal: idPrincipal(concl),
      subterms: []
    };
  }

  // Copy (structural, no connective — special case)
  if (rule === 'copy') {
    const principal = findCopyPrincipal(concl, premises[0].conclusion);
    return {
      rule: 'copy',
      principal,
      subterms: [extractTerm(premises[0], calculus)]
    };
  }

  // Mode switch (monad_r) — the forward engine ran to quiescence.
  // Three evidence levels depending on execution profile:
  //   'guided':  state.monadicTerm is a complete ILL proof term (verified by check-term.js)
  //   'full':    state.monadicTerm is an opaque CLF let-chain (informational, not verified)
  //   default:   state.trace is the raw forward trace (string or structured)
  if (rule === 'monad_r') {
    const term = {
      rule: 'monad_r',
      principal: null,
      subterms: []
    };
    if (proofTree.state?.monadicTerm) {
      term.evidence = proofTree.state.monadicTerm;
    } else {
      term.evidence = proofTree.state?.trace || null;
    }
    return term;
  }

  // Standard rules: look up descriptor.
  // The prover records spec keys (e.g., "bang_l") in proof trees, not canonical
  // rule names (e.g., "absorption"), because generic.js:ruleName() generates
  // them from formula tags. So we try direct lookup first, then scan for
  // a matching connective_side.
  let ruleObj = calculus.rules[rule];
  if (!ruleObj) {
    for (const r of Object.values(calculus.rules)) {
      if (r.descriptor && r.descriptor.connective && r.descriptor.side) {
        if (`${r.descriptor.connective}_${r.descriptor.side}` === rule) {
          ruleObj = r;
          break;
        }
      }
    }
  }
  if (!ruleObj || !ruleObj.descriptor) return null;
  const d = ruleObj.descriptor;

  // Find principal for left rules
  let principal = null;
  if (d.side === 'l') {
    principal = findPrincipal(concl, d.connective);
  }

  // Recursively extract sub-terms
  const subterms = premises.map(p => extractTerm(p, calculus));

  // Quantifier witness/eigenvariable extraction
  let witness = null;
  let eigenvariable = null;
  if (d.binding === 'metavar' || d.binding === 'eigenvariable') {
    const formula = d.side === 'l' ? principal : concl.succedent;
    if (formula && premises.length > 0) {
      const premConclusion = premises[0].conclusion;
      if (d.binding === 'eigenvariable') {
        // Eigenvariable is a fresh evar — scan premise for evars
        // not in conclusion. Evars are NOT metavars, so they survive
        // theta resolution and findFreshVar still works.
        eigenvariable = findFreshVar(concl, premConclusion);
      } else if (d.binding === 'metavar') {
        // Witness: the value that replaced bound(0) in the quantifier body.
        // After theta resolution, metavars are resolved to ground values.
        // Extract structurally by matching body against premise succedent.
        const body = Store.child(formula, 0);
        const instance = d.side === 'r'
          ? premConclusion.succedent
          : findOpenedFormula(premConclusion, d.connective);
        if (body && instance) {
          witness = boundVal(body, instance);
        }
      }
    }
  }

  const term = { rule, principal, subterms };
  if (witness !== null) term.witness = witness;
  if (eigenvariable !== null) term.eigenvariable = eigenvariable;
  return term;
}

/**
 * Find a fresh variable (evar or metavar) introduced in the premise
 * that doesn't appear in the conclusion. Used for quantifier rules.
 *
 * @returns {number|null} Hash of the fresh variable, or null
 */
function findFreshVar(conclusion, premConclusion) {
  const conclVars = collectVarHashes(conclusion);
  const premVars = collectVarHashes(premConclusion);

  for (const h of premVars) {
    if (!conclVars.has(h)) return h;
  }
  return null;
}

/**
 * Collect all evar and freevar hashes reachable from a sequent.
 */
function collectVarHashes(seq) {
  const vars = new Set();
  const visit = (h) => {
    if (!Store.isTerm(h)) return;
    const tag = Store.tag(h);
    if (tag === 'evar' || tag === 'freevar' || tag === 'metavar') {
      vars.add(h);
      return;
    }
    const ar = Store.arity(h);
    for (let i = 0; i < ar; i++) {
      visit(Store.child(h, i));
    }
  };

  for (const ctx of Object.values(seq.contexts)) {
    for (const h of ctx) visit(h);
  }
  if (seq.succedent) visit(seq.succedent);
  return vars;
}

/**
 * Extract the value that replaced bound(0) in a quantifier body.
 * Structurally matches pattern (with bound(0)) against instance (ground).
 *
 * E.g., body = p(bound(0)), instance = p(a) → returns hash(a).
 *
 * This is the inverse of debruijnSubst: given body and body[witness/bound(0)],
 * recover witness. Works because the focused prover's applyThetaToTree (now
 * MetaCtx.resolveTree) ensures the instance is fully ground by extraction time.
 *
 * @param {number} pattern - Quantifier body (contains bound(0))
 * @param {number} instance - Premise formula (ground, after theta resolution)
 * @returns {number|null}
 */
function boundVal(pattern, instance) {
  if (!Store.isTerm(pattern)) return null;
  if (Store.tag(pattern) === 'bound') return instance;
  if (!Store.isTerm(instance)) return null;
  if (Store.tag(pattern) !== Store.tag(instance)) return null;
  const ar = Store.arity(pattern);
  for (let i = 0; i < ar; i++) {
    const r = boundVal(Store.child(pattern, i), Store.child(instance, i));
    if (r !== null) return r;
  }
  return null;
}

/**
 * Find the opened formula in a premise after a left quantifier rule.
 * The quantifier was consumed; the opened body (with metavar resolved) is in linear.
 * Match by comparing: for each linear formula, check if it structurally matches
 * the quantifier body shape.
 */
function findOpenedFormula(premConclusion, connective) {
  const linear = Seq.getContext(premConclusion, 'linear');
  // The opened formula replaces the quantifier — it won't have the quantifier tag
  for (const h of linear) {
    if (Store.isTerm(h) && Store.tag(h) !== connective) return h;
  }
  return linear.length > 0 ? linear[0] : null;
}

// =============================================================================
// Phase 3: Forward Term Builder — CLF Monadic Expressions
//
// These builders produce OPAQUE monadic terms for the 'full' execution profile.
// Rule names become constructors, but the internal structure is not verified
// by check-term.js — rightFocus success + empty residual suffices.
//
// For VERIFIED terms (every step = ILL derivation), see guided-term.js which
// uses enriched traces to build copy → loli_l → tensor_r → monad_l chains
// that the type checker can fully recurse into.
// =============================================================================

/**
 * Build a CLF monadic expression from a forward trace + rightFocus term.
 *
 * Each forward step becomes a monadic let-binding (Watkins et al. 2004):
 *   let {p} = rule(args) in ...continuation...
 *
 * The full trace is a nested chain terminated by the rightFocus term:
 *   let {p0} = r0(a0) in
 *   let {p1} = r1(a1) in
 *   ...
 *   rfTerm                  -- rightFocus decomposition (return value)
 *
 * Note: these terms record WHAT happened (rule name + consumed facts) but not
 * HOW it's justified in ILL. For the 'full' profile this is sufficient —
 * the kernel returns { valid: true, unverified: 'modeSwitch' }.
 *
 * @param {Array<{rule: string, consumed: Object}>} trace - Structured forward trace
 * @param {GenericTerm} rfTerm - rightFocus decomposition term (terminal)
 * @returns {GenericTerm}
 */
function monadicTerm(trace, rfTerm) {
  // Build from the end: each step wraps the continuation
  let term = rfTerm;
  for (let i = trace.length - 1; i >= 0; i--) {
    const step = trace[i];
    term = {
      rule: step.rule,
      principal: null,
      subterms: [term],
      consumed: step.consumed
    };
  }
  return term;
}

/**
 * Build proof terms from an explore tree (opaque, 'full' profile).
 *
 * Maps explore tree nodes to proof term fragments:
 *   leaf   → rightFocusTerm (succedent decomposition)
 *   branch → let {p} = rule(args) in child_term
 *   dead   → unreachable(reason)
 *   bound  → null (incomplete — depth limit reached)
 *   cycle  → null (back-edge, coinductive — future work, TODO_0009)
 *   memo   → null (shared sub-term reference — future work)
 *
 * Multi-alt branches (oplus in rule consequent) become case splits:
 *   oplus_l(x, a -> child1, b -> child2)
 * This extends CLF's monadic grammar with case analysis — sound because
 * CALC's exhaustive exploration IS oplus elimination inside the monad.
 *
 * NOTE: This builder is for the 'full' profile only (opaque terms).
 * For 'guided' mode, guidedTerm in guided-term.js replaces this
 * with verified ILL proof terms.
 *
 * @param {Object} tree - Explore tree node
 * @param {Function} rfTermFn - (state, roles) → rightFocusTerm for leaves
 * @param {Object} [roles] - Connective role map
 * @returns {GenericTerm|null}
 */
function exploreTerm(tree, rfTermFn, roles) {
  if (!tree) return null;

  switch (tree.type) {
    case 'leaf': {
      // Terminal: rightFocus decomposition of residual state
      return rfTermFn ? rfTermFn(tree.state, roles) : null;
    }

    case 'branch': {
      if (!tree.children || tree.children.length === 0) return null;

      // Check if this is an oplus fork (children with choice field)
      const hasChoice = tree.children.some(c => c.choice !== undefined);
      if (hasChoice) {
        // Oplus case split: oplus_l(x, a -> child1, b -> child2, ...)
        const subterms = tree.children.map(c =>
          c.child ? exploreTerm(c.child, rfTermFn, roles) : null
        );
        return {
          rule: 'oplus_l',
          principal: null,
          subterms: subterms.filter(t => t !== null)
        };
      }

      // Single-alt branches: chain as monadic let-bindings
      // Each child is { rule, child }, chain them sequentially
      let term = null;
      for (let i = tree.children.length - 1; i >= 0; i--) {
        const c = tree.children[i];
        const childTerm = exploreTerm(c.child, rfTermFn, roles);
        if (!childTerm) continue;

        if (term === null) {
          // Last step: the child term IS the continuation
          term = { rule: c.rule, principal: null, subterms: [childTerm] };
        } else {
          // Wrap: let {p} = rule(args) in term
          term = { rule: c.rule, principal: null, subterms: [term] };
        }
      }
      return term;
    }

    case 'dead':
      return { rule: 'unreachable', principal: null, subterms: [], reason: 'dead_branch' };

    case 'bound':
    case 'cycle':
    case 'memo':
      return null;

    default:
      return null;
  }
}

module.exports = {
  sigMap,
  flattenedArity,
  formatSignature,
  extractTerm,
  monadicTerm,
  exploreTerm
};
