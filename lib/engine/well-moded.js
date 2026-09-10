/**
 * Well-modedness checker (task #81 / P7) — the load-time mode system that
 * discharges THY_0039 Theorem 3's hypothesis. See doc/theory/0039 §6.
 *
 * A pure load-time fence beside the datasort/priors/sort validators. It reads
 * the compiled rule set + clause set and produces, per program:
 *   - functionalPreds : Set<"pred#outPos">  — the certified-functional forced
 *     modes (§6.1), consumed by the forcing-goal check and (future) task #84.
 *   - { warnings, errors }                  — well-modedness violations.
 *
 * Enforcement is WARN-FIRST: every finding is a warning surfaced on
 * calc.wellModedLint. A calculus flips it to a hard load error by setting
 * cc.wellModed === 'strict' (the cc.typeCheck: 'strict' pattern) once its
 * corpus is confirmed inside the accepted set.
 *
 * SOUNDNESS DIRECTION (§6.4): the analysis over-approximates — it may reject a
 * well-moded program, never accept an ill-moded one. Certification is sound
 * (certified ⇒ functional): input-disjoint heads bound the clause count to ≤ 1
 * per ground input, AND a coinductive body-determinism check ensures each
 * clause's output is functionally determined from its inputs (so a relational
 * body — `p X Y <- edge X Y` — is NOT certified, and forcing it is flagged).
 *
 * This module imports only lib/ (kernel Store + the eq/neq solver); the
 * calculus supplies modes as DATA through cc (layer-dag clean).
 */

import Store from '../kernel/store.js';

// Leaf tags that denote a VARIABLE (an opaque hole a parameter may fill).
// metavar: rule/clause slot; freevar: clause body var; evar: runtime
// eigenvariable; var/bound: quantifier machinery (defensive — not expected in
// flat fact patterns, but treated as opaque rather than structural).
const _VAR_TAGS = new Set([
  Store.TAG.metavar, Store.TAG.freevar, Store.TAG.evar,
  Store.TAG.var, Store.TAG.bound,
].filter((t) => t !== undefined));

function isVar(h) {
  return _VAR_TAGS.has(Store.tagId(h));
}

/** Predicate tag of a fact/goal hash, or null if it is not a predicate. */
function predTagOf(h) {
  const t = Store.tagId(h);
  return t >= Store.PRED_BOUNDARY ? t : null;
}

/**
 * Sound non-unifiability: returns true only when a and b DEFINITELY cannot
 * unify (a witness of input-disjointness). A variable on either side unifies
 * with anything (⇒ false, conservatively "may overlap"). Distinct constructor
 * heads, distinct arities, or distinct leaf values at aligned positions ⇒ true.
 */
function nonUnifiable(a, b) {
  if (isVar(a) || isVar(b)) return false;
  const ta = Store.tagId(a);
  const tb = Store.tagId(b);
  if (ta !== tb) return true;
  const na = Store.arity(a);
  const nb = Store.arity(b);
  if (na !== nb) return true;
  for (let i = 0; i < na; i++) {
    const ca = Store.child(a, i);
    const cb = Store.child(b, i);
    if (Store.isTerm(ca) && Store.isTerm(cb)) {
      if (nonUnifiable(ca, cb)) return true;
    } else if (ca !== cb) {
      // Non-term children (atom name string, binlit/ratlit bigint index):
      // different interned value ⇒ the leaves are distinct ⇒ disjoint.
      return true;
    }
  }
  return false;
}

/** Collect the metavar/freevar hashes occurring anywhere under h into `out`. */
function collectVars(h, out) {
  if (isVar(h)) { out.add(h); return; }
  const n = Store.arity(h);
  for (let i = 0; i < n; i++) {
    const c = Store.child(h, i);
    if (Store.isTerm(c)) collectVars(c, out);
  }
}

/** Whether every var under arg `i` of `goal` is in `ground`. */
function argGround(goal, i, ground) {
  const c = Store.child(goal, i);
  if (!Store.isTerm(c)) return true;
  const vs = new Set();
  collectVars(c, vs);
  for (const v of vs) if (!ground.has(v)) return false;
  return true;
}

/** Antecedent-bound metavar hashes of a compiled rule (ground at match). */
function anteVars(rule) {
  const g = new Set();
  const a = rule.antecedent || {};
  for (const p of (a.linear || [])) collectVars(p, g);
  for (const p of (a.persistent || [])) collectVars(p, g);
  return g;
}

/**
 * §6.1 — certify the functional forced modes of the program.
 *
 * Returns Set<"predName#outPos">: predicate p is certified functional with
 * output position `out` (inputs = the other positions) when
 *   (a) its clause heads are pairwise input-disjoint (some input position is
 *       non-unifiable across every pair — ≤ 1 clause per ground input), AND
 *   (b) every clause's body functionally determines the head's output vars
 *       from its input vars, using only currently-certified premise modes
 *       (a greatest fixpoint: assume all input-disjoint modes, drop any whose
 *       body fails — so mutual/self recursion like plus is admitted, while a
 *       body that grounds its output through a non-certified (relational or
 *       EDB) predicate is rejected).
 *
 * Zero-clause predicates are certified ONLY through the FFI mode table (their
 * declared `-` positions, the documented spec-functional carve-out); a
 * zero-clause predicate with no FFI mode is a relational EDB fact and is never
 * certified — forcing it is a G1 violation.
 */
function certifyFunctional(clauses, cc) {
  // Group clause heads by predicate tag.
  const byPred = new Map(); // tag -> [{ head, premises }]
  for (const c of clauses.values()) {
    const t = predTagOf(c.hash);
    if (t === null) continue;
    if (!byPred.has(t)) byPred.set(t, []);
    byPred.get(t).push({ head: c.hash, premises: c.premises || [] });
  }

  // Candidate clausal modes: (pred, out) whose heads are input-disjoint.
  const candidate = new Set();
  for (const [t, cls] of byPred) {
    const name = Store.TAG_NAMES[t];
    const ar = Store.arity(cls[0].head);
    for (let out = 0; out < ar; out++) {
      if (inputDisjoint(cls, out, ar)) candidate.add(name + '#' + out);
    }
  }

  // FFI spec-functional certification (§6.1 carve-out): a non-multiModal FFI
  // predicate is functional at each declared `-` (output) position — the FFI
  // is the property-tested oracle, and the FFI≡clause invariant (noFFI arms)
  // makes the clause resolution compute the same unique function. This applies
  // whether or not the predicate also has clauses (their body-determinism need
  // not be re-provable by this analysis).
  const ffiCertified = new Set();
  const ffi = cc && cc.ffi;
  const modes = ffi && ffi.parsedModes;
  if (modes) {
    for (const name of Object.keys(modes)) {
      const meta = ffi.getModeMeta ? ffi.getModeMeta(name) : { modes: modes[name], multiModal: false };
      if (!meta || !meta.modes || meta.multiModal) continue;
      for (let i = 0; i < meta.modes.length; i++) {
        if (meta.modes[i] === '-') ffiCertified.add(name + '#' + i);
      }
    }
  }

  // §6.1 guard-exclusivity (task #85): heads that all unify on their inputs
  // may still be functional when their BODIES are pairwise mutually exclusive
  // — at most one clause fires per ground input. A pair is separated when the
  // union of their region constraints (head-literal equalities + order/eq/neq
  // guards, lifted onto shared head-input symbols) is UNSAT in the order+eq
  // theory. Body vars defined by a certified-functional determiner are
  // canonicalised to a shared symbol so the same computed quantity aligns
  // across clauses (e.g. Remaining = sub End Offset); a declared unbounded sum
  // (cc.domain.sumPreds) injects its monotonicity facts. Determiner modes come
  // from the input-disjoint clausal candidates ∪ the FFI carve-out — a set
  // fixed before this pass, so no ordering dependency. bodyDetermines (below)
  // still gates every mode admitted here, so an over-eager separation on a
  // non-output position is dropped rather than mis-certified.
  const dom = cc && cc.domain;
  const cpreds = dom && dom.constraintPreds;
  const evalNumeric = (dom && dom.evalNumeric) || null;
  if (evalNumeric && cpreds) {
    const canonSet = new Set([...candidate, ...ffiCertified]);
    const orderMap = cpreds.order || null;
    const eqName = cpreds.eq || null;
    const neqName = cpreds.neq || null;
    const sumPreds = (dom && dom.sumPreds) || null;
    for (const [t, cls] of byPred) {
      if (cls.length < 2) continue;
      const name = Store.TAG_NAMES[t];
      const ar = Store.arity(cls[0].head);
      for (let out = 0; out < ar; out++) {
        const key = name + '#' + out;
        if (candidate.has(key)) continue;
        if (clausesSeparated(cls, out, ar, canonSet, sumPreds, orderMap, eqName, neqName, evalNumeric)) {
          candidate.add(key);
        }
      }
    }
  }

  // Greatest fixpoint on body-determinism for the CLAUSAL candidates: start
  // optimistic, drop a clausal mode whose some clause body no longer grounds
  // its output through certified premises (mutual/self recursion admitted).
  const certified = new Set([...candidate, ...ffiCertified]);
  for (;;) {
    let changed = false;
    for (const key of [...certified]) {
      if (ffiCertified.has(key)) continue; // spec-functional, no body to check
      const hashPos = key.lastIndexOf('#');
      const name = key.slice(0, hashPos);
      const out = +key.slice(hashPos + 1);
      const cls = byPred.get(Store.TAG[name]) || [];
      for (const c of cls) {
        if (!bodyDetermines(c, out, certified)) { certified.delete(key); changed = true; break; }
      }
    }
    if (!changed) break;
  }
  return certified;
}

/**
 * §6.1′ — certify the total DECISION PROCEDURES of the program.
 *
 * A predicate is a certified total decision procedure (closed-world decidable:
 * every ground argument tuple is decided true/false, terminating) when it is
 * declared as a non-multiModal FFI predicate whose EVERY position is an input
 * (`+`) — a boolean judgment with no output slot. The FFI is the
 * property-tested total oracle, and the FFI≡clause invariant (the noFFI arms)
 * makes clause resolution decide the same relation. This is the decision-
 * procedure twin of the functionality carve-out: a clause-only decision
 * procedure would need a separate completeness+termination certificate (the
 * same hard analysis §6.1 leaves to FFI; no such predicate exists in the
 * corpus).
 *
 * Returns Set<predName>. Consumed by the runtime tell-consistency prune
 * (task #84 / THY_0039 §4 G2 residual (i)): a GROUND tell of a false decidable
 * atom drives its leaf's denotation to ∅. The prune decides the atom by DIRECT
 * value evaluation (the eq/neq ground short-circuit, evalNumeric), never by
 * clause resolution — the latter false-fails a deep ground query under the
 * backchainer's depth cap and would be unsound FFI-off.
 */
function certifyDecidable(cc) {
  const decidable = new Set();
  const ffi = cc && cc.ffi;
  const modes = ffi && ffi.parsedModes;
  if (!modes) return decidable;
  for (const name of Object.keys(modes)) {
    const meta = ffi.getModeMeta ? ffi.getModeMeta(name) : { modes: modes[name], multiModal: false };
    if (!meta || !meta.modes || meta.multiModal) continue;
    if (meta.modes.length >= 1 && meta.modes.every((m) => m === '+')) decidable.add(name);
  }
  return decidable;
}

/**
 * §6.1′ enforcement — every predicate the calculus declares as an ORDER guard
 * for the branch-pruning solver (cc.domain.constraintPreds.order: predName →
 * comparator) must be a certified total decision procedure. Its ground prune
 * computes the DECLARED comparator on the decoded arguments, so soundness rests
 * on that comparator being the predicate's true denotation — the FFI decision
 * mode is what backs it. A declared-but-uncertified order guard is a
 * mis-declaration; warn-first (the runtime also refuses to prune it — the
 * intersection with `decidablePreds` in explore).
 *
 * The eq/neq roles are NOT checked here: the solver's union-find is sound as
 * pure equality reasoning independent of any FFI backing (task #80).
 */
function checkConstraintDecls(cc, decidable, warnings) {
  const order = cc && cc.domain && cc.domain.constraintPreds && cc.domain.constraintPreds.order;
  if (!order) return;
  for (const name of Object.keys(order)) {
    if (!decidable.has(name)) {
      warnings.push(
        `order guard '${name}' is declared decidable (constraintPreds.order) but ` +
        `is not a certified total decision procedure (no non-multiModal all-input ` +
        `FFI mode; §6.1′) — the ground tell-consistency prune would rest on an ` +
        `unbacked comparator semantics; it is refused at runtime.`,
      );
    }
  }
}

/**
 * §6.1 enforcement — a declared unbounded sum (`cc.domain.sumPreds`) is a SOUND
 * monotonicity axiom only when its summands are non-negative. The guard-
 * exclusivity certifier injects `summandᵢ ≤ C` (C = Σ summands, `buildRegion`),
 * which requires the OTHER summands to be ≥ 0 — false on a signed or wrapping
 * domain, where it would fabricate a spurious `orderUnsat` and mis-certify a
 * non-functional predicate. The obligation is the domain's well-founded floor:
 * `cc.domain.orderDomain.min ≥ 0`. A `sumPreds` declaration without a
 * non-negative floor is a warn-first mis-declaration (otherwise a silent trap).
 */
function checkSumPreds(cc, warnings) {
  const dom = cc && cc.domain;
  const sumPreds = dom && dom.sumPreds;
  if (!sumPreds || Object.keys(sumPreds).length === 0) return;
  const min = dom.orderDomain && dom.orderDomain.min;
  if (min === undefined || min === null || min < 0n) {
    warnings.push(
      `sumPreds is declared (${Object.keys(sumPreds).join(', ')}) but the domain ` +
      `has no declared non-negative floor (cc.domain.orderDomain.min ≥ 0) — the ` +
      `guard-exclusivity monotonicity injection (summand ≤ sum) is unsound for a ` +
      `signed or wrapping domain (§6.1).`,
    );
  }
}

/** Heads pairwise non-unifiable on some input position (complement of `out`). */
function inputDisjoint(cls, out, ar) {
  for (let i = 0; i < cls.length; i++) {
    for (let j = i + 1; j < cls.length; j++) {
      let sep = false;
      for (let k = 0; k < ar; k++) {
        if (k === out) continue;
        if (nonUnifiable(Store.child(cls[i].head, k), Store.child(cls[j].head, k))) { sep = true; break; }
      }
      if (!sep) return false;
    }
  }
  return true;
}

// ── §6.1 guard-exclusivity (task #85) ────────────────────────────────────
//
// An order/eq atom operand is either a numeric CONSTANT { c: BigInt } or an
// opaque SYMBOL { s: string }. Head-input positions become the shared symbols
// `p<k>` (so clause i's arg k and clause j's arg k — the same ground input —
// align); a body var determined by a certified-functional premise becomes a
// canonical symbol `pred#out(inputs…)`, identical across clauses that compute
// the same quantity the same way (sound: identifying two vars asserts they
// denote one value, which the premise's functionality guarantees).

const operandKey = (o) => (o.c !== undefined ? 'c:' + o.c : 's:' + o.s);

/** Decode a clause term to an operand, or null if opaque/unmapped. */
function termOperand(h, vmap, evalNumeric) {
  if (isVar(h)) return vmap.get(h) || null;
  const v = evalNumeric(h);
  if (v === null || v === undefined) return null; // compound non-numeric
  return { c: typeof v === 'bigint' ? v : BigInt(v) };
}

/**
 * Build the region constraint atoms of one clause, treating position `out` as
 * the output and every other head position as an input. Atoms are
 * { op: '='|'≠'|'<'|'<=', a, b } over shared symbols / constants (see above).
 */
function buildRegion(clause, out, ar, canonSet, sumPreds, orderMap, eqName, neqName, evalNumeric) {
  const vmap = new Map(); // clause var hash -> operand
  const atoms = [];
  // Head inputs: a var binds to its (first) position symbol; a repeated input
  // var links its positions by equality; a numeric literal pins that position.
  for (let k = 0; k < ar; k++) {
    if (k === out) continue;
    const hk = Store.child(clause.head, k);
    const posSym = { s: 'p' + k };
    if (isVar(hk)) {
      if (vmap.has(hk)) atoms.push({ op: '=', a: vmap.get(hk), b: posSym });
      else vmap.set(hk, posSym);
    } else {
      const v = evalNumeric(hk);
      if (v !== null && v !== undefined) atoms.push({ op: '=', a: posSym, b: { c: typeof v === 'bigint' ? v : BigInt(v) } });
    }
  }
  const isGuard = (n) => n === eqName || n === neqName || (orderMap && orderMap[n] !== undefined);
  const pend = (clause.premises || []).slice();
  for (;;) {
    let progressed = false;
    for (let pi = 0; pi < pend.length; pi++) {
      const g = pend[pi];
      if (g === undefined) continue;
      const pt = predTagOf(g);
      if (pt === null) { pend[pi] = undefined; continue; }
      const pname = Store.TAG_NAMES[pt];
      const gar = Store.arity(g);
      if (isGuard(pname) && gar === 2) {
        const a = termOperand(Store.child(g, 0), vmap, evalNumeric);
        const b = termOperand(Store.child(g, 1), vmap, evalNumeric);
        if (a && b) { // both operands known — emit and consume
          const op = pname === eqName ? '=' : pname === neqName ? '≠' : orderMap[pname];
          atoms.push({ op, a, b });
          pend[pi] = undefined; progressed = true;
        }
        // else: leave pending — a later determiner may map its operand.
        continue;
      }
      // Determiner: a certified output var whose other args are all mapped.
      for (let o = 0; o < gar; o++) {
        if (!canonSet.has(pname + '#' + o)) continue;
        const outArg = Store.child(g, o);
        if (!isVar(outArg) || vmap.has(outArg)) continue;
        const ins = [];
        let ok = true;
        for (let k = 0; k < gar; k++) {
          if (k === o) continue;
          const op = termOperand(Store.child(g, k), vmap, evalNumeric);
          if (!op) { ok = false; break; }
          ins.push(op);
        }
        if (!ok) continue;
        const sym = { s: pname + '#' + o + '(' + ins.map(operandKey).join(',') + ')' };
        vmap.set(outArg, sym);
        // Unbounded-sum monotonicity (cc.domain.sumPreds): out = Σ summands, so
        // out ≥ each summand, STRICT when another summand is a positive const.
        if (sumPreds && sumPreds[pname] === o) {
          for (let si = 0; si < ins.length; si++) {
            let strict = false;
            for (let sj = 0; sj < ins.length; sj++) {
              if (sj === si) continue;
              if (ins[sj].c !== undefined && ins[sj].c > 0n) { strict = true; break; }
            }
            atoms.push({ op: strict ? '<' : '<=', a: ins[si], b: sym });
          }
        }
        pend[pi] = undefined; progressed = true;
        break;
      }
    }
    if (!progressed) break;
  }
  return atoms;
}

/**
 * Sound UNSAT test for a conjunction of order/eq/neq atoms over opaque symbols
 * and integer constants: eq-classes via union-find (a class with two distinct
 * constants ⇒ UNSAT; a `≠` inside a class ⇒ UNSAT), then transitive closure of
 * the `<`/`<=` edges over class reps — a strict self-cycle, or a constant edge
 * violating its own comparator, is UNSAT. Returns true only when the system is
 * genuinely unsatisfiable (soundness direction: never a false UNSAT).
 */
function orderUnsat(atoms) {
  const parent = new Map();
  const constOf = new Map();
  const ensure = (o) => {
    const k = operandKey(o);
    if (!parent.has(k)) { parent.set(k, k); if (o.c !== undefined) constOf.set(k, o.c); }
    return k;
  };
  const find = (k) => { while (parent.get(k) !== k) { parent.set(k, parent.get(parent.get(k))); k = parent.get(k); } return k; };
  const union = (k1, k2) => {
    const r1 = find(k1); const r2 = find(k2);
    if (r1 === r2) return true;
    const c1 = constOf.get(r1); const c2 = constOf.get(r2);
    if (c1 !== undefined && c2 !== undefined && c1 !== c2) return false;
    parent.set(r1, r2);
    if (c1 !== undefined && c2 === undefined) constOf.set(r2, c1);
    return true;
  };
  for (const at of atoms) { ensure(at.a); ensure(at.b); }
  for (const at of atoms) if (at.op === '=') { if (!union(operandKey(at.a), operandKey(at.b))) return true; }
  for (const at of atoms) if (at.op === '≠') { if (find(operandKey(at.a)) === find(operandKey(at.b))) return true; }

  const reach = new Map(); // u -> Map<v, strictness 0|1>
  const relax = (u, v, st) => { let m = reach.get(u); if (!m) { m = new Map(); reach.set(u, m); } const cur = m.get(v); if (cur === undefined || st > cur) { m.set(v, st); return true; } return false; };
  for (const at of atoms) if (at.op === '<' || at.op === '<=') relax(find(operandKey(at.a)), find(operandKey(at.b)), at.op === '<' ? 1 : 0);
  for (;;) {
    let changed = false;
    for (const [u, m] of [...reach]) {
      for (const [w, sw] of [...m]) {
        const rw = reach.get(w);
        if (!rw) continue;
        for (const [v, sv] of rw) if (relax(u, v, Math.max(sw, sv))) changed = true;
      }
    }
    if (!changed) break;
  }
  for (const [u, m] of reach) {
    if (m.get(u) === 1) return true; // strict self-cycle
    const cu = constOf.get(u);
    if (cu === undefined) continue;
    for (const [v, st] of m) {
      const cv = constOf.get(v);
      if (cv === undefined) continue;
      if (st === 1 ? !(cu < cv) : !(cu <= cv)) return true;
    }
  }
  return false;
}

/**
 * Are the clauses of a predicate pairwise functionally separated for output
 * position `out`? Each pair must be head-input-disjoint (existing route) OR
 * region-exclusive (their combined region atoms are UNSAT).
 */
function clausesSeparated(cls, out, ar, canonSet, sumPreds, orderMap, eqName, neqName, evalNumeric) {
  const regions = cls.map((c) => buildRegion(c, out, ar, canonSet, sumPreds, orderMap, eqName, neqName, evalNumeric));
  for (let i = 0; i < cls.length; i++) {
    for (let j = i + 1; j < cls.length; j++) {
      let disj = false;
      for (let k = 0; k < ar && !disj; k++) {
        if (k === out) continue;
        if (nonUnifiable(Store.child(cls[i].head, k), Store.child(cls[j].head, k))) disj = true;
      }
      if (disj) continue;
      if (orderUnsat(regions[i].concat(regions[j]))) continue;
      return false;
    }
  }
  return true;
}

/**
 * Does clause `c` functionally determine its head's `out` vars from its input
 * vars, given the currently-certified premise modes? Left-to-right saturation:
 * seed the ground set with the head's INPUT vars; a premise grounds its output
 * vars once it has a certified output mode whose other positions are all
 * ground; a premise all of whose positions are already ground is a pure guard.
 * Succeeds iff the head's OUTPUT vars end up ground.
 */
function bodyDetermines(c, out, certified) {
  const ground = new Set();
  const ar = Store.arity(c.head);
  for (let k = 0; k < ar; k++) {
    if (k === out) continue;
    const a = Store.child(c.head, k);
    if (Store.isTerm(a)) collectVars(a, ground);
  }
  const pending = (c.premises || []).slice();
  for (;;) {
    let progressed = false;
    for (let pi = 0; pi < pending.length; pi++) {
      const g = pending[pi];
      if (g === undefined) continue;
      const pt = predTagOf(g);
      if (pt === null) { pending[pi] = undefined; continue; } // non-predicate premise: ignore
      const pname = Store.TAG_NAMES[pt];
      const gar = Store.arity(g);
      // A premise is a resolvable "determiner" if it has a certified output
      // position whose every other position's vars are already ground.
      let firedOut = -1;
      for (let o = 0; o < gar; o++) {
        if (!certified.has(pname + '#' + o)) continue;
        let inputsGround = true;
        for (let k = 0; k < gar && inputsGround; k++) {
          if (k === o) continue;
          const a = Store.child(g, k);
          if (!Store.isTerm(a)) continue;
          const vs = new Set(); collectVars(a, vs);
          for (const v of vs) if (!ground.has(v)) { inputsGround = false; break; }
        }
        if (inputsGround) { firedOut = o; break; }
      }
      // Or a pure guard: every position already ground.
      let allGround = true;
      for (let k = 0; k < gar && allGround; k++) {
        const a = Store.child(g, k);
        if (!Store.isTerm(a)) continue;
        const vs = new Set(); collectVars(a, vs);
        for (const v of vs) if (!ground.has(v)) { allGround = false; break; }
      }
      if (firedOut >= 0) {
        const a = Store.child(g, firedOut);
        if (Store.isTerm(a)) collectVars(a, ground);
        pending[pi] = undefined; progressed = true;
      } else if (allGround) {
        pending[pi] = undefined; progressed = true;
      }
    }
    if (!progressed) break;
  }
  // Head output vars must all be ground.
  const outVars = new Set();
  if (out < ar) {
    const a = Store.child(c.head, out);
    if (Store.isTerm(a)) collectVars(a, outVars);
  }
  for (const v of outVars) if (!ground.has(v)) return false;
  return true;
}

/**
 * §6.1 enforcement — a forcing goal (a persistent goal determining an
 * existential slot, `compile.js` existentialGoals) must name a
 * certified-functional predicate at the slot's output position. A non-certified
 * force is the G1 violation class: committing to one witness of a possibly
 * non-functional predicate.
 */
function checkForcingGoals(compiledRules, certified, warnings) {
  for (const rule of compiledRules) {
    const eg = rule.existentialGoals;
    if (!eg) continue;
    const slotToHash = {};
    for (const h in rule.metavarSlots) slotToHash[rule.metavarSlots[h]] = +h;

    // Determiner discovery mirrors the runtime resolver's dataflow: seed the
    // ground set with the antecedent-bound vars; a goal DETERMINES a slot at
    // position i when the slot sits at i and every OTHER position is already
    // ground (antecedent var or an earlier-determined slot). That output
    // position — not any input occurrence — is what must be certified.
    const ground = anteVars(rule);
    // Gather the distinct resolver goals (existentialGoals may repeat a goal
    // under several slots — e.g. to256 C C' under both C and C').
    const goals = new Set();
    for (const slot in eg) for (const g of eg[slot]) goals.add(g);

    const flagged = new Set();
    for (;;) {
      let progressed = false;
      for (const goal of goals) {
        const pt = predTagOf(goal);
        if (pt === null) continue;
        const gar = Store.arity(goal);
        for (let i = 0; i < gar; i++) {
          const c = Store.child(goal, i);
          if (!Store.isTerm(c)) continue;
          // slot at position i not yet ground, all others ground ⇒ this goal
          // determines the slot(s) here.
          const vs = new Set(); collectVars(c, vs);
          let hasUngroundSlot = false;
          for (const v of vs) if (!ground.has(v)) { hasUngroundSlot = true; break; }
          if (!hasUngroundSlot) continue;
          let othersGround = true;
          for (let k = 0; k < gar && othersGround; k++) {
            if (k === i) continue;
            if (!argGround(goal, k, ground)) othersGround = false;
          }
          if (!othersGround) continue;
          // Determined here. Ground the slot vars.
          for (const v of vs) ground.add(v);
          progressed = true;
          const pname = Store.TAG_NAMES[pt];
          const key = pname + '#' + i;
          if (!certified.has(key) && !flagged.has(rule.name + '|' + key)) {
            flagged.add(rule.name + '|' + key);
            warnings.push(
              `rule '${rule.name}': forces non-certified-functional predicate ` +
              `'${pname}' at output position ${i} (G1 — the witness may not be ` +
              `unique; §6.1). Declare it functional or leave the goal deferred.`,
            );
          }
        }
      }
      if (!progressed) break;
    }
  }
}

// ── §6.2 — parameter-flow analysis + V1 (structural match) ──────────────
//
// Parameter-freeness over predicate-argument LEAF PATHS. A path is the index
// route from a fact's predicate root to a leaf, e.g. [0,0] = "arg0 → child0".
// taint(pred) ⊆ leaf paths that MAY hold a parameter (an eigenvariable).
//
// Taint marks only LEAF positions (where a variable/parameter sits), never the
// constructor SPINE — matching a list's cons cells is never a violation; only
// decomposing a parameter VALUE is. Unbounded recursion (a runtime stack of
// parameters, values at 0.1ᵏ.0) is handled by a REGULAR STAR PATH abstraction:
// a maximal run of a repeated child index collapses to a star `c*` (0+ repeats).
// The star keeps the value/spine distinction exact — 0.1*.0 is "a value at any
// tail depth", 0.1* is "any cons cell" — and canonicalisation bounds the path
// set, so the fixpoint terminates without the value↔spine confusion a plain
// depth truncation would introduce.
//
// Path component encoding: a concrete child index c ≥ 0, or a star of c encoded
// as the negative -(c+2). All paths in the taint sets are canonical.

const STAR = (c) => -(c + 2);
const isStarC = (x) => x < 0;
const starBase = (x) => -x - 2;

/**
 * Canonicalise a path. A run of a concrete index whose length reaches `thr`
 * collapses to a star — `thr` exceeds the deepest fixed nesting any pattern
 * inspects, so only genuine UNBOUNDED recursion (arbitrarily long runs, e.g. a
 * cons list's repeated tail-descent) is starred; fixed multi-level nesting like
 * arg0→child0 stays concrete. The absorb pass (c·c* ⇒ c*) then converges the
 * recursion under the fixpoint's shifts. A hard safety collapse at 4·thr keeps
 * any non-run growth terminating.
 */
function canonPath(p, thr) {
  const T = thr || 2;
  let src = p;
  if (src.length > 4 * T) {
    // safety: collapse the longest concrete run to a star, else drop the tail.
    let bi = -1, bl = 0;
    for (let i = 0; i < src.length;) {
      const x = src[i]; if (isStarC(x)) { i++; continue; }
      let j = i; while (j < src.length && src[j] === x) j++;
      if (j - i > bl) { bl = j - i; bi = i; } i = j;
    }
    if (bl >= 2) src = src.slice(0, bi).concat([STAR(src[bi])], src.slice(bi + bl));
    else src = src.slice(0, 4 * T);
  }
  const a = [];
  for (let i = 0; i < src.length;) {
    const x = src[i];
    if (isStarC(x)) { a.push(x); i++; continue; }
    let j = i; while (j < src.length && src[j] === x) j++;
    if (j - i >= T) a.push(STAR(x));
    else for (let q = i; q < j; q++) a.push(x);
    i = j;
  }
  const res = [];
  for (const x of a) {
    const last = res.length ? res[res.length - 1] : null;
    if (last !== null && isStarC(last)) {
      const b = starBase(last);
      if ((isStarC(x) && starBase(x) === b) || (!isStarC(x) && x === b)) continue; // absorbed into star
    }
    if (last !== null && !isStarC(last) && isStarC(x) && starBase(x) === last) {
      res[res.length - 1] = x; continue; // c · c* ⇒ c*
    }
    res.push(x);
  }
  return res;
}

const keyOfPath = (arr) => arr.join(',');
const parsePath = (s) => (s === '' ? [] : s.split(',').map(Number));

/** Predicate name of a fact/goal hash, or null. */
function predName(h) {
  const t = predTagOf(h);
  return t === null ? null : Store.TAG_NAMES[t];
}

/** Variable leaves of a fact with their (concrete) leaf paths: [{ v, path }]. */
function leafVars(fact) {
  const out = [];
  const rec = (h, path) => {
    if (isVar(h)) { out.push({ v: h, path }); return; }
    const n = Store.arity(h);
    for (let i = 0; i < n; i++) {
      const c = Store.child(h, i);
      if (Store.isTerm(c)) rec(c, path.concat(i));
    }
  };
  const n = Store.arity(fact);
  for (let i = 0; i < n; i++) {
    const c = Store.child(fact, i);
    if (Store.isTerm(c)) rec(c, [i]);
  }
  return out;
}

/**
 * V1 test: does linear pattern `pat` DEMAND structure at a parameter leaf whose
 * position is described by the (possibly starred) path `tau`? DFS the NFA of
 * tau against the finite pattern: a star `c*` traverses 0+ child-c steps
 * (matching the cons SPINE — always fine); when tau is fully consumed we are at
 * the parameter leaf, and a NON-variable there decomposes the parameter (V1);
 * an ancestor variable carries the parameter opaquely (OK).
 */
function structuralAtStar(pat, tau) {
  const seen = new Set();
  const stack = [[pat, 0]];
  while (stack.length) {
    const [cur, ti] = stack.pop();
    const k = cur + '@' + ti;
    if (seen.has(k)) continue;
    seen.add(k);
    if (ti === tau.length) { if (!isVar(cur)) return true; continue; }
    if (isVar(cur)) continue;
    const comp = tau[ti];
    if (isStarC(comp)) {
      const b = starBase(comp);
      stack.push([cur, ti + 1]); // zero repeats
      if (b < Store.arity(cur)) { const c = Store.child(cur, b); if (Store.isTerm(c)) stack.push([c, ti]); }
    } else if (comp < Store.arity(cur)) {
      const c = Store.child(cur, comp); if (Store.isTerm(c)) stack.push([c, ti + 1]);
    }
  }
  return false;
}

/**
 * Consume concrete path `pi` (a variable's leaf path in a matched pattern)
 * against starred taint path `tau`. Returns { exact, residuals }: exact ⇒ the
 * variable IS the parameter (relative ε); each residual is the starred tail of
 * tau below pi — the parameter that variable then carries.
 */
function tauResiduals(pi, tau) {
  const residuals = [];
  let exact = false;
  const seen = new Set();
  const stack = [[0, 0]];
  while (stack.length) {
    const [pj, ti] = stack.pop();
    const k = pj + '@' + ti;
    if (seen.has(k)) continue;
    seen.add(k);
    if (pj === pi.length) {
      if (ti === tau.length) exact = true;
      else residuals.push(tau.slice(ti));
      continue;
    }
    if (ti === tau.length) continue;
    const comp = tau[ti];
    if (isStarC(comp)) {
      const b = starBase(comp);
      stack.push([pj, ti + 1]);                 // zero repeats
      if (pi[pj] === b) stack.push([pj + 1, ti]); // one repeat consumes pi[pj]
    } else if (pi[pj] === comp) {
      stack.push([pj + 1, ti + 1]);
    }
  }
  return { exact, residuals };
}

/**
 * Least-fixpoint parameter-flow. Sources: every existential slot (conservatively
 * all may defer, §6.2). Transfer: a consumed pattern's variable that binds a
 * tainted position carries the parameter (as a RELATIVE starred path);
 * reproducing that variable seeds taint at the shifted position — the conduit
 * that keeps value leaves tainted while the spine stays clean.
 */
/** Max node depth (path length) in a term's argument structure. */
function maxNodeDepth(fact) {
  let mx = 0;
  const rec = (h, d) => {
    if (d > mx) mx = d;
    const n = Store.arity(h);
    for (let i = 0; i < n; i++) { const c = Store.child(h, i); if (Store.isTerm(c)) rec(c, d + 1); }
  };
  const n = Store.arity(fact);
  for (let i = 0; i < n; i++) { const c = Store.child(fact, i); if (Store.isTerm(c)) rec(c, 1); }
  return mx;
}

function buildTaint(compiledRules) {
  const taint = new Map(); // predName -> Set<pathKey>
  const getT = (p) => { let s = taint.get(p); if (!s) { s = new Set(); taint.set(p, s); } return s; };

  // Star threshold: exceed the deepest fixed nesting any pattern inspects, so
  // only unbounded recursion (arbitrarily long runs) is starred.
  let maxD = 1;
  for (const r of compiledRules) {
    for (const p of ((r.antecedent && r.antecedent.linear) || [])) { const d = maxNodeDepth(p); if (d > maxD) maxD = d; }
    for (const alt of (r.consequentAlts || [])) for (const p of ((alt.linear || []).concat(alt.persistent || []))) { const d = maxNodeDepth(p); if (d > maxD) maxD = d; }
  }
  const THR = maxD + 1;

  for (;;) {
    let changed = false;
    for (const r of compiledRules) {
      const exHashes = new Set();
      if (r.existentialSlots && r.existentialSlots.length) {
        const exSet = new Set(r.existentialSlots);
        for (const h in r.metavarSlots) if (exSet.has(r.metavarSlots[h])) exHashes.add(+h);
      }
      if (exHashes.size === 0 && !(r.consequentAlts && r.consequentAlts.length)) continue;

      const varRel = new Map(); // varHash -> Set<relPathKey>
      const addRel = (v, arr) => { let s = varRel.get(v); if (!s) { s = new Set(); varRel.set(v, s); } s.add(keyOfPath(canonPath(arr, THR))); };
      for (const v of exHashes) addRel(v, []); // ε — the slot IS a parameter

      const ante = r.antecedent || {};
      for (const pat of [...(ante.linear || []), ...(ante.persistent || [])]) {
        const pred = predName(pat); if (!pred) continue;
        const ts = taint.get(pred); if (!ts) continue;
        for (const { v, path } of leafVars(pat)) {
          for (const tauStr of ts) {
            const { exact, residuals } = tauResiduals(path, parsePath(tauStr));
            if (exact) addRel(v, []);
            for (const rd of residuals) addRel(v, rd);
          }
        }
      }

      const conseqFacts = [];
      for (const alt of (r.consequentAlts || [])) {
        for (const p of (alt.linear || [])) conseqFacts.push(p);
        for (const p of (alt.persistent || [])) conseqFacts.push(p);
      }
      for (const fact of conseqFacts) {
        const pred = predName(fact); if (!pred) continue;
        const dst = getT(pred);
        for (const { v, path } of leafVars(fact)) {
          const rels = varRel.get(v); if (!rels) continue;
          for (const relStr of rels) {
            const full = canonPath(path.concat(parsePath(relStr)), THR);
            const fk = keyOfPath(full);
            if (!dst.has(fk)) { dst.add(fk); changed = true; }
          }
        }
      }
    }
    if (!changed) break;
  }
  return taint;
}

/** §6.2 V1 — flag every linear pattern that decomposes a parameter. */
function checkStructuralMatch(compiledRules, taint, warnings) {
  const flagged = new Set();
  for (const r of compiledRules) {
    for (const pat of ((r.antecedent && r.antecedent.linear) || [])) {
      const pred = predName(pat); if (!pred) continue;
      const ts = taint.get(pred); if (!ts) continue;
      for (const tauStr of ts) {
        if (tauStr === '') continue;
        const tau = parsePath(tauStr);
        if (!structuralAtStar(pat, tau)) continue;
        const fk = r.name + '|' + pred + '|' + tauStr;
        if (flagged.has(fk)) continue;
        flagged.add(fk);
        warnings.push(
          `rule '${r.name}': matches structure against a parameter at ` +
          `${pred} arg-path [${tauStr}] (V1 — a parameter is opaque; §6.2). ` +
          `No committed-choice pattern may decompose a parameter.`,
        );
      }
    }
  }
}

// ── §6.3 — guard-coverage (V2) ──────────────────────────────────────────

/** Antecedent variables of a rule that bind EXACTLY a parameter leaf. */
function paramVarsOf(rule, taint) {
  const params = new Set();
  const ante = rule.antecedent || {};
  for (const pat of [...(ante.linear || []), ...(ante.persistent || [])]) {
    const pred = predName(pat); if (!pred) continue;
    const ts = taint.get(pred); if (!ts) continue;
    for (const { v, path } of leafVars(pat)) {
      for (const tauStr of ts) {
        if (tauResiduals(path, parsePath(tauStr)).exact) { params.add(v); break; }
      }
    }
  }
  return params;
}

/** Whether guard-region rep `rv` (a BigInt) satisfies guard `g`. */
function guardHolds(g, rv) {
  switch (g.op) {
    case '=': return rv === g.c;
    case '#': return rv !== g.c;
    case '<c': return rv < g.c;   // V < c
    case 'c<': return g.c < rv;   // c < V
    case '≤c': return rv <= g.c;  // V ≤ c
    case 'c≤': return g.c <= rv;  // c ≤ V
    default: return true;
  }
}

/**
 * The rep-point coverage/exclusion decision (§6.3), factored out so it can be
 * fuzzed against brute-force (tools/fuzz-well-moded.js). `perAlt` is the
 * per-alternative guard lists over the scrutinee (each guard `{ op, c }`);
 * `floor` is the domain's well-founded minimum (BigInt) or null (no floor).
 *
 * Sound AND complete on a DISCRETE total order (the caller gates order guards
 * on `cc.domain.orderDomain.discrete`; eq/neq are density-agnostic): every
 * guard is constant on an arrangement cell, and the reps — `floor` and each
 * `cᵢ, cᵢ ± 1` clamped ≥ floor — hit every non-empty cell exactly once. Returns
 * 'uncovered' (a cell with no feasible alternative), 'overlap' (a cell with more
 * than one), or 'ok'.
 */
function guardCoverageVerdict(perAlt, floor) {
  const hasFloor = floor !== null && floor !== undefined;
  const reps = new Set();
  if (hasFloor) reps.add(floor);
  for (const gs of perAlt) for (const g of gs) {
    for (const d of [-1n, 0n, 1n]) { const x = g.c + d; if (!hasFloor || x >= floor) reps.add(x); }
  }
  for (const rv of reps) {
    let feasible = 0;
    for (const gs of perAlt) if (gs.every((g) => guardHolds(g, rv))) feasible++;
    if (feasible === 0) return 'uncovered';
    if (feasible > 1) return 'overlap';
  }
  return 'ok';
}

/**
 * §6.3 V2 — when a parameter is the scrutinee of a ⊕ (its value decides which
 * alternative via constraint guards), the alternatives must COVER the value
 * space and be mutually EXCLUSIVE. Decided by representative-point enumeration
 * over the total order (ℕ≥0): the guards compare the scrutinee to constants
 * {cᵢ}, whose arrangement partitions the domain into points {cᵢ} and the gaps
 * between them; on each cell every guard evaluates identically, so testing one
 * representative integer per non-empty cell — 0, and cᵢ, cᵢ±1 (clamped ≥ 0) —
 * is exact and complete. In every cell exactly one alternative must be feasible
 * (zero ⇒ coverage fails; more than one ⇒ exclusion fails).
 *
 * The fragment is eq/neq (task #80/#81) PLUS the certified-total order guards
 * (`cc.domain.constraintPreds.order` ∩ `calc.decidablePreds`, task #86 — the
 * §6.1′ decision-procedure certificate backs the comparator's semantics, the
 * same certificate #84's runtime prune consumes). A guard comparing the
 * scrutinee to a NON-constant, or an uncertified order guard, is undecidable
 * here and flagged.
 */
function checkGuardCoverage(compiledRules, taint, cc, decidablePreds, warnings) {
  const dom = cc && cc.domain;
  const cp = dom && dom.constraintPreds;
  if (!cp || !cp.eq || !cp.neq) return; // no decidable fragment declared
  const eqName = cp.eq;
  const neqName = cp.neq;
  const evalNumeric = dom.evalNumeric || null;
  if (!evalNumeric) return; // cannot evaluate guard constants → cannot decide
  // The scrutinee value domain (cc.domain.orderDomain): `min` is the
  // well-founded floor for the rep-point clamp (null → no floor); `discrete`
  // is the SOUNDNESS gate for ORDER guards — rep-point enumeration (cᵢ ± 1) is
  // exact only on a discrete order, so on a dense (e.g. ℚ) domain order guards
  // stay undecidable here. eq/neq are density-agnostic and need neither.
  const od = dom.orderDomain || null;
  const floor = od && od.min !== undefined ? od.min : null;
  const discrete = !!(od && od.discrete);
  // Order guards usable here = declared AND certified total decision procedures.
  const order = cp.order || {};
  const orderOp = (pn) => (Object.prototype.hasOwnProperty.call(order, pn)
    && decidablePreds && decidablePreds.has(pn)) ? order[pn] : null;
  const isGuardPred = (pn) => pn === eqName || pn === neqName
    || Object.prototype.hasOwnProperty.call(order, pn);

  for (const rule of compiledRules) {
    const alts = rule.consequentAlts;
    if (!alts || alts.length < 2) continue;
    const params = paramVarsOf(rule, taint);
    if (params.size === 0) continue;

    const guardAtoms = alts.map((a) =>
      (a.persistent || []).filter((h) => isGuardPred(predName(h))));

    for (const V of params) {
      // Per-alternative V-guards, reduced to { op, c }; a guard comparing V to a
      // non-constant — or an uncertified order guard — is undecidable.
      let mentioned = false;
      let undecidable = false;
      const perAlt = guardAtoms.map((atoms) => {
        const gs = [];
        for (const h of atoms) {
          const a0 = Store.child(h, 0);
          const a1 = Store.child(h, 1);
          const vLeft = a0 === V;
          const other = vLeft ? a1 : (a1 === V ? a0 : null);
          if (other === null) continue; // atom does not mention V
          mentioned = true;
          const c = evalNumeric(other);
          if (c === null) { undecidable = true; continue; }
          const cv = typeof c === 'bigint' ? c : BigInt(c);
          const pn = predName(h);
          if (pn === eqName) gs.push({ op: '=', c: cv });
          else if (pn === neqName) gs.push({ op: '#', c: cv });
          else {
            const cmp = orderOp(pn); // '<' | '<=' | null(uncertified)
            // Uncertified predicate, or a non-discrete domain where rep-point
            // enumeration is unsound — undecidable here.
            if (cmp === null || !discrete) { undecidable = true; continue; }
            const strict = cmp === '<';
            gs.push({ op: vLeft ? (strict ? '<c' : '≤c') : (strict ? 'c<' : 'c≤'), c: cv });
          }
        }
        return gs;
      });
      if (!mentioned) continue; // V carried opaquely through the ⊕ — well-moded
      if (undecidable) {
        warnings.push(
          `rule '${rule.name}': ⊕-guard on parameter '${varLabel(V)}' compares it to ` +
          `a non-constant, via an uncertified predicate, or over a non-discrete ` +
          `domain — coverage is undecidable here (V2; §6.3).`);
        continue;
      }

      const verdict = guardCoverageVerdict(perAlt, floor);
      if (verdict === 'uncovered') {
        warnings.push(
          `rule '${rule.name}': ⊕-guards on parameter '${varLabel(V)}' do not COVER ` +
          `its value space — some value takes no branch (V2 coverage; §6.3).`);
      } else if (verdict === 'overlap') {
        warnings.push(
          `rule '${rule.name}': ⊕-guards on parameter '${varLabel(V)}' are not mutually ` +
          `EXCLUSIVE — a value takes more than one branch (V2 exclusion; §6.3).`);
      }
    }
  }
}

/** Human-readable name of a metavar/freevar hash (its interned label). */
function varLabel(v) {
  const c = Store.child(v, 0);
  return typeof c === 'string' ? c : String(v);
}

/**
 * The load-time well-modedness check (THY_0039 §6). Returns
 * { functionalPreds, warnings, errors }; warn-first ⇒ errors stays empty
 * unless cc.wellModed === 'strict' (applied by the caller).
 */
function checkWellModed({ compiledRules, clauses, cc }) {
  const rules = compiledRules || [];
  const functionalPreds = certifyFunctional(clauses || new Map(), cc);
  const decidablePreds = certifyDecidable(cc);
  const warnings = [];
  const errors = [];
  checkForcingGoals(rules, functionalPreds, warnings);
  const taint = buildTaint(rules);
  checkStructuralMatch(rules, taint, warnings);
  checkGuardCoverage(rules, taint, cc, decidablePreds, warnings);
  checkConstraintDecls(cc, decidablePreds, warnings);
  checkSumPreds(cc, warnings);
  return { functionalPreds, decidablePreds, warnings, errors, taint };
}

export {
  checkWellModed,
  certifyFunctional,
  certifyDecidable,
  orderUnsat,
  guardCoverageVerdict,
  guardHolds,
  buildTaint,
  nonUnifiable,
  isVar,
  predTagOf,
  predName,
  collectVars,
  leafVars,
  structuralAtStar,
  canonPath,
};
export default { checkWellModed };
