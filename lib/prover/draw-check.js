/**
 * @draw step checker (TODO_0298 item 1b) — kernel-side verification of ONE
 * collapse event against the PROGRAM'S sort system and declared priors.
 *
 * The sequent shape it certifies (THY_0026 §5: collapse is a principal
 * cut of ∃_ρ-R against ∃-L; the minted token is the record the reduct
 * keeps — the step is DERIVABLE from will.rules drawn_l + superpose_l
 * + cut, checked here as one step):
 *
 *   Γ ; Δ, A[w/x]@t …            (opened body conjuncts, split at the
 *   ─────────────────────────     wave's stamp; ! conjuncts land in Γ)
 *   Γ ; Δ, superpose(s, ∃x.A)@t, drawn(c, s) ⊢ C
 *
 * Non-circularity: the check never runs the decimation driver. A draw
 * node carries the witness record (`state.draw`: { sort, member,
 * witness?, weight?, wave? }); the checker re-derives everything from
 * the program's declarative data:
 *
 *   - sort s is a classifier and c one of its members (program.sorts)
 *   - the witness TREE determines the tokens: every DRAWN head in the
 *     witness contributes one ground `drawn(atom(c_i), atom(s_i))` —
 *     the root at the wave's sort, constructor args at their declared
 *     arg sorts, recursively; an EVAR subterm contributes nothing (a
 *     still-suspended arg wave — the lazy head-only discipline, or a
 *     wave dropped un-observed: no choice made, no token, no factor).
 *     A fully ground rung-2 witness is therefore the COMPOSITE of its
 *     per-head draws (iterated ∃_ρ, THY_0027 §8) checked as one node.
 *   - the recorded weight, when present, equals Π ρ(c_i) over the
 *     contributing heads (program.priors; unannotated member = 1) —
 *     weight is DATA re-derived from the program, never trusted
 *   - premise = conclusion − wave − tokens ⊎ body[witness/x] split at
 *     the wave's stamp (splitBody — the same definition the driver uses)
 *
 * OPEN records (`state.draw`: { open: true, sort?, witness, wave? })
 * certify a token-FREE opening: the witness is a fresh evar and the
 * step is ∃-L — superpose_l when `sort` names the wave's classifier,
 * plain exists_l when `sort` is null (the M1 skolem). Freshness is
 * checked SYNTACTICALLY (the evar occurs nowhere else in the conclusion),
 * so unlike search-level eigenvariable steps this carries no
 * unverified:['binding'] degradation.
 *
 * Config comes from `calculus.draw` (declared at the calculus assembly
 * point — kit.js makeSequentLoader): { stampTag }. The kernel routes the
 * binding via calculus.stepCheckers and knows nothing about draws.
 */

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';
import Context from './context.js';
import { debruijnSubst } from '../kernel/substitute.js';
import { splitBody, DECIMATE_PREDS } from '../engine/decimate.js';
import { _parseSignature } from '../engine/type-check.js';

const atom = (n) => Store.put('atom', [n]);

/** Strip an optional stamp wrapper. */
function stripStamp(h, stampTag) {
  return Store.tag(h) === stampTag
    ? { inner: Store.child(h, 0), stamp: Store.child(h, 1) }
    : { inner: h, stamp: null };
}

/** Does evar e occur anywhere inside term h? */
function occursIn(h, e) {
  if (h === e) return true;
  if (Store.tag(h) === 'evar') return false;
  const a = Store.arity(h);
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c) && occursIn(c, e)) return true;
  }
  return false;
}

/**
 * Walk a witness tree collecting the drawn heads: root at `sort`,
 * constructor args at their declared arg sorts. An evar contributes
 * nothing (still suspended / dropped un-observed). Accumulates one
 * token and one prior factor per drawn head into `out`.
 */
function walkWitness(term, sort, program, out) {
  if (Store.tag(term) === 'evar') return null;
  // A datasort in the sort slot (m4: tokens carry the BINDER's sort name)
  // restricts membership to its subset; priors stay member-keyed (B4:
  // conditioning is restriction — surviving weights unchanged).
  // stateInfo resolves declared datasorts AND product keys (slice 3 —
  // products are deterministic from the declared clauses, so the checker
  // rebuilds them independently of the driver)
  const dsInfo = program.sorts.stateInfo ? program.sorts.stateInfo(sort)
    : (program.sorts.isDatasort && program.sorts.isDatasort(sort)
      ? program.sorts.datasortInfo(sort) : null);
  const isDs = dsInfo !== null && dsInfo !== undefined;
  if (!isDs && !program.sorts.isClassifier(sort)) {
    return `draw sort '${sort}' is not a classifier or datasort`;
  }
  const isAtom = Store.tag(term) === 'atom';
  const member = isAtom ? Store.child(term, 0) : Store.tag(term);
  let found = false;
  if (isDs) {
    // admitted heads: nullary members + automaton transitions (slice 2)
    found = dsInfo.members.has(member) || dsInfo.trans.has(member);
  } else {
    for (const m of program.sorts.membersOf(sort)) if (m === member) { found = true; break; }
  }
  if (!found) return `'${member}' is not a member of ${isDs ? 'datasort' : 'classifier'} '${sort}'`;
  const sigHash = program.definitions && program.definitions.get(member);
  const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
  const arity = sig ? sig.argSorts.length : 0;
  if (isAtom) {
    if (arity !== 0) {
      return `witness head '${member}' is a constructor of arity ${arity}, not a nullary member`;
    }
  } else if (Store.arity(term) !== arity || arity === 0) {
    return `witness head is not '${member}' at its declared arity ${arity}`;
  }
  out.tokens.push(Store.put(DECIMATE_PREDS.DRAWN, [atom(member), atom(sort)]));
  const prior = (program.priors && program.priors.get(member)) || [1n, 1n];
  out.weight = [out.weight[0] * prior[0], out.weight[1] * prior[1]];
  if (!isAtom) {
    // composite witnesses recurse at the automaton's CHILD STATES when
    // the sort is a datasort with a transition (subtrees are checked in
    // the child LANGUAGES); ⊤/classifier sorts use the declared arg sorts
    const childSorts = isDs && dsInfo.trans.has(member)
      ? dsInfo.trans.get(member) : sig.argSorts;
    for (let i = 0; i < arity; i++) {
      const err = walkWitness(Store.child(term, i), childSorts[i], program, out);
      if (err) return err;
    }
  }
  return null;
}

/**
 * Validate the DATA of one draw step (no resource threading): the record
 * against the program's sort system and priors. Returns { error } or
 * { open, sort, witness, tokens } — tokens the ground drawn facts the
 * step must consume ([] for an open record).
 */
function checkDrawData(draw, { program }) {
  if (!draw) return { error: 'draw step carries no state.draw record' };
  if (!program || !program.sorts) {
    return { error: 'draw step requires a program with a sort system (opts.program)' };
  }

  // open record: token-free ∃-L (superpose_l / exists_l) with a
  // syntactically fresh evar — freshness is the TREE-level check
  if (draw.open) {
    const witness = draw.witness;
    if (witness === undefined || Store.tag(witness) !== 'evar') {
      return { error: 'open record needs an evar witness (the eigenvariable)' };
    }
    const sort = draw.sort !== undefined ? draw.sort : null;
    if (sort !== null && !program.sorts.isClassifier(sort) &&
        !(program.sorts.isDatasort && program.sorts.isDatasort(sort))) {
      return { error: `open sort '${sort}' is not a classifier or datasort` };
    }
    return { open: true, sort, witness, tokens: [] };
  }

  const { sort, member } = draw;
  if (typeof sort !== 'string' || typeof member !== 'string') {
    return { error: 'draw record needs { sort, member } names' };
  }
  const witness = draw.witness !== undefined ? draw.witness : atom(member);
  if (Store.tag(witness) === 'evar') {
    return { error: 'a draw witness cannot be an evar (use an open record for ∃-L)' };
  }
  const rootMember = Store.tag(witness) === 'atom' ? Store.child(witness, 0) : Store.tag(witness);
  if (rootMember !== member) {
    return { error: `witness head '${rootMember}' ≠ recorded member '${member}'` };
  }
  // Effective conditioning state (slice 4): a within-conditioned draw
  // records the product/datasort state it was drawn from; the member
  // must be admitted by it (states resolve deterministically from the
  // declared clauses — stateInfo — so this is re-derivation, not trust).
  if (draw.state !== undefined) {
    const sInfo = program.sorts.stateInfo ? program.sorts.stateInfo(draw.state) : null;
    if (!sInfo) return { error: `recorded conditioning state '${draw.state}' does not resolve` };
    const regInfo = program.sorts.stateInfo ? program.sorts.stateInfo(sort) : null;
    const waveBase = regInfo ? regInfo.base : sort;
    if (sInfo.base !== waveBase) {
      return { error: `conditioning state '${draw.state}' refines '${sInfo.base}' but the wave is over '${waveBase}'` };
    }
    if (!sInfo.members.has(member) && !sInfo.trans.has(member)) {
      return { error: `'${member}' is not admitted by the recorded conditioning state '${draw.state}'` };
    }
  }

  const out = { tokens: [], weight: [1n, 1n] };
  const err = walkWitness(witness, sort, program, out);
  if (err) return { error: err };

  // recorded weight, when present, must equal Π ρ over the drawn heads
  if (draw.weight != null) {
    const [n, d] = [BigInt(draw.weight[0]), BigInt(draw.weight[1])];
    if (d <= 0n || n < 0n) return { error: 'recorded draw weight is not a nonnegative rational' };
    if (n * out.weight[1] !== out.weight[0] * d) {
      return { error: `recorded weight ${n}/${d} ≠ declared prior product ${out.weight[0]}/${out.weight[1]} for the witness of '${member}'` };
    }
  }

  return { open: false, member, sort, witness, tokens: out.tokens, weight: out.weight };
}

/**
 * Full tree-level check of one draw node: data check + wave/token
 * consumption + opened-body introduction, in the kernel's lazy delta
 * discipline (same contract as the @fire tree step).
 */
function checkDrawTreeStep(node, childLeftovers, { calculus, program }) {
  const cs = (calculus && calculus.contextStructure) || Seq.DEFAULT_CONTEXT_STRUCTURE;
  const config = calculus.draw;
  if (!config) return { error: 'calculus declares no draw config' };
  const draw = node.state && node.state.draw;
  const data = checkDrawData(draw, { program });
  if (data.error) return data;

  if (node.premises.length !== 1) {
    return { error: `draw expects exactly 1 premise, got ${node.premises.length}` };
  }
  const seq = node.conclusion;
  const child = node.premises[0];
  if (child.conclusion.succedent !== seq.succedent) {
    return { error: 'draw must not change the succedent' };
  }

  const ST = config.stampTag;
  const roles = calculus.roles || {};
  // Union-pool read (TODO_0285) — zone-routing-independent, like fire-check.
  const pool0 = Context.fromArray(Seq.consumablePool(seq, cs));
  {
    let need = pool0;
    for (const tok of data.tokens) {
      if (!Context.has(need, tok)) {
        return { error: `token ${Store.pretty ? Store.pretty(tok) : tok} not in the conclusion context` };
      }
      need = Context.remove(need, tok);
    }
  }

  // candidate suspended facts, up to a stamp: superpose(atom(sort),
  // exists(body)) for a wave; bare exists(body) for an open with no sort
  const sortAtom = data.sort !== null ? atom(data.sort) : null;
  const candidates = [];
  for (const h of Context.toArray(pool0)) {
    if (draw.wave != null && h !== draw.wave) continue;
    const { inner, stamp } = stripStamp(h, ST);
    let ex;
    if (data.sort !== null) {
      if (Store.tag(inner) !== DECIMATE_PREDS.SUPERPOSE) continue;
      if (Store.child(inner, 0) !== sortAtom) continue;
      ex = Store.child(inner, 1);
    } else {
      ex = inner;
    }
    if (Store.tag(ex) !== 'exists') continue;
    candidates.push({ fact: h, body: Store.child(ex, 0), stamp });
  }
  if (candidates.length === 0) {
    return { error: draw.wave != null
      ? 'recorded wave fact not in the conclusion context (or malformed)'
      : data.sort !== null
        ? `no superposed wave over '${data.sort}' in the conclusion context`
        : 'no suspended exists fact in the conclusion context' };
  }

  // open records: the eigenvariable must be syntactically FRESH — it
  // occurs nowhere in the conclusion (candidates carry it only via the
  // premise's opened body)
  if (data.open) {
    const e = data.witness;
    for (const h of Context.toArray(pool0)) {
      if (occursIn(h, e)) return { error: 'open eigenvariable occurs in the conclusion (not fresh)' };
    }
    for (const h of Seq.getContext(seq, cs.copySource)) {
      if (occursIn(h, e)) return { error: 'open eigenvariable occurs in the conclusion (not fresh)' };
    }
    if (occursIn(seq.succedent, e)) {
      return { error: 'open eigenvariable occurs in the succedent (not fresh)' };
    }
  }

  const childLin = Context.fromArray(Seq.consumablePool(child.conclusion, cs));
  const childCart = new Set(Seq.getContext(child.conclusion, cs.copySource));

  let firstError = null;
  for (const cand of candidates) {
    // expected insertions: body opened with the witness, split like the driver
    const opened = debruijnSubst(cand.body, 0n, data.witness);
    const { linear, persistent } = splitBody(opened, roles);
    const intro = linear.map((f) =>
      cand.stamp === null ? f : Store.put(ST, [f, cand.stamp]));

    let pool = pool0;
    for (const tok of data.tokens) pool = Context.remove(pool, tok);
    pool = Context.remove(pool, cand.fact);

    // premise linear = intro ⊎ a sub-multiset of the remaining pool
    let di = childLin;
    let ok = true;
    for (const f of intro) {
      if (!Context.has(di, f)) { ok = false; firstError = firstError || 'premise missing an opened-body conjunct'; break; }
      di = Context.remove(di, f);
    }
    if (!ok) continue;
    if (!Context.contains(pool, di)) {
      firstError = firstError || 'premise carries formulas not in the available context';
      continue;
    }
    let persOk = true;
    for (const f of persistent) {
      if (!childCart.has(f)) { persOk = false; firstError = firstError || 'premise missing a persistent opened-body conjunct'; break; }
    }
    if (!persOk) continue;

    return { leftover: Context.merge(Context.subtract(pool, di), childLeftovers[0]) };
  }
  return { error: firstError || 'no wave candidate matches the premise' };
}

/**
 * Verify a claimed inside-mass table BY SUBSTITUTION (slice 4, round-2
 * spec B7): for every state reachable from `states`, the claimed mass
 * must satisfy its own equation m(s) = Σ_heads ρ(h)·Π m(children) in
 * exact rational arithmetic. This checker never runs the solver and
 * never imports it — uniqueness of the solution is the load-time
 * subcriticality discipline; plug-in equality is the whole check.
 * Returns { errors } (empty = verified).
 */
function verifyMasses(program, states) {
  const errors = [];
  const masses = program.masses;
  if (!masses) {
    if (states.length > 0) errors.push('claimed conditioning states but no mass table');
    return { errors };
  }
  const headsOf = (s) => {
    const info = program.sorts.stateInfo ? program.sorts.stateInfo(s) : null;
    if (info) {
      return [
        ...[...info.members].map((m) => ({ name: m, children: [] })),
        ...[...info.trans.entries()].map(([m, cs]) => ({ name: m, children: cs })),
      ];
    }
    if (program.sorts.isClassifier(s)) {
      return [...program.sorts.membersOf(s)].map((m) => {
        const h = program.definitions && program.definitions.get(m);
        const sig = h !== undefined ? _parseSignature(h) : null;
        return { name: m, children: sig ? sig.argSorts : [] };
      });
    }
    return null;
  };
  const seen = new Set();
  const stack = [...states];
  while (stack.length > 0) {
    const s = stack.pop();
    if (seen.has(s)) continue;
    seen.add(s);
    const hs = headsOf(s);
    if (hs === null) { errors.push(`state '${s}' does not resolve`); continue; }
    const m = masses.get(s);
    if (!m) { errors.push(`no claimed mass for state '${s}'`); continue; }
    let total = [0n, 1n];
    for (const h of hs) {
      let w = (program.priors && program.priors.get(h.name)) || [1n, 1n];
      for (const c of h.children) {
        const mc = masses.get(c);
        if (!mc) { errors.push(`no claimed mass for child state '${c}' of '${s}'`); w = null; break; }
        w = [w[0] * mc[0], w[1] * mc[1]];
        stack.push(c);
      }
      if (w === null) { total = null; break; }
      total = [total[0] * w[1] + w[0] * total[1], total[1] * w[1]];
    }
    if (total !== null && (m[0] * total[1] !== total[0] * m[1])) {
      errors.push(`claimed mass ${m[0]}/${m[1]} for '${s}' does not satisfy its equation (Σ heads = ${total[0]}/${total[1]})`);
    }
  }
  return { errors };
}

/**
 * The checker pair will binds via `calculus.stepCheckers` (kit.js
 * makeSequentLoader `draw:` option) — same slot routing as @fire.
 */
const drawChecker = Object.freeze({
  step(conclusion, state, { calculus, program }) {
    if (!calculus.draw) return { error: 'calculus declares no draw config' };
    const r = checkDrawData(state && state.draw, { program });
    if (r.error) return { error: r.error };
    // data-level presence: every token must be in the conclusion context
    const cs = calculus.contextStructure || Seq.DEFAULT_CONTEXT_STRUCTURE;
    let lin = Context.fromArray(Seq.consumablePool(conclusion, cs));
    for (const tok of r.tokens) {
      if (!Context.has(lin, tok)) return { error: 'draw token not in the conclusion context' };
      lin = Context.remove(lin, tok);
    }
    return {};
  },
  tree(node, childLeftovers, deps) {
    return checkDrawTreeStep(node, childLeftovers, deps);
  },
});

export { checkDrawData, checkDrawTreeStep, drawChecker, verifyMasses };
export default { checkDrawData, checkDrawTreeStep, drawChecker, verifyMasses };
