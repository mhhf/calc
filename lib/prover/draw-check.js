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
 *   - the witness term's HEAD is c: atom(c) for a nullary member, a
 *     c-headed term of the declared arity for a constructor member
 *     (rung 2 — lazy draws record the head only, so the TOKEN is always
 *     the ground `drawn(atom(c), atom(s))`; THY_0027 §1 fences)
 *   - the recorded weight, when present, equals the declared prior
 *     ρ(c) = @w ratio (program.priors; unannotated member = 1) — weight
 *     is DATA re-derived from the program, never trusted from the record
 *   - premise = conclusion − wave − token ⊎ body[witness/x] split at the
 *     wave's stamp (splitBody — the same definition the driver uses)
 *
 * Config comes from `calculus.draw` (declared at the calculus assembly
 * point — kit.js makeSequentLoader): { stampTag }. The kernel routes the
 * binding via calculus.stepCheckers and knows nothing about draws.
 */

import Store from '../kernel/store.js';
import Seq from '../kernel/sequent.js';
import Context from './context.js';
import { debruijnSubst } from '../kernel/substitute.js';
import { splitBody } from '../engine/decimate.js';
import { _parseSignature } from '../engine/type-check.js';

const atom = (n) => Store.put('atom', [n]);

/** Strip an optional stamp wrapper. */
function stripStamp(h, stampTag) {
  return Store.tag(h) === stampTag
    ? { inner: Store.child(h, 0), stamp: Store.child(h, 1) }
    : { inner: h, stamp: null };
}

/**
 * Validate the DATA of one draw step (no resource threading): the record
 * against the program's sort system and priors. Returns { error } or
 * { member, sort, witness, token } (token = the ground drawn fact).
 */
function checkDrawData(draw, { program }) {
  if (!draw) return { error: 'draw step carries no state.draw record' };
  if (!program || !program.sorts) {
    return { error: 'draw step requires a program with a sort system (opts.program)' };
  }
  const { sort, member } = draw;
  if (typeof sort !== 'string' || typeof member !== 'string') {
    return { error: 'draw record needs { sort, member } names' };
  }
  if (!program.sorts.isClassifier(sort)) {
    return { error: `draw sort '${sort}' is not a classifier` };
  }
  let found = false;
  for (const m of program.sorts.membersOf(sort)) if (m === member) { found = true; break; }
  if (!found) return { error: `'${member}' is not a member of classifier '${sort}'` };

  // witness head discipline (rung 1: the member atom; rung 2: a
  // member-headed term of the declared constructor arity)
  const sigHash = program.definitions && program.definitions.get(member);
  const sig = sigHash !== undefined ? _parseSignature(sigHash) : null;
  const arity = sig ? sig.argSorts.length : 0;
  const witness = draw.witness !== undefined ? draw.witness : atom(member);
  if (arity === 0) {
    if (witness !== atom(member)) {
      return { error: `witness for nullary member '${member}' must be the member atom` };
    }
  } else if (Store.tag(witness) !== member || Store.arity(witness) !== arity) {
    return { error: `witness head is not '${member}' at its declared arity ${arity}` };
  }

  // declared prior ρ(c) — the record's weight, when present, must agree
  const declared = (program.priors && program.priors.get(member)) || [1n, 1n];
  if (draw.weight != null) {
    const [n, d] = [BigInt(draw.weight[0]), BigInt(draw.weight[1])];
    if (d <= 0n || n < 0n) return { error: 'recorded draw weight is not a nonnegative rational' };
    if (n * declared[1] !== declared[0] * d) {
      return { error: `recorded weight ${n}/${d} ≠ declared prior ${declared[0]}/${declared[1]} for '${member}'` };
    }
  }

  return { member, sort, witness, token: Store.put('drawn', [atom(member), atom(sort)]) };
}

/**
 * Full tree-level check of one draw node: data check + wave/token
 * consumption + opened-body introduction, in the kernel's lazy delta
 * discipline (same contract as the @fire tree step).
 */
function checkDrawTreeStep(node, childLeftovers, { calculus, program }) {
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
  const pool0 = Context.fromArray(Seq.getContext(seq, 'linear'));
  if (!Context.has(pool0, data.token)) {
    return { error: `token ${Store.pretty ? Store.pretty(data.token) : data.token} not in the conclusion context` };
  }

  // candidate wave facts: superpose(atom(sort), exists(body)) up to a stamp
  const sortAtom = atom(data.sort);
  const candidates = [];
  for (const h of Context.toArray(pool0)) {
    if (draw.wave != null && h !== draw.wave) continue;
    const { inner, stamp } = stripStamp(h, ST);
    if (Store.tag(inner) !== 'superpose') continue;
    if (Store.child(inner, 0) !== sortAtom) continue;
    const ex = Store.child(inner, 1);
    if (Store.tag(ex) !== 'exists') continue;
    candidates.push({ fact: h, body: Store.child(ex, 0), stamp });
  }
  if (candidates.length === 0) {
    return { error: draw.wave != null
      ? 'recorded wave fact not in the conclusion context (or malformed)'
      : `no superposed wave over '${data.sort}' in the conclusion context` };
  }

  const childLin = Context.fromArray(Seq.getContext(child.conclusion, 'linear'));
  const childCart = new Set(Seq.getContext(child.conclusion, 'cartesian'));

  let firstError = null;
  for (const cand of candidates) {
    // expected insertions: body opened with the witness, split like the driver
    const opened = debruijnSubst(cand.body, 0n, data.witness);
    const { linear, persistent } = splitBody(opened, roles);
    const intro = linear.map((f) =>
      cand.stamp === null ? f : Store.put(ST, [f, cand.stamp]));

    let pool = Context.remove(pool0, data.token);
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
 * The checker pair will binds via `calculus.stepCheckers` (kit.js
 * makeSequentLoader `draw:` option) — same slot routing as @fire.
 */
const drawChecker = Object.freeze({
  step(conclusion, state, { calculus, program }) {
    if (!calculus.draw) return { error: 'calculus declares no draw config' };
    const r = checkDrawData(state && state.draw, { program });
    if (r.error) return { error: r.error };
    // data-level presence: the token must be in the conclusion context
    const lin = Seq.getContext(conclusion, 'linear');
    if (!lin.includes(r.token)) return { error: 'draw token not in the conclusion context' };
    return {};
  },
  tree(node, childLeftovers, deps) {
    return checkDrawTreeStep(node, childLeftovers, deps);
  },
});

export { checkDrawData, checkDrawTreeStep, drawChecker };
export default { checkDrawData, checkDrawTreeStep, drawChecker };
