/**
 * proof-tree/v1 — canonical JSON serialization of a ProofTree.
 *
 * This is the contract between the prover/engine and viewer renderers
 * (bussproofs, Gentzen, tactic-script, indented-tree). The proof tree
 * IS the proof term (Curry-Howard); we serialize its structure without
 * pre-rendering to strings, so one shape supports many layouts.
 *
 * Top-level shape:
 *   {
 *     format: "proof-tree/v1",
 *     calculus: string,
 *     profile: string,
 *     profileHash?: string,
 *     formulas: { [key]: FormulaAST },
 *     root: ProofNode,
 *     meta?: object              // open bag, passed through verbatim
 *   }
 *
 * FormulaAST (tag-dispatched, extensible):
 *   atom/freevar/metavar         → { tag, name }
 *   strlit                       → { tag, value }               (string)
 *   binlit/bound/evar            → { tag, value }               (decimal string)
 *   charlit                      → { tag, codepoint }           (number)
 *   arrlit                       → { tag, elements: [ref, …] }
 *   one/zero/ (nullary)          → { tag }
 *   everything else (term-only)  → { tag, args: [ref, …] }      (tensor,
 *                                    loli, with, oplus, bang, monad,
 *                                    exists, forall, predicates, …)
 *
 * Non-standard mixed children (a string or bigint on a tag not in the
 * primitive-value sets above) land in `extras: [{kind, value}]` — the
 * format stays lossless even for calculi we haven't seen yet.
 *
 * ProofNode:
 *   { id, sequent, rule, premises, proven }
 *   — id is an FNV-1a content hash over (rule, canonical sequent,
 *     premise ids); identical sub-proofs in the same serialize() call
 *     carry identical ids.
 *   — rule is a string or null (null = unproven goal).
 *
 * Sequent:
 *   { contexts: { [name]: [ref, …] }, succedent: ref | null }
 *   — context map is preserved verbatim from the internal Seq (linear,
 *     cartesian, or whatever the calculus uses), not flattened.
 *
 * Stability guarantees (v1):
 *   — Within one serialize() call: byte-stable — same ProofTree →
 *     same JSON (pool keys assigned deterministically via DFS).
 *   — Same process, same Store state, same tree built again: byte-stable.
 *   — Cross-process portability of ids/keys is NOT guaranteed in v1
 *     (pool keys are sequential f1, f2, …; node ids hash over them).
 *     Format v2 may introduce content-addressed keys if needed.
 */

'use strict';

const Store = require('../kernel/store');
const { hashString, hashCombine2 } = require('../hash');

const FORMAT_VERSION = 'proof-tree/v1';

// Tags whose single string child is a human-readable name.
const NAME_TAGS = new Set(['atom', 'freevar', 'metavar']);
// Tags whose single string child is a literal value.
const STRING_VALUE_TAGS = new Set(['strlit']);
// Tags whose single bigint child is an integer value (de Bruijn index,
// literal value, existential-variable index).
const BIGINT_VALUE_TAGS = new Set(['binlit', 'bound', 'evar']);

function newContext(opts) {
  const o = opts || {};
  return {
    calculus: o.calculus || 'unknown',
    profile: o.profile || 'default',
    profileHash: o.profileHash || null,
    meta: o.meta || null,
    formulas: Object.create(null),
    hashToKey: new Map(),
    nextKey: 1,
  };
}

function makeRef(h, ctx) {
  if (!Store.isTerm(h)) return null;
  const existing = ctx.hashToKey.get(h);
  if (existing !== undefined) return existing;

  const tagName = Store.tag(h);
  const obj = { tag: tagName };

  if (tagName === 'charlit') {
    // Raw uint32 codepoint — not a term ref.
    obj.codepoint = Store.child(h, 0);
  } else if (tagName === 'arrlit') {
    const elems = Store.getArrayElements(h) || new Uint32Array(0);
    const arr = new Array(elems.length);
    for (let i = 0; i < elems.length; i++) arr[i] = makeRef(elems[i], ctx);
    obj.elements = arr;
  } else {
    const ch = Store.children(h);
    if (ch.length === 0) {
      // nullary (one, zero, empty, any, …): { tag } only.
    } else if (NAME_TAGS.has(tagName) && ch.length === 1 && typeof ch[0] === 'string') {
      obj.name = ch[0];
    } else if (STRING_VALUE_TAGS.has(tagName) && ch.length === 1 && typeof ch[0] === 'string') {
      obj.value = ch[0];
    } else if (BIGINT_VALUE_TAGS.has(tagName) && ch.length === 1 && typeof ch[0] === 'bigint') {
      obj.value = ch[0].toString();
    } else {
      // Generic: term-ref children → args[]; any stray primitives →
      // extras[] so nothing is lost for future/user-defined tags.
      const args = [];
      const extras = [];
      for (let i = 0; i < ch.length; i++) {
        const c = ch[i];
        if (typeof c === 'number') {
          args.push(makeRef(c, ctx));
        } else if (typeof c === 'string') {
          extras.push({ kind: 'string', value: c });
        } else if (typeof c === 'bigint') {
          extras.push({ kind: 'int', value: c.toString() });
        } else if (c instanceof Uint32Array) {
          const elems = new Array(c.length);
          for (let j = 0; j < c.length; j++) elems[j] = makeRef(c[j], ctx);
          extras.push({ kind: 'array', elements: elems });
        } else {
          extras.push({ kind: 'other', value: String(c) });
        }
      }
      if (args.length > 0) obj.args = args;
      if (extras.length > 0) obj.extras = extras;
    }
  }

  // Assign key AFTER children so deepest formulas get the earliest keys
  // (bottom-up DFS). JSON object insertion order reflects this.
  const key = 'f' + (ctx.nextKey++);
  ctx.hashToKey.set(h, key);
  ctx.formulas[key] = obj;
  return key;
}

function serializeFormula(h, ctx) {
  return makeRef(h, ctx);
}

function serializeSequent(s, ctx) {
  if (!s) return { contexts: Object.create(null), succedent: null };
  const contexts = Object.create(null);
  // Preserve calculus-native context names (linear, cartesian, …) and
  // the multiset order they were stored in.
  const names = Object.keys(s.contexts || {});
  for (const name of names) {
    const list = s.contexts[name] || [];
    const refs = new Array(list.length);
    for (let i = 0; i < list.length; i++) refs[i] = makeRef(list[i], ctx);
    contexts[name] = refs;
  }
  const succedent = s.succedent ? makeRef(s.succedent, ctx) : null;
  return { contexts, succedent };
}

/**
 * Content-derived node id. Canonicalizes context ref lists (sort) so
 * multiset-equivalent sequents hash the same. Premise ids are already
 * stable inductively.
 */
function computeNodeId(rule, sequentJson, premiseIds) {
  let h = hashString(FORMAT_VERSION);
  h = hashCombine2(h, hashString(rule || ''));
  const parts = [];
  const ctxNames = Object.keys(sequentJson.contexts).sort();
  for (const n of ctxNames) {
    const refs = sequentJson.contexts[n].slice().sort();
    parts.push(n + ':' + refs.join(','));
  }
  parts.push('|-' + (sequentJson.succedent || ''));
  h = hashCombine2(h, hashString(parts.join(';')));
  for (let i = 0; i < premiseIds.length; i++) {
    h = hashCombine2(h, hashString(premiseIds[i]));
  }
  return 'n' + (h >>> 0).toString(16).padStart(8, '0');
}

function serializeNode(pt, ctx) {
  const sequentJson = serializeSequent(pt.conclusion, ctx);
  const premises = [];
  const list = pt.premises || [];
  for (let i = 0; i < list.length; i++) premises.push(serializeNode(list[i], ctx));
  const premiseIds = premises.map((p) => p.id);
  const id = computeNodeId(pt.rule, sequentJson, premiseIds);
  return {
    id,
    sequent: sequentJson,
    rule: pt.rule || null,
    premises,
    proven: !!pt.proven,
  };
}

function serializeTree(pt, opts) {
  const ctx = newContext(opts);
  const root = serializeNode(pt, ctx);
  const out = {
    format: FORMAT_VERSION,
    calculus: ctx.calculus,
    profile: ctx.profile,
  };
  if (ctx.profileHash) out.profileHash = ctx.profileHash;
  out.formulas = ctx.formulas;
  out.root = root;
  if (ctx.meta) out.meta = ctx.meta;
  return out;
}

module.exports = {
  FORMAT_VERSION,
  serializeTree,
  serializeFormula,
  serializeSequent,
  computeNodeId,
  // Exposed for targeted tests / composition; not part of the public
  // API contract for consumers.
  _newContext: newContext,
};
