# NEXT: two work items (handoff doc — DELETE after both land)

Written 2026-08-20 for a fresh context. Denis's order: **do §4 first, then §5.**
Both are follow-ups to the TODO_0011 rung-1 arc (all landed on `main`, latest
commits: `424ffa88` rung-1 sorts, `d9ca95a8` §3 numeric collapse, `91f906b5`
D4 revision). Standing rules: never `git push`; commit at green checkpoints;
`hq` CLI needs `dangerouslyDisableSandbox: true`; PRF golden pins
(tests/engine/till-settle.test.js:~118, till-woplus.test.js:~93) legitimately
re-roll on any arena/interning shift — verify intent, then re-pin (protocol in
the test comments). TODO_0271 (store-identity audit) is parked — do NOT start it.

Gates to run: `npm test` (fast), `npm run test:ill`, `npm run test:till`,
`npm run test:noffi:till`, and for parser work `npm run test:bun`.

---

## §4. `subsort` rename + materialized closure (~2–3 h)

**Goal**: rules can carry `!subsort X resource` premises, answered totally and
correctly — by making the closure ORDINARY GROUND FACTS at load. This DELETES
the committed-choice completeness caveat instead of working around it (Denis's
call: "just generate the transitive closure at compile time — the DAG is
small"). No FFI handler needed (facts enumerate unbound queries naturally).

**Rename** (Denis: `leq` reads as arithmetic and collides with the collapsed
numeric `le`): the closure predicate is **`subsort`**. The declared-edge
predicate `sedge` stays (internal generator name — Denis only vetoed leq).

**Current state to change**:
- `lib/engine/sorts.js`: `SORT_PREDS = { EDGE: 'sedge', LEQ: 'leq', SORT, TYPE }`;
  `certifyLeq(system, a, b, clauses, definitions)` = BFS path over
  `system.edges` + per-hop `sedge` proofs (the "certificate turn" — existed
  because the backchainer is committed-choice per subgoal, so the recursive
  `leq/step` clause is incomplete over multi-edge nodes).
- `calculus/till/prelude/sorts.till`: declares `sort`, `sedge`, `leq` +
  clauses `leq/refl`, `leq/step`.
- `lib/engine/convert.js` loadFile pass 1: `A <: B.` decl → synthesizes unit
  clause `sedge/A_B: sedge A B` into the clauses Map.
- `tests/sorts-fuzz.test.js`: table ≡ certifyLeq ≡ independent reachability.
- `doc/theory/0020_refinement-sorts.md` §3: documents the certificate turn.

**Steps**:
1. sorts.till: rename `leq` decl → `subsort: (a: sort) -> (b: sort) -> type.`;
   keep ONE clause `subsort/refl: subsort S S.`; DELETE `leq/step` (and the
   old leq decl/clauses). Update the file header (facts are the closure,
   synthesized at load; the loader's closure computation is the one-time
   deduction).
2. sorts.js: `SORT_PREDS.LEQ` → `SORT_PREDS.SUB = 'subsort'` (fix all refs).
   DELETE `certifyLeq` (superseded). Expose the ancestor pairs, e.g.
   `closurePairs()` iterating (a, b) with a≤b, a≠b, over declared+calc edges
   (classifier≤type pairs: EXCLUDE — 'type' isn't an atom; keep that
   definitional as today).
3. `lib/engine/index.js` `_buildCalc`: after `buildSortSystem` succeeds,
   inject ground facts into `clauses`:
   `clauses.set('subsort/'+a+'_'+b, { hash: Store.put('subsort',[atom a, atom b]), premises: [] })`
   for every closure pair. Injection is BEFORE checkAll (facts get
   sort-checked: atoms at (a: sort) pass via isSort meta-membership — already
   works, same as sedge facts) and before `backward.buildIndex` (so queries
   see them). Idempotent on cache-restore re-entry (Map.set, same content).
4. tests/sorts-fuzz.test.js: replace certifyLeq with a real backchain query
   `prove(subsort a b)` — assert table ≡ QUERY ≡ independent reachability.
   The query is now complete (facts + refl only), which is the point: assert
   the OLD failing shape too (multi-out-edge node, e.g. edges a→b, a→c, c→d:
   query a≤d must prove — this was the live incompleteness before).
5. tests/engine/till-sorts.test.js: hygiene error strings mention
   'sedge'/'leq' ("needs the sorts prelude (declares ...)") — update message
   + test regex. grep -rn "leq" lib tests tools calculus doc CLAUDE.md and
   sweep every reference.
6. THY_0020 §3 rewrite: "the certificate turn" → "the materialized closure"
   (loader computes the closure once = the deduction; facts are its
   theorems; in-logic `!subsort X resource` premises are total; the
   committed-choice caveat is GONE, not worked around). Also fix §5's
   passing mentions if any. CLAUDE.md Refinement Sorts section: update
   machinery names + drop the certifyLeq mention.
7. Optional demo: a PP2 rule with a `!subsort`-style premise is possible but
   classifiers already cover PP2's needs — skip unless trivial.
8. Gates + commit. Update TODO_0011 via hq (patch-body + bump): rename +
   materialization landed, caveat deleted.

---

## §5. Parser fold + ambiguity instrument + `4 wood` sugar (own session)

**Goal**: one grammar mechanism (sorted templates, 0268-A) instead of four
hand-written families in `lib/parser/earley-grammar.js` (infix `operators`,
`circumfix` `{ }`, `gradedPrefix` `!`, plus `unaryPrefix`/`nullary` tables);
plus first-class ambiguity detection; plus attempt `4 wood` parcel sugar.
Order matters: **instrument FIRST, fold second, sugar third.**

**5a. Ambiguity detector (~20 LOC, lib/parser/earley.js)**. Facts: the accept
loop takes the FIRST accepting item and breaks (earley.js ~line 284); each
chart item keeps ONE back-pointer — `add()` drops a second derivation of the
same (rule, dot, origin) item, so ambiguity is silently first-wins today (no
SPPF). Change: in `add()`, when the item exists and a DISTINCT new
back-pointer arrives, mark it / bump a per-parse counter; also detect
multiple accepting items. Expose a strict mode (throw on ambiguity) +
always-on counter. Caveat (documented): item-level dual-backs are an
over-approximation (dup may sit off the accepted spine) — fine for an
instrument; refine to spine-only if the corpus sweep is noisy. Context for
docs: static CFG ambiguity is UNDECIDABLE — per-input detection is the
honest maximum; the generator-level collision throws (duplicate circumfix,
one graded prefix, mixfix-shape errors) are the decidable static layer we
already have.

**5b. Acceptance harness (build BEFORE folding)**:
- Corpus sweep: parse every .ill/.till under calculus/ + tests/fixtures with
  strict ambiguity ON → zero findings = baseline.
- Comparative fuzz: keep the legacy family-extraction path behind a flag
  during transition; generative fuzz (sample strings FROM the grammar
  productions) + full corpus: parse under legacy and folded grammars →
  HASH-IDENTICAL results required. Only after parity: delete the legacy
  code paths. Expect NO PRF golden re-pins (identical hashes) — a needed
  re-pin is a red flag, not routine.
- Perf: same Earley engine either way (both paths emit productions into the
  same grammar) — verify with a parse-time comparison on the corpus.

**5c. The fold**: re-express `*`-style infix (operators table), `{ #2 }`
circumfix, `! #2` gradedPrefix (incl. `!_k`/`!_W` suffix forms — check the
grade-atom actions g0/gw at earley-grammar.js ~440-490), and keyword
prefix/nullary forms as declared sorted templates. The one-aux-sort fence is
already gone (all cross-sort holes share the GRADE chain; sorts are the
checker's job — commit `424ffa88` area). deriveRoles/computationRole read
@category annotations, not the parser tables — unaffected, but verify.

**5d. `4 wood` sugar** (parcel = `!_4 wood`, D4-revised reading "4 of any
age"; the shell already renders costs as "2 spc_s"). Decisions from
discussion: `f g q` is a NON-issue (application is flat first-order:
f(g, q) always; nesting needs parens). Risk lives ONLY where NUMBER IDENT
juxtaposition meets application arguments (`f 4 wood` must stay f(4, wood);
`shelf r 4 * wood` must stay shelf(r,4) ⊗ wood). Plan: add the parcel
production at FORMULA-OPERAND positions only, run the ambiguity sweep; if
any clash → fall back to Denis's fused form **`4wood`** (lexer: NUMBER
immediately followed by ident-start char, NO whitespace → one PARCEL token —
lexically unambiguous by construction since identifiers can't start with a
digit). If the sugar lands, optionally teach the renderer to emit it.

**Files**: lib/parser/earley.js (detector), lib/parser/earley-grammar.js
(fold + sugar), tests/engine/sorted-templates.test.js (extend), new
tests/parser-fold-fuzz.test.js (harness), tools/? none. Gates: full set incl.
test:bun; corpus hash-parity is THE acceptance criterion.

**hq bookkeeping**: this is TODO_0268's leftover item — record landing there
(patch-body + bump), not in 0011.
