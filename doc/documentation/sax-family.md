# The SAX Family — Second Structural Family

The semi-axiomatic sequent calculus (DeYoung–Pfenning–Pruiksma, FSCD 2020)
as calc's second structural family (TODO_0309). `family/sax/` +
`calculus/sax/` are the empirical test of family-genericity: the engine and
prover receive both families as data and cannot tell them apart.

## What it is

**Family** (`family/sax/`): the single-zone linear judgment `Δ ⊢ C`,
declared as data — `@position_modes "linear linear"`, exchange only. The
derived `contextStructure` is the first with `copySource: null` (no
cartesian zone). All four engine protocol slots (`proveNaive`,
`matchDynamicRule`, `drainDynamicRules`, `resolveEx`) are **null**: SAX's
forward regime needs only the engine's generic baseline. The four slots are
exactly the LNL-shaped part of the family protocol.

**Calculus** (`calculus/sax/`): ILL's propositional connective table
(`sax.calc`, explicit `@polarity` on every connective) under the
semi-axiomatic rule regime (`sax.rules`):

- every **non-invertible** rule is a zero-premise **axiom** (X-rule):
  `A, B |- A * B` (⊗X), `A, A -o B |- B` (⊸X), `A & B |- A` (&X₁),
  `A |- A + B` (⊕X₁), `|- I` (1X);
- **invertible** rules are unchanged from G3-ILL;
- **cut is explicit** — the computation rule. Search realizes the
  snip-bounded discipline: cut formulas come from the sequent's proper
  subformula closure (finite by FSCD Thm. 7), tried as the last focus
  alternative. `A ⊗ (B ⊗ C) ⊢ (A ⊗ B) ⊗ C` and `A ⊸ B, B ⊸ C ⊢ A ⊸ C`
  have no snip-free proofs and are the canonical pins.

The polarity table makes the SAX/focusing correspondence exact: the axiom
side of each connective is precisely its non-invertible (focus-phase) side.

**Operational semantics** (`programs/machine.sax`): the propositional
core of the FSCD Fig. 6 multiset-rewriting machine, sax-native —
writes (pair/unit/injection markers), forward, case, and unit-wait;
allocation/cut (fresh-cell spawning) and the negative connectives are
deferred. `proc D P` (linear process),
`hole D` (linear allocated-unwritten cell), `!cell D V` (persistent
write-once cell). Addressing is SNAX-style (MFPS 2022 §3.2): pair
components live at calculable projections `p1 D` / `p2 D`, so every machine
step is first-order and binder-free (the FSCD values embed addresses, which
needs binders in continuations — deferred to the store-as-SNAX phase).
Confluence (FSCD Thm. 10) is checked empirically: explore over all
interleavings reaches one quiescent state; violating write-once is
observably non-confluent (`tests/engine/sax-forward.test.js`, and the same
encoding under plain ILL in `tests/engine/sax-encoding.test.js`).

## Generic capability the build added (all descriptor-driven, no `sax` literal in lib/)

- **Exact axioms with companions** (`rules2-parser.js` → `rule-interpreter.js`
  → `generic.js`/`kernel.js`): a zero-premise rule with a principal and no
  context vars compiles as a template with a `companions` list; apply-time
  consumes them from the pool (the `{ premises, consume }` contract).
  `zero_l`-style discarding axioms (context var present) keep the old path.
- **Explicit cut** (`rules2-parser.js` detection → `focused.js` search →
  `kernel.js` verification): the canonical no-principal shape
  `D, D' |- C <- D |- A <- D', A |- C` marks `descriptor.cut`; search
  instantiates the cut formula from the subformula closure (path-scoped
  loop guard); the kernel re-derives the split from the recorded premises —
  an unconsumed cut formula leaks into the root leftover check.
- **Matching completeness** (P0, `match.js`/`forward.js`/`state-ops.js`):
  tier-2 backtracking join on non-functional joins; fingerprint-index
  ambiguity degradation; `_byKey` invalidation when explore mutates the
  indexed group. These were latent generic bugs, observable the moment a
  program had several similar processes.
- **Loader**: self-`@extends` resolution guard (a calculus named after its
  family must resolve `family/<name>/`, not itself); null-`copySource`
  guards in premise construction; untimed `=>` spec dispatch
  (`spec-runner.js` exec-to-quiescence).

## Recorded interface gaps (the remaining LNL-shape — feeds the parametric ⊢_fwd, TODO_0309 P3)

1. **Polarity inference ignores axiom-flow rules** — a calculus whose right
   rules are all axioms gets no inferred polarities; `sax.calc` annotates
   explicitly. A principled extension (exact right axiom ⇒ positive, exact
   left axiom ⇒ negative) is sound for SAX but would repolarize till's
   deliberately-unpolarized template axioms (`at_l`) — deferred.
2. **Companion matching is exact-hash** — a companion instantiating to a
   non-ground pattern is not unified against the pool. Ground-goal search
   is unaffected.
3. **Persistent-witness commitment** — tier-2 backtracks linear candidate
   choices but `provePersistent` still commits per goal; a multi-witness
   persistent goal feeding a later persistent goal can under-match.
4. **explore branches per rule, not per match** — `findAllMatches` returns
   one match per rule, so explore under-approximates interleavings (final
   states of confluent programs are unaffected; relevant to the
   explore-completeness theorem, TODO_0042).
5. **Manual strategy has no cut action** — `applicableRules` never
   enumerates no-principal rules; cut is auto-search and kernel only.
6. **`.rules` descriptor schema field names** (`cartesian`/`linear`) remain
   LNL-shaped serialization artifacts, remapped via `contextStructure`.

## Running

```bash
npm run test:sax        # executable specs (calculus/sax/tests/)
npm test                # includes tests/sax-prover.test.js + engine guards
```
