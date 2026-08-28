# till sequent calculus

Backward provability for till (TODO_0265 Phase 6b). Loaded via
`loadTillSequent()` (calculus/till/calculus-config.js): `till.calc` +
`till.rules`, the graded-syntax parser, and **the theory engine
(`tillTheory`) over the same numeric theory the forward engine runs**
(prelude/rat.ill) — backward grade side conditions and forward
`after (Q+D)` goals share one semantics (D13/TODO_0273).
Sequent-prover level (`createProver`/`createKernel`); `settle` remains the
execution semantics and doubles as the proof-search oracle for the timed
judgment (below). Theory: THY_0018 (the delay-graded lax monad) and
THY_0019 (timed matching / settle).

## Rules (till.rules)

| Fragment | Rules | Reading |
|---|---|---|
| multiplicatives, `with` | ill.rules verbatim | shared core |
| ω bang `!A` | `bang_r/l/l2` = promotion/dereliction/absorption, **template-matched** | the ω grade is part of the pattern — never fires on `!_k` |
| counted bang `!_k A` | `bang_l3/l4` (peel/weaken), `bang_r2/r3` (peel/zero) | `!_k A ≡ A ⊗ … ⊗ A` (k parcels, SELL/BLL) |
| graded monad `{A}@d` | `monad_l` (bind, `!qsub F E H` — the partial residual ⊖), `monad_r` (unit·sub, `!le 0 E`) | THY_0018 §4: the grade is an upper BOUND — graded-μ `{{A}@d}@e ⊢ {A}@(d+e)` and subeffecting `{A}@d ⊢ {A}@e` (d ≤ e) derivable; the critical path is a strict lower bound (`{A}@4` from `{{A}@2}@3` refuted) |
| `@fire` | `fire` (bound via `calculus.stepCheckers` — no annotation; TODO_0294) | THY_0018 §5's timed promotion as a first-class step: consume the recorded cohort, produce at `a ⊕ d`, `a` the forced join. No principal — keyed by name, never enumerated in tag-driven search (settle is the search strategy, the kernel the judge); verified against the PROGRAM'S declared rule data + theory (`lib/prover/timed/fire-check.js`), never by running settle |

**Counted-bang completeness** (THY_0023 Theorem 6, full induction on k):
`!_k A ⊣⊢ A^⊗k` derivable with the four rules for every ground k ∈ ℕ; with
cut admissibility (THY_0023 Theorem 8) a sequent is provable in the counted
reading iff its expansion is provable in the bang-free fragment. `bang_r3`
closes with no empty-context requirement, which is what lets rebuilds thread
mid-chain. The split/merge iso `!_{a+b} A ⊣⊢ !_a A ⊗ !_b A` follows; the
provability grid witnesses the instances.

**Metatheory** (THY_0023): cut admissibility (linear/lax/persistent cuts),
identity expansion (id admissible at ground-grade compound formulas from
atomic axioms), and WORK ADEQUACY — the pure calculus with rules encoded as
linear/counted hypotheses derives `{⊗R}@W` iff W bounds the execution's
TOTAL WORK (Σ of fired delays); makespan (max-plus) is contributed only by
the settle bridge (`tests/till-pure-adequacy.test.js` pins both columns).

Fences: ground grades only (non-numeric grades fail every side condition —
`!_W` goals are unprovable, not errors); surface `!_0` is the g0 **label**
(no rules — compile-time grade), count zero is binlit 0 and only arises
from peeling; `woplus` has no sequent rules (the weight needs a
probabilistic judgment — THY-A).

## The timed judgment (Stage 2)

Context entries may be stamped atoms `at(A,t)` — content-addressed
(formula, stamp) pairs (D5). Two additions:

- **Retiming** `at_l: G ; D, A@T1 ⊢ A@T2` (theory premise `!le T1 T2`) — a
  zero-premise template axiom: delaying availability is free, never early
  (THY_0018 §5). No ambient rule: an unstamped context atom does not
  retime (`a ⊬ a@3`); the bridge canonicalizes `A@0 ≡ A` at the state
  boundary instead.
- **The settle bridge** `monad_r2` (`@modeShift true`): for a sequent
  `Δ ⊢ {S}@T` with a settle-capable `opts.engineCalc`, the succedent
  monad grade is read as the **observation horizon** (THY_0018 §5, n=0
  boundary) — `settle(Δ, T)`, then exact `rightFocus` of `S` against the
  residual timed multiset, with `A@0 ≡ A` canonicalized on both sides.
  **Soundness, stated precisely (THY_0018 §5 bridge-soundness theorem):**
  each firing is one `@fire` instance, so bridge success implies both
  settle-reachability AND derivability — the bridge is a sound oracle.
  It is NOT complete for derivability, and derivability does not imply
  settle-reachability: `monad_r` (subeffecting) proves `a ⊢ {a}@d` for
  any `d ≥ 0` with no forward step. A `prove` failure refutes the sequent
  because BOTH paths (pure backward and bridge) are searched; a bridge
  failure alone refutes only the bridge route. **Elaboration (TODO_0294
  B2, default ON):** the bridge elaborates the settle event trace into a
  chain of `fire` steps closed by `monad_r` + decomposition
  (`lib/prover/timed/elaborate-trace.js`) — the returned tree contains NO
  `monad_r2` node and reaches FULL kernel verification against the
  program's rule data (`verifyTree(tree, { program:
  programFromCalc(engineCalc) })`). Elaboration is total on legal traces
  of supported rules (THY_0018 §5 residual partiality); unsupported
  shapes — whole-bind (`!_W`) antecedents, counted/bang consequents or
  succedents — fall back to the structural `monad_r2` oracle node
  reported in `unverified` (`opts.elaborate: false` forces the old
  behavior). `certifyRun` (B3) applies the same machinery to an arbitrary
  settle run, with the residual state itself as the certified goal;
  section 7 of `tools/fuzz-till.js` (B4) fuzzes it on random programs.
  Tried after the backward unit `monad_r`; without an engine it is simply
  inapplicable.

Adequacy tests (`tests/till-adequacy.test.js`) wrap the executable specs'
`#expect` gate hashes as sequents and witness THY_0018 Thm 5 (in-flight
atomicity as underivability) and Thm 3 (fission ≡ fusion) at the judgment
level. Counted bangs in bridge succedents are unsupported (rightFocus's
exponential case is ω-shaped — recorded residue).

## Template rules (.rules DSL extension)

A rule is a **template rule** iff it has theory premises, `@template true`,
or a compound premise formula; otherwise it compiles to the index-based
descriptor exactly as before (zero-delta for ill.rules). A **theory
premise** (TODO_0273) is a premise line without a turnstile starting with
`!` — `<- !qsub F E H` — read as a goal over the calculus's theory engine
(`calculus.theory`, for till the numeric theory prelude/rat.ill with the
FFI face as O(1) fast path). Variables not bound by the conclusion are
OUTPUT vars, bound by the derivation and visible to later goals and the
sequent premises. Template apply:

1. unify the principal pattern against the focused formula (pattern
   metavars bind; sequent content is rigid),
2. for left rules, unify the conclusion-succedent pattern (`@side l`
   forces left-principal detection when the succedent is compound),
3. discharge theory premises in order — underivable ⇒ rule inapplicable
   (`!qsub F E H` binds H to F ⊖ E and has no proof when F < E: the fence
   is derivational, THY_0022; non-numeric grades fail structurally),
4. instantiate premise patterns by substitution.

Zero-premise template rules still run the full check, so theory goals are
enforced in search **and** kernel verification (`verifyStep` recomputes
premises via the same `makePremises`; for left rules it tries every
context formula with the principal's tag). Variable boundness is validated
at load time. Template rules require the metavar-producing parser
(`multiCharFreevars`) — test sequents therefore use lowercase atoms;
uppercase identifiers are pattern variables.

## Kernel verification contract

`verifyTree` checks rule shapes **and** linear resource accounting: it
re-threads the prover's lazy delta discipline (each premise context =
rule-introduced formulas ⊎ a sub-multiset of the unconsumed pool;
leftovers flow through siblings; the root leftover must be empty), so
forged trees that leak context (`a ⊗ b ⊢ a` via id) are rejected. `fire`
steps are FULLY re-derived against the program's declared rule data
(`fire-check.js`, needs `opts.program`): antecedent/consequent bags under
the recorded theta, forced-join activation, done stamp via the `qsub`
partial residual, read survival, persistent goals/conclusions, plus
resource threading — they never enter `unverified`. Steps the kernel
cannot re-derive are accepted but reported in `result.unverified`:
fallback settle-bridge steps (`'modeSwitch'` — only for traces the
elaborator marks unsupported) and quantifier steps with fresh
eigenvariables (`'binding'`). **Full verification = `valid &&
!unverified`**; pure sequent proofs (all of Stage 1) meet it, and since
TODO_0294 B2 elaborated bridge trees (Stage 2 adequacy) meet it too.
`verifyStep` alone is shape-only — never a resource check.

Tests: `tests/till-prover.test.js` (provability grid, kernel gates),
`tests/rules2-template.test.js` (DSL compilation + validation).

## Open gap: woplus proof theory (THY-A)

`woplus` (`A +[q] B`, weighted additive disjunction, weight `q ∈ [0,1]`) is the
one till connective with **operational semantics but no sequent rules** — the
weight is a probabilistic annotation the current additive left/right rules
cannot express. This is a named open contribution, tracked as **THY-A**; the
proof-theory draft (probabilistic/weighted judgment, cut cases, and how it
relates to `oplus`) lives in `doc/theory/0021_weighted-additive-disjunction.md`.
Until it lands, `woplus` is a consequent-only forward form: `compile.js` rejects
it in antecedents, and the sequent prover has no `woplus_l`/`woplus_r`.
