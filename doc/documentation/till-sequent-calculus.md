# till sequent calculus (graded fragment)

Backward provability for till (TODO_0265 Phase 6b Stage 1). Loaded via
`loadTillSequent()` (calculus/till/calculus-config.js): `till.calc` +
`till.rules`, the graded-syntax parser, and **the same `tillGrades` record
the timed scheduler reads** — one grade algebra, two faces (D13).
Sequent-prover level only (`createProver`/`createKernel`); `settle` remains
the execution semantics. The timed judgment (stamps in the context) is
Stage 2, gated on THY-A/THY-B.

## Rules (till.rules)

| Fragment | Rules | Reading |
|---|---|---|
| multiplicatives, `with` | ill.rules verbatim | shared core |
| ω bang `!A` | `bang_r/l/l2` = promotion/dereliction/absorption, **template-matched** | the ω grade is part of the pattern — never fires on `!_k` |
| counted bang `!_k A` | `bang_l3/l4` (peel/weaken), `bang_r2/r3` (peel/zero) | `!_k A ≡ A ⊗ … ⊗ A` (k parcels, SELL/BLL) |
| graded monad `{A}@d` | `gmonad_l` (bind, `H := F − E` monus), `gmonad_r` (unit·sub, `E ≥ 0`) | THY_0018 §4: the grade is an upper BOUND — graded-μ `{{A}@d}@e ⊢ {A}@(d+e)` and subeffecting `{A}@d ⊢ {A}@e` (d ≤ e) derivable; the critical path is a strict lower bound (`{A}@4` from `{{A}@2}@3` refuted) |

Fences: ground grades only (non-numeric grades fail every side condition —
`!_W` goals are unprovable, not errors); surface `!_0` is the g0 **label**
(no rules — compile-time grade), count zero is binlit 0 and only arises
from peeling; `woplus` has no sequent rules (the weight needs a
probabilistic judgment — THY-A); no modeShift (`gmonad_r` is pure η — the
settle bridge is Stage 2).

## Template rules (.rules DSL extension)

A rule is a **template rule** iff it has `@grade` lines, `@template true`,
or a compound premise formula; otherwise it compiles to the index-based
descriptor exactly as before (zero-delta for ill.rules). Template apply:

1. unify the principal pattern against the focused formula (pattern
   metavars bind; sequent content is rigid),
2. for left rules, unify the conclusion-succedent pattern (`@side l`
   forces left-principal detection when the succedent is compound),
3. evaluate `@grade` steps in order through `calculus.grades` —
   `X := A ± B` defs (`-` is a monus: negative ⇒ rule inapplicable) and
   `A ⋈ B` guards (⋈ ∈ =, <, >, <=, >=),
4. instantiate premise patterns by substitution.

Zero-premise template rules still run the full check, so grade guards are
enforced in search **and** kernel verification (`verifyStep` recomputes
premises via the same `makePremises`; for left rules it tries every
context formula with the principal's tag). Variable boundness is validated
at load time. Template rules require the metavar-producing parser
(`multiCharFreevars`) — test sequents therefore use lowercase atoms;
uppercase identifiers are pattern variables.

Tests: `tests/till-prover.test.js` (provability grid, kernel gates),
`tests/rules2-template.test.js` (DSL compilation + validation).
