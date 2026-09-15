# Governance sandbox (dill)

A live, role-scoped sandbox for experimenting with governance over the `dill`
calculus (gill + the possession modality `says K A`). It realizes TODO_0276's
operational core and TODO_0318, on ILL-term-level principals (P0, Rep1).

## Pieces

| Piece | Path | What it is |
|---|---|---|
| Forward specs | `calculus/dill/tests/forward/*.ill` | `#expect … => … (settle: T)` specs run by `npm run test:dill` (dill is a `CALC_SPEC` calculus in `tools/test-calc.js`) |
| Prelude | `calculus/dill/prelude/governance.ill` | reusable voting machinery: `cast_vote` (the audited [⪰] bridge), the incremental linear tally, threshold `tally_close`, the `enact` cell |
| Programs | `calculus/dill/programs/name_the_org.ill` | scenario fixtures loaded by tests + the server |
| Runtime lib | `calculus/dill/lib/govern.js` | `loadGovernance` / `inject` / `extractGov` / `value` / the voting **kernels** (`argmax-oldest`, `threshold`, `n-of-set`, `priority`, `time-locked`) + `consensus()` |
| Server | `src/server/gov-api.js` | `handleGov(route, body)` — a live State per session, admin/actor verbs; mounted at `/api/gov/*` in `server.js` (prod) and `src/ui/plugins/vite-docs.ts` (dev) |
| Web menu | `src/ui/pages/Governance.tsx` | `/governance` — context panel, role switcher, kernel selector, consensus + enact, inject/query boxes, timeline |

## Two consensus faces (both are "kernels")

- **Eager / in-logic threshold** — forward rules sum ballots via `!plus`/`!le` and
  mint `says C (authorized P)` (see `company_cake.ill`). The tally sums plain
  rational terms; the grade index's partial-⊕ is never invoked (the forward/
  backward split, THY_0045/0046).
- **Lazy / derived-view argmax** — `govern.js` `consensus()` folds
  `Σ share·vote` over the settled state and picks argmax + oldest-wins. This is
  memhub's read-time `consens` *outside* the transition system, which is exactly
  why the engine's lack of NAF/argmax never bites.

## The forward/backward split

Under `settle`, `says K A` is an opaque structural wrapper — governance rules
consume and produce it freely. The **entity-veil** (`says 1 a ⊬ says 3 a`) lives
in the **backward** prover (`poss_l` index unification), reached via
`governanceSequent()` and exposed as the server's `query` verb.

## Role-scoping is the logic

`admin` = the mint authority (any `says K X`), the single mint authority the
logic reserves for the consensus kernel. `actor K` may touch only its own
`says K (…)` zone — the operational twin of `poss_l` (THY_0046 NI-1) enforced at
the API boundary.

## Tests

`npm run test:dill` (forward specs) · `tests/engine/dill-governance.test.js`
(the runtime lib + kernels + entity-veil) · `tests/gov-api.test.js` (the server).

## Deploy

Everything lives under already-packaged dirs (`calculus/`, `src/`, `lib/`), so no
flake change is needed. calc.denis.page is deployed by a manual `./deploy.sh`
(there is no auto-deploy on push for calc).
