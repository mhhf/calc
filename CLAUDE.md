# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Principles
- Rather then guessing, lying or faking confidence, admit you don't know or have incomplete information - ask me questions or tell me how i can support you, i'm happy to help.
- Keep the root directory clean (only CLAUDE.md and README.md). All documents go in `doc/` — see **doc/ Placement Rule** below
- Don't write 'status update' documents or other verbose documents unless its told expricitly. Keep all documents descriptive of what IS not how it changed. Keep it VERY short and concise
- rather then simply recognizing an error and fixing it - think always how to isolate it and test it in isolation - e.g. via unit and integration tests. If its not possible then how to encapsule it (e.g. via logs), then either testing the failed state via unit tests or testing your hypothesis via verifying the logs. only after you verified the fail and isolated the error, you should think about fixing it
- Prefer reusable tools in the repo (tools/) before writing one-off /tmp scripts
- For refactor TODOs, grade the finished work against a mechanical rubric (shape / contract / semantic / performance / docs) — see `doc/documentation/audit-rubric.md`

## Term / Resource / Proposition Principle

Three categories in ILL — use the right one:
- **Term** (constructor, `→ bin`): what something IS. `write(addr,val,M)`, `sha3(bytes)`, `eq_expr(X,Y)`. Inert data, pattern-matched by backward clauses.
- **Resource** (linear fact, `→ type`): what you POSSESS. `storage K V`, `gas N`, `mem M`. Consumed/produced by forward rules.
- **Proposition** (persistent fact, `!`): what you KNOW. `!plus A B C`, `!gt X Y 0 1`. Derived by backward chaining.

Decision: *"Can I write down what this object IS?"* → Term. *"Do I know a fact about it?"* → Proposition. *"Do I possess it?"* → Resource.

Backward predicates DERIVE propositions FROM terms (pattern matching on constructor structure). See `doc/documentation/term-resource-proposition.md`.

## Project Overview

CALC is a proof calculus system for experimenting with sequent-calculi with an implementation for Intuitionistic Linear Logic (ILL). Its inspired by the [calculus toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html). It implements backward proof search (Andreoli focusing), forward execution (multiset rewriting), and exhaustive symbolic exploration — all generated from declarative rule definitions.

## Build & Development Commands

```bash
npm run dev           # Development server (http://localhost:3000)
npm run build:ui      # Production build to out/ui/
npm run build:bundle  # Regenerate out/ill.json from calculus specs
npm test              # All fast tests (3565 tests, ~40s) — RUN THIS DURING DEVELOPMENT
npm run test:bun      # Same suite under bun (per-file isolation via tools/test-bun.sh)
npm run test:ill      # ILL-native tests (98 tests, ~0.2s) — .ill files as provability judgments
npm run test:till     # till executable specs (forward/debug directives)
npm run test:gill     # gill executable specs (incl. depot shortest-path)
npm run test:will     # will executable specs (scaffold smoke; noFFI arm: test:noffi:will)
npm run test:noffi    # noFFI adversarial soundness (13 tests, ~1s) — only after engine/FFI changes
npm run test:noffi:till  # till noFFI arm (also test:noffi:gill) — after engine/FFI changes
npm run test:zk       # ZK witness tests (94 tests) — only after ZK changes
npm run test:heavy    # Slow + drift tests (~5 min, dominated by rule-analysis's exhaustive cross-check) — fine as an inline gate after engine/rules changes. (The old "~a day" claim was measured false 2026-09-01: even the commit that recorded it runs in ~11 min cold.)
npm run test:all      # Everything combined (includes test:ill)
npm run debug:ill     # Debug runner — observation directives + verbose judgment output
npm run bench:diff    # Cross-commit benchmark comparison (use this when asked to benchmark)
```

## Architecture

**Backward prover** (L1-L4): kernel.js → generic.js → focused.js → strategy/ (manual, auto)
**Forward engine** (L4): Three-layer lego architecture:
- **Generic core**: match.js → strategy.js → forward.js / explore.js — pattern matching, rule selection, committed-choice/exhaustive execution. Configurable via `matchOpts` callbacks.
- **LNL layer** (`lnl/`): persistent goal proving, loli (dynamic rule) matching, existential resolution. Adds the linear/persistent distinction.
- **ILL layer** (`calculus/ill/`): binary arithmetic theories, ILL-specific backchainer defaults. Lives OUTSIDE lib/ — plugged in via equational theories and `matchOpts` composition through the calculus config (calculus/ill/calculus-config.js + calculus/ill/lib/).
**Lax monad** `{A}`: polarity shift (async→sync) at `lib/prover/bridge.js`. Three execution profiles: `'full'` (default, opaque), `'guided'` (oracle + verified ILL terms), `'off'` (pure backward)
**Content-addressed store**: formulas are hashes (numbers), O(1) equality via `lib/kernel/store.js`
**Equational theories** (`kernel/eq-theory.js`): pluggable cross-tag matching. O(1) dispatch via `_rewriteFromTag[tagId]` lookup. Built-in: strlit. Calculus-registered: binlit (ILL).

See `doc/documentation/architecture.md` for the full prover lasagne (L1-L5).
See `doc/documentation/parser-pipeline.md` for the three parser paths (one shared Earley parser).

**Web UI:** SolidJS + TypeScript + Tailwind CSS + Vite. Source: `src/ui/`, Build: `out/ui/`

## Directory Structure

```
lib/
├── kernel/              # Content-addressed AST: store, sequent, unify, substitute, ast, eq-theory
├── prover/              # Backward proof search (5-layer architecture)
│   ├── kernel.js        # L1: proof verification
│   ├── generic.js       # L2: search primitives
│   ├── focused.js       # L3: Andreoli focusing
│   ├── strategy/        # L4: manual, auto
│   ├── bridge.js        # Lax monad mode switch (backward ↔ forward); timed bridge ELABORATES traces (0294)
│   ├── sld-check.js     # SLD certificate checker — clause derivations checked, not trusted (TODO_0295)
│   ├── draw-check.js    # @draw step checker — one collapse event re-derived from the program's sort system + declared priors (TODO_0298; drawn tokens minted here only)
│   ├── timed/           # Timed verification face (generic over till/gill/will; TODO_0294)
│   │   ├── fire-check.js      # @fire step checker — one firing re-derived from PROGRAM RULE DATA + theory
│   │   ├── elaborate-trace.js # settle events → kernel-checked @fire proof trees; certifyRun (any-run certificates)
│   │   └── elaborate-collapse.js # decimation runs → kernel-checked trees (post-hoc grounding); certifyCollapse — endsequent carries ⟨Θ⟩ (TODO_0298)
│   └── rule-interpreter.js  # descriptor → premise computation
├── calculus/            # Calculus loader (from .calc/.rules files)
│   └── builders.js      # Parser factory (Earley delegation), deriveRoles()
├── engine/              # Forward/backward execution engine (3-layer lego)
│   ├── formula-utils.js # Generic: connective-aware formula decomposition (shared across pipeline)
│   ├── labels.js        # Generic: StampTable — per-State label interning over a calculus value algebra (THY_0024)
│   ├── match.js         # Generic: pattern matching + tryMatch pipeline
│   ├── strategy.js      # Generic: rule selection (fingerprint, disc-tree, dynamic rules)
│   ├── forward.js       # Generic: committed-choice main loop
│   ├── explore.js       # Generic: exhaustive DFS exploration + mutation/undo
│   ├── compile.js       # Generic: rule compilation (de Bruijn slots, metavar analysis)
│   ├── backchain.js     # Generic: backward chaining (SLD-style, renamed from prove.js)
│   ├── fact-set.js      # Generic: FactSet (sorted typed-array groups) + Arena (undo log)
│   ├── sorts.js         # Generic: refinement-sort system (subsort DAG index + certified proofs, TODO_0011)
│   ├── materialize.js   # Generic: load-time clause materialization (sort system + subsort-closure/mass/prior fact riders)
│   ├── convert.js       # .ill → content-addressed hashes
│   ├── priors.js        # Generic: @w constructor-prior validation + Chi–Geman subcriticality (presence-gated)
│   ├── decimate.js      # Generic: decimation driver — ∃_ρ waves, lazy recursion, datasort conditioning, sample/exact/solve (calc.collapse; TODO_0297 P2/P3, TODO_0011 fence B)
│   ├── compose.js       # Generic: grade-0 cut-elimination pipeline (cutPair/predMap/compose0) + chain fusion + SROA + SLD tabling (THY_0015/0016); runs on every non-cached load
│   ├── compose-profile.js # Generic: compose profiling emission (onPhase-gated, pure — fuse/tabling rollups + leaves)
│   ├── lnl/             # LNL layer: linear/persistent distinction
│   │   ├── persistent.js  # Persistent goal proving (state → cache → backchain)
│   │   ├── loli.js        # Dynamic rule matching (linear implications)
│   │   ├── loli-drain.js  # Persistent-trigger loli drain (generic, moved from ill/)
│   │   └── existential.js # ∃-variable resolution
│   ├── timed/           # Timed layer: wall-clock scheduler over the stamp algebra (generic over cc.grades/cc.stampTag; TODO_0265)
│   │   ├── timed.js       # buildTimedConfig, settle loop, stamp-aware matching (tryTimedMatch/fire)
│   │   ├── timed-api.js   # grades-gated API construction (settle/views/game + D16/C1-C3 lints) — index.js delegates here
│   │   ├── timed-game.js  # Interactive with-projection menus over timed state
│   │   ├── timed-render.js # #trace/#timeline/#why debug renderings
│   │   ├── timed-lint.js  # D16 Zeno warning + timedAdvice: C1 chain-collapse, C2 Hypothesis-S (menu-exempt + cc.lintExempt machinery predicates), C3 whole-bind arrivals
│   │   ├── certify.js     # T2-applicability certifier: structural / monotone-relaxation pairwise check (calc.certifyContention)
│   │   ├── timed-views.js # timedSubset/timedExact state projections
│   │   ├── accel.js       # orbit detection + state jumping (accelerate opt)
│   │   ├── coalesce.js    # cohort merging
│   │   ├── covariance.js  # shift-degree analysis (rebase safety)
│   │   └── dirty-sched.js # dirty-tracking scheduler
│   └── opt/             # Toggleable optimization modules
│       ├── compiled-clauses.js # Tier 1 compiled clause dispatch (zero-subgoal → direct lookup)
│       ├── existential-compile.js # Compiled ∃-chain (per-goal FFI fast path for existential resolution)
│       ├── ffi.js             # FFI-first persistent goal proving (state → FFI → compiled → clause)
│       ├── fingerprint.js     # First-argument fingerprint indexing for rule selection
│       ├── prediction.js      # Rule applicability prediction (pre-filter before full match)
│       └── structural-memo.js # Structural memoization for explore (control hash → subtree skip)
├── meta-parser/         # Meta-level parser (@extends chain resolution)
├── parser/              # Earley parser + grammar generation + sequent parser
│   ├── earley.js        # Core Earley engine (recognizer, chart, extraction)
│   ├── earley-grammar.js # Grammar generation from .calc annotations
│   ├── declarations.js  # Declaration extraction from .calc files (types, grammars, roles)
│   ├── sequent-parser.js # Sequent notation parser (antecedent ⊢ succedent)
│   └── balanced-split.js # Bracket-aware string splitting for sequent components
├── rules/               # .rules file parser (sequent notation → descriptors)
├── browser.js           # Browser-compatible API (loads from ill.json bundle)
└── index.js             # Node.js API entry point

calculus/ill/            # ILL calculus definition + ILL-bound machinery
├── ill.calc             # Connective definitions
├── ill.rules            # Inference rules (sequent notation)
├── lnl.family           # Family infrastructure (LNL structural framework)
├── index.js             # ILL engine facade: mde with calculusConfig pre-bound (+ normalizeQuery) — what ILL-implicit callers import
├── calculus-config.js   # Single assembly point: layered config (L0-L6) — the generic engine receives it via opts.calculusConfig
├── lib/                 # ILL-bound machinery (calculus/<name>/lib pattern — imported only via the config/plugins, never by the generic engine)
│   ├── backchain-ill.js # ILL defaults for backchainer (explicit initILL())
│   ├── binlit-theory.js # Equational theory: binlit ↔ i/o/e
│   ├── bytecode-loader.js # EVM bytecode loader
│   ├── bytecode-normalize.js # EVM bytecode → trie/arrlit/semantic
│   ├── compose-config.js  # ILL bindings for the generic compose pipeline (chain/SROA predicates)
│   ├── residual-resolver.js # compile-time persistent-goal resolver for grade-0 specialized rules
│   ├── connectives.js   # ILL connective table (derived from ill.calc)
│   ├── guided-term.js   # ILL guided-profile term builder (self-registers with prover/bridge)
│   ├── prove-source.js  # proof-from-source API (server.js backend)
│   ├── ffi/             # Foreign function interface (arithmetic, memory, calldata, arrays)
│   └── zk/              # ZK witness extraction (witness.js, flat-witness.js — EVM/STARK domain)
├── prelude/             # Type bounds, booleans, arrays
├── programs/            # EVM model, binary arithmetic, multisig contracts
└── tests/               # ILL-native tests (provability judgments, run via test:ill)

calculus/till/           # till — timed ILL (TODO_0265)
├── till.calc            # Connectives + grade sorts (delay/count/weight <: grade)
├── till.rules           # Sequent rules (graded monad/bang)
├── calculus-config.js   # Single assembly point (incl. cc.sorts: literal classification + fences)
├── prelude/sorts.till   # Refinement-sort machinery (sort/sedge/subsort; closure materialized at load)
├── prelude/rat.ill      # Numeric tower: q, bin <: q, frac <: q + exact rational q-ops
├── game/PP2.till        # Playable demo (classifiers + schema expansion; npm run shell:till)
└── tests/               # till executable specs (forward/, debug/)

calculus/gill/           # gill — graded ILL (TODO_0284): grade algebras as data; till frozen as the time instance
├── gill.calc            # till's graded surface + dist grade sort + haul `!!_d A` (graded transport comonad, @category comonad)
├── gill.rules           # till.rules fragment + haul rules (fetch/dereliction/unit — the monad's spatial dual, same ⊖ premise) + @fire (config-bound checker, TODO_0296: gill runs certify — see gill-dist.test.js depot certification)
├── calculus-config.js   # Assembly point: by-sort grade registry (delay→tillGrades, dist→distGrades, weight→weightGrades; gradeAlgebraFor), min/max tower collapse
├── prelude/num.gill     # Imports till's rat.ill; dist tower edges + collapsed min/max /q instances
└── tests/               # gill executable specs incl. depot shortest-path (npm run test:gill / test:noffi:gill)

calculus/will/           # will — weighted ILL (TODO_0292/0297): the measure-class calculus (THY_0026) — ∃_ρ surface, decimation driver, lazy recursion
├── will.calc            # @family will + @extends gill — the FIRST cross-calculus @extends chain (surface inherited, not copied; meta-parser resolves sibling calculus dirs); drawn token family + superpose @ascii pattern forms
├── will.rules           # will-OWN sequent rules (THY_0027 §2, TODO_0298): drawn_l = ∃_ρ-R (consumes a drawn token; @binding witness C opens the binder with the token's member), drawn_l2 = ghost (@affine trace weakening), superpose_l = ∃-L (eigenvariable), draw = checker-bound oracle. Loaded AFTER gill.rules — calculus.load takes a rules-file LIST (shared fragment by reference, never copied)
├── calculus-config.js   # Composes gill's exported layer pieces (M2); scheduler chooser 'entropy' (M5); binderSorts grammar opt-in (∃_ρ); backward fragment = [gill.rules, will.rules]; sequent parser gains binders; @draw checker bound via kit.js
├── lib/datasort-mass.js # Inside-mass solver (fence B) — will-BOUND oracle machinery (cc.datasortMasses); the checker never imports it
├── prelude/measure.will # Imports gill's num.gill (tower + sorts machinery transitively; import labels are basenames — hence not num.will)
├── game/WFC.will        # Wave function collapse demo on the ∃_ρ + bias surface: one wave per cell, propagation = bias derivation, driven by calc.collapse / the shell's collapse mode (npm run shell:will -- calculus/will/game/WFC.will)
└── tests/               # will executable specs (npm run test:will / test:noffi:will); fast-suite guards: tests/engine/will-{scaffold,wfc,priors,draw-check}.test.js + tests/will-prover.test.js

tests/                   # Test suite (core: *.test.js, engine: engine/)
benchmarks/              # Performance benchmarks (engine/, proof/, micro/)
tools/                   # CLI utilities + shared tool infrastructure
├── directive-loader.js  # Shared directive loading (test-ill.js, debug-ill.js, explore-inspect.js)
out/                     # Generated: ill.json (bundled calculus), ui/ (built app)
```

## ILL Connectives

| Connective | ASCII | Polarity | Notes |
|---|---|---|---|
| tensor | `*` | positive | multiplicative conjunction |
| loli | `-o` | negative | linear implication |
| one | `I` | positive | multiplicative unit |
| with | `&` | negative | additive conjunction (external choice) |
| oplus | `+` | positive | additive disjunction (internal choice) — renamed from `plus` |
| zero | `zero` | positive | additive false — `zero_l` discards linear context |
| bang | `!` | positive | exponential (reusable resource) — binary: `bang(grade, formula)`, `!A` is sugar for `bang(GRADE_W, A)` |
| monad | `{ _ }` | negative | graded lax monad — binary: `monad(grade, body)`, `{A}` is sugar for `monad(unit, A)` with unit = binlit 0; till's `{A}@d` fills the grade |
| exists | `exists` | positive | existential |
| forall | `forall` | negative | universal |

Precedence: loli 50 < tensor 60 < oplus 65 < with 70 < bang 80

## Preserved Resource Sugar (`$`)

`$P` on a forward rule antecedent marks P as preserved — consumed and re-produced identically. Purely syntactic sugar (Ceptre convention).

```ill
evm/add:
  $bytecode BC *        % desugars to: bytecode BC on both LHS and RHS
  pc PC * ...
  -o { pc PC' * ... }.
```

- Parser: `$P` → `preserved(P)` wrapper node (`earley-grammar.js`, only with `forwardRules: true`)
- Desugaring: `convert.js:desugarPreserved()` strips wrappers, injects into consequent — before content-addressing
- `$!P` is an error (persistent resources are never consumed)
- `$` in the consequent is an error
- Engine already optimizes preserved patterns via `rule-analysis.js:analyzeDeltas()`

## Refinement Sorts (till-only, TODO_0011 rung 1)

Extrinsic Curry-style refinements over the closed-world checker; presence-gated twice (calculus needs `cc.sorts`, program needs sort declarations) — ILL stays sortless. See `doc/theory/0020_refinement-sorts.md`.

```ill
bin <: q.                                    % subsort edge = a persistent sedge fact
resource: sort.  wood: resource.             % classifier + member (wood stays a proposition)
sub: (s <: q) (a: s) -> (b: s) -> (r: s) -> type.   % bounded sort variable
spoil: (r: resource) r@Q * after (Q+20) -o { I }.   % schema: expands per member at load
```

- Machinery: `prelude/sorts.till` (facts are semantics) + `lib/engine/sorts.js` (compiled DAG index, `closurePairs()`). The loader MATERIALIZES the reflexive-transitive closure as ground `subsort a b` facts at load — in-logic `!subsort X s` premises are total fact lookups (no recursive closure clause, no committed-choice caveat). No sort name/edge may appear in engine JS — edges live in logic files, literal classification + value fences (delay nonneg, count integral, weight [0,1]) in till's calculus-config.
- Bounded vars solve s := lub(arg sorts) and need a clause INSTANCE at s (inferred from head patterns); mixed-sort goals are legal iff a bound-level instance exists (strictness = instance absence).
- Grade sorts: `delay`/`count`/`weight <: grade` in till.calc; the grammar folds them onto the one GRADE chain, the checker keeps them distinct.
- The q-namespace collapse (qplus→plus) is the deferred dispatch rider — prelude names stay split, now with honest q sorts.
- Datasorts (fence B, TODO_0011 — COMPLETE, THY_0030): `even <: lst.` with an UNDECLARED lhs introduces a datasort, defined by ordinary membership clauses — nullary heads (`warm/s: warm sea.`) or constructor heads with datasort premises on immediate subterm variables (`even/c: even (cons H T) <- odd T.`). The name gets a loader-synthesized dual role (sort atom + unary membership predicate, sound post-f7ec930a; `!even T` backward goals just work). Clauses compile to a top-down deterministic tree automaton; INSIDE MASSES are solved EXACTLY at load (datasort-mass.js solveMasses: SCC decomposition, linear systems by rational Gaussian elimination; `calc.masses`). Fences, each a named load error: f1 head = one depth-1 constructor pattern with distinct variables; f2 premises = unary datasort goals on head argument variables, each at most once, base-compatible; f3 one clause per (datasort, head) — determinism (masses double-count under overlap); f4 ≤1 recursive argument per head within its SCC (nonlinear = fence B″, algebraic masses); empty language (no base case) = load error; critical/supercritical mass systems (singular or negative solution) = load error. Conditioning a wave: static `exists X: even @w.` at the binder, or dynamic `!within E S` facts (program declares `within: (x: base) -> (s: sort) -> type.`) — multiple withins and the registered sort combine into an anonymous PRODUCT state (canonical key `d1&d2`, sorted/'&'-joined; `sortSystem.stateInfo` resolves declared names AND product keys uniformly — intersection MEMBERSHIP needs no machinery, proving both goals is the intersection; the product is only the mass/draw index, cached, deterministic, so checkers rebuild it independently). Semantics is RESTRICTION, not renormalization (B4): surviving worlds keep their masses; the conditioned sampler draws heads ∝ ρ·Π m(child states) while the recorded mass factor stays ρ·bias, so importance ≡ m(S) for every seed on bias-free programs (B6, zero-variance; when masses exist, ⊤ structured waves also draw mass-proportionally — exact ancestral sampling, needed for the telescope); product-state masses solve LAZILY against the load-time table; empty products = contradiction (M9), not an error; child waves register at the automaton's child STATES (product keys included); tokens carry the BINDER's sort name (`drawn cons even`, m4) and draw-check walks composite witnesses at child states. THE SOLVER IS CALCULUS-BOUND ORACLE MACHINERY, not core: `calculus/will/lib/datasort-mass.js` is bound by will's config (`cc.datasortMasses`) — calculi without the binding structurally lack the concept (recursive datasorts under them = load error); solved masses materialize as ground `mass s m` facts when the program declares the predicate (the subsort/prior discipline — in-logic `!mass S M` premises are total lookups). Certification (slice 4): @draw records carry the EFFECTIVE conditioning state (`state:` on trace/node records when within-derived ≠ registered sort); checkDrawData re-derives admission against it; certifyCollapse verifies every structured conditioning state's claimed mass BY SUBSTITUTION into its own equation (draw-check.js verifyMasses — the checker never imports the solver; doctored masses and doctored states are pinned rejections). Pins: tests/engine/will-datasorts.test.js (worked example: m(even)=8/3, m(odd)=4/3, partition = m(lst)=4; entangled product m(even∧allb0)=32/15 solved lazily).

## FFI Principle

FFI is optimization, theory is semantics. Every FFI predicate MUST have backward clause definitions. FFI off → clause resolution takes over (slower but correct).

- `provePersistent` (match.js → ffi.js): state lookup → FFI → compiled clause → full clause resolution
- FFI failure is advisory: `{ success: false }` falls through to clause resolution
- All FFI predicates have backward clause definitions (FFI is optimization only)

## Common Gotchas

- `mde.load`/`precompile`/`loadPrecompiled` REQUIRE `opts.calculusConfig` — the engine holds no default and lib/ never imports calculus/ (layer-dag enforced). ILL-implicit code imports `calculus/ill/index.js` (the facade: mde with the ILL config pre-bound, plus `normalizeQuery`, which is EVM domain machinery — not generic engine API)
- `Store.tagId()` returns 0 for both invalid IDs and `atom` tag — use `isTerm()` first
- Atoms share tag 0, predicates have tag >= `PRED_BOUNDARY` (36) — use `hasPredicate`/`groupForPred`. Appending kernel tags shifts the boundary and invalidates every serialized Store — batch into one commit and bump the store-binary VERSION
- Nullary constructors (e.g. `empty_mem`) are `atom('empty_mem')` not tag — use helpers
- `code` facts are **linear** in EVM rules (consumed and re-produced)
- `linearMeta.persistentDeps` (Set) needs Array↔Set conversion for JSON serialization
- Per-rule compiled matchers were attempted and reverted — 59 closures → V8 megamorphic → ~25% regression (RES_0069). `compilePS` works: only ~4 closure types stays within V8 polymorphic IC threshold.
- Manual prover: `getApplicableActions(state, { mode: 'focused' })` (default) vs `{ mode: 'unfocused' }`
- Focus action names: `Focus_L` / `Focus_R` (not just `Focus`)
- Counted parcels (D4 revised): binding discipline decides cohort discipline. `!_k A` = k copies of ANY ages (spreads across cohorts oldest-first; activation = newest taken stamp); `!_k A@T` = k copies at ONE stamp T; `!_W A` = ALL copies (W binds the total); `!_W A@T` = one whole cohort (W its size, T its stamp). Fused sugar `4wood` ≡ `!_4 wood` (till only, one lexer token); spaced `4 wood` stays application juxtaposition, `4wood@3` is a loud error (write `!_4 wood@3`)
- Whole-bind chases arrivals: `!_W A` includes in-flight cohorts a producer just scheduled, so a rule like `!_W g * !lt CAP W` re-activates at every arrival and a deterministic chooser can starve it FOREVER (the PRF chooser merely hides it). Trim/cap rules must use a counted take — `!_201 g -o { !_200 g }` pins activation oldest-first and is starvation-free under any chooser (PP2 §3b)
- Grammar emission is ONE mechanism (sorted templates, TODO_0268 §5c): operator/prefix/nullary/circumfix/gradedPrefix tables are normalized into synthetic template records in `earley-grammar.js` — new surface syntax should be a declared `@ascii` template, not a new family. Per-input ambiguity detection: `setStrictAmbiguity(true)` in `earley.js` (corpus sweep: `tests/parser-fold-fuzz.test.js`)
- Labelled timed state (THY_0024): `at(A, t)` exists only at BOUNDARIES (plain objects, store-binary, event records, rule patterns). Live timed states are rows (innerHash, stampId, count) — the runtime fact handle is a packed 52-bit ref (`labels.js` packRef/refInner/refStamp); stamp ids index the per-State StampTable (`state.linear.stamps`), whose ids are history-dependent — hash/PRF inputs must derive from VALUES, never ids
- Certified execution (TODO_0294/0295): the timed bridge returns ELABORATED @fire proof trees — FULL kernel verification (`verifyTree(tree, { program: programFromCalc(engineCalc) })`), no `unverified: 'modeSwitch'`; elaboration failure with a bound checker THROWS (engine/elaborator disagreement). The kernel routes calculus-declared step checkers via `calculus.stepCheckers` (bound in kit.js makeSequentLoader's `fire:`/`draw:` options — no rule annotations); clause-derived persistent goals carry SLD certificates (sld-check.js, emitted clause-only `useFFI: false`); the checker also PROVES clause-only (fire-check stamp judgments + scope-guarded theory goals — the numeric FFI is never on the verification path). TCB = kernel + eq-theory canon + numeric prelude CLAUSES under the clause-only backchainer. `certifyRun` certifies arbitrary settle runs; fuzz-till §7 fuzzes it
- Constructor priors: `sea: tile_t @w 2.` is the ONE annotation program files admit (regex-narrow parse — exactly `ident @w numeral[/numeral]` as the whole body, so stamp positions `food@Q`/`{...}@3` can never match). Lands on `calc.priors` as exact [n,d] ℚ≥0 ratios (DATA, never facts — D5; in-logic evidence is bias facts, P2); unannotated member = weight 1 at the consumer. Chi–Geman subcriticality (T2) warns at load (`calc.priorLint`)
- Chooser `'entropy'` (M5, will's default): among tied candidates, least Shannon entropy of the consequent distribution fires first (H=0 deterministic rules → propagation before collapse); residual ties → PRF. Semantics-free tuning (D6) — override per run via settle `opts.chooser`
- Decimation (`calc.collapse`, TODO_0297 P2/P3): the ∃_ρ surface `exists X: s @w. A` (will-only binder rule) settles to a SUSPENDED `superpose(s, exists(body))` fact — inert under plain settle (D4 opt-in); plain `exists X. A` is a SKOLEM under the driver (M1). The driver opens suspended facts (fresh evar, conjuncts split at the stamp), re-settles so `!bias E c Q` rules bind the evar (bias rules need a LINEAR trigger — persistent-conclusion $-rules Zeno-loop), posteriors = prior · Π distinct bias facts (M8; clause-derived bias is ALL-SOLUTIONS via `calc.proveAll` — independent clauses multiply, same-value derivations dedup), draws min-entropy-first (PRF, value-derived keys — never evar ids), `substituteEvar`s, repeats. Modes: `sample` (restart on contradiction, M9; importance = Π totals, unbiased PER ATTEMPT — T3 caveat in THY_0026 §8), `exact` (collapse tree, unnormalized masses — T1; woplus forks inside settle are enumerated via settleExplore — both ⊕; genuine conflicts error loudly, `settleBranching: 'seed'` restores the chooser-resolved reading), `solve` (first-solution DFS). Rung 2: classifier members may be CONSTRUCTORS (`cons: (a: lst) -> lst @w Q.`) — draws instantiate one head, arg evars become new waves (lazy PCFG); structured sorts need explicit maxCollapses in exact/solve (truncated = monotone lower mass approximant); schema expansion over them is a load error
- ∃_ρ sequent rules (TODO_0298, THY_0027): weight is a function of the ENDSEQUENT — `drawn c s` tokens are linear hypotheses; ∃_ρ-R is mechanically a LEFT rule on the token (`drawn_l`, @binding witness — no superpose_r exists, so superpose/drawn stay UNPOLARIZED at search level like `at`; the focused ∃_ρ-positive assignment is the paper's counting discipline). Ghost (`drawn_l2` @affine) is a LAST-RESORT focus choice + boundary discharge (root leftovers, with_r branch balancing) — never searched greedily. `drawn` is kernel-reserved: programs may neither produce nor match it (convert fence); `@w` priors materialize as ground `prior s c ρ` facts per TOUCHED classifier when the program declares the predicate (bias discipline). `!_0` surface = g0 marker (no sequent rules); count-zero is binlit 0 (bang_r3, empty linear zone). Run certification (`certifyCollapse`, elaborate-collapse.js): a SAMPLE run (`collapse` opts.trace) elaborates post-hoc-grounded into ONE kernel-checked tree — endsequent `Δ₀, ⟨Θ⟩ ⊢ {∃skolems. ⊗residual}@h`, one token per drawn head, each wave = one @draw node at its OPENING position (rung-2 witness tree = composite iterated ∃_ρ, checker consumes one token per ground head; evar subterm = dropped wave, no token); token-free OPEN records certify ∃-L with syntactic eigenvariable freshness; Π ρ over ⟨Θ⟩ = run mass on bias- and woplus-free programs (bias factors and woplus alt weights ride the @fire records, not the endsequent; sample-mode `mass` includes woplus branch weights — importance does not, the factors cancel in the T3 estimator)
- Cohort firing (TODO_0278 B1, default ON): settle fires a unique candidate ONCE at multiplicity k (state-identical to per-item). Event records carry PER-FIRE facts + `multiplicity` (the list is an RLE — expand to get the sequential multiset); `steps`/Zeno/maxSteps count firing STEPS, eventTotals count fires. `batch: false` restores per-item firing

## Tooling

- `tools/bench-compare.js` — cross-commit benchmark comparison via git worktrees
- `tools/bench-history.js` — commit-history benchmark across N commits
- `tools/bench-to-doc.js` — converts bench-history JSON to markdown/chart
- `tools/bytecode-to-ill.js` — EVM hex bytecode → CALC facts converter
- `tools/collect-tags.js` — regenerate `doc/tags.yaml` tag index (`npm run tags`)
- `tools/explore-inspect.js` — `node tools/explore-inspect.js [--leaf N] [--all] <files...>`
- `tools/fuzz-ffi.js` — FFI correctness fuzzer (FFI vs clause comparison)
- `tools/fuzz-till.js` — till fuzzer: q-ops FFI∥clause∥BigInt reference + activation spec (`node tools/fuzz-till.js [--count N] [--seed N]`)
- `tools/till-shell.js` — live TTY for till programs (`npm run shell:till -- <file> [--init <directive>] [--speed x] [--demo "t:i,..."]`): wall-clock settle loop, menus from the state, digits = with-projection clicks, menuStatus greying. COLLAPSE MODE (auto on suspended ∃_ρ facts, or `--collapse`): stepwise decimation via `calc.collapseView`/`collapseDraw` — entropy-sorted wave menu (facts with the evar as `?`), digits draw, `a` auto, `R` restart (M9 attempt counter); demo grammar `--demo "a,a,1,a" --seed N`
- `tools/precompile.js` — binary cache precompiler for .ill files
- `tools/test-timing.js` — per-file test execution time profiler
- `tools/debug-ill.js` — `npm run debug:ill -- <file.ill> [--only trace]` (observation directives + verbose judgments). Directives: `#trace`, `#dump_state`, `#debug`, `#benchmark`, `#compare`, `#inspect`, `#profile`
- `tools/analyze-csub.js` — compiled substitution analysis (recipe coverage stats)
- `lib/engine/show.js` — `show(hash)`, `classifyLeaf(state)`, `showInteresting(state)`
- `out/ill.json` precomputes: parserTables, rendererFormats, ruleSpecMeta, connectivesByType
- `lib/engine/store-binary.js` — binary serialize/deserialize for precompiled SDK loading

## Engine Hooks API

Opt-in callbacks on `calc.exec()`/`calc.explore()` for instrumentation. Zero cost when not provided.

```js
calc.exec(state, {
  onStep: ({ step, rule, consumed, theta, slots, state }) => { ... },  // step: monotonic counter
  onProveFail: (goal, reason) => { ... },  // reason: 'cached_failure'|'external_binding'|'exhausted'|'ffi_mismatch'
  onProveSuccess: (goal, method) => { ... },  // method: 'ffi'|'state'|'compiled'|'cache'|'clause'
});
calc.explore(state, {
  onStep: ({ depth, rule, consumed, theta, slots, state }) => { ... },  // depth: DFS nesting level
  onProveSuccess: (goal, method) => { ... },  // same as exec
  onProveFail: (goal, reason) => { ... },     // same as exec
});
```

`exec()` emits `{ step }` (1-based counter), `explore()` emits `{ depth }` (0-based DFS level). `consumed`/`theta` are snapshots; `state` is live (inspect via show.js, don't mutate). When `onProveSuccess`/`onProveFail` hooks are provided, the compiled persistent step fast path is bypassed (same as evidence mode) to ensure all goals are observable. See `doc/documentation/ill-debug-framework.md`.

## doc/ Placement Rule

| Subdirectory | What goes there | Naming | Examples |
|---|---|---|---|
| `doc/theory/` | **Our original contributions** — novel theorems, proof sketches, design frameworks unique to CALC | `NNNN_title.md` + `meta.yaml` | `0001_exhaustive-forward-chaining.md` |
| `doc/documentation/` | **How CALC works NOW** — system architecture, data-flow docs, reference material | free-form | `architecture.md`, `content-addressed-store.md` |
| `doc/def/` | **Atomic definitions** — one concept per file, encyclopedia of terms | `NNNN_title.md` + `meta.yaml` | `0005_internal-vs-external-choice.md` |

**Decision heuristic:** "Did we invent it?" → `theory/`. "Does it describe the system as-is?" → `documentation/`. "Is it a single concept/term to define?" → `def/`.

**Research** documents and **TODOs** are managed externally via the `hq` CLI, not in this repo. Use `hq doc/research <action>` for research docs and `hq todo <action>` for todos. Reference them by identifier: `RES_0068`, `TODO_0068`. Do not create `doc/research/` or `doc/todo/` here.

## Diagrams

Use ` ```mermaid` fenced code blocks for all diagrams in documentation. Renders as SVG via [Beautiful Mermaid](https://agents.craft.do/mermaid).
