# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Principles
- Rather then guessing, lying or faking confidence, admit you don't know or have incomplete information - ask me questions or tell me how i can support you, i'm happy to help.
- Keep the root directory clean (only CLAUDE.md and README.md). All documents go in `doc/` — see **doc/ Placement Rule** below
- Don't write 'status update' documents or other verbose documents unless its told expricitly. Keep all documents descriptive of what IS not how it changed. Keep it VERY short and concise
- rather then simply recognizing an error and fixing it - think always how to isolate it and test it in isolation - e.g. via unit and integration tests. If its not possible then how to encapsule it (e.g. via logs), then either testing the failed state via unit tests or testing your hypothesis via verifying the logs. only after you verified the fail and isolated the error, you should think about fixing it
- Prefer reusable tools in the repo (tools/) before writing one-off /tmp scripts

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
npm test              # Core tests (431)
npm run test:engine   # Engine tests (338)
npm run test:all      # All tests (769)
npm run bench:diff    # Cross-commit benchmark comparison (use this when asked to benchmark)
```

## Architecture

**Backward prover** (L1-L4): kernel.js → generic.js → focused.js → strategy/ (manual, auto)
**Forward engine** (L4): Three-layer lego architecture:
- **Generic core**: match.js → strategy.js → forward.js / explore.js — pattern matching, rule selection, committed-choice/exhaustive execution. Configurable via `matchOpts` callbacks.
- **LNL layer** (`lnl/`): persistent goal proving, loli (dynamic rule) matching, existential resolution. Adds the linear/persistent distinction.
- **ILL layer** (`ill/`): binary arithmetic theories, ILL-specific backchainer defaults, loli drain. Plugged in via equational theories and `matchOpts` composition.
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
│   ├── bridge.js        # Lax monad mode switch (backward ↔ forward)
│   └── rule-interpreter.js  # descriptor → premise computation
├── calculus/            # Calculus loader (from .calc/.rules files)
│   └── builders.js      # Parser factory (Earley delegation), deriveRoles()
├── engine/              # Forward/backward execution engine (3-layer lego)
│   ├── match.js         # Generic: pattern matching + tryMatch pipeline
│   ├── strategy.js      # Generic: rule selection (fingerprint, disc-tree, dynamic rules)
│   ├── forward.js       # Generic: committed-choice main loop
│   ├── explore.js       # Generic: exhaustive DFS exploration + mutation/undo
│   ├── compile.js       # Generic: rule compilation (de Bruijn slots, metavar analysis)
│   ├── backchain.js     # Generic: backward chaining (SLD-style, renamed from prove.js)
│   ├── fact-set.js      # Generic: FactSet (sorted typed-array groups) + Arena (undo log)
│   ├── convert.js       # .ill → content-addressed hashes
│   ├── lnl/             # LNL layer: linear/persistent distinction
│   │   ├── persistent.js  # Persistent goal proving (state → cache → backchain)
│   │   ├── loli.js        # Dynamic rule matching (linear implications)
│   │   └── existential.js # ∃-variable resolution
│   ├── ill/             # ILL layer: ILL-specific logic
│   │   ├── backchain-ill.js # ILL defaults for backchainer
│   │   ├── binlit-theory.js # Equational theory: binlit ↔ i/o/e
│   │   ├── connectives.js   # ILL connective configuration
│   │   ├── loli-drain.js    # Loli drain optimization
│   │   └── ffi/             # Foreign function interface (arithmetic, memory)
│   └── opt/             # Toggleable optimization modules
├── meta-parser/         # Meta-level parser (@extends chain resolution)
├── parser/              # Earley parser + grammar generation + sequent parser
│   ├── earley.js        # Core Earley engine (recognizer, chart, extraction)
│   ├── earley-grammar.js # Grammar generation from .calc annotations
│   └── macros.js        # @def abbreviation macros (extract + expand)
├── rules/               # .rules file parser (sequent notation → descriptors)
├── browser.js           # Browser-compatible API (loads from ill.json bundle)
└── index.js             # Node.js API entry point

calculus/ill/            # ILL calculus definition
├── ill.calc             # Connective definitions
├── ill.rules            # Inference rules (sequent notation)
├── lnl.family           # Family infrastructure (LNL structural framework)
├── prelude/             # Type bounds, booleans, arrays
└── programs/            # EVM model, binary arithmetic, multisig contracts

tests/                   # Test suite (core: *.test.js, engine: engine/)
benchmarks/              # Performance benchmarks (engine/, proof/, micro/)
tools/                   # CLI utilities (bench-compare.js, explore-inspect.js)
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
| zero | `0` | positive | additive false — `zero_l` discards linear context |
| bang | `!` | positive | exponential (reusable resource) |
| monad | `{ _ }` | negative | lax monad (invertible right, sticky left) |
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

## Abbreviation Macros (`@def`)

`@def` provides parameterized formula abbreviations, expanded before content-addressing. Extralogical (Twelf `%abbrev` model) — engine never sees macro names.

```ill
@def evm_state(BC, PC, GAS, S) := bytecode BC * pc PC * gas GAS * stack S.
@def dispatch(BC, PC, OP, PC2) := !arr_get BC PC OP * !inc PC PC2.

evm/add:
  $bytecode BC * dispatch(BC, PC, 0x01, PC') * ...
  -o { ... }.
```

- Pre-pass: `macros.js:extractMacros()` runs after `resolveImports`, before `parseDeclarations`
- Expansion: `macros.js:expandMacros()` wraps the expression parser — text-level substitution
- Produces identical content-addressed hashes to writing things out longhand
- Nested macros: iterative fixed-point with cycle detection
- `$macro(args)` is an error — use `$` on individual atoms inside the macro body
- Macros require ≥1 parameter; word boundary checks prevent false matches

## FFI Principle

FFI is optimization, theory is semantics. Every FFI predicate MUST have backward clause definitions. FFI off → clause resolution takes over (slower but correct).

- `provePersistentGoals` (match.js): FFI → state lookup → clause resolution
- FFI failure is advisory: `{ success: false }` falls through to clause resolution
- FFI-only (no clause fallback): `mem_expand`, `mod`

## Common Gotchas

- `Store.tagId()` returns 0 for both invalid IDs and `atom` tag — use `isTerm()` first
- Atoms share tag 0, predicates have tag >= `PRED_BOUNDARY` (26) — use `hasPredicate`/`groupForPred`
- Nullary constructors (e.g. `empty_mem`) are `atom('empty_mem')` not tag — use helpers
- `code` facts are **linear** in EVM rules (consumed and re-produced)
- `linearMeta.persistentDeps` (Set) needs Array↔Set conversion for JSON serialization
- Per-rule compiled matchers were attempted and reverted — 59 closures → V8 megamorphic → ~25% regression (RES_0069). `compilePersistentStep` works: only ~4 closure types stays within V8 polymorphic IC threshold.
- Manual prover: `getApplicableActions(state, { mode: 'focused' })` (default) vs `{ mode: 'unfocused' }`
- Focus action names: `Focus_L` / `Focus_R` (not just `Focus`)

## Tooling

- `tools/bench-compare.js` — cross-commit benchmark comparison via git worktrees
- `tools/explore-inspect.js` — `node tools/explore-inspect.js [--leaf N] [--all] <files...>`
- `lib/engine/show.js` — `show(hash)`, `classifyLeaf(state)`, `showInteresting(state)`
- `out/ill.json` precomputes: parserTables, rendererFormats, ruleSpecMeta, connectivesByType
- `lib/engine/store-binary.js` — binary serialize/deserialize for precompiled SDK loading

## doc/ Placement Rule

| Subdirectory | What goes there | Naming | Examples |
|---|---|---|---|
| `doc/theory/` | **Our original contributions** — novel theorems, proof sketches, design frameworks unique to CALC | `NNNN_title.md` + `meta.yaml` | `0001_exhaustive-forward-chaining.md` |
| `doc/documentation/` | **How CALC works NOW** — system architecture, data-flow docs, reference material | free-form | `architecture.md`, `content-addressed-store.md` |
| `doc/def/` | **Atomic definitions** — one concept per file, encyclopedia of terms | `NNNN_title.md` + `meta.yaml` | `0005_internal-vs-external-choice.md` |

**Decision heuristic:** "Did we invent it?" → `theory/`. "Did someone else write about it?" → `research/`. "Does it describe the system as-is?" → `documentation/`. "Is it a single concept/term to define?" → `def/`.

**Research** documents live in `doc/research/`. They only contain **External knowledge** — literature surveys, paper summaries, technique catalogs sourced from existing work - named via `NNNN_title.md` e.g. `0007_chr-linear-logic.md`

**TODOs** are managed externally via the `hq` CLI, not in this repo. Reference them by identifier (e.g., `TODO_0068`) — don't create `doc/todo/` here. When referencing TODOs from calc docs (research, theory, documentation), use the identifier only: `TODO_0068`. Do not create links to local files. Use `hq todo <action>` to work with todos (show, list, search, edit, patch-body, etc.)

## Diagrams

Use ` ```mermaid` fenced code blocks for all diagrams in documentation. Renders as SVG via [Beautiful Mermaid](https://agents.craft.do/mermaid).
