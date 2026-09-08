# CALC

**CALC** (Calculus for Accountable Linear Computations) is a proof calculus system for [Intuitionistic Linear Logic](https://en.wikipedia.org/wiki/Linear_logic) (ILL). It implements backward proof search (Andreoli focusing), forward execution (multiset rewriting), and exhaustive symbolic exploration — all generated from declarative rule definitions.

The driving insight: double-entry bookkeeping is applied linear logic. Resources are tracked exactly, consumed on use, and never duplicated — the same discipline accountants have followed since Pacioli (1494). CALC makes this connection formal and computational.

Inspired by the [calculus toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html).

**New here? Take the course.** The web UI ships an interactive book (`/book` after `npm run dev`) — 21 chapters from "what is a sequent" to the research frontier, with clickable proof exercises, live forward-execution steppers, a playable timed game, and a wave-function-collapse demo. Content lives in `doc/book/` (authoring guide: `doc/book/AUTHORING.md`).

## Quick Start

```bash
npm install
npm run dev           # Development server (http://localhost:3000)
npm test              # Fast suite (~3584 tests, ~40s)
npm run test:ill      # ILL-native provability tests (98)
npm run test:noffi    # noFFI adversarial soundness (13)
npm run test:all      # Everything (fast + ill + till + noffi + zk + heavy)
```

## What It Does

**Backward proof search** — Given a sequent (goal), find a proof. Uses a five-layer architecture: L1 kernel (verification) → L2 generic search → L3 Andreoli focusing → L4 strategy (manual/auto). Adding a new connective requires only `.calc` + `.rules` changes; all layers pick it up automatically.

**Forward execution** — Committed-choice strategy for the monadic fragment: same ILL derivation rules as the backward prover, but without search. Operates as multiset rewriting — consume resources, produce new ones, repeat until quiescence. Rules compile to indexed matchers with fingerprint/discrimination-tree strategy stacks. Persistent predicates resolve via FFI (arithmetic) or backward clause resolution.

**Symbolic exploration** — Exhaustive DFS over all possible forward executions, building execution trees. Handles nondeterminism (which rule fires) and additive choice (internal branching). Used for model checking and program verification.

**Application: EVM symbolic execution** — a forward-rule model of the Ethereum Virtual Machine. Symbolic memory via write-logs, comparison branching via ⊕, constraint solving for branch pruning. Verifies smart contract properties by exploring all execution paths.

## Architecture

```
lib/
├── kernel/          # Content-addressed AST: store, sequent, unify, substitute
├── prover/          # Backward proof search (L1-L4)
│   ├── kernel.js    # L1: proof verification
│   ├── generic.js   # L2: search primitives (Hodas-Miller lazy splitting)
│   ├── focused.js   # L3: Andreoli focusing
│   └── strategy/    # L4: manual, auto
├── engine/          # Forward/backward execution engine — minimal-essence core
│   ├── compile.js   # Rule compilation (de Bruijn slots, discriminators)
│   ├── match.js     # Pattern matching + persistent proving
│   ├── strategy.js  # Rule selection stack (one channel: engine.buildStrategy)
│   ├── forward.js   # Main loop (committed-choice execution)
│   ├── explore.js   # Exhaustive DFS exploration + backtracking
│   ├── backchain.js # Backward chaining for persistent antecedents
│   ├── compose.js   # Grade-0 cut-elimination pipeline + SLD tabling (semantic passes)
│   ├── convert.js   # .ill → content-addressed hashes
│   ├── sorts.js     # Refinement-sort system (subsort DAG, till-only)
│   ├── cache/       # Persistence: store-binary, compose disk cache, engine version
│   └── opt/         # Toggleable optimizations (fingerprint, disc-tree, FFI dispatch,
│                    #   compose fusion/SROA, prediction, memo) — semantics-free, gated
├── timed/           # Timed layer ABOVE the engine: wall-clock scheduler over the
│                    #   stamp algebra (settle, StampTable, accel/coalesce, lints)
├── measure/         # Measure layer ABOVE the engine: decimation driver (collapse),
│                    #   CI-criterion certifier, constructor priors
├── calculus/        # Calculus loader from .calc/.rules definitions
├── parser/          # Earley parser + grammar generation
├── meta-parser/     # Meta-level parser (@extends chain resolution)
└── rules/           # .rules file parser (sequent notation → descriptors)

family/lnl/          # LNL structural family (shared by calculi, imports lib/ only)
├── lnl.family       # Declarative: sequent constructor, structural rules
├── family-config.js # Executable: cc.family engine hooks
└── lib/             # persistent.js, loli.js, loli-drain.js, existential.js

family/sax/          # SAX structural family — semi-axiomatic sequent calculus
                     # (single-zone Δ ⊢ C, no cartesian zone, null engine hooks)

calculus/ill/        # ILL calculus definition
├── ill.calc         # Connective definitions (tensor, loli, with, oplus, bang, monad, ...)
├── ill.rules        # Inference rules (sequent notation)
├── prelude/         # Type bounds, booleans, arrays
└── programs/        # EVM model, binary arithmetic, multisig contracts

calculus/till/       # till — timed ILL (delay-graded lax monad, refinement sorts)
calculus/sax/        # sax — semi-axiomatic ILL: non-invertible rules as axioms,
                     # explicit cut/snip search, write-once-cell machine (SNAX addressing)

src/ui/              # SolidJS web frontend
doc/                 # Documentation (theory/, documentation/, def/)
```

## Build Commands

```bash
npm run dev              # Dev server
npm run build:ui         # Production build → out/ui/
npm run build:bundle     # Regenerate out/ill.json from calculus specs
npm run bench:diff       # Cross-commit benchmark comparison
```

## Documentation

See `doc/` for detailed documentation:

- `doc/documentation/architecture.md` — Prover lasagne (L1-L5), forward engine internals
- `doc/documentation/content-addressed-store.md` — Store & term architecture
- `doc/documentation/parser-pipeline.md` — Three parser paths from one Earley parser
- `doc/documentation/forward-chaining-engine.md` — Forward engine modules and data flow
- `doc/documentation/lax-monad.md` — `{A}` monad: polarity shift, execution profiles, connective roles
- `doc/theory/0001_exhaustive-forward-chaining.md` — Theoretical foundations
- `doc/theory/0002_motivation.md` — Vision and research directions
