# CALC


**CALC** (Calculus for Accountable Linear Computations) is a proof calculus system for [Intuitionistic Linear Logic](https://en.wikipedia.org/wiki/Linear_logic) (ILL). It implements backward proof search (Andreoli focusing), forward execution (multiset rewriting), and exhaustive symbolic exploration — all generated from declarative rule definitions.

The driving insight: double-entry bookkeeping is applied linear logic. Resources are tracked exactly, consumed on use, and never duplicated — the same discipline accountants have followed since Pacioli (1494). CALC makes this connection formal and computational.

Inspired by the [calculus toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html).

## Quick Start

```bash
npm install
npm run dev           # Development server (http://localhost:3000)
npm test              # Core tests (431)
npm run test:engine   # Engine tests (338)
npm run test:all      # All tests (769)
```

## What It Does

**Backward proof search** — Given a sequent (goal), find a proof. Uses a five-layer architecture: L1 kernel (verification) → L2 generic search → L3 Andreoli focusing → L4 strategy (manual/auto). Adding a new connective requires only `.calc` + `.rules` changes; all layers pick it up automatically.

**Forward execution** — Committed-choice strategy for the monadic fragment: same ILL derivation rules as the backward prover, but without search. Operates as multiset rewriting — consume resources, produce new ones, repeat until quiescence. Rules compile to indexed matchers with fingerprint/discrimination-tree strategy stacks. Persistent predicates resolve via FFI (arithmetic) or backward clause resolution.

**Symbolic exploration** — Exhaustive DFS over all possible forward executions, building execution trees. Handles nondeterminism (which rule fires) and additive choice (internal branching). Used for model checking and program verification.

**Application: EVM symbolic execution** — 44 forward rules model the Ethereum Virtual Machine. Symbolic memory via write-logs, comparison branching via ⊕, constraint solving for branch pruning. Verifies smart contract properties by exploring all execution paths.

## Architecture

```
lib/
├── kernel/          # Content-addressed AST: store, sequent, unify, substitute
├── prover/          # Backward proof search (L1-L4)
│   ├── kernel.js    # L1: proof verification
│   ├── generic.js   # L2: search primitives (Hodas-Miller lazy splitting)
│   ├── focused.js   # L3: Andreoli focusing
│   └── strategy/    # L4: manual, auto
├── engine/          # Forward execution engine
│   ├── compile.js   # Rule compilation (de Bruijn slots, discriminators)
│   ├── match.js     # Pattern matching + persistent proving
│   ├── strategy.js  # Rule selection (fingerprint → disc-tree → predicate)
│   ├── forward.js   # Main loop (committed-choice execution)
│   ├── explore.js   # Exhaustive DFS exploration + backtracking
│   ├── backchain.js # Backward chaining for persistent antecedents
│   ├── ffi/         # Foreign function interface (arithmetic, memory)
│   └── opt/         # Toggleable optimization modules
├── calculus/        # Calculus loader from .calc/.rules definitions
├── parser/          # Earley parser + grammar generation
├── meta-parser/     # Meta-level parser (@extends chain resolution)
└── rules/           # .rules file parser (sequent notation → descriptors)

calculus/ill/        # ILL calculus definition
├── ill.calc         # Connective definitions (tensor, loli, with, oplus, bang, monad, ...)
├── ill.rules        # Inference rules (sequent notation)
├── prelude/         # Type bounds, booleans, arrays
└── programs/        # EVM model, binary arithmetic, multisig contracts

src/ui/              # SolidJS web frontend
doc/                 # Documentation (research/, theory/, documentation/, def/)
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
