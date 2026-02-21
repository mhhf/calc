# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Principles
- Rather then guessing, lying or faking confidence, admit you don't know or have incomplete information - ask me questions or tell me how i can support you, i'm happy to help.
- always keep the git repository clean. On the end of a task, stash and commit with the correct message - keep it short. For a big chunk of work that will require iteration, user feedback, multiple commits, potentially sessions over multiple days - create a feature-branch, then rebase once you are done
- Keep the root directory clean (only CLAUDE.md and README.md). All documents go in `doc/` — see **doc/ Placement Rule** below
- Don't write 'status update' documents or other verbose documents unless its told expricitly. Keep all documents descriptive of what IS not how it changed. Keep it VERY short and concise
- rather then simply recognizing an error and fixing it - think always how to isolate it and test it in isolation - e.g. via unit and integration tests. If its not possible then how to encapsule it (e.g. via logs), then either testing the failed state via unit tests or testing your hypothesis via verifying the logs. only after you verified the fail and isolated the error, you should think about fixing it


## ANKI

I want to create an anki deck where I learn potential concepts. Whenever I tell you or once we have research results (with my approval) - write new discoveries as flashcards of the style Q:A to doc/ANKI.md. They should have the style of mdanki
```
## questions

answer
```


## Project Overview

CALC is an experimental proof calculus system for linear logic, inspired by the [calculus toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/doc/introduction.html). It implements a proof search engine with forward/backward chaining rules, dynamic parser generation, and multi-format output.

## Build & Development Commands

```bash
npm run dev           # Development server (http://localhost:3000)
npm run build:ui      # Production build to out/ui/
npm run build:bundle  # Regenerate out/ill.json from calculus specs
npm test              # Run core tests (417 tests)
npm run test:engine   # Run engine tests (107 tests)
npm run test:all      # Run everything
```

## Directory Structure

```
lib/                     # Core library
├── kernel/              # Content-addressed AST: store, sequent, unify, substitute, ast
├── prover/              # Proof search engine (5-layer architecture)
│   ├── kernel.js        # L1: proof verification
│   ├── generic.js       # L2: search primitives
│   ├── focused.js       # L3: Andreoli focusing
│   ├── strategy/        # L4: manual, auto, forward, symexec
│   ├── rule-interpreter.js  # descriptor → premise computation
│   ├── context.js       # multiset operations
│   ├── state.js         # proof state
│   └── pt.js            # proof trees
├── calculus/            # Calculus loader (from .calc/.rules files)
├── engine/              # Forward/backward execution engine
│   ├── convert.js       # .ill → content-addressed hashes
│   ├── prove.js         # backward chaining
│   └── ffi/             # foreign function interface
├── meta-parser/         # Meta-level parser (tree-sitter CST → AST)
│   ├── cst-to-ast.js    # CST → structured AST
│   └── loader.js        # @extends chain resolution
├── parser/              # Sequent string parser
├── rules/               # .rules file parser (sequent notation → descriptors)
├── tree-sitter-mde/     # Tree-sitter grammar (shared by meta-parser + engine)
├── browser.js           # Browser-compatible API (loads from ill.json bundle)
├── index.js             # Node.js API entry point
└── hash.js              # Content-addressing hash functions

calculus/ill/            # ILL calculus definition
├── ill.calc             # Connective definitions
├── ill.rules            # Inference rules (sequent notation)
├── lnl.family           # Family infrastructure
├── prelude/types.ill    # Type bounds, booleans
└── programs/            # Real programs (EVM, binary arithmetic, multisig)

src/ui/                  # SolidJS frontend
├── lib/calculus.ts      # Calculus API for browser
├── lib/proofLogic.ts    # Proof logic adapter
├── pages/               # Route pages
└── components/          # UI components

tests/                   # Test suite
├── engine/              # Engine tests + fixtures
└── *.test.js            # Core prover tests

benchmarks/              # Performance benchmarks
├── engine/              # Engine benchmarks & profiles
├── proof/               # Proof search benchmarks
└── micro/               # Micro-benchmarks

out/                     # Generated outputs
├── ill.json             # Bundled calculus for browser
└── ui/                  # Built SolidJS app
```

## doc/ Placement Rule

| Subdirectory | What goes there | Naming | Examples |
|---|---|---|---|
| `doc/research/` | **External knowledge** — literature surveys, paper summaries, technique catalogs sourced from existing work | `NNNN_title.md` + `meta.yaml` | `0007_chr-linear-logic.md` |
| `doc/theory/` | **Our original contributions** — novel theorems, proof sketches, design frameworks unique to CALC | `NNNN_title.md` + `meta.yaml` | `0001_exhaustive-forward-chaining.md` |
| `doc/documentation/` | **How CALC works NOW** — system architecture, data-flow docs, reference material | free-form | `architecture.md`, `content-addressed-store.md` |
| `doc/todo/` | **Numbered task specs** — planned work, bugs, research tasks | `NNNN_title.md` + `meta.yaml` | `0041_unified-rule-matching.md` |
| `doc/def/` | **Atomic definitions** — one concept per file, encyclopedia of terms | `NNNN_title.md` + `meta.yaml` | `0005_internal-vs-external-choice.md` |

**Decision heuristic:** "Did we invent it?" → `theory/`. "Did someone else write about it?" → `research/`. "Does it describe the system as-is?" → `documentation/`. "Is it a concrete task to do?" → `todo/`. "Is it a single concept/term to define?" → `def/`.

## Architecture

See `doc/documentation/architecture.md` for the full prover lasagne (L1-L5).
See `doc/documentation/parser-pipeline.md` for the three parser paths.

**Web UI (SolidJS):**
- Tech: SolidJS + TypeScript + Tailwind CSS + Vite
- Source: `src/ui/`
- Build: `out/ui/`
- Imports `lib/` directly (CommonJS modules)
