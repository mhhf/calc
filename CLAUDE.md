# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Principles
- Rather then guessing, lying or faking confidence, admit you don't know or have incomplete information - ask me questions or tell me how i can support you, i'm happy to help.
- always keep the git repository clean. On the end of a task, stash and commit with the correct message - keep it short. For a big chunk of work that will require iteration, user feedback, multiple commits, potentially sessions over multiple days - create a feature-branch, then rebase once you are done
- Keep the root directory clean, write all documents, except CLAUDE.md and README.md in the doc/ or dev/ folder, don't keep junk in the root
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
# New SolidJS UI
npm run dev           # Development server (http://localhost:3000)
npm run build:ui      # Production build to out/ui/

# Core
npm run build:parser  # Regenerate parser from ll.json
npm test              # Run Mocha tests
make                  # Install CLI symlinks

# Legacy CycleJS UI (deprecated)
npm run ui:legacy     # Build and serve old UI
```

## Directory Structure

```
lib/                  # Core library (used by CLI and UI)
├── types/            # TypeScript type definitions
├── calc.js           # Calculus database
├── node.js           # AST representation
├── parser.js         # Jison grammar generation
├── sequent.js        # Logical sequents
├── proofstate.js     # Proof search engine
├── pt.js             # Proof trees
└── ...

src/ui/               # SolidJS frontend
├── components/       # Reusable components
│   ├── layout/       # Shell, TabNav
│   ├── math/         # KaTeX, FormulaInput, InferenceRule
│   ├── graph/        # ASTView, ProofTree
│   └── common/       # ErrorBoundary, Loading
├── pages/            # Route pages
│   ├── Sandbox.tsx   # Formula sandbox
│   ├── CalculusOverview.tsx
│   └── MetaOverview.tsx
├── state/            # UI-only state
└── styles/           # Tailwind CSS

libexec/              # CLI entry points
out/                  # Generated outputs
├── parser.js         # Generated Jison parser
├── calc.json         # Calculus data for browser
└── ui/               # Built SolidJS app
```

## CLI Usage

All commands are invoked via `calc <cmd> <options>`:
- `calc parse <str>` - Parse formula, output tree and LaTeX
- `calc proof` - Interactive/automated proof generation
- `calc genparser` - Regenerate parser from ll.json
- `calc gendoc` - Generate documentation
- `calc debug-*` - Various debugging utilities

## Architecture

**Core Data Flow:**
```
Formula Input → Parser (jison) → Node/AST → Sequent → Proofstate → Proof Tree → Output
```

**Key Components:**
- `ll.json` - Master calculus definition (grammar, precedence, output formats)
- `lib/parser.js` - Dynamically generates Jison grammar from ll.json
- `lib/node.js` - AST with format-polymorphic rendering (ASCII, LaTeX, Isabelle)
- `lib/sequent.js` - Logical sequent structure
- `lib/proofstate.js` - Proof search with inversion and focusing
- `lib/types/` - TypeScript definitions for all lib modules

**Web UI (SolidJS):**
- Tech: SolidJS + TypeScript + Tailwind CSS + Vite
- Source: `src/ui/`
- Build: `out/ui/`
- Three tabs: Sandbox, Calculus Overview, Meta Overview
- Imports `lib/` directly (CommonJS modules)

**Custom Rule Language (LLT):**
- Grammar: `src/llt.jison`
- Programs: `programs/*.llt`
