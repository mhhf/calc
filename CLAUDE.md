# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Principles
- Rather then guessing, lying or faking confidence, admit you don't know or have incomplete information - ask me questions or tell me how i can support you, i'm happy to help.
- always keep the git repository clean. On the end of a task, stash and commit with the correct message - keep it short. For a big chunk of work that will require iteration, user feedback, multiple commits, potentially sessions over multiple days - create a feature-branch, then rebase once you are done
- Keep the root directory clean, write all documents, except CLAUDE.md and README.md in the doc/ or dev/ folder, don't keep junk in the root
- Don't write 'status update' documents or other verbose documents unless its told expricitly. Keep all documents descriptive of what IS not how it changed. Keep it VERY short and concise
- rather then simply recognizing an error and fixing it - think always how to isolate it and test it in isolation - e.g. via unit and integration tests. If its not possible then how to encapsule it (e.g. via logs), then either testing the failed state via unit tests or testing your hypothesis via verifying the logs. only after you verified the fail and isolated the error, you should think about fixing it

## Directory Structure

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
make              # Install symlinks to /usr/local (default)
make test         # Run Mocha tests
make html         # Build web UI bundle (runs genparser + webpack)
make clean        # Clean output directory
make uninstall    # Remove installed symlinks
```

Run tests directly:
```bash
./node_modules/mocha/bin/mocha tests           # All tests
./node_modules/mocha/bin/mocha tests/node.js   # Single test file
```

## CLI Usage

All commands are invoked via `calc <cmd> <options>`:
- `calc parse <str>` - Parse formula, output tree and LaTeX
- `calc proof` - Interactive/automated proof generation
- `calc gendoc` - Generate documentation from src/* to doc/
- `calc genparser` - Regenerate parser from ll.json
- `calc saturate` - Apply rule saturation
- `calc compare` - Compare formulas
- `calc gencalc` - Generate Isabelle theories
- `calc debug-*` - Various debugging utilities (grammar, precedence, rules, proof, etc.)

## Architecture

**Core Data Flow:**
```
Formula Input → Parser (jison) → Node/AST → Sequent → Proofstate → Proof Tree → Output
```

**Key Components:**
- `ll.json` - Master calculus definition containing grammar rules, operator precedence, and multi-format output specs (ASCII, LaTeX, Isabelle)
- `lib/parser.js` - Dynamically generates Jison grammar from ll.json
- `lib/node.js` - AST node representation with format-polymorphic rendering
- `lib/sequent.js` - Logical sequent structure (persistent_ctx, linear_ctx, succedent)
- `lib/proofstate.js` - Proof search engine with auto-prover, inversion, forward/backward chaining
- `lib/llt_compiler.js` - Compiles custom rule definitions from .llt files
- `libexec/calc-*` - CLI command entry points

**Custom Rule Language (LLT):**
- Grammar defined in `src/llt.jison` and `lib/llt.jison`
- Rule programs in `programs/*.llt`

**Web UI:**
- Built with Cycle.js, KaTeX (math rendering), and Viz.js (graph visualization)
- Source in `src/html/`, output to `out/html/`
