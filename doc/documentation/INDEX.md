# Documentation

Technical documentation for how CALC works.

## Architecture

| Document | Description |
|----------|-------------|
| [[architecture]] | Prover lasagne: L1 kernel → L2 generic → L3 focused → L4 strategy → L5 UI |
| [[content-addressed-store]] | Store & term architecture — node model, hashing, substitution, unification, complexity |
| [[parser-pipeline]] | Three parser paths from one Earley parser |
| [[family-design]] | Calculus family abstraction and @extends mechanism |
| [[matchOpts-reference]] | matchOpts configuration object — all fields, assembly, profile impact |
| [[proof-term-pipeline]] | End-to-end proof term flow: backward → bridge → guided → check |

## Forward Engine

| Document | Description |
|----------|-------------|
| [[forward-chaining-engine]] | Three-layer engine architecture, matching pipeline, strategy stack, optimizations |
| [[optimization-architecture]] | Profile-driven engine config, module map, cache semantics |
| [[existential-compile]] | Compiled ∃-chain — partial evaluation for deterministic predicates |
| [[calldata-representation]] | Unified calldata model — sconcat chain, cd_read/cd_copy clauses, byte_join, FFI |
| [[grade0-composition]] | Grade-0 cut elimination — compile-time composition of `!_0` intermediate types |
| [[fusion-symex-spectrum]] | Compile-time fusion and runtime symex as a continuous spectrum — where fusion saves work, frontier |
| [[sell-graded-modality]] | SELL graded modality `!_a` with {0,1,ω} semiring |
| [[sell-rule-filtering]] | SELL label-based rule filtering |

## Debugging & Testing

| Document | Description |
|----------|-------------|
| [[ill-debug-framework]] | ILL debug framework — observation directives, hooks, profiling |
| [[test-overview]] | Test suite overview — scripts, per-file timing, architecture layers |
| [[audit-findings]] | Codebase audit findings (TODO_0192) |

## Reference

| Document | Description |
|----------|-------------|
| [[ANKI]] | Flashcards for learning proof theory concepts |
