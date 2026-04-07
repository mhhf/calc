# Documentation

Technical documentation for how CALC works.

## Architecture

| Document | Description |
|----------|-------------|
| [[architecture]] | Prover lasagne: L1 kernel → L2 generic → L3 focused → L4 strategy → L5 UI |
| [[content-addressed-store]] | Store & term architecture — node model, hashing, substitution, unification, complexity |
| [[parser-pipeline]] | Three parser paths from one Earley parser |
| [[family-design]] | Calculus family abstraction and @extends mechanism |

## Forward Engine

| Document | Description |
|----------|-------------|
| [[forward-chaining-engine]] | Three-layer engine architecture, matching pipeline, strategy stack, optimizations |
| [[grade0-composition]] | Grade-0 cut elimination — compile-time composition of `!_0` intermediate types |
| [[sell-graded-modality]] | SELL graded modality `!_a` with {0,1,ω} semiring |
| [[sell-rule-filtering]] | SELL label-based rule filtering |

## Reference

| Document | Description |
|----------|-------------|
| [[CHANGELOG]] | Release history and changes |
| [[notes]] | Miscellaneous technical notes |
| [[ANKI]] | Flashcards for learning proof theory concepts |
| [[benchmark-v2]] | Proof search benchmark results |
