---
term: "Delta-Driven Activation"
summary: "A CHR compilation technique where only newly added constraints trigger rule evaluation, avoiding redundant re-scanning."
tags: [chr, optimization, compilation]
see_also: [DEF_0002]
references:
  - "Holzbaur, Frühwirth, 'Compiling Constraint Handling Rules into Prolog with attributed variables', 2000"
  - "Miranker, 'TREAT: A new and efficient match algorithm for AI production systems', 1987"
---

# Delta-Driven Activation

In standard CHR execution, every step re-scans all candidate rules against all constraints. **Delta-driven activation** (also called "active constraint" or TREAT-style dirty tracking) only evaluates rules triggered by newly added or modified constraints.

When a new constraint is added, it becomes the **active constraint**. Only rules whose head matches the active constraint are attempted. This skips ~80% of rule evaluations at scale.

## Example

If a rule has heads `h1(X), h2(Y)` and only `h2(5)` was just added, only rules with `h2` in a head position are checked — rules involving only `h1` are skipped entirely.

## In CALC

CALC currently re-scans all candidates per step. Adding delta-driven activation is a known optimization opportunity (see TODO_0044 semi-naive evaluation).
