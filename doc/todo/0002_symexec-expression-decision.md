---
title: "Symbolic Execution: Expression vs Pure Backward Chaining Decision"
created: 2026-02-18
modified: 2026-02-18
summary: "Decide whether symbolic execution needs expression constructors or can use pure backward chaining"
tags: [symexec, expressions, design-decision]
type: design
status: planning
priority: 9
depends_on: [TODO_0041]
required_by: [TODO_0003, TODO_0004, TODO_0005]
---

# Symbolic Execution: Expression vs Pure Backward Chaining

Expression constructors (`plus_expr`, `mul_expr`) embed computation results in term structure. This may conflict with ILL's philosophy: all computation lives in persistent backward-chaining predicates, terms are inert data.

## TODO_0002.Option_1 — Expression constructors (R1)

Skolem-style expression terms in the Store. Catch-all backward clauses for equational completion. Requires confluence proof.

## TODO_0002.Option_2 — Pure backward chaining (T6+R2)

Loli-freeze: auto-emit loli on FFI mode mismatch. Mercury modes for reverse-mode FFI. Eigenvariable fresh generation. Keeps terms inert.

## Tasks

- [ ] Prototype both: expression catch-alls (R1) vs loli-freeze (T6+R2)
- [ ] Evaluate: does the engine need expression terms, or can backward chaining handle everything?
- [ ] Decision checkpoint

See: `doc/dev/evm-modeling-approaches.md`, `doc/research/symbolic-arithmetic-design-space.md`
