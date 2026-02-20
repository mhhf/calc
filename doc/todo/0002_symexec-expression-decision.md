---
title: "Symbolic Execution: Expression vs Pure Backward Chaining Decision"
created: 2026-02-18
modified: 2026-02-19
summary: "Decide whether symbolic execution needs expression constructors or can use pure backward chaining"
tags: [symexec, expressions, design-decision]
type: design
status: planning
priority: 9
depends_on: []
required_by: [TODO_0003, TODO_0004, TODO_0005]
---

# Symbolic Execution: Expression vs Pure Backward Chaining

Expression constructors (`plus_expr`, `mul_expr`) embed computation results in term structure. This may conflict with ILL's philosophy: all computation lives in persistent backward-chaining predicates, terms are inert data.

## TODO_0002.Option_1 — Expression constructors (R1)

Skolem-style expression terms in the Store. Catch-all backward clauses for equational completion. Requires confluence proof.

## TODO_0002.Option_2 — Pure backward chaining (T6+R2)

Loli-freeze: auto-emit loli on FFI mode mismatch. Mercury modes for reverse-mode FFI. Eigenvariable fresh generation. Keeps terms inert.

## Open Questions

### Existentials (∃) and Eigenvariables

CLF allows `∃` inside the monad — forward rules can create fresh names. CALC doesn't have this yet. Symbolic values (eigenvariables) in symexec ARE existentially quantified — making this explicit could clarify the design:

- **Option 1 (Skolem / R1):** expression terms `plus_expr(X, 3)` are implicitly Skolemized existentials
- **Option 2 (Loli-freeze / R2):** eigenvariables with deferred binding are explicit existentials with suspended proof obligations
- **∃ in monad** would give clean scoping: `∃Y. (plus(X, 3, Y) ⊗ stack(SH, Y))` means "there exists a Y such that plus(X,3,Y) and stack(SH,Y)"
- This connects Skolemization (R1) and loli-freeze (R2) as two different elimination strategies for the same existential

Research needed: how does Celf handle `∃` in forward chaining? Does it solve the symbolic value problem cleanly?

**QCHR connection (Barichard & Stéphan, TOCL 2025):** QCHR extends CHR with ∃/∀ quantified rules and a dynamic binder (quantifiers generated at runtime). This is exactly the pattern CALC needs:
- Expression terms (R1) = Skolemized ∃ (eliminate the quantifier by naming the witness)
- Loli-freeze (R2) = deferred ∃ (suspend the quantifier until more information available)
- QCHR's ∃-elimination rule: find at least one value in [low,up] making body succeed
- QCHR's ∀-elimination: all values must succeed (= symexec exhaustive exploration)
- The ω_l^{∃∀} proof framework handles both elimination strategies uniformly

See: `doc/theory/exhaustive-forward-chaining.md` §Q1, §Q6; `doc/research/chr-linear-logic.md` §2.5; `doc/todo/0043_chr-linear-logic-mapping.md` §8

## Tasks

- [ ] Prototype both: expression catch-alls (R1) vs loli-freeze (T6+R2)
- [ ] Evaluate: does the engine need expression terms, or can backward chaining handle everything?
- [ ] Investigate ∃ in monad as unifying framework for R1/R2
- [ ] Decision checkpoint

See: `doc/dev/evm-modeling-approaches.md`, `doc/research/symbolic-arithmetic-design-space.md`
