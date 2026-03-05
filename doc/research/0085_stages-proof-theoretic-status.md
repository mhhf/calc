---
title: "Stages in Linear Logic Programming — Proof-Theoretic Status"
created: 2026-03-04
summary: "Why Ceptre-style stages are extra-logical, and how CLF's lax monad subsumes them"
tags: [Ceptre, stages, forward-engine, CLF, lax-monad, quiescence, focusing, proof-theory]
category: "Forward Chaining"
source: "Extracted from TODO_0010 (now subsumed by TODO_0006)"
---

# Stages in Linear Logic Programming — Proof-Theoretic Status

## 1. Why Stages Are Not a Logical Connective

Ceptre stages (Martens 2015) are named rule subsets running to quiescence with inter-stage transitions via a `qui` token. They are **extra-logical**:

1. **No introduction/elimination rules.** `qui` is injected by the runtime, not derived by proof search.
2. **No CLF encoding.** Stages are not part of CLF. The monad `{A}` provides single-block forward-until-quiescence but not multi-phase sequencing.
3. **Quiescence is meta-level.** "No rules can fire" requires checking all rules against all instantiations — a global property that cannot be expressed by finite linear logic rules.
4. **Cannot be derived from the logic.** Quiescence is negation-as-failure. Partial encodings (explicit completion tokens, counters) require the programmer to manually encode failure conditions.

## 2. How the Lax Monad Subsumes Stages

With backward chaining + lax monad `{A}` (now implemented in CALC):

- Quiescence = `forward.run()` returns because `findMatch()` found nothing
- Backward chaining naturally sequences phases: `phase1 -o { rules1 }. phase2 -o { rules2 }.`
- No `qui` token, no extra-logical injection

| System | Needs `qui`? | Why |
|--------|-------------|-----|
| **Ceptre** | Yes | Forward-only — no "phase done" mechanism |
| **CLF/LolliMon** | No | Backward chaining orchestrates, monad exits on quiescence |
| **CALC** | No | `forward.run()` returns on quiescence, backward prover sequences |

## 3. Comparison of Staging Approaches

| Approach | Proof-theoretic? | Automatic? | Expressiveness |
|----------|-----------------|------------|----------------|
| Ceptre stages | No | No (declared) | Full |
| CLF lax monad | Yes | No (programmed) | Sequential phases |
| Focusing phases | Yes | Yes | Per-formula only |
| Loli continuations | Yes | No (encoded) | Ad-hoc barriers |
| Predicate stratification | Partially | Yes (inferred) | Acyclic only |
| CHR priorities | No | No (annotated) | Full |
| Guard predicates | Yes | No (encoded) | Full (manual) |

## 4. Practical Staging Patterns Without Stages

All patterns encodable with loli continuations + lax monad:

**Game phases** (combat → exploration → dialogue → combat):
```ill
combat_done(X) -o exploration_start(X).
exploration_done(X) -o dialogue_start(X).
```

**Compilation phases** (acyclic dependency → auto-stratifiable):
Predicate dependency graph is acyclic; rules naturally fire in order.

**Protocol phases** (handshake → exchange → close):
Exactly what session-typed linear logic already does.

## 5. References

- Martens (2015). *Programming Interactive Worlds with Linear Logic.* PhD thesis, CMU.
- Watkins et al. (2004). *A Concurrent Logical Framework: The Propositional Fragment.*
- Lopez et al. (2005). *Monadic Concurrent Linear Logic Programming.* PPDP.
- Chaudhuri & Pfenning (2006). *A Logical Characterization of Forward and Backward Chaining.* IJCAR.
- Simmons (2012). *Substructural Logical Specifications.* PhD thesis, CMU.
