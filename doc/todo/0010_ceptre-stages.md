---
title: "Ceptre Stages"
created: 2026-02-18
modified: 2026-02-19
summary: "Named rule subsets running to quiescence with inter-stage transitions"
tags: [Ceptre, stages, forward-engine]
type: research
cluster: CLF
status: planning
priority: 2
depends_on: [TODO_0006]
required_by: []
---

# Ceptre Stages

Named rule subsets running to quiescence with inter-stage transitions.

## Status: Deferred

Stages feel theoretically unsatisfying — more like an operational hack than a principled contribution. They impose control structure *outside* the logic rather than deriving it from the logic itself. We want to find the right theory/ontology before implementing them.

The SHA3 helper pattern (which motivated stages as a potential solution) already works via loli continuations — the `concatMemory` recursive helper runs to completion, then `unblockConcatMemory(Z)` fires the dormant loli. This is a direct application of loli-left on linear state, not an ad-hoc staging mechanism.

**Open questions before pursuing stages:**
- Is there a proof-theoretic justification for stages (not just operational convenience)?
- Can focusing discipline subsume what stages do? (Invertible rules run eagerly = a "phase")
- Do Ceptre stages correspond to any logical connective or judgment form?
- Could a stratification discipline (like Datalog stratification) emerge from the rule structure rather than being declared?

## Tasks (deferred)

- [ ] Study Ceptre stage semantics
- [ ] Research whether stages have proof-theoretic justification
- [ ] Design stage syntax for .calc/.rules (only if justified)
- [ ] Implement stage engine with transitions

See: `doc/research/clf-celf-ceptre.md`
