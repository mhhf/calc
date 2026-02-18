---
title: "Hypersequent Interpretation of Symexec Trees"
created: 2026-02-18
modified: 2026-02-18
summary: "Formalize symexec tree as hypersequent using Avron's framework"
tags: [research, hypersequent, symexec, Avron]
type: research
status: planning
priority: 3
depends_on: []
required_by: []
---

# Hypersequent Interpretation

The symexec tree is structurally a hypersequent: each leaf is a component sequent, the whole tree is their meta-level disjunction. Plus-left creates object-level alternatives; `explore()` builds the hypersequent. Pruning infeasible leaves = eliminating hypersequent components.

- [ ] Study Avron (1991) hypersequent calculus in context of symexec trees
- [ ] Formalize: is the symexec tree exactly a hypersequent derivation?
- [ ] Relationship between plus-left (object-level case split) and hypersequent external structural rules

See: `doc/research/symbolic-branching.md`
