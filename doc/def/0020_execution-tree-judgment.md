---
term: "Execution Tree Judgment"
summary: "A proof-theoretic judgment Σ; Δ ⊢_fwd T : A witnessing all reachable quiescent states from initial state Δ under program Σ via exhaustive forward chaining."
tags: [proof-theory, execution-tree, forward-chaining, linear-logic, judgment]
see_also: [DEF_0001, DEF_0005]
references:
  - "Stéphan (2018) A New Proof-Theoretical Linear Semantics for CHR, ICLP, OASIcs 4:1-4:17"
  - "Barichard, Stéphan (2025) Quantified Constraint Handling Rules, ACM TOCL 26(3):1-46"
  - "Simmons (2012) Substructural Logical Specifications, CMU-CS-12-142"
---

# Execution Tree Judgment

The judgment `Σ; Δ ⊢_fwd T : A` asserts that under program Σ (persistent forward rules) and initial linear state Δ, the execution tree T witnesses all reachable quiescent states. T is a proof term with six constructors: `leaf` (quiescent), `step` (deterministic rule application), `fork` (⊕ case split), `branch` (nondeterministic rule selection), `cycle` (back-edge), `bound` (depth truncation).

Each root-to-leaf path in T is a valid forward-chaining trace (an ω_l proof in Stéphan's framework). Branch nodes represent ∀-quantification over rule choices (exhaustive exploration). Fork nodes represent ⊕L inversion (case analysis on disjunctive consequents).

The tree extends CLF's committed-choice execution (single trace) with don't-know nondeterminism: CLF gives ∃ trace. S →* Q; the execution tree gives the universal quantification T where every path is a valid trace.

## Example

```
step(evm/add, {PC↦0,A↦3,B↦5},
  fork(
    leaf({pc(1), stack(0,0), !neq(3,5)}),     -- branch: 3≠5
    leaf({pc(1), stack(0,1), !eq(3,5)})        -- branch: 3=5
  ))
```

## In CALC

Implemented by `explore.js:explore()`. Tree nodes are `{type, state, children}` objects. The judgment's soundness follows from Betz/Frühwirth Theorem 4.8 (per-step) composed with CHR∨ soundness (⊕ forks). The most promising unified formalization maps to QCHR's ω_l^{∃∀} system (Theorem 5.1). See TODO_0045.
