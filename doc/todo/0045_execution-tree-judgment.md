---
title: "Formalize Execution Tree Judgment"
created: 2026-02-19
modified: 2026-02-19
summary: "Formalize the execution tree as a proof-theoretic judgment — the central theoretical contribution of CALC's exhaustive forward chaining"
tags: [theory, execution-tree, judgment, proof-theory, formalization]
type: research
status: planning
priority: 6
depends_on: [TODO_0041, TODO_0043]
required_by: [TODO_0042]
---

# Formalize Execution Tree Judgment

## The Goal

Give a rigorous proof-theoretic judgment for CALC's execution trees. This is the formalization of `doc/theory/exhaustive-forward-chaining.md` §Formal Judgment.

## Proposed Judgment

`Sigma; Delta |-_fwd T : A`

- `Sigma` = persistent rules (compiled forward rules)
- `Delta` = linear state (multiset of linear facts, including loli continuations)
- `T` = execution tree
- `A` = goal type (or unconstrained)

### Tree Constructors

- `leaf(Delta_q)` — quiescent state (no rules fire)
- `step(r, theta, T')` — deterministic step: rule `r` with substitution `theta`
- `fork(T_1, T_2)` — `⊕` case split (from `plus` in consequent)
- `branch(r_1:T_1, ..., r_n:T_n)` — nondeterministic branch (multiple applicable rules)
- `cycle(Delta)` — back-edge to previously seen state
- `bound(Delta)` — depth limit reached

### Relationship to Existing Frameworks

- **Simmons' SLS (2012):** closest existing work. SLS uses ordered linear lax logic. CALC's judgment extends SLS to ILL with additives and exhaustive exploration.
- **Andreoli focusing (1992):** the tree structure mirrors focused proof search — invertible (eager) phases correspond to deterministic steps, focus (choice) phases correspond to branches.
- **CHR∨ semantics (Betz & Frühwirth 2013):** soundness of ⊕ in consequents should follow from CHR∨ results (see TODO_0043).
- **Stéphan's ω_l (ICLP 2018):** CHR derivations ARE proof trees in ω_l. Each root-to-leaf path in the execution tree is an ω_l proof. Branch nodes = different &L choices (which rule). The non-focused/focused phases map to CALC's `findAllMatches`/`tryMatch`. Program as & (additive conjunction) captures committed choice naturally. See `doc/research/chr-linear-logic.md` §2.4.
- **Stéphan & Barichard's ω_l^{∃∀} (TOCL 2025):** Extends ω_l with ∃/∀ quantified rules. The execution tree is an ω_l^{∃∀} proof where ∀-branching = rule nondeterminism (exhaustive exploration) and ∃-branching = ⊕ disjunction. Dynamic binder = loli continuations. This is the most promising framework for formalizing the full execution tree judgment. See `doc/research/chr-linear-logic.md` §2.5, `doc/todo/0043_chr-linear-logic-mapping.md` §7-8.

## Tasks

- [ ] Write inference rules for each tree constructor
- [ ] Prove soundness: every leaf reachable (compositional, per-constructor)
- [ ] Prove completeness: every reachable quiescent state is a leaf (depends on TODO_0042)
- [ ] Connect to Simmons' SLS — is CALC's judgment a fragment/extension of SLS?
- [ ] Connect to Andreoli focusing — formalize the strategy stack as a focusing strategy
- [ ] Write up as `doc/theory/execution-tree-judgment.md`

## References

- `doc/theory/exhaustive-forward-chaining.md` — proposed judgment (informal), Q5+Q6
- `doc/research/chr-linear-logic.md` — CHR survey, §2.4 (ω_l), §2.5 (QCHR), §10.2-10.3 (CALC mappings)
- [TODO_0042](0042_exhaustive-exploration-completeness.md) — completeness of exploration
- [TODO_0043](0043_chr-linear-logic-mapping.md) — CHR∨ soundness (⊕ justification), §7-8 (ω_l + QCHR)
- Stéphan (2018) "A New Proof-Theoretical Linear Semantics for CHR" ICLP 2018, OASIcs 4:1-4:17
- Barichard, Stéphan (2025) "Quantified Constraint Handling Rules" ACM TOCL 26(3):1-46
- Simmons (2012) "Substructural Logical Specifications" CMU-CS-12-142
- Andreoli (1992) "Focusing Proofs in Linear Logic" JLC 2(3):297-347
