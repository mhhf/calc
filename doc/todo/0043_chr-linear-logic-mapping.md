---
title: "CHR/CHR∨ ↔ Linear Logic: Soundness Mapping for CALC"
created: 2026-02-19
modified: 2026-02-19
summary: "Apply Betz & Frühwirth's CHR ↔ linear logic results to CALC: formal soundness proof for forward engine, CHR∨ soundness for ⊕ in consequents, confluence analysis, compilation techniques"
tags: [CHR, linear-logic, soundness, forward-engine, oplus, theory]
type: research
status: planning
priority: 10
depends_on: []
required_by: [TODO_0041, TODO_0042]
---

# CHR/CHR∨ ↔ Linear Logic Mapping

## Why This Matters

CALC's forward engine IS a CHR engine (simpagation rules with guards). Betz & Frühwirth (2005-2018) proved soundness and completeness results mapping CHR to linear logic. These results should transfer to CALC, giving us formal guarantees essentially for free.

CHR∨ (CHR with disjunction) maps disjunctive rule bodies to `⊕` in linear logic. CALC's `⊕` in forward-chaining consequents is exactly this. The CHR∨ soundness result would formally justify our `⊕` extension.

## Key Results to Apply

### 1. Simpagation ↔ ILL forward rules (Betz & Frühwirth 2005)

CALC's forward rules with persistent + linear antecedents and guards (FFI) are simpagation rules:
- Kept head = persistent antecedent (`!A`)
- Removed head = linear antecedent
- Guard = backward proving / FFI
- Body = consequent

**Theorem 4.8 (Soundness):** operational derivation implies linear logic entailment. Verify this transfers to CALC's specific rule format.

### 2. CHR∨ disjunction ↔ ⊕ (Betz & Frühwirth 2013)

Disjunctive rule bodies `(B1 ; B2)` translate to `B1^L ⊕ B2^L`. CALC's `⊕` in consequents is this. The soundness result should extend directly.

**Task:** Verify the CHR∨ → ⊕ mapping matches CALC's `expandItem` behavior for `plus`.

### 3. Confluence analysis

CHR confluence = "different rule firing orders produce equivalent final states." For terminating programs, decidable via critical pair analysis. Could give us guarantees about EVM rule determinism (for ground execution).

### 4. Compilation techniques

CHR compilation (occurrence indexing, join ordering, guard scheduling) directly applies to CALC's `tryMatch`. Could inform future optimization stages.

## Research Tasks

- [ ] Read Betz & Frühwirth CP 2005, TOCL 2013, ICLP 2018 papers in full
- [ ] Map CALC's specific rule format to CHR simpagation translation
- [ ] Verify Theorem 4.8 soundness transfers (identify any gaps)
- [ ] Map CHR∨ disjunction to CALC's `⊕` in consequents
- [ ] Analyze confluence for EVM rule set (critical pairs)
- [ ] Extract concrete compilation improvements (join ordering, guard scheduling)
- [ ] Integrate findings into `doc/theory/exhaustive-forward-chaining.md`
- [ ] Update `doc/research/forward-chaining-networks.md` with CHR compilation details

## References

- `doc/research/chr-linear-logic.md` — comprehensive CHR survey
- `doc/theory/exhaustive-forward-chaining.md` — CALC's theoretical position
- Betz & Frühwirth (2005) "A Linear-Logic Semantics for CHR" CP 2005
- Betz & Frühwirth (2013) "CHR with Disjunction" ACM TOCL 14(1)
- Betz & Frühwirth (2018) "A New Proof-Theoretical Linear Semantics for CHR" ICLP 2018
- Betz (2014) PhD thesis: unified framework
