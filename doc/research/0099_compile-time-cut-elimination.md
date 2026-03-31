---
title: "Compile-Time Cut Elimination for Forward Rule Composition"
created: 2026-03-31
modified: 2026-03-31
summary: "Survey of techniques for composing forward rules via cut elimination on intermediate resource types at compile time"
tags: [linear-logic, forward-chaining, proof-theory, focusing, optimization, cut-elimination]
category: "Forward Chaining"
---

# Compile-Time Cut Elimination for Forward Rule Composition

## Motivation

EVM rules in CALC share repeated resource patterns (dispatch preamble, gas accounting, memory context) across 100+ rules. Rather than extralogical text macros, the principled approach is to define abstract intermediate resource types with expansion rules, then compose them with the EVM rules at compile time via cut elimination — producing equivalent rules with the intermediate types eliminated.

This is a logical operation (cut on ILL sequents), not a syntactic one.

## Core Theory: Cut in ILL

Given two forward rules sharing an intermediate resource type M:

```
R₁: A₁ * ... * Aₙ  -o  { M * B₁ * ... * Bₖ }
R₂: M * C₁ * ... * Cₘ  -o  { D₁ * ... * Dⱼ }
```

Cut on M yields the composed rule:

```
R₁;R₂: A₁ * ... * Aₙ * C₁ * ... * Cₘ  -o  { B₁ * ... * Bₖ * D₁ * ... * Dⱼ }
```

This is the multiplicative cut rule in linear sequent calculus:

```
  Γ ⊢ M ⊗ Δ₁        M, Γ₂ ⊢ Δ₂
  ─────────────────────────────────  (Cut on M)
       Γ, Γ₂ ⊢ Δ₁ ⊗ Δ₂
```

**Soundness:** Cut elimination holds for ILL (Girard 1987, Pfenning 1994). The composed rule is provably equivalent to the two-step sequence. For the multiplicative fragment (tensor, loli — no exponential cuts), cut elimination is polynomial.

## Focusing and Synthetic Rules

Andreoli's focusing discipline (JLC 1992) organizes proof search into alternating synchronous (committed) and asynchronous (invertible) phases. Each forward rule is one **synthetic step** — a complete synchronous phase.

Chaudhuri, Miller, Saurin (TCS 2008) show that focused derivations compose via **multi-focused cut elimination**: if R₁ and R₂ are focused rules chaining through intermediate M, the composition R₁;R₂ is also a valid focused rule. The intermediate M never appears in the composed proof.

Key result from Chaudhuri's thesis (CMU-CS-06-162): "derived rules are constructed for neutral sequents that make intermediate focal and active sequents irrelevant." This is exactly compile-time composition — the intermediate type is eliminated at the proof-theoretic level.

## Partial Deduction for Linear Logic

Küngas & Matskin (DALT 2004/2005) adapt classical partial deduction to the `!`-Horn fragment of ILL. Their **unfolding** operation replaces an intermediate linear atom in a rule body with the body of the rule that produces it — a direct operational form of cut.

**Soundness theorem:** For the `!`-Horn fragment, partial deduction is sound and complete. The residual program has the same derivable conclusions.

**Conditions:**
- The intermediate atom must be produced uniquely by the rules being unfolded through
- Closedness: every atom in the residual rules is in the original base or specialized residuals

## Unfold/Fold Transformations

The Tamaki-Sato (ICLP 1984) / Pettorossi-Proietti (JLP 1994) framework provides a general theory of program transformation via unfolding (inlining) and folding (abstracting). Unfolding a non-recursive clause preserves the least Herbrand model.

**Limitation for ILL:** Classical unfold/fold assumes contraction and weakening (free copying/discarding). In ILL, each resource must be used exactly once. Naive unfolding would double-consume antecedent resources. The linear-aware version must track that the composed rule uses each input exactly once — which the cut rule guarantees by construction.

## Petri Net Series-Place Reduction

The composition has a direct analog in Petri net theory. An intermediate type M with exactly one producing transition (R₁) and one consuming transition (R₂) is a **series place**. Series-place elimination (fusing R₁ and R₂, removing M) preserves reachability, boundedness, and liveness.

This gives a decision criterion: if M has exactly one producer and one consumer in the rule set, composition is unconditionally safe.

## CHR Operational Equivalence

Constraint Handling Rules (Frühwirth 1998) provides a decidable syntactic condition for operational equivalence of terminating confluent programs. For the simplification-only fragment (which corresponds to pure linear multiset rewriting), rule composition via critical pair analysis is sound.

## Conservative Extension Conditions

Adding intermediate types + expansion rules is a **conservative extension** of the base theory if:

1. **M is abstract:** type M does not appear in the base signature
2. **M is fully produced:** every M token comes from expansion rules
3. **M is fully consumed:** every M token is consumed by composition targets
4. **M is not observable:** M does not appear in initial states or goals

When these hold, the expanded system (with M) and the composed system (without M) are observationally equivalent for all states expressible in the base types.

## Application to CALC EVM Rules

### The dispatch/dispatch_re pattern

```ill
dispatch: bin -> bin -> bin -> bin -> type.
dispatch_re: bin -> type.

dispatch/expand:
  bytecode BC * pc PC * !arr_get BC PC OP * !inc PC PC'
  -o { dispatch BC PC OP PC' * dispatch_re BC }.

dispatch_re/contract:
  dispatch_re BC -o { bytecode BC }.
```

Abstract EVM rule:
```ill
evm/add:
  dispatch BC PC 0x01 PC' * gas GAS * !checked_sub GAS 3 GAS' *
  stack [A, B | REST]
  -o { dispatch_re BC *
       exists Z. (pc PC' * gas GAS' * stack [Z | REST] * !add A B Z) }.
```

**Composition** (cut on `dispatch`, then `dispatch_re`):

1. Cut `dispatch/expand` into `evm/add` on `dispatch`:
   - Antecedent: `bytecode BC * pc PC * !arr_get BC PC 0x01 * !inc PC PC' * gas GAS * !checked_sub GAS 3 GAS' * stack [A, B | REST]`
   - Consequent: `dispatch_re BC * exists Z. (pc PC' * gas GAS' * stack [Z | REST] * !add A B Z)`

2. Cut `dispatch_re/contract` on `dispatch_re`:
   - Final consequent: `bytecode BC * exists Z. (pc PC' * gas GAS' * stack [Z | REST] * !add A B Z)`

Result is identical to the longhand rule.

### Multi-resource expansion

For gas accounting, memory context, etc., define separate intermediate types and compose in sequence. Each cut eliminates one intermediate type. Order of composition doesn't matter (cuts commute on disjoint types).

## Implementation Strategy in CALC

### Where in the pipeline

```
loadFile:
  resolveImports → parseDeclarations → pass1 (definitions) → pass2 (rules)
  → composeRules(forwardRules)     ← NEW: cut elimination pass
  → compileRule()                  ← existing compilation
```

### Algorithm sketch

1. Identify **expansion rules**: rules whose antecedent consists entirely of base types and whose consequent includes an abstract type
2. Identify **contraction rules**: rules whose antecedent includes an abstract type and whose consequent consists entirely of base types
3. For each abstract type M, find its unique producer (expansion) and consumers (abstract EVM rules)
4. For each consumer: unify M-pattern in consumer's antecedent with M-pattern in producer's consequent → substitution σ
5. Apply σ, merge antecedents (excluding M), merge consequents (excluding M)
6. For `_re` types: repeat the process for the consequent side
7. Feed composed raw rules into `compileRule()`

### Required infrastructure

- `unify.unify(a, b)` — already exists, handles metavars + equational theories
- `flattenAntecedent(h, rc)` — already exists, decomposes tensor spines
- `Store.put('tensor', [...])` — already exists, reconstructs formulas
- `collectMetavars(h)` + `freshMetavar()` — already exist, for alpha-renaming before composition
- **New:** multiset matching (match R₁'s consequent facts against R₂'s antecedent facts)
- **New:** marking rules as expansion/contraction (annotation or naming convention)

## References

- Girard, "Linear Logic" (TCS, 1987) — cut elimination for ILL
- Pfenning, "Structural Cut Elimination in Linear Logic" (CMU-CS-94-212, 1994)
- Andreoli, "Logic Programming with Focusing Proofs in Linear Logic" (JLC, 1992)
- Chaudhuri, Miller, Saurin, "Canonical Sequent Proofs via Multi-Focusing" (TCS, 2008)
- Chaudhuri, "The Focused Inverse Method for Linear Logic" (CMU-CS-06-162, 2006)
- Chaudhuri, Miller, Saurin, "Multi-focused Cut Elimination" (arXiv 1502.04771)
- Küngas, Matskin, "Partial Deduction for Linear Logic" (DALT 2004, Springer LNCS 3476)
- Tamaki, Sato, "Unfold/Fold Transformations of Logic Programs" (ICLP, 1984)
- Pettorossi, Proietti, "Transformation of Logic Programs" (JLP, 1994)
- Frühwirth, "Theory and Practice of Constraint Handling Rules" (JLP, 1998)
- Cervesato, "Typed MSR: Syntax and Examples" (MMM-ACNS, 2001)
- Cervesato, Pfenning, Walker, Watkins, "A Concurrent Logical Framework" (CMU-CS-02-101, 2002)
- Harland, Pym, Winikoff, "Forward and Backward Chaining in Linear Logic" (CADE, 2000)
- Simmons, Pfenning, "Linear Logical Algorithms" (ICALP, 2008)
- Martens, "Ceptre: A Language for Modeling Generative Interactive Systems" (PhD thesis, CMU, 2015)
