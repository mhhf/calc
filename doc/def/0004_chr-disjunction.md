---
term: "CHR∨ (CHR with Disjunction)"
summary: "Extension of CHR allowing disjunctive rule bodies, mapping to additive disjunction (⊕) in linear logic."
tags: [chr, linear-logic, oplus, disjunction]
see_also: [DEF_0005, DEF_0002]
references:
  - "Betz & Frühwirth, 'Linear-logic based analysis of constraint handling rules with disjunction', 2013"
---

# CHR∨ (CHR with Disjunction)

CHR∨ extends standard CHR with disjunctive rule bodies: a rule can produce one of several alternative constraint sets. The translation to linear logic is:

```
(B₁ ; B₂)^L = B₁^L ⊕ B₂^L
```

Disjunctive rule bodies map to additive disjunction (`⊕` / internal choice). The system decides which branch to take.

## Example

A comparison rule with two outcomes:

```
eq(X,Y) ⟺ (result(true) ; result(false))
```

translates to `eq(X,Y) ⊢ result(true) ⊕ result(false)`.

## In CALC

CALC uses `⊕` in forward-chaining consequents for EVM comparison branching (`eq`, `iszero`, `jumpi`). The CHR∨ soundness result formally justifies this extension.
