---
term: "Prefix Firing"
summary: "A triple ⟨rule, substitution, consumed facts⟩ representing one forward-chaining step, with O(1) amortized cost under proper indexing."
tags: [forward-chaining, cost-semantics, complexity]
see_also: [DEF_0008]
references:
  - "Simmons & Pfenning, 'Linear logical algorithms', ICALP, 2008"
---

# Prefix Firing

A **prefix firing** is a triple `⟨r, σ, [l₀,...,lₖ₋₁]⟩` consisting of:

- `r` — the rule being fired
- `σ` — the substitution (variable bindings)
- `[l₀,...,lₖ₋₁]` — the consumed linear facts

The **abstract running time** of a forward-chaining program is the total number of prefix firings to quiescence. Simmons & Pfenning show there exists an interpreter achieving O(1) amortized cost per firing with appropriate indexing.

## Example

For rule `a(X), b(X) ⊸ c(X)` firing on facts `a(5), b(5)`:

```
⟨ a(X),b(X)⊸c(X),  {X↦5},  [a(5), b(5)] ⟩
```

## In CALC

Each `tryMatch` + `mutateState` in the forward engine is one prefix firing. The strategy stack (opcode index + disc tree) achieves near-O(1) rule lookup per firing.
