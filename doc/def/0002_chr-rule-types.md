---
term: "CHR Rule Types"
summary: "The three kinds of Constraint Handling Rules: simplification, propagation, and simpagation."
tags: [chr]
see_also: [DEF_0001, DEF_0007]
references:
  - "Frühwirth, 'Constraint Handling Rules', Cambridge University Press, 2009"
---

# CHR Rule Types

Constraint Handling Rules come in three forms:

| Type | Syntax | Behavior |
|---|---|---|
| **Simplification** | `H ⟺ G \| B` | Consume all heads, produce body |
| **Propagation** | `H ⟹ G \| B` | Keep all heads, add body |
| **Simpagation** | `H₁ \ H₂ ⟺ G \| B` | Keep `H₁`, consume `H₂`, produce body |

Simpagation subsumes both: simplification is simpagation with empty `H₁`, propagation is simpagation with empty `H₂`.

## Example

```
gcd @ gcd(N) \ gcd(M) ⟺ N ≤ M | gcd(M - N).
```

This simpagation rule keeps one `gcd(N)` and consumes another `gcd(M)`, replacing it with `gcd(M-N)` when `N ≤ M`.

## In CALC

All CALC forward rules are simpagation rules. Persistent antecedents = kept heads (`H₁`). Linear antecedents = removed heads (`H₂`).
