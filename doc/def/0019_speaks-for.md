---
term: "Speaks-For"
summary: "A delegation relation where `A speaks for B` means anything A says is automatically attributed to B; formally ∀φ.(A says φ) → (B says φ)."
tags: [authorization, delegation, principals, modal-logic]
see_also: [DEF_0018]
references:
  - "Abadi, Burrows, Lampson, Plotkin, 'A Calculus for Access Control', 1993"
---

# Speaks-For

`A speaks for B` is a delegation primitive: if A affirms φ, then B is considered to also affirm φ. It is transitive and reflexive but NOT symmetric. Formally: `speaks_for(A, B) ≡ ∀φ. (A says φ) → (B says φ)`.

## Example

```
ssh_key speaks for Alice
ssh_key says "open session"
────────────────────────── (speaks-for)
Alice says "open session"
```

Restricted delegation is also possible: `A speaks for B on topic T`.

## In CALC

Delegation would enable modeling proxy contracts, role-based access, and hierarchical authority. Not yet implemented — identified as a future extension built on the ownership modality.
