---
term: "Says Modality"
summary: "A modal operator `A says φ` expressing that principal A affirms or authorizes proposition φ; behaves like necessity □_A indexed by principal A."
tags: [authorization, modal-logic, ownership, principals]
see_also: [DEF_0019]
references:
  - "Abadi, Burrows, Lampson, Plotkin, 'A Calculus for Access Control', 1993 (ABLP)"
  - "Garg et al., 'Linear Logic of Authorization and Knowledge', ESORICS 2006"
---

# Says Modality

`A says φ` is a principal-indexed modal operator from authorization logic (ABLP, 1993). It means principal A affirms, believes, or authorizes φ. Combined with linear logic, linear affirmations are consumable (one-time credentials) while exponential affirmations are reusable.

## Example

```
Alice says transfer(Bob, BTC, 0.5)
```
Alice authorizes transferring 0.5 BTC to Bob. If linear, this authorization is consumed on use.

## In CALC

CALC's ownership modality `[Alice] A` is related: it expresses that Alice holds resource A. The `says` modality focuses on authorization (what A approves), while `[A]` focuses on possession (what A has). Both are principal-indexed modalities.
