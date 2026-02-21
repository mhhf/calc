---
term: "CHR Confluence"
summary: "A CHR program is confluent when all derivations from a state lead to logically equivalent final states."
tags: [chr, confluence, determinism]
see_also: [DEF_0002, DEF_0012]
references:
  - "Abdennadher, Frühwirth, Meuss, 'Confluence and Semantics of Constraint Simplification Rules', 1999"
---

# CHR Confluence

A CHR program is **confluent** if for any state `S`, all possible derivation sequences from `S` lead to equivalent final states (up to logical equivalence / state entailment).

Confluence implies determinism of results: the order of rule application doesn't matter.

## Example

GCD computation is confluent: regardless of which pair of `gcd(N), gcd(M)` values we reduce first, we always reach the same final `gcd(result)`.

## In CALC

CALC's EVM rules are confluent for ground execution (deterministic opcode dispatch — there is only one applicable rule per state). They are non-confluent for symbolic execution (`⊕` creates choice points, by design — exploring all branches is the goal).
