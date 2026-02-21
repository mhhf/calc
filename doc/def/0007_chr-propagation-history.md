---
term: "CHR Propagation History"
summary: "A mechanism that records which rule+constraint combinations have fired, preventing infinite re-firing of propagation rules."
tags: [chr, termination]
see_also: [DEF_0002]
references:
  - "Duck, Stuckey, Garcia de la Banda, Holzbaur, 'The refined operational semantics of CHR', ICLP, 2004"
---

# CHR Propagation History

Propagation rules keep their heads — without a history mechanism, they would fire indefinitely on the same constraints. The **propagation history** records tuples `(rule, {constraint IDs})` to prevent re-firing the same rule on the same constraints.

## Example

```
log @ c(X) ==> log(X).
```

Without history, this rule would infinitely produce `log(X)` from `c(X)`. The history records that `(log, {c₁})` has fired, blocking further applications.

## In CALC

CALC doesn't need a propagation history because linear facts are consumed when matched, naturally preventing re-fire. Persistent facts (`!A`) are kept heads but are only on the proving side (guards), not the consuming side.
