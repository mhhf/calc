---
term: "Internal vs External Choice (⊕ vs &)"
summary: "⊕ (plus/internal choice) means the producer decides which branch; & (with/external choice) means the consumer decides."
tags: [linear-logic, connectives, oplus, with]
see_also: [DEF_0004]
references:
  - "Girard, 'Linear Logic', Theoretical Computer Science 50(1), 1987"
---

# Internal vs External Choice (⊕ vs &)

Linear logic has two forms of disjunction/conjunction at the additive level:

| Connective | Name | Who decides | Notation |
|---|---|---|---|
| `⊕` | Plus / internal choice | Producer (system) | `A ⊕ B` |
| `&` | With / external choice | Consumer (environment) | `A & B` |

**Internal choice** (`⊕`): the provider of the resource decides which alternative to offer. The consumer must handle whichever branch is chosen.

**External choice** (`&`): the consumer picks which alternative to use. The provider must be prepared to deliver either.

## Example

- `eq(X,Y) ⊢ result(true) ⊕ result(false)` — the comparison result (system) decides which branch. Internal choice.
- `menu ⊢ coffee & tea` — the customer (consumer) picks. External choice.

## In CALC

EVM comparison branching uses `⊕` because the comparison result is system-determined. The backward prover treats `&` as invertible on the right (consumer picks = we must prove both), and `⊕` as non-invertible (producer picks = we prove one).
