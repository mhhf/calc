---
term: "Pacioli Group"
summary: "The group of differences P = {[x // y] : x, y >= 0} modeling double-entry T-accounts, with addition [a//b]+[c//d]=[a+c//b+d] and inverse -[a//b]=[b//a]; isomorphic to the integers."
tags: [accounting, linear-logic, resource-semantics, grothendieck-group]
see_also: []
references:
  - "Ellerman, 'On Double-Entry Bookkeeping: The Mathematical Treatment', arXiv:1407.1898"
---

# Pacioli Group

The Pacioli Group P is the group of differences (Grothendieck group) constructed from non-negative reals. Elements are T-accounts `[x // y]` where x = debit, y = credit.

- **Addition:** `[a // b] + [c // d] = [a+c // b+d]`
- **Identity:** `[0 // 0]`
- **Inverse:** `-[a // b] = [b // a]` (swap debit/credit)
- **Equality:** `[a // b] = [c // d]` iff `a + d = b + c`

Isomorphic to Z (or R) via debit-iso `[x//y] -> x-y` or credit-iso `[x//y] -> y-x`.

## Example

A $100 transfer from Alice to Bob produces two T-account entries: Alice gets `[0 // 100]` (credit = decrease), Bob gets `[100 // 0]` (debit = increase). Sum: `[100 // 100] = [0 // 0]` — the zero-sum conservation law.

## In CALC

Proposed as a grading semiring for quantitative modalities: `[]_{[x//y]} A` = "have x of A, owe y of A". Settlement: `[]_{[x//y]} A (x) []_{[y//x]} A^perp |- []_{[0//0]} 1`. See RES_0001 for full treatment.
