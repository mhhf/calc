---
title: "CLF Theory Questions: Loli, Monad, Layer Separation"
created: 2026-02-18
modified: 2026-02-18
summary: "Answer foundational questions about CLF monadic decomposition, loli firing, and engine layer separation"
tags: [research, CLF, loli, monad, theory]
type: research
status: planning
priority: 7
depends_on: []
required_by: [TODO_0001]
---

# CLF Theory Questions

Extracted from TODO_0001.Stage_3. Pure research — independent of the bug fix.

## Q1: Why does CLF exclude lolis from the monad?

CLF restricts `{C}` to atoms, tensor, bang, one, existentials — NO lolis inside monads. Possible reasons:
- Lolis inside monads create "dormant rules" needing a firing mechanism?
- Monadic let already gives sequencing — nested lolis redundant?
- Metatheoretic properties (subject reduction, progress) break?
- Keeping monad's operational semantics simple (committed choice)?

Read CLF paper sections 3-4.

## Q2: Why `!P -o {Q}` and not `!P -o Q`?

- `!P -o {Q}`: "if P, then run computation producing Q" (monadic sequencing)
- `!P -o Q`: "if P, then Q holds" (pure implication)
- Is the monadic wrapper needed for forward chaining, or an artifact of parser treating `-o {...}` specially?

## Q3: What IS `_tryFireLoli` theoretically?

Should loli continuations compile into rules (fire via `tryMatch`) or remain a separate mechanism? How does this relate to CLF operational semantics?

## Q4: Layer separation

The forward engine conflates:
- L1: Multiset rewriting (pure theory)
- L2: Monadic decomposition (expandItem)
- L3: Continuation management (_tryFireLoli)
- L4: Search strategy (symexec)
- L5: Optimizations (strategy stack, mutation+undo, FFI bypass, compiled sub)

Which are theory? Which are optimizations? Can we selectively enable/disable?

## Q5: Is `expandItem` theoretically clean?

Derive from CLF monadic decomposition. What about nested structures like `!(A tensor B)`?

See: `doc/research/clf-celf-ceptre.md`
