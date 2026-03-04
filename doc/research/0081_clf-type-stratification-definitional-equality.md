---
title: "CLF Type Stratification, Definitional Equality, and Synchronous/Asynchronous Classification"
created: 2026-03-04
modified: 2026-03-04
summary: "Why CLF splits types into synchronous and asynchronous, what definitional equality means for monadic computations, why this forbids nested monads and lolis-in-monad, why CALC can violate these restrictions, and how bang/lax/whynot relate via adjoint shifts."
tags: [clf, type-stratification, definitional-equality, synchronous, asynchronous, focusing, polarity, lax-monad, theory, adjoint-logic, shifts, whynot, exponentials]
category: "Proof Theory"
---

# CLF Type Stratification, Definitional Equality, and Synchronous/Asynchronous Classification

## Status: Stub for Future Deep Research

This document captures initial understanding. A deep study is planned to fully work through the proof theory, understand whether CALC should/could implement definitional equality, and what the sync/async naming convention really means at the proof-theoretic level.

## 1. The Type Stratification

CLF splits types into two layers:

```
Asynchronous:  A ::= P | A -o B | A & B | T | {S}
Synchronous:   S ::= P | S₁ * S₂ | 1 | !A | ∃x.S
```

The monad `{S}` is the **only bridge** from synchronous to asynchronous. `!A` is the **only bridge** back (it embeds an asynchronous type A into the synchronous fragment).

### Why "synchronous" and "asynchronous"?

**Needs deep research.** The naming comes from the connection to focusing (Andreoli 1992) and concurrent process calculi. Initial understanding:

- **Synchronous** types require coordination — they correspond to *positive* connectives in focusing. When you decompose a synchronous type on the right, you must make choices (which disjunct, which witness). The decomposition is a "synchronization point."
- **Asynchronous** types can be decomposed without coordination — they correspond to *negative* connectives in focusing. Their right rules are invertible (no choice, just do it). The decomposition is "asynchronous" in the sense that it doesn't block.

In the concurrent process interpretation (CLF's Curry-Howard): synchronous types correspond to messages that require a receiver to be ready (rendezvous), while asynchronous types correspond to messages that can be sent without waiting.

**Open question:** Is there a deeper connection to the concurrency theory notion of synchronous/asynchronous communication? The CLF papers (Watkins et al. 2002-2004) develop this connection formally.

## 2. Definitional Equality

CLF identifies monadic expressions that differ only in the order of independent steps. For example:

```
{produce(a) * produce(b)}
```

The two expressions "produce a then b" and "produce b then a" are **definitionally equal** in CLF. This is captured by commuting conversions on proof terms.

### What commuting conversions are

If step X and step Y are independent (X doesn't consume what Y produces, and vice versa), then:

```
let {p₁} = X in (let {p₂} = Y in E)
≡
let {p₂} = Y in (let {p₁} = X in E)
```

This equation is part of CLF's type theory — the two proof terms are **the same proof**.

### Why the stratification enables decidable equality

The synchronous/asynchronous split confines commuting conversions to a well-structured space:

1. Synchronous types inside `{S}` are flat data (atoms, tensors, bangs, existentials). No suspended computations.
2. Asynchronous types outside `{S}` have standard structural rules. No monadic sequencing.
3. The monad boundary is the **only** place where commuting conversions arise.

If you allow nested monads (`{ A * { B } }`), the inner `{B}` creates a sequencing dependency inside what should be flat data. Commuting conversions now need to reason about nested computation boundaries — the space of equal terms explodes.

If you allow lolis inside the monad (`{ A * (trigger -o { B }) }`), the dormant loli creates a **future ordering constraint**: when `trigger` appears, the loli fires, producing more state. This makes the commutativity analysis much harder — you can't freely permute steps if one step might activate a dormant loli that changes what other steps can do.

### Why CALC can violate this

CALC doesn't implement definitional equality. It doesn't normalize proof terms or check whether two computations are "the same." CALC is an execution engine — it runs forward rules to quiescence and returns the result. The theoretical problems (undecidable equality, intractable commuting conversions) don't manifest because CALC never asks "are these two executions equal?"

**Open question for future research:** Should CALC ever want definitional equality? Possible motivations:
- Proof-term normalization for certificates
- Optimization: if two execution paths are definitionally equal, only explore one
- Formal verification of forward-chaining programs

## 3. Why CLF Forbids Nested Monads

Three reasons (see §2 for details on each):

1. **Definitional equality breaks** — nested computation boundaries create ordering dependencies that break permutation-based equality
2. **Decidable type checking** — commuting conversions become intractable with nesting
3. **Clean operational semantics** — forward state should be flat data, not suspended computations

## 4. Why CLF Forbids Lolis in Monads

Same three reasons, applied to linear implications:

1. Dormant lolis create future ordering constraints that break commuting conversions
2. Conditional continuations make the space of equal proof terms much larger
3. Forward engine needs extra machinery (matchLoli, drain) to handle deferred rules in state

## 5. Why CALC Violates Both Restrictions

CALC extends CLF with loli-in-monad (THY_0001) because:
- CALC doesn't implement proof-term equality or type checking
- The extra machinery (matchLoli, drainPersistentLolis) is well-understood and tested
- Conditional continuations (guarded branches) are essential for EVM symbolic execution
- The pragmatic trade (lose equational theory, gain expressiveness) is worth it for an execution engine

## 6. Shifts Subsume Bang, Lax, and Whynot

In adjoint logic (Pruiksma et al. 2018), `↑` (up-shift, negative) and `↓` (down-shift, positive) between modes are the only primitives. All exponentials and the lax monad are composed shifts:

```
!A  =  ↓(↑A)     down(up(A))     unrestricted → linear → unrestricted
{A} =  ↑(↓A)     up(down(A))     linear → unrestricted → linear
?A  =  ↑(↓A)     up(down(A))     linear → unrestricted → linear  (classical only)
```

### Can CALC replace bang and lax with raw shifts?

In principle yes. In practice, CALC should keep them as primitives for three reasons:

1. **Performance.** `!A` is one Store node. `↓(↑A)` is three nodes with two rule firings instead of one. Every persistent fact uses bang — this is the hot path.
2. **Compilation.** `compile.js` recognizes `!` directly to classify persistent vs linear dependencies. Recognizing the composed pattern `↓(↑(...))` is fragile.
3. **Familiarity.** `!A` is standard notation.

The right design: keep `!` and `{_}` as primitive connectives that the mode theory *validates* as consistent with the shift decomposition. The mode theory knows `!` behaves like `↓∘↑` and `{_}` behaves like `↑∘↓`, deriving their polarity and focusing behavior. At runtime, single-node, single-rule primitives.

### Lax `{A}` vs Whynot `?A`

Structurally analogous but in different worlds:

| | Whynot `?A` (classical LL) | Lax `{A}` (intuitionistic) |
|---|---|---|
| Dual of | `!A` (bang) | Nothing — no dual (intuitionistic) |
| Structural rules | Weakening + contraction on `?A` | None on `{A}` itself |
| Shift decomposition | `↑(↓A)` | `↑(↓A)` |
| Polarity | Negative (async) | Negative (async) |
| Operational meaning | "A available with weakening/contraction" | "A is result of effectful computation" |

The shift decomposition is identical: both are `↑(↓A)`. The difference is what the *modes* mean:

- **Classical LL:** two modes are "linear" and "unrestricted." `?A = ↑(↓A)` takes A from linear to unrestricted and back, granting structural rules. `?` is the de Morgan dual of `!`: `?A = (!A⊥)⊥`.
- **Intuitionistic LL (CALC):** no negation/duality. `{A}` is the lax modality — it marks "A was produced by forward computation." The shift goes from backward (goal-directed) to forward (data-driven) mode and back. Not about structural rules, but *mode of reasoning*.

In a system with enough modes (full adjoint logic / MTDC), both could coexist:

```
modes: linear, unrestricted, backward, forward

!A  = ↓_ul(↑_lu(A))    -- unrestricted/linear shifts (structural rules)
?A  = ↑_lu(↓_ul(A))    -- dual of ! (classical only)
{A} = ↑_bf(↓_fb(A))    -- backward/forward shifts (mode of reasoning)
```

For CALC: no `?` (intuitionistic, no duality). `!` and `{_}` operate on *different mode axes* — they're independent features, not duals. The adjoint framework unifies them structurally while keeping their operational meanings distinct.

## References

- Watkins, Cervesato, Pfenning, Walker. [CLF: A Concurrent Logical Framework](https://www.cs.cmu.edu/~fp/papers/clf04.pdf). (2004).
- Watkins et al. [A Concurrent Logical Framework: The Propositional Fragment](https://www.cs.cmu.edu/~fp/papers/types03.pdf). TYPES 2003.
- Andreoli. [Logic Programming with Focusing Proofs in Linear Logic](https://doi.org/10.1006/jlpe.1992.1013). JLP 1992.
- Pruiksma, Chargin, Pfenning, Reed. [Adjoint Logic with a 2-Category of Modes](https://www.cs.cmu.edu/~fp/papers/lics18.pdf). LICS 2018.
- RES_0052 — CLF Lax Monad deep study (§6-8 on adjunction, CALC extensions)
- RES_0074 — QTT, Graded Types, Adjoint Logic, MTDC
- THY_0001 — Exhaustive Forward Chaining (CALC's three CLF extensions)

## Open Questions for Deep Study

- [ ] Work through CLF's commuting conversions formally (Watkins et al. 2004 §4)
- [ ] Understand the process calculus interpretation of sync/async (CLF §5)
- [ ] Evaluate whether CALC should implement definitional equality (what would it buy us?)
- [ ] Analyze whether CALC's loli-in-monad extension could be given a clean equational theory (even if different from CLF's)
- [ ] Connection to session types: sync/async in CLF vs sync/async in session type theory
- [ ] Work through the shift decomposition of ! and {_} formally (Pruiksma et al. 2018 §3)
- [ ] Could CALC validate that ! and {_} are consistent with their shift decompositions at load time?
- [ ] If CALC adds classical LL features, how would ? relate to the existing {_}? Same shift, different mode pair?
