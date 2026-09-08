---
title: "Certifying Everything"
part: 5
partTitle: The Frontier
chapter: 21
summary: Three layers of trust — proof terms a tiny kernel can check, forward runs that elaborate into verified proof trees, and STARK circuits that let a third party certify a run without seeing it.
---

Chapter 6 showed that the backward prover finds a proof by search.
This chapter asks a harder question: how do you know it found a **correct** proof?

## The problem with trusting a large engine

The backward prover, the forward engine, the FFI layer — together they amount to thousands of lines of code.
Any of them could have a subtle bug.
If the engine says "provable", you want to be sure it is not lying.

The answer is a **proof term**: a small data structure that records every step of the derivation.
A separate, much smaller checker verifies the term.
The checker contains the real logic; the engine is just a strategy for finding terms.

## Layer 1: Proof terms

Every backward proof in CALC produces a term alongside the derivation.
The term is built from constructors named after the rules.

Here are three constructors and what they mean:

| Constructor | Rule | Meaning |
|---|---|---|
| `id(x)` | identity | resource `x` is used directly |
| `tensor_r(t1, t2)` | `tensor_r` | split context; prove left half with `t1`, right half with `t2` |
| `loli_r(x -> t)` | `loli_r` | introduce hypothesis `x`, prove body with `t` |

A proof of $A \multimap B, A \vdash B$ produces the term `loli_l(z, id(x), y -> id(y))`:
decompose the implication `z`, use `id(x)` to supply the antecedent, name the result `y`, return `id(y)`.

```{prove}
goal: A -o B, A |- B
title: Modus ponens — one step, one term
hint: Apply loli_l on the left hypothesis.
id: ch21-mp
rules: loli_l, id
```

A proof of $A, B \vdash A \otimes B$ produces `tensor_r(id(x), id(y))` — the context splits cleanly:

```{prove}
goal: A, B |- A * B
title: Pairing two resources
hint: Apply tensor_r, then close each half with id.
id: ch21-pair
rules: tensor_r, id
```

The checker in `lib/prover/check-term.js` (~470 lines) walks the term and tracks the linear context.
Each constructor case maps to exactly one inference rule.
Context splitting is **deterministic**: the term dictates which sub-term uses which hypotheses, so the checker does no search.
If the term is well-typed, the derivation is valid.

```{exercise, title=Read the term}
The proof of `A * B |- B * A` produces `tensor_l(z, x y -> tensor_r(id(y), id(x)))`.
Without running any code, read the term aloud: what does each constructor do?
```

```{solution}
`tensor_l(z, x y -> ...)` — decompose hypothesis `z : A * B` into two hypotheses `x : A` and `y : B`.
`tensor_r(id(y), id(x))` — build the pair `B * A` by sending `y` to the left and `x` to the right.
```

```{prove}
goal: A * B |- B * A
title: Commutativity of tensor
hint: Decompose the left side, then re-pack in reverse order.
id: ch21-comm
rules: tensor_l, tensor_r, id
```

**The trust boundary is minimal.**
Everything inside `check-term.js` is trusted.
Everything outside — the prover, the engine, the FFI, the strategy — is untrusted.
If the prover is buggy and produces a wrong term, the checker rejects it.

## Layer 2: Certified forward execution

Forward execution (Part II) fires rules, consuming and producing facts.
Each firing step is called an **@fire step**.
Certification means: re-derive every @fire step from the program's rule descriptors, not from the engine's claim.

Three classes of steps are each checked separately:

**Ordinary rule firings.** The checker (`lib/prover/timed/fire-check.js`) re-runs the pattern match on the consumed facts, using the rule's descriptor, and confirms the produced facts follow.
If the engine altered a fact, the re-match fails.

**Clause-derived persistent goals.** When a persistent goal like `!plus A B C` is proved by backward chaining through clauses, the elaborated trace carries a full SLD certificate — a proof tree for the clause derivation, kernel-checked.
The FFI can accelerate the computation, but the certificate speaks only of the clause.

**Random draws.** Chapter 16 introduced waves — weighted existentials drawn by the collapse driver.
Each draw produces a `@draw` record that the checker (`lib/prover/draw-check.js`) re-derives against the program's declared priors, verifying that the chosen member was admissible.

After certification, the result is a single proof term in which every leaf is verified.
The function `certifyRun` assembles this for an arbitrary settle trace.

## Layer 3: Zero-knowledge proof

The third layer goes further: a **third party** can verify a run **without seeing the program or the prover**.

The insight: instead of running `checkTerm` in JavaScript, compile it into a STARK circuit.
The circuit takes the proof term as input and checks each rule application against the formula ROM (a commitment to the program's connective structure, fixed at verification key time).
If the circuit accepts, the proof is valid — no trust in the engine, the JS runtime, or the prover's author.

CALC uses Plonky3 / OpenVM stark-backend for the STARK proof.
Two paths exist:

**Tree path.** Walks the full proof term.
Each term node becomes one row in the chip trace.
Use this for backward proofs and full derivation certificates.

**Flat path.** Records each forward firing step as `(rule, consumed facts, produced facts)`.
10× fewer rows, 32× smaller witness than the tree path.
Use this for forward execution traces.
The two paths share the same STARK infrastructure and can be combined at the monad boundary.

The circuit itself contains **zero ILL-specific code**.
The same compiled binary verifies proofs from any calculus defined in CALC.
Rule specifications, connective tags, and formula ROMs are derived from `.calc` and `.rules` files at witness generation time.

```{quiz, id=ch21-q1}
Q: Why does the STARK circuit contain no ILL-specific code?
- [ ] The circuit is hand-written for each calculus.
- [x] Rule specs and connective tags are derived from `.calc`/`.rules` descriptors at witness generation time.
- [ ] The circuit only checks format, not logical correctness.
- [ ] ZK proofs do not need to know the logic's rules.
explanation: The architecture is calculus-agnostic. The same compiled Rust binary can certify proofs in ILL, till, gill, will, or sill, because the rule structure is passed as data from the declarative calculus files.
```

## A case study: the witness capture bug

Certification layers exist because bugs hide in complexity.
Here is a real example.

In a 2026 refactor of the EVM symbolic executor, the engine's query function was updated.
The change looked harmless: when the engine asked "what is `unknown + 3`?", it pattern-matched against the store of already-computed facts.
The stored fact happened to share a hash with the output variable.
The engine silently returned the stored value and did not create a fresh eigenvariable for the unknown output.

The result: **31 symbolic execution paths collapsed to 2**.
The remaining paths were simply the ones whose output happened to be identical to the stored fact.
No error was thrown.
The tests still passed, because the test suite checked only whether paths were found, not how many.

The bug was discovered only by benchmark archaeology: a developer noticed that a benchmark that previously reported 31 paths was now reporting 2, and started diffing commits.

The fix was straightforward: every fresh output in a symbolic rule application **immediately gets a new eigenvariable**, never reuses a stored atom.
An unknown is unknown until the proof term binds it.

The moral has two parts.

First, **observation must not change semantics**.
Querying "what fact is stored here?" is an observation.
It changed the semantics of the symbolic execution tree.
Fresh eigenvariables are opaque — they can be observed but not confused with stored values.

Second, **certified paths make such bugs impossible to miss**.
If the proof term had been checked by the kernel, the term would have carried a `loli_l` node that bound an eigenvariable to the output.
Re-running the check with a different stored-fact value would have produced a **different term** — not the same stale one.
The kernel would have caught the discrepancy immediately, because two derivations cannot share a term node whose variable binding differs.

```{quiz, id=ch21-q2}
Q: What made the witness capture bug hard to detect?
- [ ] The kernel rejected the term but the error was suppressed.
- [x] No error was thrown; paths were silently dropped, and tests only checked existence not count.
- [ ] The STARK verifier flagged it but the report was ignored.
- [ ] The bug only affected the ZK path, which was not in the test suite.
explanation: The engine returned a cached result without error. Tests confirmed at least one path existed. The count regression was invisible until a developer noticed a benchmark anomaly.

Q: How does a fresh eigenvariable prevent the bug?
- [ ] It makes all queries slower, so mismatches become visible.
- [ ] It disables the FFI, forcing clause resolution.
- [x] It is opaque — it cannot match a stored ground value, so the pattern match correctly fails until a binding is established.
- [ ] It encrypts the variable so it cannot be read by the store.
explanation: An eigenvariable is a placeholder that has no ground value yet. The pattern-matching step can unify it with a value, but it cannot be confused with an existing atom in the store. This is the fundamental distinction between a variable and a constant.
```

## What you learned

- Every backward proof produces a **proof term** — a structured record of every rule application.
  A small trusted kernel verifies the term independently of the prover.
- Forward execution elaborates into **kernel-checked proof trees**.
  @fire steps are re-derived from rule descriptors; clause goals carry SLD certificates; random draws are certified against declared priors.
- **STARK circuits** compiled from the same `.calc`/`.rules` descriptors let a third party verify any run without trusting the engine, the runtime, or the prover's author.
- Certification catches bugs that tests miss — including the witness capture regression, where symbolic paths silently collapsed because a cached value was mistaken for a fresh unknown.

## Going deeper

- [[documentation/proof-terms]] — full term language, typing rules, and the two-layer architecture (generic terms from descriptors + optional interpretation maps).
- [[documentation/zk-proof-certification]] — bus architecture, chip inventory, flat vs. tree paths, performance numbers, and the soundness model.
- [[documentation/architecture]] — the full prover lasagne (L1-L5) and where the kernel sits in the stack.
