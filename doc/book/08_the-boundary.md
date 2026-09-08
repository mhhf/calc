---
title: "The Boundary: {A}"
part: 2
partTitle: Logic that Runs
chapter: 8
summary: How the lax monad {A} divides backward proof search from forward execution — and why every forward rule conclusion wears braces.
---

Chapter 6 showed how polarity and focusing give the backward prover a disciplined
search strategy; this chapter introduces the one connective that stops that
search and hands control to a running program.

## Rules that produce effects

Consider a simple vending machine written as ILL rules.
You put in a coin.
You get coffee.

```
grind : coin -o { grounds }
brew  : grounds -o { coffee }
```

The braces around `grounds` and `coffee` are not decoration.
They say: **this is produced by execution, not found by proof search**.

In every forward rule you will ever write, the conclusion wears braces.
That is not a convention — it is enforced by the type of the connective `{ }`.

## The lax monad

`{A}` is called the **lax monad** (written $\{A\}$ in math).
It is a connective with one argument: `{A}` packages formula $A$ as the result
of a computation.

Its polarity is **negative** — even when $A$ itself is positive.
This one fact determines everything about how the prover handles it.

```{formula}
{ coin -o { grounds } }
```

Try editing the formula in the box above to see different shapes parsed.

## The right rule: monad_r

Because `{A}` is negative, its **right rule** (`monad_r`, read ${}_R$) is
**invertible**.
The inversion phase fires it eagerly, without choice.

```{rule monad_r}
```

The rule says: to prove `{ A }` from context $\Delta$, prove $A$ from $\Delta$.
Syntactically simple — but hidden in that step is the **mode switch**.

When the focused prover applies `monad_r`, it does not recurse into another
backward-search subgoal.
Instead it **transfers the entire linear context** $\Delta$ to the forward
execution engine and runs the program to quiescence.
After the forward engine finishes, the prover checks that what remains in the
state matches $A$.

This is the boundary:

```
backward prover          |  forward engine
─────────────────────────┼──────────────────────────
  ...                    │
  monad_r fires          │  state = Δ (all resources)
                ─────────▶  rules fire until quiescent
                         │  check: residual = A
```

The backward prover never looks inside the braces during search.
It sees `monad_r` as a leaf.

## The boundary in action

The program below has two rules.
Start with one `coin`.
Watch what fires at each step.

```{exec ill}
file: doc/book/programs/boundary.ill
query: expect_go
title: Two rules, two steps
maxSteps: 5
```

Step 1 fires `grind`, consuming `coin` and producing `grounds`.
Step 2 fires `brew`, consuming `grounds` and producing `coffee`.
Each rule consumed the previous state and produced a new one — that is the
forward engine doing its job behind the boundary.

The backward prover's only job was to prove the *type* of the overall result
(`{ coffee }`) without knowing which rules would fire or in what order.

## The left rule: monad_l

Now suppose you **have** a monadic value `{ A }` as a hypothesis and you need
to prove another monadic goal `{ C }`.
The rule `monad_l` (${}_L$) extracts the inner formula.

```{rule monad_l}
```

Two things to notice:

1. **Not invertible.** `monad_l` is not in the inversion phase.
   To use it, the focused prover must explicitly choose to focus on the `{ A }`
   hypothesis.

2. **Sticky.** The conclusion requires the succedent to already be monadic
   (`{ C }` on the right).
   You cannot use `monad_l` to "escape" from a computation and land in a
   non-monadic goal.
   Once you enter the monadic world, you stay there.

The stickiness property enforces a clean discipline: the monadic and
non-monadic parts of a sequent never mix.

## Exercises

### Warmup: identity through the monad

The formula `{ P }` is a single connective applied to the atom `P`.
Like any formula, it can appear on both sides of the turnstile.

```{prove}
goal: { P } |- { P }
title: Identity through the monad
hint: The whole formula { P } is identical on both sides — the identity rule applies directly to it as a unit.
id: ch8-monad-id
rules: id, monad_r, monad_l
```

```{exercise, title=What rule fired?}
The proof above closed by `id`.
No `monad_l` was needed, and `monad_r` did not trigger (there is no forward
engine in this interactive prover).
Why is that correct?
```

```{solution}
`{ P }` is a single formula.
Identity (`id`) matches when the same formula appears on both sides — here `{ P }` matches `{ P }` directly.
The monad rules are only needed when you want to *open* or *close* the braces.
```

### Using monad_l: extract and chain

Now use `monad_l` explicitly.
You have `{ P }` as a hypothesis and a rule `P -o { Q }`.
Your goal is `{ Q }`.

```{prove}
goal: { P }, P -o { Q } |- { Q }
title: Extract and apply
hint: Start with monad_l on { P } to extract the inner P. Then focus on P -o { Q } and use loli_l — it needs P (from the left branch) and produces { Q } (matched by id on the right).
id: ch8-monad-l
rules: monad_l, loli_l, id
```

### Chaining two steps

Forward programs often chain rules: the output of one step feeds the next.
Here you have two rules (`P -o { Q }` and `Q -o { R }`) and the initial value
`{ P }`.

```{prove}
goal: { P }, P -o { Q }, Q -o { R } |- { R }
title: Chain two forward steps
hint: Apply monad_l to { P } to extract P. Use loli_l with P -o { Q } (P goes left, the { Q } result goes right). The right branch is { Q }, Q -o { R } |- { R } — apply monad_l again, then loli_l.
id: ch8-monad-chain
rules: monad_l, loli_l, id
```

This mirrors what the forward engine does automatically: it fires each rule
in sequence, passing the state from step to step.
Here you reconstructed that chain by hand using `monad_l` and `loli_l`.

## Three execution profiles

CALC offers three ways to handle the monad boundary, controlled by an
`opts.forward` flag passed to the prover.

**`'full'` (default):** The forward engine runs freely, and the backward
prover sees only an opaque leaf — fast and suitable for production.

**`'guided'`:** The forward engine runs as an oracle and each firing step maps
to a sequence of explicit ILL inference rules; the complete proof term is
verified step by step — about 2–5× slower in the monadic fragment but
produces a fully checked proof.

**`'off'`:** The forward engine is not used at all; the backward prover
searches *inside* the monad directly — theoretically complete but intractable
for any non-trivial program.

## Quiz

```{quiz, id=ch8-q1}
Q: Where does backward proof search stop in ILL?
- [x] At `{ }` — the monad connective triggers `monad_r`, which hands all resources to the forward engine
- [ ] At every negative connective on the right
- [ ] At atoms — the prover stops as soon as it sees a non-compound formula
- [ ] At `!` — the bang connective marks the boundary

explanation: `monad_r` is the mode-switch point. When the focused prover encounters `{ A }` as the succedent, it fires `monad_r` and transfers the entire linear context to the forward execution engine. No other connective triggers this switch.

Q: The rule `monad_r` is invertible. What does that mean for proof search?
- [ ] It can be skipped — it is always optional
- [x] The inversion phase fires it eagerly without backtracking
- [ ] It requires choosing which branch to take
- [ ] It can only fire when the linear context is empty

explanation: Invertible rules are always safe to apply — applying them never destroys provability. The inversion phase (Phase 1 in Andreoli's focusing algorithm) fires all invertible rules eagerly. `monad_r` is invertible because there is only one way to prove `{ A }`: produce `A`.

Q: The rule `monad_l` is called "sticky". What does that mean?
- [ ] It makes the proof tree irreversible
- [ ] It can only fire once per sequent
- [x] The succedent must be monadic — you cannot use `monad_l` to escape into a non-monadic goal
- [ ] It copies the hypothesis rather than consuming it

explanation: `monad_l`'s conclusion requires the succedent to also be wrapped in `{ }`. You can only eliminate a monadic hypothesis when you are already inside a monadic goal. This keeps the boundary clean: once you enter computation mode, you stay there.
```

## What you learned

- `{A}` is the **lax monad**: a negative connective that marks a value produced by computation, not found by proof search.
- **`monad_r`** is the right rule — invertible, fires eagerly, and triggers the **mode switch** that hands all linear resources to the forward execution engine.
- **`monad_l`** is the left rule — not invertible, **sticky** (requires a monadic succedent), and extracts the inner formula from a monadic hypothesis.
- The boundary is the single seam between the two halves of CALC: backward proof search (polarity, focusing, inversion) lives outside the braces; forward execution (rules firing, state changing) lives inside.
- Three execution profiles (`'full'`, `'guided'`, `'off'`) control how the mode switch is handled — from an opaque fast leaf to a fully verified ILL proof term.

## Going deeper

- [[documentation/lax-monad]] — formal treatment of the mode switch, the bridge data flow, rightFocus succedent decomposition, and the three execution profiles.
- [[documentation/backward-prover]] — the full four-layer prover architecture where `monad_r` lives at layer L3 (focused.js).
- [[documentation/forward-chaining-engine]] — the forward engine that runs inside the braces, including the committed-choice loop and the three-layer lego architecture.
- [[def/0044_rule-monad_r]] and [[def/0045_rule-monad_l]] — atomic reference cards for the two monad rules.
