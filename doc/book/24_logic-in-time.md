---
title: "Logic in Time: the Next Modality"
part: 6
partTitle: Induction and Coinduction
chapter: 24
summary: The ○ ("next") modality says a resource arrives one tick from now. Combined with the fixed points of the previous two chapters, it turns proofs into reactive programs — a signal is a ν-fixpoint that renews every tick, a stream a μ-fixpoint that fires eventually.
---

Chapter 22 gave us data that is built up step by step (`μ`), and Chapter 23
gave us data that goes on forever (`ν`). Both live *outside* time — a `List`
is finished, a `Stream` is complete-but-infinite. This chapter adds **time**
itself: a way to say "this resource is not here now, but it will be at the
next tick."

That one idea, written `○A`, is enough to describe thermostats, buttons,
clocks, and streams of events — reactive programs — as linear proofs. The
calculus is called **rill** (reactive ILL). It is `fill` plus a single new
connective.

## A value that has not arrived yet

Think of a thermostat. The current temperature is available **now**. The
*next* reading is not — it arrives one tick later. A button press is similar:
the event is not here at this instant; it will (or will not) arrive at some
future tick.

Plain linear logic cannot separate "now" from "later." A resource `a` is
simply available, full stop. We need a way to stamp a resource with *when* it
is usable. That stamp is the **next modality**:

$$\bigcirc A \quad\text{—}\quad \text{“}A\text{ is available at the \emph{next} tick, not now.”}$$

In source you write it with a capital `O`:

```
O a          % a, one tick from now
O (a -o b)   % a function that arrives next tick
O (O a)      % a, two ticks from now
```

`○` is unary, positive, and — this is the whole point — it does **not**
collapse. `○a` is a genuinely different resource from `a`.

## The tick: advancing the whole world by one step

How do you ever use an `○a`? You cannot pull `a` out of it while standing in
the present. Instead, you advance the *entire sequent* forward one step. That
is the single rule of rill, called the **tick**:

$$
\frac{\Gamma \;;\; \Delta \;\vdash\; C}
     {\Gamma \;;\; \bigcirc\!\Delta \;\vdash\; \bigcirc C}
     \;\;\bigcirc
$$

Read the rule bottom-up, the way proof search does. To prove `○C`:

1. every linear hypothesis must already be `○`-wrapped (the context is
   `○Δ = ○X₁, ○X₂, …`);
2. strip one `○` off the goal **and** off every hypothesis at once;
3. the persistent zone `Γ` (the `!`-resources) passes straight through — a
   reusable resource is available at every tick.

The tick fires only when the goal is `○`-headed *and* the whole linear context
is `○`-wrapped. If even one linear resource is bare, the rule is stuck.

That single condition is what makes `○` a real modality:

- **`○a ⊬ a`** — you cannot use a next-tick resource now. The goal `a` is not
  `○`-headed, so the tick cannot fire, and nothing else strips the `○`.
- **`a ⊬ ○a`** — you cannot postpone a here-and-now resource. The hypothesis
  `a` is not `○`-wrapped, so the tick is stuck.

Neither direction holds. Time only moves when *everything* moves together.

```{quiz, id=ch24-q1}
Q: The tick rule requires that, to prove `○C`, every **linear** hypothesis is already `○`-wrapped. What happens to a **persistent** hypothesis `!a` under a tick?
- [x] It passes through unchanged — a reusable resource is available at every tick.
- [ ] It must also be written `○(!a)`, or the tick is stuck.
- [ ] It is consumed, exactly like a linear resource.
- [ ] It blocks the tick entirely.
explanation: The persistent zone Γ is copied into the premise untouched. A `!`-resource is reusable forever, so it is available now and at every future tick — no `○` needed.
```

## The tick is also elimination: temporal cut

The empty-context case of the tick, `Γ ; · ⊢ ○A` reducing to `Γ ; · ⊢ A`, is an
**introduction** — it is exactly the shape of promotion (`!R`): only persistent
resources are around, so the goal can be pushed to the next tick freely.

But when the linear context is non-empty, the very same rule is an
**elimination**. Advancing `○(a ⊸ b), ○a ⊢ ○b` one tick lands you at

$$a \multimap b,\; a \;\vdash\; b,$$

which is ordinary modus ponens — a sequent you have been proving since
Chapter 3. So the temporal goal *reduces to a goal you already know how to
prove*. This is the applicative pattern `○(a⊸b), ○a ⊢ ○b`: a function that
arrives next tick, applied to an argument that arrives next tick, gives a
result next tick.

The tick you are about to reduce lands on plain ILL. Prove that landing
sequent live:

```{prove}
goal: a -o b, a |- b
title: The landing sequent of the applicative tick
hint: Decompose the implication on the left with loli_l, then close both leaves with id.
id: ch24-modus-ponens
rules: id, loli_l
```

The same trick works for combining signals. `○a, ○b ⊢ ○(a ⊗ b)` — two
next-tick resources bundle into a next-tick pair — ticks down to `a, b ⊢ a ⊗ b`,
plain tensor introduction:

```{prove}
goal: a, b |- a * b
title: The landing sequent of the monoidal tick
hint: One application of tensor_r, splitting a to the left premise and b to the right.
id: ch24-tensor
rules: id, tensor_r
```

This is the sense in which `○` is **lax monoidal**: it distributes over the
whole context. In fact it is *strong* monoidal — `○(a ⊗ b) ⊣⊢ ○a ⊗ ○b`, in both
directions — because the tick preserves the resource multiset exactly. Nothing
is duplicated (`○a ⊬ ○a ⊗ ○a`), nothing is created (`⊬ ○a ⊗ ○b`), nothing is
discarded (`○(a ⊗ b) ⊬ ○a`, because the leftover `○b` fails the emptiness check
at the root). Linear accounting survives time travel.

## Signals: values that renew every tick

Now combine `○` with the fixed points from the last two chapters. A **signal**
is a value that is available *now, and again next tick, forever*. "Forever" is
coinduction, so a signal is a **greatest** fixed point:

$$\Box A \;:=\; \nu X.\,(A \mathbin{\&} \bigcirc X).$$

Unfold it once: `A & ○X` says "you may take `A` now, **and** the same signal is
waiting at the next tick." Because it is a `ν`, you may keep unfolding without
end.

Here is the key fact, and it is subtle. A signal can only be *sustained* by a
persistent resource:

$$!a \;\vdash\; \nu X.\,(a \mathbin{\&} \bigcirc X).$$

This proves — coinductively, with exactly one back-edge — because `!a` sits in
the persistent zone. Each unfold takes an `a` by dereliction, and the `!a`
survives to feed the next tick. The tick advances the goal while `!a` passes
through unchanged, the sequent recurs, and the cycle closes. The linear pool is
empty at the bud, so the guard condition of Chapter 23 is satisfied. A signal
backed by a one-shot linear `a` would *not* prove — you cannot promise a value
forever out of a resource you may spend only once.

```{quiz, id=ch24-q2}
Q: Why is a signal `νX.(a & ○X)` provable from a persistent `!a` but not from a linear `a`?
- [x] The cycle needs an empty linear pool at the back-edge; only a persistent `!a`, which lives in the cartesian zone and survives every tick, can feed each unfold while leaving the linear pool empty.
- [ ] Linear resources are simply faster, so the prover gives up on them.
- [ ] `ν` only accepts persistent hypotheses by definition of the rule.
- [ ] A linear `a` would make the proof finite, which `ν` forbids.
explanation: This is the coinductive-weakening guard from Chapter 23. A linear `a` conserved but never consumed around an infinite cycle would be silently discarded — unsound — so the guard demands the linear pool be empty at the bud. A persistent `!a` supplies the value every tick from the cartesian zone, leaving the linear pool empty. Forever-availability must be backed by a reusable resource.
```

## Streams: values that arrive eventually

Dualize. A **stream** (or event) fires *now, or at some later tick*. "At some
finite point" is induction, so a stream is a **least** fixed point:

$$\Diamond A \;:=\; \mu X.\,(A \oplus \bigcirc X).$$

Unfold it: `A ⊕ ○X` says "either `A` fires now (left), **or** check again next
tick (right)." Because it is a `μ`, every proof must reach the `A`-now case
after finitely many ticks — the value really does arrive.

A resource available now injects as an event immediately:

$$a \;\vdash\; \mu X.\,(a \oplus \bigcirc X)$$

by one `μ`-unfold and the left injection `⊕R₁`. No cycle is needed — this proof
is purely inductive and finite. Signals coinduct (`ν`, back-edge); streams
induct (`μ`, terminating). Same `○`, opposite fixed points.

```{exercise, title=Signal versus stream}
Without looking below, decide which fixed point — `μ` or `ν` — belongs to each
description, and why:

1. "A heartbeat that beats at every tick, forever."
2. "A doorbell that will ring at some tick, then it's done."
3. "A temperature sensor you can read at any tick from now on."
```

```{solution}
1. **`ν` (signal).** Availability at *every* tick, forever, is a greatest
   fixed point: `νX.(beat & ○X)`.
2. **`μ` (stream/event).** "At some tick, then done" is a finite,
   eventually-reached property — a least fixed point: `μX.(ring ⊕ ○X)`.
3. **`ν` (signal).** "Readable at any tick from now on" is again
   forever-availability: `νX.(temp & ○X)`, and it must be backed by a
   persistent source.
```

## Why time needed no new engine

Here is the quiet punchline. Adding `○` did **not** touch the proof engine.
`○` is declared with a *fresh* category (`modality`), which the role system
does not recognize as a fixed point or an exponential — so the cyclic-proof
machinery of Chapter 23 never even sees it. A signal `νX.(a & ○X)` coinducts
through the **existing** guard checker: the `νR` unfold supplies the *progress*
the guard demands, and `○` acts as the *syntactic guard* that separates one
turn of the cycle from the next. The tick itself is a whole-sequent transform,
re-derived from scratch by the trusted kernel (never merely trusted from the
search), with exact-equality checks that reject any forged advance.

New connective, new calculus, zero new trusted code. That modularity is the
theme of the next chapter, where grades, fixed points, and time all stack up
together.

## What you learned

- **`○A`** ("next") says `A` arrives one tick from now. It is a genuine
  modality: `○a ⊬ a` and `a ⊬ ○a`.
- The **tick** rule advances the whole sequent one step: to prove `○C`, every
  linear hypothesis must be `○`-wrapped; the tick strips one `○` from the goal
  and each hypothesis, and passes the persistent zone through unchanged.
- The empty-context tick is an **introduction** (promotion-shaped); the
  non-empty tick is **elimination / temporal cut**, reducing a temporal goal to
  an ordinary ILL goal — e.g. `○(a⊸b), ○a ⊢ ○b` becomes `a⊸b, a ⊢ b`.
- `○` is **strong monoidal**: `○(a ⊗ b) ⊣⊢ ○a ⊗ ○b`. No duplication, creation,
  or discard survives — linear accounting is preserved across time.
- A **signal** `□A = νX.(A & ○X)` is a coinductive, forever-renewing value; it
  is provable only when backed by a persistent resource (`!a ⊢ νX.(a & ○X)`).
- A **stream/event** `◇A = μX.(A ⊕ ○X)` is an inductive value that fires after
  finitely many ticks (`a ⊢ μX.(a ⊕ ○X)`).
- Adding time required **no** new engine or trusted code: `○` rides the
  existing fixed-point machinery, with the kernel re-deriving every tick.

## Going deeper

- [[theory/0043_next-modality-guarded-signals|THY_0043: the next modality and guarded signals]] — the full theory of the whole-context tick, the non-collapse proofs, and how signals coinduct through the unchanged trace condition.
- [[theory/0042_cyclic-proofs-fixed-points|THY_0042: fixed points and cyclic proofs]] — the guard condition (GTC) and the empty-linear-pool requirement that Chapter 23 introduced and this chapter relied on for signals.
- [[documentation/architecture|the prover architecture]] — where the tick lives: bypassed in the focused search (`focused.js`) and fully re-derived in the kernel (`kernel.js`).
