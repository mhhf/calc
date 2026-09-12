---
title: "A Different Sequent: Semi-Axiomatic Message Passing"
part: 7
partTitle: A Second Family
chapter: 26
summary: Chapter 19 showed connectives and rules are data. This chapter goes one level deeper: even the shape of the sequent is data. A second structural family, sax, turns non-invertible rules into axioms and makes cut the engine of computation — modelling message-passing processes.
---

Chapter 19 made a bold claim: a logic is *data*. Its connectives, its rules,
its zones — all declared in files, loaded by a generic engine that knows no
specific logic. Every calculus since — till, gill, will, sill, and the whole
fixed-point family of Part VI — was built by writing declarations, not engine
code.

But all of them shared one thing that looked hard-wired: the **shape of the
sequent** itself. `Γ ; Δ ⊢ C` — a persistent zone, a linear zone, a conclusion.
Is *that* data too, or is it the one thing baked into the machine?

This chapter answers by building a calculus with a *different* sequent shape,
under a *different* structural discipline, and showing it runs on the very same
engine. That calculus is **sax**, and it comes from a beautiful idea:
computation is the elimination of cut.

## What a family is

The pieces below the connectives — how many zones a sequent has, which
structural rules (exchange, contraction, weakening) govern each, and how the
engine threads resources through them — are packaged into a **family**. Every
calculus in the book so far belongs to one family, called `lnl`:

$$\Gamma \;;\; \Delta \;\vdash\; C \qquad\text{(the \texttt{lnl} family: two zones)}$$

`Γ` is the cartesian zone — reusable resources, with contraction and weakening.
`Δ` is the linear zone — one-shot resources, with neither. That two-zone shape is
what made `!` and the linear/persistent distinction work.

`sax` is a **second** family. Its sequent has just **one** zone:

$$\Delta \;\vdash\; C \qquad\text{(the \texttt{sax} family: one linear zone)}$$

No cartesian zone at all — only exchange, no contraction, no weakening. This is
the first structural shape in the system with no reusable zone, and getting it
to run forced every hidden assumption about "there is always a persistent zone"
out into the open. The engine, once corrected, does not care: it reads the zone
structure from the family declaration and threads resources accordingly. Two
families, two shapes, one engine.

```{quiz, id=ch26-q1}
Q: What distinguishes the `sax` family's sequent from the `lnl` family's?
- [x] `sax` has a single linear zone (`Δ ⊢ C`) with no cartesian zone — so no contraction and no weakening — while `lnl` has two zones (`Γ ; Δ ⊢ C`).
- [ ] `sax` has three zones instead of two.
- [ ] `sax` uses the same two zones but swaps their structural rules.
- [ ] `sax` has no linear zone, only a persistent one.
explanation: The family declaration fixes the number of zones and their structural rules. `lnl` is two-zone (cartesian Γ + linear Δ); `sax` is one-zone (linear Δ only), the first shape in the system without a reusable zone. The engine derives its context handling from this declaration — no engine code names either family.
```

## The semi-axiomatic idea

Ordinary sequent calculus (the `lnl` family) has a left rule and a right rule
for every connective, and proof search must carefully manage the non-invertible
ones with focusing. The semi-axiomatic calculus makes a startling move: it turns
every **non-invertible** rule into a **zero-premise axiom**.

Take tensor. In `lnl`, building `A ⊗ B` on the right is a rule with two
premises (prove `A`, prove `B`). In `sax`, it is an axiom — a rule with *no*
premises — that simply consumes `A` and `B` from the context:

$$A,\; B \;\vdash\; A \otimes B \qquad(\otimes\text{X, an axiom})$$

The `A` and `B` here are **companion** formulas: the rule matches only when both
are sitting in the context, and consumes them when it fires. There is nothing
left to prove — the axiom *is* the proof.

The **invertible** rules are untouched. Decomposing a tensor on the left is the
same safe rule as always:

$$\frac{D,\; A,\; B \vdash C}{D,\; A \otimes B \vdash C}\;\otimes\text{L}$$

So the calculus is *semi*-axiomatic: axioms carry the non-invertible half
(constructors, with their companions), ordinary invertible rules carry the rest.

And the piece that ties it together — **cut** — is now an *explicit* rule, not
something quietly admissible in the background:

$$\frac{D \vdash A \qquad D',\, A \vdash C}{D,\, D' \vdash C}\;\text{cut}$$

Search only reaches for cut as a last resort, drawing the cut formula `A` from
the finite set of subformulas of the goal. Some sequents — like the
associativity of tensor — have *no* proof without it, so cut earns its keep.

## Cut is computation

Why turn a logic inside out like this? Because in this form, **cut reduction is
message passing**.

Picture a system of concurrent processes communicating through single-use cells.
A process that *writes* to a cell `D` corresponds to a proof of `D ⊢ A`. A
process that *reads* from `D` corresponds to `D, A ⊢ C`. Putting them together —
one writer meeting one reader — is exactly a cut on `A`. Reducing that cut is the
communication event: the value flows from writer to reader.

The cells obey a **write-once** discipline: a cell is allocated empty (a
`hole`), written exactly once (becoming a persistent `!cell`), and read any
number of times after. Two processes writing *different* cells never conflict —
so independent communications commute, and the whole machine is **confluent**
(the order of independent steps does not change the outcome).

CALC ships this machine as a small program, `machine.sax`, using three fact
kinds:

```
proc D P     % an ephemeral process P writing to destination D   (linear)
hole D       % an allocated but unwritten cell                    (linear)
!cell D V    % a filled cell — write-once, read-many              (persistent)
```

and eight steps that are the propositional core of the classic message-passing
machine. Here are the ones you will watch fire:

```
sax/write_in2: proc D win2 * hole D           -o { !cell D vin2 }.
sax/case_in1:  proc D (pcase S P1 P2) * !cell S vin1 -o { proc D P1 }.
sax/case_in2:  proc D (pcase S P1 P2) * !cell S vin2 -o { proc D P2 }.
```

A `case` process reads a filled sum-cell and continues down the branch matching
the cell's tag. A `write` process consumes its `hole` (enforcing write-once) and
leaves a persistent `!cell` behind.

## Stepping the machine

The widget below runs the **negation** configuration: cell `c` already holds the
tag `vin1`, and a process at `d` cases on it, writing the *opposite* tag. Step
through it. Watch `case_in1` fire first (reading `c`, selecting the `win2`
branch), then `write_in2` fill cell `d` and consume its hole:

```{exec sax}
file: calculus/sax/tests/forward/configs.sax
query: expect_sax_negation
title: Negation — case reads a cell, then writes the opposite tag
```

Two steps, and `d` holds `vin2` — the negation of `c`'s `vin1`. Every step was
a communication: a read of `c`, then a write of `d`. Cut reduction, running.

```{quiz, id=ch26-q2}
Q: In the machine, why can a `!cell` be read by many processes but a `hole` be written by only one?
- [x] `!cell` is persistent (reusable — many reads never consume it); `hole` is linear (a write consumes it exactly once), which is precisely the write-once discipline that makes the machine confluent.
- [ ] `hole` is persistent and `!cell` is linear.
- [ ] Both are linear; the difference is only naming.
- [ ] The engine special-cases cells to allow multiple writes.
explanation: A filled cell is a persistent fact (`!cell`) — reads are non-consuming lookups, so any number of processes may read it. An unwritten cell is a linear fact (`hole`) — the write rule consumes it, so exactly one write can ever succeed. Write-once + read-many is what guarantees independent steps commute (confluence).
```

## The big idea

Here is the payoff, and it closes an arc that opened in Chapter 19.

That chapter showed the **connectives and rules** are data. This one shows the
**structural layer** — the sequent shape, the zone count, the structural rules —
is data too. The generic engine contains no `if (family === "lnl")` and no
`if (family === "sax")`. It reads a family declaration, derives the context
structure, and threads resources accordingly. Point it at the two-zone `lnl`
declaration and it proves ILL; point it at the one-zone `sax` declaration and it
runs message-passing processes. Same engine, both times.

The sharpest evidence is what sax's family declaration leaves *empty*. The
family protocol has four specialized hooks — for persistent-goal proving,
dynamic rules, and existential resolution — that the `lnl` family fills in. In
sax, **all four are null**. Its entire operational behaviour runs on the generic
engine's baseline, with no special machinery at all. That was not planned; it was
*discovered* by building the family and finding the engine already sufficed. The
four hooks turned out to be the `lnl`-shaped part of the protocol, not a
universal requirement.

A logic is data — connectives, rules, zones, and the structural discipline over
them, all the way down.

```{exercise, title=Two more configurations}
The same program file has other configurations you can run by changing the
`query:` line of an exec widget (or reading them in
`calculus/sax/tests/forward/configs.sax`):

- `expect_sax_pipeline` — two case-processes chained; the second **blocks**
  until the first writes its cell.
- `expect_sax_swap` — three processes over a pair's projections that swap the
  pair's two components.

For the **pipeline**, predict: which of the two case-processes fires first, and
why can it not be the other order?
```

```{solution}
The process reading cell `c` fires first. The second process cases on cell `m`,
which does not exist yet — it is written only when the first process fires. Until
then the second is **stuck** (its `pcase m …` has no `!cell m …` to read). This
is write-once synchronization: a reader blocks until its cell is written, so data
dependencies force the order even though the processes were launched
concurrently. Independent processes (as in the swap) commute; dependent ones
serialize automatically. That is confluence and synchronization falling out of
the write-once discipline — no scheduler required.
```

## What you learned

- The structural layer — sequent shape, zone count, structural rules — is
  bundled into a **family**. All prior calculi use the two-zone `lnl` family
  (`Γ ; Δ ⊢ C`); **sax** is a second family with one linear zone (`Δ ⊢ C`), no
  contraction or weakening.
- A **semi-axiomatic** calculus turns every non-invertible rule into a
  **zero-premise axiom** with **companion** formulas consumed on firing (e.g.
  `A, B ⊢ A ⊗ B`); invertible rules are unchanged; **cut is explicit**.
- In this form, **cut reduction is message passing**: a writer `D ⊢ A` meets a
  reader `D, A ⊢ C` at a cut on `A`; reducing it moves the value.
- The machine uses **write-once** cells — `hole` (linear, written once) becomes
  `!cell` (persistent, read many) — which makes independent steps commute:
  **confluence**, and blocking synchronization, for free.
- The deep point: even the structural layer is **data**. One generic engine runs
  both families with no family-specific branches — and sax needs *none* of the
  `lnl` family's four specialized hooks, running entirely on the baseline.

## Going deeper

- [[documentation/sax-family|the sax family]] — the full construction: axioms with companions, the explicit-cut search over the subformula closure, and the four null hooks.
- [[theory/0036_destination-discipline-confluence-certificate|THY_0036: the destination-discipline confluence certificate]] — the write-once discipline as a machine-checkable confluence guarantee.
- [[theory/0037_store-as-snax-concretization|THY_0037: the store as a SNAX concretization]] — how the projection addressing (`p1 D`, `p2 D`) keeps every machine step first-order and binder-free.
- [[def/0014_hidden-cut|the hidden cut]] — cut as a rule, and what it means for it to be admissible versus explicit.
