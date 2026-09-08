---
title: "A Calculus Is Data"
part: 5
partTitle: The Frontier
chapter: 19
summary: How the CALC engine stays generic — a logic is a declaration package of connectives, rules, zones, and grade algebras, not hard-coded engine logic.
---

Chapter 6 showed how the backward prover uses polarity to separate invertible from
non-invertible rules — but notice that the prover itself contains no mention of
`tensor` or `loli`. Those names live in a **declaration package** that the engine
reads at startup. This chapter explains what is in that package and how the entire
family of logics (ILL, till, gill, will, sill) is built by writing files, not patching
the engine.

## A logic as a file

Every calculus in CALC lives in a directory such as `calculus/ill/` or
`calculus/till/`. The heart of each directory is a `.calc` file — a plain-text
declaration of connectives — and a `.rules` file of inference rules. The generic
engine reads them at load time. Nothing in `lib/` names a specific connective.

A declaration package has five ingredients:

| Ingredient | Where | Controls |
|---|---|---|
| Connectives | `.calc` | names, arities, ASCII/LaTeX syntax, precedence, polarity, category |
| Inference rules | `.rules` | sequent-notation clauses, `@invertible`, `@pretty` labels |
| Zone structure | `.calc` | `@position_modes` on the sequent constructor + `@structural` rules |
| Grade sorts | `.calc` | subsort edges such as `delay <: grade` |
| Family / inheritance | `@family` / `@extends` | which structural bundle to inherit |

The engine's four faces — backward prover, forward executor, exhaustive explorer,
timed scheduler — read this package at load time and derive their entire behavior
from it.

## Connective declarations

Here is the declaration of `tensor` from `calculus/ill/ill.calc`:

```
tensor: formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\otimes #2"
  @prec 60 left
  @category multiplicative
  @polarity positive.
```

`tensor` takes two formulas and returns a formula. `@ascii` supplies the infix
surface syntax (`A * B`). `@prec 60 left` controls operator precedence. `@polarity
positive` tells the prover that `tensor` inverts on the left (`tensor_l`) and is a
focus choice on the right (`tensor_r`). The prover reads this annotation — it never
hard-codes which connectives are positive.

Here is the companion declaration for `loli`:

```
loli: formula -> formula -> formula
  @ascii "_ -o _"
  @latex "#1 \\multimap #2"
  @prec 50 right
  @category multiplicative
  @polarity negative.
```

One word changes — `positive` to `negative` — and the entire focusing strategy
adapts. Negative connectives invert on the right and are focus choices on the left.

## Inference rules

Connective declarations say what formulas look like. Inference rules say how to prove
them. They live in `.rules` files in sequent notation:

```
tensor_r: G ; D, D' |- A * B
  <- G ; D |- A
  <- G ; D' |- B
  @pretty "⊗R".

loli_r: G ; D |- A -o B
  <- G ; D, A |- B
  @pretty "⊸R".
```

`tensor_r` splits the linear context `D, D'` between two premises — the engine
reads this and knows to enumerate context splits when it tries `tensor_r`. `loli_r`
has one premise and no context split; combined with its `@polarity negative`
declaration, the engine applies it eagerly in the inversion phase. The engine
contains no rule-specific code; it compiles these clauses from the file.

## Zone structure

A **zone** is a region of the sequent with its own structural policy. ILL's two zones
are declared in the `lnl` family file:

```
seq: structure -> structure -> structure -> sequent
  @position_modes "cartesian linear linear"
  @role sequent.
```

Three positions: a cartesian context (position 1, where hypotheses can be copied and
discarded), a linear context (position 2, where each hypothesis is used exactly once),
and the succedent (position 3). The `@structural` rules attached to each position
(`cart_contraction`, `cart_weakening`, `lin_exchange`, …) fill in the policy details.

Adding a zone means writing a new `@position_modes` annotation — no engine code
changes.

## The family DAG

Each calculus declares a **family** and optionally **extends** a parent:

```{mermaid}
graph TD
  lnl["lnl family\n(cartesian + linear zones\nexchange / contraction / weakening)"]
  ill["ill\nILL connectives + rules\ntensor · loli · with · oplus · bang · monad"]
  till["till\n+ grade sorts (delay / count / weight)\n+ timed surface: stamps, windows, woplus"]
  gill["gill\n+ dist grade sort\n+ haul comonad !!_d A"]
  will["will   (@extends gill)\n+ superpose ∃ρ binder\n+ drawn tokens"]
  sill["sill   (@extends gill)\n+ place sort\n+ loc @@ modality\n+ three-zone sequent"]

  lnl --> ill
  ill --> till
  till --> gill
  gill --> will
  gill --> sill
```

Each arrow means: the child's package includes the parent's connectives and structural
rules, plus its own additions. `@extends` is resolved at load time by the meta-parser,
which merges parent and child tables. The engine receives one assembled package.

## A tour of the family

### till: three grade sorts

`calculus/till/till.calc` adds grade sorts to the single `grade` surface type:

```
delay  <: grade.
count  <: grade.
weight <: grade.
```

Three lines in a data file are *all* that separates a duration from a count in the
type checker. The monad's grade position is restricted to `delay`, the bang's to
`count`, and `woplus`'s probability argument to `weight`. No engine code knows these
names — it reads the sort-edge table and enforces the restrictions at load time.

### gill: a new grade and a comonad

`calculus/gill/gill.calc` adds `dist <: grade.` (transport cost) and the `haul`
comonad:

```
dist <: grade.

haul: dist -> formula -> formula
  @ascii "!!_#1 #2"
  @prec 80
  @category comonad
  @polarity positive.
```

A new connective with its own category (`comonad`) and its own grade sort. The
scheduler routes `dist`-graded runs to a (min, +) tropical algebra — also declared
as data in gill's config file, not hard-wired in the engine.

### will: inheriting a surface

`calculus/will/will.calc` opens with two lines:

```
@family will.
@extends gill.
```

That is the entire surface inheritance. Every connective in gill (and transitively till
and the lnl family) is available in will programs without copying. will then adds only
what is will-specific — the $\exists_\rho$ wave binder and its draw tokens:

```
superpose: sort -> formula -> formula
  @ascii "superpose #1 #2".

drawn: member -> sort -> formula
  @ascii "drawn #1 #2".
```

Two new constructors, one `@extends` line. The engine's four faces handle will
programs without modification.

### sill: a third zone

`calculus/sill/sill.calc` also opens with `@extends gill`, then declares the located
modality and a four-position sequent:

```
loc: formula -> place -> formula
  @ascii "#1 @@ #2"
  @prec 85 left
  @category located.

seq: structure -> structure -> structure -> structure -> sequent
  @position_modes "cartesian linear located linear"
  @role sequent.
```

The `@position_modes "cartesian linear located linear"` introduces a third consumable
zone — the located zone $\Lambda$ — where facts are linear *per place*
(`food @@ paris` and `food @@ rome` are independent resources). This required no
engine changes: the prover's union-pool was already zone-count-agnostic. The sill
developer wrote a declaration, not a diff to `lib/`.

## Try the formula surface

Every `.calc` declaration produces a parser and renderer. The widget below starts
with an ILL formula; edit it freely. Try `A * B -o B * A`, or `exists X. X & A`,
or `!P -o P * P` to see how the AST builds up from the declarations above.

```{formula}
(A -o B) * !C
```

## Quiz

```{quiz, id=ch19-q1}
Q: Where does the backward prover learn that `tensor` is a positive connective?
- [ ] It is hard-coded in `lib/prover/focused.js`
- [x] It reads the `@polarity positive` annotation in the `.calc` declaration at load time
- [ ] It infers polarity by trying both phases and recording which terminates first
- [ ] The prover does not use polarity — it tries all rules in alphabetical order
explanation: The polarity table is derived from the `.calc` declarations at load time. No connective name appears in the prover's source code. Changing `@polarity positive` to `@polarity negative` in the declaration would reverse the invertibility rules for that connective everywhere.

Q: Adding a spatial zone to a calculus — as sill does — requires:
- [ ] Editing the union-pool data structure in `lib/kernel/sequent.js`
- [ ] Adding a new search phase to `lib/prover/focused.js`
- [x] Declaring a four-position `@position_modes` on the sequent constructor
- [ ] Writing a dedicated engine backend for spatial logic
explanation: Zone structure is calculus data. The `@position_modes` annotation on the sequent constructor is the only change needed. The prover's pool plumbing was designed to be zone-count-agnostic, so a third zone lands as a declaration, not an engine patch.

Q: What does `@extends gill` at the top of `will.calc` accomplish?
- [ ] It copies all of gill's connective declarations into will.calc at build time
- [ ] It imports gill's JavaScript config module at runtime
- [x] The meta-parser merges gill's constructor and sort-edge tables into will's package at load time
- [ ] Nothing — it is documentation only and has no runtime effect
explanation: `@extends` is resolved by the meta-parser (lib/meta-parser/), which chains parent and child declaration tables into one assembled package for the engine. No copying and no code import — pure data merging.

Q: Which file would you edit to change the ASCII surface syntax of `loli` from `-o` to `⊸`?
- [ ] `lib/parser/earley-grammar.js`
- [ ] `calculus/ill/ill.rules`
- [x] `calculus/ill/ill.calc` — the `@ascii "_ -o _"` annotation on the `loli` declaration
- [ ] `lib/prover/focused.js`
explanation: Syntax is a declaration. The `@ascii` annotation on each connective in the `.calc` file is what feeds the grammar generator. Changing it there changes parsing and rendering everywhere; no engine code needs to be touched.
```

## What you learned

- A **calculus** in CALC is a declaration package: `.calc` files for connectives and
  zone structure, `.rules` files for inference rules, and `@family`/`@extends`
  directives for inheritance.
- The **generic engine** has no knowledge of specific connectives. It reads `@polarity`,
  `@category`, `@position_modes`, and rule clauses, then derives backward search,
  forward execution, exhaustive exploration, and timed scheduling.
- **Adding a new logic** means writing declarations. Sill's third zone, gill's `dist`
  sort and `haul` comonad, and will's $\exists_\rho$ surface each required new `.calc`
  entries — not engine patches.
- The **family DAG** (lnl → ill → till → gill → {will, sill}) is a composition chain:
  each node adds what it owns and inherits the rest via `@extends`.

## Going deeper

- [[documentation/architecture]] — the full engine architecture and how the four faces
  (backward prover, forward executor, exhaustive explorer, timed scheduler) share the
  declaration package.
- [[documentation/family-design]] — the family mechanism in detail: what `@family` and
  `@extends` do, and why calculi share engine hooks rather than engine code.
- [[theory/mode-preorders-and-context-structure]] — the formal account of zone policies
  and the contextStructure derivation from `@position_modes` + `@structural` annotations.
- [[theory/routed-zones-product-stamps]] — the routed-column equivalence theorem:
  why one union pool with wrapper routing is sound and complete for the declared zone
  discipline (the metatheorem behind sill's "declaration, not patch" claim).
