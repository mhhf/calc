---
title: "LF Type Checking — Algorithms, Hereditary Substitution, Practical Implementation"
created: 2026-03-02
modified: 2026-03-02
summary: "How Twelf/Celf check LF signatures: bidirectional typing, canonical forms, hereditary substitution, and what a minimal implementation requires."
tags: [lf, type-checking, dependent-types, logical-framework, hereditary-substitution, bidirectional, type-theory, implementation]
category: "Implementation"
---

# LF Type Checking

## 1. LF Syntax (Canonical Forms)

LF has three syntactic levels: kinds, type families, and terms. In the canonical presentation (Watkins et al., Harper & Pfenning), terms are stratified into **canonical** (beta-normal, eta-long) and **atomic** (neutral/elimination) forms:

```
Kinds          K ::= type | Pi x:A. K
Type families  A ::= a | A M | Pi x:A1. A2
Atomic terms   R ::= c | x | R M
Canonical terms M ::= R | lam x. M
```

- `a` = type family constant (e.g. `bin`, `plus`)
- `c` = object constant (e.g. `e`, `i`, `plus/z1`)
- `x` = variable
- `Pi x:A. B` = dependent function type (non-dependent when `x` not free in `B`, written `A -> B`)

Key property: **canonical forms are closed under typing but NOT under substitution**. Substituting a lambda for a head variable creates a beta-redex. This is why hereditary substitution exists.

## 2. Judgments

LF type checking uses five judgment forms:

```
Sig |- ok           Signature well-formed
Sig; Gamma |- K ok  Kind well-formed
Sig; Gamma |- A : K Type family has kind K
Sig; Gamma |- M <= A Canonical term checks against type A    (CHECK)
Sig; Gamma |- R => A Atomic term synthesizes type A          (SYNTH)
```

The last two are the bidirectional pair.

## 3. Bidirectional Type Checking

The core insight: **introduction forms are checked, elimination forms synthesize**.

### Checking (M <= A)

```
Gamma, x:A |- M <= B
------------------------------ [check-lam]
Gamma |- lam x. M <= Pi x:A. B

Gamma |- R => A'    A = A'
--------------------------- [check-atom]
Gamma |- R <= A
```

Lambda abstractions check against Pi types by extending the context and checking the body. Atomic terms switch to synthesis mode and compare the synthesized type against the expected type.

### Synthesis (R => A)

```
c : A in Sig
-------------- [synth-const]
Gamma |- c => A

x : A in Gamma
---------------- [synth-var]
Gamma |- x => A

Gamma |- R => Pi x:A. B    Gamma |- M <= A
--------------------------------------------- [synth-app]
Gamma |- R M => [M/x]B
```

The application rule is where hereditary substitution appears: `[M/x]B` must produce a canonical type family.

## 4. Hereditary Substitution

Ordinary substitution `[M/x]N` can produce non-canonical terms when `x` is the head of an application `x N1 ... Nk` and `M = lam y. M'`. The result `(lam y. M') N1 ... Nk` contains a redex.

Hereditary substitution continues reducing: it substitutes `N1` for `y` in `M'` (hereditarily), then applies the result to `N2`, etc. The process terminates because each reduction step **consumes one arrow** from the type of the variable being substituted.

### Algorithm (for simple types, sufficient for CALC)

Given `[M/x]_A N` (substitute M for x at type A in N):

```
[M/x]_A (lam y. N)       = lam y. [M/x]_A N          (y fresh)
[M/x]_A (c N1 ... Nk)    = c ([M/x]_A N1) ... ([M/x]_A Nk)
[M/x]_A (y N1 ... Nk)    = y ([M/x]_A N1) ... ([M/x]_A Nk)     (y != x)
[M/x]_A (x N1 ... Nk)    = M @ ([M/x]_A N1) ... ([M/x]_A Nk)   (REDEX case)
```

Where `M @ N1 ... Nk` (hereditary application):

```
(lam y. M') @_{A->B} N    = [N/y]_A M'          (continue hereditarily)
R @_base N                 = R N                  (no redex, already atomic)
```

### Termination

Lexicographic order on `(type_size(A), term_size(N))`. Each hereditary application step reduces `type_size` because `A -> B` shrinks to `A` or `B`. Within the same type, structural recursion on the term decreases.

### For CALC specifically

CALC's type language is first-order: types are base types (`bin`, `nat`, `mem`) and arrow chains (`bin -> bin -> type`). There are no type-level lambdas. This means:
- Hereditary substitution in types is just ordinary substitution (no redexes possible in types)
- Hereditary substitution in terms only matters when substituting a constructor application into a higher-order position, which CALC currently does not have
- **For Stages 1-2 of TODO_0065, hereditary substitution is not needed at all**

## 5. Signature Well-Formedness

A signature is checked declaration by declaration, in order:

```
Sig |- ok    Sig |- A : type
------------------------------ [sig-const]
Sig, c:A |- ok

Sig |- ok    Sig |- K ok
------------------------------ [sig-type-family]
Sig, a:K |- ok
```

For each declaration `c : A`:
1. Check that `A` is a well-formed type (or kind) under the signature so far
2. Add `c : A` to the signature
3. Proceed to next declaration

For type family declarations like `plus : bin -> bin -> bin -> type`:
1. `bin -> bin -> bin -> type` is a kind (returns `type`)
2. Check each argument type is well-formed: `bin` must be a declared type
3. Add `plus` with kind `bin -> bin -> bin -> type`

For constructor declarations like `plus/z1 : plus e e e`:
1. `plus e e e` is a type (returns a type family application)
2. Check `e` has type `bin` (synthesize type of `e`, compare with what `plus` expects)
3. Add `plus/z1 : plus e e e`

For clause declarations like `plus/s1 : plus (o M) (o N) (o R) <- plus M N R`:
1. `<-` is sugar for `Pi` (reverse arrow): `Pi _: plus M N R. plus (o M) (o N) (o R)`
2. `M, N, R` are implicitly universally quantified (Pi-bound)
3. Full type: `Pi M:bin. Pi N:bin. Pi R:bin. plus M N R -> plus (o M) (o N) (o R)`
4. Check each sub-expression at the expected type

## 6. Sort Checking vs Full LF Type Checking

### Sort checking (simple types, Stage 2)

- Erase all indices: `plus : bin -> bin -> bin -> type` becomes `plus : bin * bin * bin`
- Every ground term has a unique sort: `e : bin`, `i X : bin` when `X : bin`
- Check: does each argument have the right sort?
- Metavariables are unconstrained (checked at instantiation)
- **Complexity**: O(n) per term, n = AST size. One pass.
- **No substitution needed**: sorts are flat, no computation in types

### Full LF type checking (Stage 3)

- Preserves indices: `plus/z1 : plus e e e` means exactly `plus` applied to `e, e, e`
- Type equality requires comparing type family applications: `plus (o M) (o N) (o R)` vs expected type
- **Requires hereditary substitution** in application rule (for dependent Pi)
- **Requires normalization** for type equality (reduce both sides, compare structurally)
- **Complexity**: O(n * d) where d = nesting depth of Pi types. Still polynomial for LF (no general recursion in types).

### What CALC needs first

Sort checking catches 95% of bugs (wrong constructor in wrong position) at near-zero cost. Full LF checking catches the remaining 5% (wrong index values) but requires more infrastructure. **Stage 2 first, Stage 3 later.**

## 7. Metavariables in LF Type Checking

Two distinct roles:

### (a) Implicit arguments (Twelf-style)

Twelf auto-quantifies uppercase variables. `plus/s1: plus (o M) (o N) (o R) <- plus M N R` becomes:

```
plus/s1 : {M:bin} {N:bin} {R:bin} plus M N R -> plus (o M) (o N) (o R)
```

At use sites, implicit arguments are filled by higher-order pattern unification. **This is type reconstruction, not type checking.** CALC already has explicit metavar declarations (`@metavar bin M N R`), so implicit quantification is handled at parse time. Type checking just verifies the result.

### (b) Pattern variables during matching

When a forward rule like `plus (o M) (o N) (o R) -o { ... }` matches against a fact `plus (o (i e)) (o e) (o (i e))`, the pattern variables `M, N, R` get instantiated. Type checking here means: **after instantiation, does the fact have the right type?**

For sort checking, this is trivial: if the fact was well-typed when produced, and the pattern is well-typed, then any match preserves types. This is a free theorem from the sort structure.

### (c) Constraint solving (full dependent case)

For full LF type checking with indices, matching generates type equalities like `plus M N R = plus (i e) e (i e)`. These are solved by unification. In the pattern fragment (all metavar arguments are distinct bound variables), unification is decidable with most general unifiers. Outside the pattern fragment, it is undecidable in general but Twelf uses a constraint-postponement strategy.

**CALC's pattern variables always fall in the pattern fragment** (they appear applied to zero arguments), so unification is trivial first-order unification.

## 8. Practical Complexity

| Aspect | Sort Checking | Full LF |
|--------|--------------|---------|
| Time per term | O(n) | O(n * d) |
| Substitution | none | hereditary |
| Normalization | none | WHNF for type equality |
| Metavar handling | unconstrained | first-order unification |
| Implementation LOC | ~100-200 | ~400-600 |
| Catches | arity + sort errors | + index errors |
| When to run | compile time | compile time |

For CALC's current type language (no type-level computation, first-order terms), full LF type checking degenerates to:
1. Sort checking (base type compatibility)
2. Structural comparison of type family applications

No WHNF computation is needed because there are no type-level redexes.

## 9. Minimal Implementation Plan

### Data structures needed

```javascript
// Sort table (built from declarations)
sortTable = {
  'bin':  { kind: 'type' },
  'e':    { argTypes: [], returnType: 'bin' },
  'i':    { argTypes: ['bin'], returnType: 'bin' },
  'plus': { argTypes: ['bin','bin','bin'], returnType: 'type' },
  // ...
}
```

### Algorithm: `checkTerm(hash, expectedSort, ctx)`

```
checkTerm(hash, expectedSort, ctx):
  tag = Store.tag(hash)
  if tag == ATOM:
    name = Store.atomName(hash)
    if ctx.has(name): return ctx.get(name) == expectedSort  // metavar
    info = sortTable[name]
    if !info: error("unknown: " + name)
    if info.argTypes.length != 0: error("arity: expects args")
    return info.returnType == expectedSort
  if isPredTag(tag):
    name = Store.TAG_NAME[tag]
    info = sortTable[name]
    args = Store.children(hash)
    if args.length != info.argTypes.length: error("arity")
    for i in 0..args.length:
      checkTerm(args[i], info.argTypes[i], ctx)
    return info.returnType == expectedSort  // 'type' for predicates
  // constructors (tag < PRED_BOUNDARY)
  ... similar
```

### Integration point

In `compile.js`, after parsing a rule but before generating the compiled matcher:

```javascript
function compileRule(rule, calc) {
  // ... existing compilation ...
  if (calc.typeCheck) {
    checkRuleWellTypedness(rule, calc.sortTable);
  }
  // ... rest of compilation ...
}
```

## 10. Key References

- Harper, Honsell, Plotkin. "A Framework for Defining Logics" (1993) -- original LF
- Harper, Pfenning. "On Equivalence and Canonical Forms in the LF Type Theory" (2005) -- canonical LF
- Watkins, Cervesato, Pfenning, Reed. "A Concurrent Logical Framework" (2002) -- introduced hereditary substitution
- Pfenning. "Computation and Deduction" lecture notes -- LF type checking tutorial
- Abel. helf (Haskell) -- minimal bidirectional LF type checker (~600 LOC core)
- Bauer. "How to implement dependent type theory" (2012) -- practical tutorial with OCaml code
