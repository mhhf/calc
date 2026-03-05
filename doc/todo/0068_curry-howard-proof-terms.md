---
title: "Curry-Howard Proof Terms for ILL"
created: 2026-03-05
modified: 2026-03-05
summary: "Assign proof terms to all ILL connectives via the Curry-Howard correspondence. Two-layer design: Layer 1 generic terms derived from rule descriptors (rule name = constructor), Layer 2 optional interpretation maps (lambda, session types, etc.). Subsumes TODO_0067."
tags: [proof-theory, clf, linear-logic, curry-howard, lax-monad, architecture, verification, soundness, logical-framework]
type: design
cluster: Theory
status: planning
priority: 9
depends_on: []
required_by: [TODO_0045, TODO_0008]
starred: true
---

# Curry-Howard Proof Terms for ILL

## 1. Goal

Assign proof terms to every ILL derivation. A derivation of sequent `Gamma; Delta |- A` produces a term `t` such that `t : A`. The term is the computational content of the proof -- it records *how* A was proved, not just *that* it was proved.

This is the standard Curry-Howard correspondence applied to CALC's intuitionistic linear logic with lax monad.

**What this gives us:**
- Proofs are first-class data (content-addressed in Store, serializable, composable)
- Type-checking a term against a type = verifying a proof (de Bruijn criterion)
- Forward execution produces monadic let-bindings (CLF proof terms)
- The monad_r trust gap closes: `{E} : {S}` is verified by type-checking E
- Experimentable: Layer 1 generic terms derived free from descriptors, Layer 2 interpretation maps give different computational readings (lambda, sessions, plans) without changing the engine

**What this subsumes:**
- TODO_0067 (proof certificates) -- proof terms ARE certificates, but better: they compose, have computational meaning, and follow naturally from the logic instead of being bolted on

### 1.1 Two-Layer Architecture: Generic Terms + Interpretation

Proof terms follow a two-layer design inspired by LF/Twelf (Harper-Honsell-Plotkin 1993):

**Layer 1 -- Generic terms (derived automatically from rule descriptors):**

The rule name IS the proof term constructor. No manual term definitions needed. The descriptor fields (`side`, `premises`, `binding`, `contextSplit`, `copyContext`) mechanically determine each constructor's arity and binding structure:

```
genericTerm(rule) = rule_name(principal?, bindings -> subproof, ...)
```

Examples:
```
tensor_l descriptor: { side:'l', premises:[{linear:[0,1]}] }
-> tensor_l(z, x0 x1 -> u0)

loli_r descriptor: { side:'r', premises:[{linear:[0], succedent:1}] }
-> loli_r(x0 -> u0)

with_r descriptor: { side:'r', copyContext:true, premises:[{succedent:0},{succedent:1}] }
-> with_r(u0, u1)
```

This is exactly what LF does: one constructor per inference rule, adequacy guaranteed (bijection between proofs and well-typed terms). The existing `ProofTree` (with `rule` name + `premises`) is already 90% of a generic term -- it just needs binding annotations, which the descriptor provides.

**Layer 2 -- Interpretation maps (optional, swappable):**

A fold/catamorphism over generic terms that assigns computational meaning:

```
Layer 1 (generic):     tensor_l(z, x y -> u)
                            v  "lambda" interpretation
Layer 2a:              let (x, y) = z in [[u]]
                            v  "session-type" interpretation
Layer 2b:              z?(x).z?(y).[[u]]
                            v  "planning" interpretation
Layer 2c:              decompose(z, x, y); [[u]]
```

This is the "zoo of term assignments" (Martens 2014): same logic, different computational readings.

**Why NOT define terms in `.calc`/`.rules`:** The generic approach avoids needing new Store tags, new parser declarations, or new `.calc` entries for proof terms. Generic terms reuse existing infrastructure (ProofTree, rule names, descriptors). Layer 2 interpretations are post-processing, not part of the proof engine.

### 1.2 `.term` Files -- Interpretation Maps

Layer 2 interpretations are defined in `.term` files. Each `.term` file maps generic constructors to notation in a target language via pattern-based rendering templates:

```
% ill-lambda.term
@name "lambda-calculus".

tensor_r(u0, u1)                => (u0, u1).
tensor_l(z, x0 x1 -> u0)       => let (x0, x1) = z in u0.
loli_r(x0 -> u0)                => \x0. u0.
loli_l(z, u0, x1 -> u1)        => z u0; x1. u1.
with_r(u0, u1)                  => <u0, u1>.
with_l1(z, x0 -> u0)            => let x0 = fst z in u0.
with_l2(z, x1 -> u0)            => let x1 = snd z in u0.
oplus_r1(u0)                    => inl u0.
oplus_r2(u0)                    => inr u0.
oplus_l(z, x0 -> u0, x1 -> u1) => case z of inl x0 => u0 | inr x1 => u1.
one_r                            => ().
one_l(z, u0)                    => let () = z in u0.
bang_r(u0)                       => !u0.
bang_l(z, y0 -> u0)              => let !y0 = z in u0.
monad_r(u0)                     => {u0}.
monad_l(z, x0 -> u0)            => let {x0} = z in u0.
```

A different `.term` file for the same logic:

```
% ill-session.term
@name "session-types".

tensor_r(u0, u1)                => send u0; u1.
tensor_l(z, x0 x1 -> u0)       => (x0, x1) <- recv z; u0.
loli_r(x0 -> u0)                => x0 <- accept; u0.
with_r(u0, u1)                  => offer { left: u0, right: u1 }.
oplus_r1(u0)                    => select left; u0.
oplus_l(z, x0 -> u0, x1 -> u1) => branch z { left: x0.u0, right: x1.u1 }.
bang_r(u0)                       => accept!; u0.
monad_r(u0)                     => spawn u0.
```

**Loading pipeline:**

```
.calc -> .rules -> proof search -> ProofTree
                                     v
                               extractTerm()  [automatic from descriptors]
                                     v
                               Generic proof term
                                     v
                  .term file -> renderTerm()
                                     v
                               Rendered specific term
```

```javascript
// Calculus object includes interpretations:
calc.interpretations = {
  'lambda-calculus': loadTermFile('ill-lambda.term'),
  'session-types':   loadTermFile('ill-session.term'),
};

// Rendering:
const generic = extractTerm(proofTree, calc);
const rendered = renderTerm(generic, calc.interpretations['lambda-calculus']);
// -> "\x. let (y, z) = x in (z, y)"
```

`.term` files are **optional**. Without one, generic terms render as-is: `tensor_l(z, x0 x1 -> u0)`. Multiple `.term` files = different views of the same proof. Rules not mentioned in a `.term` file fall back to generic rendering.

**What `.term` is NOT (yet):** A rendering specification, not a full target language type system. Does not define reduction rules or type-checking for the target language. Could be extended later (e.g., `.theory` files with beta-reduction for the lambda interpretation).

### 1.3 Role Removal

The existing `deriveRoles()` function (`lib/calculus/builders.js`) maps `(category, arity, polarity) -> semantic role name`. This indirection is used in `bridge.js` (rightFocus) and `compile.js` (flattenTensor, expandChoiceItem, etc.) to identify connective behavior.

Roles should be removed: they are redundant middleware. The same information is available directly from the connective's descriptor annotations. Replace `tag === roles.product` with a direct lookup of the connective's `(category, arity, polarity)` triple:

```javascript
// Before (roles):
if (tag === roles.product) { ... }

// After (direct descriptor properties):
const info = calc.connectiveInfo[tag];
if (info?.category === 'multiplicative' && info?.polarity === 'positive' && info?.arity === 2) { ... }

// Or with a precomputed lookup:
if (calc.isProduct(tag)) { ... }
```

The `connectiveInfo` table is already computable from `.calc` annotations -- it's what `deriveRoles` reads from. Precompute boolean lookup tables (e.g., `isProduct[tagId]`, `isUnit[tagId]`) at calculus load time for O(1) hot-path checks. Same performance, no semantic naming layer.

---

## 2. The Term Language

Dual-context judgment (DILL, Barber-Plotkin 1996):

```
Gamma; Delta |- t : A
```

- `Gamma` = cartesian context (weakening + contraction), variables usable many times
- `Delta` = linear context, each variable used exactly once

### 2.1 Multiplicatives

**Tensor (`A * B`):**
```
Gamma; Delta1 |- t1 : A    Gamma; Delta2 |- t2 : B
------------------------------------- *R
   Gamma; Delta1, Delta2 |- (t1, t2) : A * B

Gamma; Delta1 |- t : A * B    Gamma; Delta2, x:A, y:B |- u : C
-------------------------------------------------- *L
   Gamma; Delta1, Delta2 |- let (x, y) = t in u : C
```

**One (`1`):**
```
---------------- 1R          Gamma; Delta1 |- t : 1    Gamma; Delta2 |- u : C
Gamma; . |- () : 1               ----------------------------------- 1L
                              Gamma; Delta1, Delta2 |- let () = t in u : C
```

**Loli (`A -o B`):**
```
Gamma; Delta, x:A |- t : B                     Gamma; Delta1 |- t : A -o B    Gamma; Delta2 |- u : A
--------------------- -oR               --------------------------------------- -oL
Gamma; Delta |- \x. t : A -o B                   Gamma; Delta1, Delta2 |- t u : B
```

### 2.2 Additives

**With (`A & B`):**
```
Gamma; Delta |- t1 : A    Gamma; Delta |- t2 : B
---------------------------------- &R     (same Delta for both!)
  Gamma; Delta |- <t1, t2> : A & B

fst t : A    snd t : B                   (from t : A & B)
```

**Oplus (`A oplus B`):**
```
  Gamma; Delta |- t : A                            Gamma; Delta |- t : B
---------------------- oplusR1              ---------------------- oplusR2
Gamma; Delta |- inl t : A oplus B                   Gamma; Delta |- inr t : A oplus B

Gamma; Delta1 |- t : A oplus B    Gamma; Delta2, x:A |- u1 : C    Gamma; Delta2, y:B |- u2 : C
------------------------------------------------------------------------- oplusL
       Gamma; Delta1, Delta2 |- case t of inl x => u1 | inr y => u2 : C
```

**Zero (`0`):**
```
No introduction.

Gamma; Delta |- t : 0
---------------- 0L
Gamma; Delta |- abort t : C
```

### 2.3 Exponential

**Bang (`!A`):**
```
Gamma; . |- t : A
--------------- !R    (empty linear context)
Gamma; . |- !t : !A

Gamma; Delta1 |- t : !A    Gamma, x:A; Delta2 |- u : C
---------------------------------------- !L    (x moves to cartesian)
   Gamma; Delta1, Delta2 |- let !x = t in u : C
```

### 2.4 Lax Monad

**Monad (`{A}`):**
```
Gamma; Delta |-_lax t : A
---------------------- {A}R
Gamma; Delta |- {t} : {A}

Gamma; Delta1 |- t : {A}    Gamma; Delta2, x:A |-_lax u : C
----------------------------------------------- {A}L
     Gamma; Delta1, Delta2 |-_lax let {x} = t in u : C
```

The `|-_lax` judgment is **sticky**: once entered, you cannot return to `|-`. This is the type-theoretic expression of the mode switch -- backward proving enters `|-_lax` via `monad_r`, and the forward engine operates entirely within `|-_lax`.

Via Moggi's computational monad: `{t}` = `return t`, `let {x} = t in u` = `bind t (\x. u)`.

Via Pfenning-Davies (2001): `|-` = "A is true", `|-_lax` = "A is achievable (through computation)".

### 2.5 Quantifiers

**Universal (`forallx.A`):**
```
Gamma; Delta |- t : A[y/x]                          (y fresh -- eigenvariable)
-------------------- forallR
Gamma; Delta |- \y.t : forallx.A

Gamma; Delta, u:A[s/x] |- t : C
------------------------ forallL                  (instantiate with term s)
Gamma; Delta, u:forallx.A |- t : C
```

Note on forallL: The principal formula `forallx.A` is on the LEFT (antecedent) and is deconstructed to `A[s/x]`. The proof term `t` in the conclusion is the same as in the premise -- the rule just substitutes `u` for the instantiated hypothesis. In the generic term view: `forall_l(u, s, t)` where `u` is the principal, `s` is the witness term, `t` is the continuation proof. Spined notation (RES_0086): `u[s] . t`.

**Existential (`existsx.A`):**
```
Gamma; Delta |- t : A[s/x]
------------------------ existsR                  (witness s + proof t)
Gamma; Delta |- pack(s, t) : existsx.A

Gamma; Delta, y:A[a/x] |- t : C                     (a fresh -- eigenvariable)
------------------------ existsL
Gamma; Delta, u:existsx.A |- t : C
```

Note on existsL: The principal formula `existsx.A` is on the LEFT and is deconstructed by opening the existential with fresh eigenvariable `a`. In the generic term view: `exists_l(u, a -> t)`.

**Reading direction:** Sequent calculus rules are read bottom->top for proof search. The conclusion (bottom) ALWAYS has the complex connective. The premise (top) has simpler sub-formulas. Reading bottom->top, you DECONSTRUCT. Reading top->bottom (proof construction), you INTRODUCE. Both perspectives describe the same rule.

In CLF: exists is synchronous (inside the monad `{S}`), while forall (as `Pi`) is asynchronous. Implementation deferred until quantifiers appear in forward programs. See TODO_0011 for the dependent case (`Pix:A.B`).

### 2.6 Identity and Cut

```
------------ id               Gamma; Delta1 |- t : A    Gamma; Delta2, x:A |- u : C
Gamma; x:A |- x : A               ---------------------------------------- cut
                                Gamma; Delta1, Delta2 |- u[t/x] : C
```

### 2.7 Generic Term Grammar (Layer 1 -- Primary)

Generic proof terms are the primary representation. Each rule name IS a constructor. Arity and bindings are derived from the rule's descriptor:

- `side='l'` -> first arg is principal `z` (consumed from antecedent)
- Each premise -> one sub-proof `ui`
- `premises[i].linear` -> bound variables `xj` scoped over `ui` (arrow notation: `xj -> ui`)
- `premises[i].cartesian` -> bound variables `yj` moved to Gamma
- `binding='eigenvariable'` -> fresh variable bound in sub-proof
- `binding='metavar'` -> witness term argument

All constructors for ILL (pseudocode -- this is not a parsed grammar, just a catalog):

```
id(x)                                   identity
tensor_r(u0, u1)                        tensor-R (context split)
tensor_l(z, x0 x1 -> u0)               tensor-L (decompose, bind two)
one_r()                                 one-R (empty context)
one_l(z, u0)                            one-L
loli_r(x0 -> u0)                        loli-R (bind argument)
loli_l(z, u0, x1 -> u1)                loli-L (apply, bind result)
with_r(u0, u1)                          with-R (context copied)
with_l1(z, x0 -> u0)                    with-L1 (first projection)
with_l2(z, x1 -> u0)                    with-L2 (second projection)
oplus_r1(u0)                            oplus-R1
oplus_r2(u0)                            oplus-R2
oplus_l(z, x0 -> u0, x1 -> u1)         oplus-L (case split)
zero_l(z)                               zero-L (abort, discards context)
bang_r(u0)                              bang-R (empty linear context)
bang_l(z, y0 -> u0)                     bang-L (y0 moves to Gamma)
monad_r(evidence)                       monad-R (mode switch)
monad_l(z, x0 -> u0)                    monad-L
forall_r(a -> u0)                       forall-R (eigenvariable)
forall_l(z, s, u0)                      forall-L (instantiate with s)
exists_r(s, u0)                         exists-R (witness s)
exists_l(z, a -> u0)                    exists-L (eigenvariable)
unreachable(reason)                     dead branch (unverified)
ffi(name, args, result)                 FFI axiom (unverified)
```

### 2.8 Lambda Interpretation (Layer 2 -- from `ill-lambda.term`)

ss2.1-2.5 above show typing rules using lambda notation. This notation is NOT built into the system -- it comes from a `.term` file. The `.term` file maps generic constructors to human-readable syntax (see ss1.2 for the full file format).

Without a `.term` file, proofs render using the generic grammar (ss2.7). With `@import "ill-lambda.term"` in a `.rules` file, rules can use lambda notation for term annotations. The `.term` file provides bidirectional mapping: parse (for `.rules` annotations) and render (for display).

---

## 3. Proof Terms in CALC's Two Modes

### 3.1 Backward Prover -> Natural Deduction Terms

The backward prover (L2-L3) already builds proof trees. Each rule application maps to a generic proof term constructor (Layer 1). The right column shows the lambda interpretation (Layer 2, from `.term` file):

| Rule name | Generic term | Lambda view |
|---|---|---|
| `id` | `id(x)` | `x` |
| `tensor_r` | `tensor_r(u0, u1)` | `(u0, u1)` |
| `tensor_l` | `tensor_l(z, x0 x1 -> u0)` | `let (x0, x1) = z in u0` |
| `loli_r` | `loli_r(x0 -> u0)` | `\x0. u0` |
| `loli_l` | `loli_l(z, u0, x1 -> u1)` | `z u0` (+ continuation) |
| `with_r` | `with_r(u0, u1)` | `<u0, u1>` |
| `with_l1` / `with_l2` | `with_l1(z, x0 -> u0)` | `fst z` / `snd z` |
| `oplus_r1` / `oplus_r2` | `oplus_r1(u0)` | `inl u0` / `inr u0` |
| `oplus_l` | `oplus_l(z, x0 -> u0, x1 -> u1)` | `case z of ...` |
| `zero_l` | `zero_l(z)` | `abort z` |
| `one_r` | `one_r()` | `()` |
| `one_l` | `one_l(z, u0)` | `let () = z in u0` |
| `bang_r` | `bang_r(u0)` | `!u0` |
| `bang_l` | `bang_l(z, y0 -> u0)` | `let !y0 = z in u0` |
| `copy` | `copy(z, y0 -> u0)` | = `bang_l` (moves `!A` to Gamma) |
| `monad_r` | `monad_r(evidence)` | `{e}` (delegates to forward engine) |
| `monad_l` | `monad_l(z, x0 -> u0)` | `let {x0} = z in u0` |

### 3.2 Forward Engine -> Monadic Let-Bindings (CLF)

Each forward step IS a monadic let-binding. A forward rule `r : A1 * A2 * !P -o {B1 * B2}` applied with theta produces:

```
let {(b1, b2)} = r (a1, a2, !p) in ...continuation...
```

This is exactly CLF's monadic expression (Watkins et al. 2004):
```
E ::= let {p} = R in E    -- forward step
    | M                    -- return (quiescence)
```

A full forward trace is a nested sequence of let-bindings:
```
let {(b1, b2)} = r1 (a1, a2) in
let {c}         = r2 (b1, b3) in
(c, b2)                              -- final state = return value
```

**Loli continuations:** When state contains `f : A -o {B}` and `a : A`, `matchFirstLoli` fires. This is loli elimination (function application): `f a : {B}`. In the monadic setting: `let {p} = (f a) in ...`. Same shape as any rule application -- the loli IS the rule being applied.

### 3.3 rightFocus -> Synchronous Decomposition Term

After quiescence, `rightFocus` decomposes the succedent against residual state. This produces a term built from tensor/one/bang/id constructors:

```
rightFocus(state, A * B) = (rightFocus(Delta1, A), rightFocus(Delta2, B))
rightFocus(., 1)          = ()
rightFocus(state, !A)     = !(id_persistent(A))
rightFocus(state, atom)   = id_linear(atom)
```

### 3.4 Explore Tree and Proof Terms

Non-fork nodes map straightforwardly to proof term structure:

| Node type | Term fragment |
|---|---|
| `leaf` | Return value: rightFocus decomposition term |
| `branch` child | `let {p} = r args in ...child_term...` |
| `bound` | `_|_` (incomplete -- no term) |
| `cycle` | Back-edge reference (coinductive -- future work, TODO_0009) |
| `memo` | Pointer to previously computed term |

### 3.5 Oplus Forks -> Case Splits in Proof Terms

When a rule produces `A oplus B`, the explore tree forks. Each fork becomes an `oplus_l` (case split) in the proof term:

```
let {x} = evm_eq(args) in           -- x : S1 oplus S2
  oplus_l(x,
    a -> ...continuation1...,       -- eq branch
    b -> ...continuation2...        -- neq branch
  )
```

The explore tree IS the proof term tree:

| Explore node | Proof term |
|---|---|
| `branch(rule, child)` | `let {p} = rule(args) in child_term` |
| `fork(children)` | `oplus_l(x, a -> child1, b -> child2)` |
| `leaf` | return value (rightFocus decomposition) |
| `dead` | `unreachable(reason)` -- see ss3.6 |
| `bound` | `_|_` (incomplete) |
| `cycle` | back-edge (future work, TODO_0009) |
| `memo` | shared sub-term reference |

Nested forks = nested case splits. k nested binary forks -> one proof term with k nested `oplus_l`, 2^k leaves. All paths are captured in a single term.

**CLF extension:** CLF's monadic expression grammar is `E ::= let {p} = R in E | M`. We extend it with case analysis: `E ::= let {p} = R in E | oplus_l(x, a -> E, b -> E) | M`. CLF excluded oplus from `{S}` for committed-choice semantics. CALC's exhaustive exploration IS case analysis -- we're not doing committed choice, we're computing both branches. The extension is proof-theoretically sound: oplus elimination inside the monad.

**Nested consequent choices:** `(A oplus B) * C` in a consequent decomposes via tensor then case:

```
let {y} = rule(args) in             -- y : (A oplus B) * C
  tensor_l(y, x c ->
    oplus_l(x,
      a -> ...                       -- A, C world
      b -> ...                       -- B, C world
    )
  )
```

### 3.6 Dead Branches

With Option A (ss3.5), dead branches NEED proof terms -- the case split requires a term for every branch.

**Decision:** Two-tier approach:

**Primary -- Materialize the contradiction (fully verified):**

CALC has `contra/eq_neq : !eq X Y * !neq X Y -o { zero }`. When the constraint solver detects UNSAT, fire the contradiction rule explicitly:

```
oplus_l(x,
  a. ...normal continuation...,       -- live branch
  b. let {z} = contra_eq_neq(         -- dead branch: fire contradiction
       !eq_witness, !neq_witness       -- witnesses from persistent state
     ) in zero_l(z)                    -- z : 0 -> abort -> any type
)
```

Fully sound. `zero_l(z) : C` for any C when `z : 0`. The solver already tracks witnesses.

**Fallback -- `unreachable(reason)` for exotic UNSAT:**

When no contradiction rule exists (complex union-find chains, transitive inequalities):

```
oplus_l(x,
  a. ...normal continuation...,
  b. unreachable("eq(X,Y) and neq(X,Y)")    -- trusted axiom
)
```

Checker flags `{ valid: true, unverified: 'constraintUNSAT' }`. Same pattern as `unverified: 'modeSwitch'`.

---

## 4. Type Checker (Trusted Kernel Extension)

A small, independent module that verifies `t : A`. This is the de Bruijn criterion applied via Curry-Howard: the prover (untrusted, complex) produces terms, the checker (trusted, small) validates them.

### 4.1 Interface

```javascript
// lib/prover/check-term.js (~150 LOC, trusted)
function checkTerm(gamma, delta, term, type) -> { valid: boolean, error?: string }
```

Input: contexts, term, expected type -- all as expanded term objects (not Store hashes). Store stays outside the trust boundary (same principle as TODO_0067 ss4).

### 4.2 What It Checks -- Per-Rule Map Lookup

The checker uses a generated map from rule name to checking function. Each rule gets its own entry. The map is generated at calculus load time from descriptors -- no handwriting needed, but the runtime dispatch is a simple key lookup:

```javascript
// Generated at load time from descriptors:
const checkers = {
  'tensor_r': (gamma, delta, term, type) => {
    // type must be tensor(A, B)
    // split delta by variable usage
    // check term.children[0] : A with delta1
    // check term.children[1] : B with delta2
  },
  'tensor_l': (gamma, delta, term, type) => {
    // term.principal : tensor(A, B) in delta
    // remove principal, add x0:A, x1:B
    // check term.body : type with extended delta
  },
  'loli_r': (gamma, delta, term, type) => { ... },
  'id':       (gamma, delta, term, type) => { ... },
  'unreachable': () => ({ valid: true, unverified: 'constraintUNSAT' }),
  'ffi':      (gamma, delta, term, type) => ({ valid: true, unverified: 'ffiAxiom' }),
  // ...one entry per rule
};

// Runtime: simple map lookup, no pattern matching
function checkTerm(gamma, delta, term, type) {
  const check = checkers[term.rule];
  if (!check) return { valid: false, error: 'unknown rule: ' + term.rule };
  return check(gamma, delta, term, type);
}
```

**Walkthrough:** Check `tensor_r(id(a), id(b)) : A * B` with `delta = {a:A, b:B}`:

```
1. checkers['tensor_r'] -- direct map lookup
2. type = tensor(A, B) -- verify tag
3. split delta by variable usage: delta1={a:A}, delta2={b:B}
4. checkers['id'](gamma, {a:A}, id(a), A) -- ok
5. checkers['id'](gamma, {b:B}, id(b), B) -- ok
```

~150 LOC total. The map is generated from descriptors (so new connectives get checkers automatically), but at runtime each rule has its own explicit function -- no descriptor interpretation at check time. Explicit, debuggable, no magic.

**Context splitting is deterministic.** The term determines the split: track which variables each sub-term uses. Each variable used exactly once (linearity). No search needed.

### 4.3 Trust Boundary

| Trusted | Size | Role |
|---|---|---|
| `kernel.js` (existing) | 205 LOC | Backward proof step verification |
| `check-term.js` (new) | ~150 LOC | Forward proof term type-checking |
| Term equality + substitution | ~25 LOC | Shared utilities |
| **Total** | **~380 LOC** | |

Everything else (Store, forward engine, backward prover, FFI, strategy) is untrusted.

---

## 5. Implementation

### Phase 1: Generic Term Extraction (~50 LOC)

No new `.calc` declarations needed. Generic proof terms are derived directly from rule descriptors.

New module `lib/prover/generic-term.js`:

```javascript
function genericTermShape(rule) {
  const d = rule.descriptor;
  const args = [];
  if (d.side === 'l') args.push('z');  // principal consumed from antecedent
  d.premises.forEach((p, i) => {
    const bindings = [
      ...(p.linear || []).map(idx => `x${idx}`),
      ...(p.cartesian || []).map(idx => `y${idx}`)
    ];
    const sub = `u${i}`;
    args.push(bindings.length ? `${bindings.join(' ')} -> ${sub}` : sub);
  });
  return { constructor: rule.name, args };
}
```

Generic terms are lightweight JS objects: `{ type: 'tensor_l', principal: hash, premises: [{ bindings: [...], body: subterm }] }`. No Store tags consumed, no FactSet impact, no binary cache invalidation.

Variables use de Bruijn indices (via existing `bound(n)` nodes) for binding positions. The descriptor's `premises[i].linear` array maps directly to binding indices.

**What about Store/content-addressing?** Generic terms live OUTSIDE the Store. They annotate proofs, not participate in forward execution. If Layer 2 interpretations ever need Store representation (e.g., for dependent types where terms appear inside formulas), Store tags can be added then. But Layer 1 doesn't need them.

### Phase 2: Backward Term Builder (~80 LOC)

Extend `lib/prover/generic-term.js` (untrusted). Given a completed ProofTree, extract the corresponding generic proof term:

```javascript
function extractTerm(proofTree, calculus) -> genericTerm
```

Post-hoc extraction: the prover builds the proof tree as now, then `extractTerm` walks it and constructs a generic term using `genericTermShape` for binding structure. No changes to the prover itself. Returns a lightweight JS object tree, not Store hashes.

### Phase 3: Forward Term Builder (~60 LOC)

Extend `forward.run()` and `explore()` to optionally record monadic terms. Opt-in via `{ terms: true }`:

```javascript
// forward.js -- when terms enabled
trace.push({ rule, theta, consumed, produced, termHash });

// At quiescence: rightFocus produces decomposition term
const rfTerm = buildRightFocusTerm(residualState, succedent);
```

Function pointer swap at entry (same pattern as TODO_0067): no branches in the hot path when terms are disabled.

### Phase 4: Type Checker (~150 LOC)

New module `lib/prover/check-term.js` (trusted). Works on generic term objects, no Store dependency:

```javascript
// lib/prover/check-term.js
const checkers = buildCheckerMap(calculus);  // generated from descriptors

function checkTerm(gamma, delta, term, type) {
  const check = checkers[term.rule];
  if (!check) return { valid: false, error: 'unknown rule: ' + term.rule };
  return check(gamma, delta, term, type);
}
```

`buildCheckerMap` reads descriptors once at load time and generates one checking function per rule. At runtime, dispatch is a plain map lookup -- explicit, debuggable, no descriptor interpretation on the hot path. New connectives get checkers automatically via the generator.

### Phase 5: Bridge Integration (~30 LOC)

Wire `monad_r` to produce and verify terms:

```javascript
// bridge.js -- executeModeSwitch
if (opts.terms) {
  const monadicTerm = buildMonadicTerm(trace, rfTerm);
  // Type-check: monadicTerm : innerSuccedent
  const check = checkTerm(gamma, delta, expand(monadicTerm), expand(innerSucc));
  evidence = { term: monadicTerm, verified: check.valid };
}
```

Kernel verification for monad_r changes from `{ valid: true, unverified: 'modeSwitch' }` to `{ valid: true }` when term verification succeeds.

### Phase 6: Tests (~80 LOC)

- Term construction: each connective -> correct term shape
- Type checking: valid terms accepted, invalid rejected
- Round-trip: backward proof -> extract term -> type-check -> valid
- Forward trace -> monadic term -> type-check -> valid
- Tampered terms rejected (wrong variable, missing resource, type mismatch)
- Zero-overhead: `{ terms: false }` matches baseline performance

---

## 6. Relationship to Other TODOs

| TODO | Relationship |
|---|---|
| **TODO_0067** (proof certificates) | **Subsumed.** Proof terms are strictly more useful than ad-hoc certificates. Terms compose, have computational meaning, and follow standard theory. 0067 demoted to priority 3. |
| **TODO_0045** (execution tree judgment) | **Consumer.** The tree `T` in `Sigma; Delta |-_fwd T : A` is now a tree of monadic proof terms. |
| **TODO_0008** (metaproofs) | **Consumer.** Invariant witnesses become typed proof terms. Counterexample traces are well-typed monadic expressions. |
| **TODO_0011** (CLF dependent types) | **Orthogonal.** Dependent types add `Pix:A.B` -- proof terms depend on values. This TODO handles the non-dependent base case. |
| **TODO_0009** (induction/coinduction) | **Future extension.** Fixed-point terms (mu/nu constructors) and cyclic proof terms extend this term language. |
| **TODO_0066** (modular architecture) | **Aligns.** The architecture's hook points (certificateHook in explore, evidence in monad_r) are where terms get recorded. |
| **TODO_0064** (higher-order extensions) | **Axis 1, Level 0->1.** This is the first step on the term-level type discipline axis. |

---

## 7. Key Design Decisions

**Post-hoc extraction, not inline construction.** The backward prover builds proof trees as it does now. Terms are extracted from completed trees. This avoids threading term-building through the search loop. The forward engine records traces (it already does); terms are built from traces. Clean separation: search is search, terms are terms.

**Opt-in, zero overhead when off.** Same function-pointer-swap pattern as the existing `provePersistentWithFFI` / `provePersistentNaive` dispatch. No `if (terms)` in hot loops.

**Store-free checker.** The type checker works on expanded ASTs, not hashes. Store is untrusted infrastructure. The checker is a pure function: `(contexts, term, type) -> valid/invalid`.

**No definitional equality (yet).** CLF identifies monadic expressions up to reordering of independent let-bindings. CALC doesn't need this -- the forward engine commits to a specific execution order. If needed later (e.g., for confluence proofs), commuting conversions can be added to the checker.

**FFI as axiom (configurable).** Two modes for persistent goals when terms are enabled:
1. **FFI axiom mode** (default, fast): FFI results produce axiom terms `ffi("plus", [3, 2, 5])`. The type checker validates by re-computing. Preserves FFI performance.
2. **Clause resolution mode** (strict): FFI disabled, clause resolution produces full proof subtrees. Slower (~10-20x for arithmetic-heavy programs) but terms are self-contained.

Configurable alongside other profile settings (e.g., `{ terms: true, ffiAxioms: true }`). Same function-pointer-swap dispatch as existing FFI opt-in.

---

## 8. Theory Compliance

### 8.1 Soundness

If `checkTerm(Gamma, Delta, t, A)` returns valid, then `Gamma; Delta |- t : A` is a valid ILL+lax derivation. Proof: each case of the checker corresponds to exactly one ILL inference rule. The checker is a direct implementation of the typing rules in ss2.

### 8.2 Adequacy

The term assignment is **adequate** in the LF sense (Harper-Honsell-Plotkin 1993): there is a compositional bijection between ILL proofs and well-typed terms of the corresponding type.

- **Faithfulness (injectivity):** Different proofs produce different terms (each rule application produces a distinct constructor).
- **Fullness (surjectivity):** Every well-typed term corresponds to a proof (the checker validates exactly the derivable judgments).
- **Compositionality:** Term construction commutes with substitution: `extractTerm(D[s/x]) = extractTerm(D)[extractTerm(s)/x]`.

### 8.3 Canonical Forms

Generic proof terms (Layer 1) are lightweight JS objects. If needed, they can be content-addressed via Store (Layer 2 may require this for dependent types). The current system doesn't need beta-reduction because terms are constructed in normal form (post-hoc extraction from cut-free proofs).

---

## 9. Future Optimizations

Captured here for later exploration, not part of initial implementation.

1. **Streaming term construction:** Build terms during DFS exploration, undo with the Arena alongside state undo. Avoids post-hoc tree walk. Only worth it if extraction becomes a bottleneck.

2. **Term sharing:** If two explore paths produce identical sub-proof terms, share them. Content-addressing (Store) gives this for free. Reduces memory for trees with many isomorphic subtrees.

3. **Incremental checking:** Type-check terms as they're built (each monadic let-binding). Catches errors early, before full tree extraction completes.

4. **FFI axiom compilation:** Pre-generate checker code per FFI operation, so `ffi("plus", [a,b,c])` validates in O(1) (just recompute and compare) rather than going through generic checker dispatch.

5. **Zig-friendly flat arena:** Proof terms as `struct ProofTerm { tag: u8, arity: u8, children: [4]u32 }` in a bump arena. ~10 bytes per node. Cache-friendly, zero allocation, trivially serializable. The JS implementation can use `Uint8Array` + `Uint32Array` SoA to match.

6. **Lazy extraction:** For very large explore trees (10K+ nodes), extract terms only for paths the user inspects, not the full tree.

7. **Store tag capacity:** Currently `tags = new Uint8Array(capacity)` limits tag values to 0-255. If Layer 2 interpretations ever need Store-resident terms (e.g., dependent types), upgrading to `Uint16Array` (65536 tags) is a one-line change. `STRING_CHILD_TAGS`/`BIGINT_CHILD_TAGS` lookup tables would grow from 256B to 64KB (still trivial). PRED_BOUNDARY (currently 28) is unrelated -- it separates built-in tags from dynamic predicates. The generic Layer 1 approach avoids this concern entirely by keeping terms outside the Store.

---

## 10. References

### Foundational
- Barber & Plotkin (1996) -- "Dual Intuitionistic Linear Logic" (DILL). Dual-context judgment `Gamma; Delta |- M : A`
- Benton (1995) -- "A Mixed Linear and Non-Linear Logic" (LNL). Adjoint decomposition `!A = G(F(A))`
- Bierman, Benton, de Paiva, Hyland (1992) -- "Term Assignments for ILL". First complete term assignment
- Girard (1987) -- "Linear Logic" TCS 50(1). The logic itself

### CLF and Logical Frameworks
- Watkins, Cervesato, Pfenning, Walker (2004) -- "CLF: A Concurrent Logical Framework". Monadic proof terms `let {p} = R in E`
- Cervesato & Pfenning (2002) -- "A Linear Logical Framework" (LLF). `\Pi -o & T`
- Harper, Honsell & Plotkin (1993) -- "A Framework for Defining Logics" (LF). Canonical forms, adequacy

### Lax Monad
- Pfenning & Davies (2001) -- "A Judgmental Reconstruction of Modal Logic". Lax modality as `|-_lax`, terms = Moggi's monad
- Moggi (1991) -- "Notions of Computation and Monads". Computational monad = `{A}`
- Fairtlough & Mendler (1997) -- "Propositional Lax Logic"

### Session Types & Term Zoos
- Caires & Pfenning (2010) -- "Session Types as Intuitionistic Linear Propositions". Proofs = processes
- Wadler (2014) -- "Propositions as Sessions". Classical variant
- Martens (2014) -- "Zoo of Term Assignments for Linear Sequent Calculus". Same logic, different computational meanings (lambda terms, processes, plans)

### Internal
- [TODO_0045](0045_execution-tree-judgment.md) -- Execution tree judgment (consumer of proof terms)
- [TODO_0067](0067_proof-certificates.md) -- Proof certificates (subsumed, priority 3)
- [TODO_0011](0011_clf-dependent-types.md) -- CLF dependent types (orthogonal extension)
- [TODO_0064](0064_higher-order-extensions-overview.md) -- Higher-order extensions (Axis 1)
- [RES_0052](../research/0052_clf-lax-monad-deep-study.md) -- CLF lax monad deep study
- [RES_0038](../research/0038_resource-term-semantics.md) -- Resource term semantics
- [RES_0077](../research/0077_modular-proof-kernel-architectures.md) -- Proof kernel architectures
- [RES_0086](../research/0086_quantifier-proof-terms.md) -- Quantifier proof terms survey
- `doc/documentation/lax-monad.md` -- Mode switch & connective roles
