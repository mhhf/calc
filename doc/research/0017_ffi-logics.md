---
title: "FFI for Logics: Trusted External Computation in Proof Search"
created: 2026-02-10
modified: 2026-02-10
summary: Approaches for integrating trusted external computation in logic systems including mode declarations, CLP, oracles, and proof-carrying code for computational predicates.
tags: [ffi, oracles, mode-checking, CLP, trusted-computation]
category: "Implementation"
---

# FFI for Logics: Trusted External Computation in Proof Search

How to escape proof search for computational predicates like `plus(A,B,C)` where A+B=C.

---

## Table of Contents

1. [The Problem](#the-problem)
2. [Approaches in Existing Systems](#approaches-in-existing-systems)
3. [Mode Declarations](#mode-declarations)
4. [Constraint Logic Programming](#constraint-logic-programming)
5. [Proof Assistants and FFI](#proof-assistants-and-ffi)
6. [Oracle Predicates](#oracle-predicates)
7. [Design for CALC](#design-for-calc)
8. [Security Considerations](#security-considerations)
9. [Sources](#sources)

---

## The Problem

### The Scenario

You want a predicate like:
```
plus(A, B, C)   -- true when A + B = C
```

When `A` and `B` are **concrete** (ground terms), you don't want proof search to:
1. Backchain through recursive rules
2. Enumerate all possible derivations
3. Waste time on what's essentially arithmetic

Instead, you want to **call out to JavaScript**:
```javascript
function plus(a, b) {
  return [a, b, a + b];  // Just compute it!
}
```

### The Trust Question

This raises a fundamental question:
- **Proof search** = verified derivation from axioms
- **External computation** = "just trust me"

How do we integrate these safely?

---

## Approaches in Existing Systems

### 1. Prolog's `is/2` Predicate

Prolog's classic solution: the `is` predicate **escapes unification** for arithmetic.

```prolog
X is 3 + 4.   % X = 7 (computed, not unified)
X = 3 + 4.   % X = 3+4 (unified, not computed)
```

**How it works:**
- Right-hand side must be **ground** (fully instantiated)
- Evaluator computes the result
- Result is unified with left-hand side

**Key insight:** `is` is a **mode-restricted** built-in. It only works when inputs are ground.

### 2. Twelf: No Built-ins (Pure)

Twelf takes the opposite approach: **no built-in arithmetic**.

```twelf
nat : type.
z : nat.
s : nat -> nat.

plus : nat -> nat -> nat -> type.
plus/z : plus z N N.
plus/s : plus (s M) N (s P) <- plus M N P.
```

**Philosophy:** Everything is derived from axioms. No external trust.

**Consequence:** Arithmetic is slow (Peano-style), but proofs are guaranteed.

### 3. Celf: Forward + Backward Chaining

Celf extends Twelf with linear logic and a **monad** for forward chaining:

```
Outside monad: backward chaining (proof search)
Inside monad:  forward chaining (committed choice)
```

The monad acts as a **mode boundary**:
- Outside: nondeterministic proof search
- Inside: deterministic state transitions

This is closer to FFI — the monad is "trusted" to maintain invariants.

### 4. Ceptre: State Transitions

Ceptre (Chris Martens) uses linear logic for **game mechanics**:

```ceptre
stage play {
  move : player P * at P Loc * adjacent Loc Loc'
       -o at P Loc'.
}
```

Rules are **forward-chaining** state transitions. The system commits to choices.

**Relevance:** Shows how linear logic can model "just do it" computation alongside proof search.

---

## Mode Declarations

### The Key Mechanism

Mode declarations specify **information flow**:

```
%mode plus +A +B -C.
```

- `+` = input (must be ground when predicate is called)
- `-` = output (will be ground after predicate succeeds)
- `*` = unrestricted

### How It Enables FFI

If a predicate has mode `+A +B -C`:
1. When called, check A and B are ground
2. If ground, you CAN use external computation
3. The output C will be produced (not searched for)

```javascript
// Pseudo-code for mode-aware FFI
function callPredicate(pred, args) {
  if (pred.hasFFI && allGround(pred.inputArgs, args)) {
    return pred.ffiFunction(...getGroundValues(pred.inputArgs, args));
  } else {
    return proofSearch(pred, args);
  }
}
```

### Twelf's Mode Checking

Twelf performs **abstract interpretation**:
1. Track which variables are known-ground
2. For each subgoal, verify inputs will be ground
3. Mark outputs as ground after success

This ensures the **information flow** is well-defined.

---

## Constraint Logic Programming

### CLP: A Different Paradigm

CLP(X) extends Prolog with **constraint solvers** over domain X:

| System | Domain | Description |
|--------|--------|-------------|
| CLP(FD) | Finite domains | Integer constraints |
| CLP(R) | Real numbers | Real arithmetic |
| CLP(Q) | Rationals | Rational arithmetic |
| CLP(B) | Booleans | SAT solving |

### How CLP Works

```prolog
?- X #> 3, X #< 7, X #= Y + 2.
```

Instead of backtracking:
1. **Constraints are collected** (not immediately solved)
2. A **solver** propagates constraints
3. Search only happens when needed

### The Solver as "Trusted Oracle"

The constraint solver is essentially an **FFI**:
- It's not part of the logic
- It's trusted to correctly solve constraints
- It returns results that proof search uses

```
Prolog unification ──→ Constraint solver ──→ Results
    (logical)              (external)         (logical)
```

### Relevance to CALC

For accounting with real numbers:
- CLP(R) or CLP(Q) could handle `0.5 BTC + 0.3 BTC = 0.8 BTC`
- The solver is "trusted" but well-understood
- No need to axiomatize real arithmetic in the logic

---

## Proof Assistants and FFI

### Agda's Approach

Agda uses **postulates** as the FFI mechanism:

```agda
postulate
  plus : Nat → Nat → Nat

{-# COMPILE GHC plus = (+) #-}
```

**At type-checking time:** `plus` is treated as an uninterpreted function.
**At runtime:** The Haskell implementation is used.

### The Safety Gap

**Critical warning from Agda docs:**
> "There are no checks to ensure that the Agda code and the Haskell code behave the same and discrepancies may lead to undefined behaviour."

This is the fundamental tension:
- Type system trusts the postulate's type signature
- Runtime trusts the external implementation
- **No verification** that they match

### Safe Agda

With `--safe` flag:
- Postulates are **forbidden**
- FFI is effectively disabled
- Everything must be proven

This shows the trade-off: **safety vs. practicality**.

### Coq's Approaches

Coq offers multiple mechanisms:

| Mechanism | Description | TCB Impact |
|-----------|-------------|------------|
| `vm_compute` | Bytecode evaluation | Trusted VM |
| `native_compute` | OCaml native code | Trusted compiler |
| Extraction | Generate OCaml/Haskell | External code untrusted |
| Axioms | Postulated facts | Potentially inconsistent |

**Reflection** (Rtac): Write tactics in Coq itself, verify they're correct.

---

## Oracle Predicates

### The Concept

An **oracle predicate** is a predicate whose truth is determined by an external source:

```
oracle_plus(A, B, C) :- external_call(plus, [A, B], C).
```

The oracle:
1. Receives a query
2. Returns an answer
3. Is **trusted** to be correct

### Oracle-Based Proof-Carrying Code

From Necula & Lee's PCC work:
> "The proof checker is replaced by a nondeterministic higher-order logic interpreter, and the proof by an oracle implemented as a stream of bits."

The oracle **guides** proof search without being verified.

### Certified Computation

A safer approach: **certifying** oracles.

```
oracle_plus(A, B, C) :-
  external_call(plus, [A, B], C),
  verify_plus(A, B, C).  % Check the answer!
```

The oracle gives an answer; we **verify** it's correct.

For arithmetic: verification is cheap (just check A + B = C).

---

## Design for CALC

### Proposed Architecture

```
┌─────────────────────────────────────────────────────┐
│                    CALC Core                         │
│                                                      │
│  Proof Search Engine                                 │
│  ├── Backward chaining (rules from ll.json)         │
│  ├── Forward chaining (inversion)                   │
│  └── FFI dispatch ◄─────────────────────┐           │
│                                          │           │
└──────────────────────────────────────────┼───────────┘
                                           │
┌──────────────────────────────────────────┼───────────┐
│                    FFI Layer             │           │
│                                          ▼           │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐  │
│  │ Arithmetic  │  │ String ops  │  │ Custom...   │  │
│  │ plus, times │  │ concat, len │  │             │  │
│  └─────────────┘  └─────────────┘  └─────────────┘  │
│                                                      │
└──────────────────────────────────────────────────────┘
```

### Rule Annotation

In `ll.json`, mark rules as FFI:

```json
{
  "name": "Plus",
  "type": "FFI",
  "mode": ["+", "+", "-"],
  "ffi": {
    "function": "arithmetic.plus",
    "verify": true
  },
  "conclusion": "plus($A, $B, $C)"
}
```

### FFI Implementation

```javascript
// lib/ffi/arithmetic.js

const ffi = {
  plus: {
    // Mode: +A +B -C
    compute: (a, b) => {
      // Security: validate inputs
      if (typeof a !== 'number' || typeof b !== 'number') {
        throw new Error('plus: arguments must be numbers');
      }
      return a + b;
    },
    // Optional: verify result
    verify: (a, b, c) => a + b === c
  }
};

module.exports = ffi;
```

### Integration with Proof Search

```javascript
// In proofstate.js

function applyRule(rule, goal) {
  if (rule.type === 'FFI') {
    return applyFFIRule(rule, goal);
  } else {
    return applyLogicalRule(rule, goal);
  }
}

function applyFFIRule(rule, goal) {
  // 1. Extract arguments from goal
  const args = extractArgs(rule.conclusion, goal);

  // 2. Check mode: inputs must be ground
  const inputArgs = rule.mode
    .map((m, i) => m === '+' ? args[i] : null)
    .filter(x => x !== null);

  if (!inputArgs.every(isGround)) {
    // Fall back to proof search or fail
    return null;
  }

  // 3. Call FFI function
  const ffiFunc = loadFFI(rule.ffi.function);
  const inputValues = inputArgs.map(termToValue);
  const outputValue = ffiFunc.compute(...inputValues);

  // 4. Optionally verify
  if (rule.ffi.verify && ffiFunc.verify) {
    const allValues = args.map((a, i) =>
      rule.mode[i] === '-' ? outputValue : termToValue(a)
    );
    if (!ffiFunc.verify(...allValues)) {
      throw new Error('FFI verification failed');
    }
  }

  // 5. Construct result
  const outputArg = args[rule.mode.indexOf('-')];
  return unify(outputArg, valueToTerm(outputValue));
}
```

### Example Usage

```
-- In ll.json or similar:
Rule: plus(A, B, C)  [FFI: arithmetic.plus, mode: +A +B -C]

-- Proof search query:
owns(alice, X, btc), plus(0.3, 0.2, X) ⊢ owns(alice, 0.5, btc)

-- Resolution:
1. Goal: plus(0.3, 0.2, X)
2. FFI dispatch: 0.3 and 0.2 are ground
3. Compute: 0.3 + 0.2 = 0.5
4. Unify: X = 0.5
5. Continue proof search with X = 0.5
```

---

## Security Considerations

### The Trust Boundary

```
┌────────────────────────────────────────┐
│           VERIFIED ZONE                │
│  (Proof search, type checking, etc.)   │
│                                        │
│    ┌────────────────────────────┐      │
│    │    Trust Boundary          │      │
│    └────────────────────────────┘      │
│                 │                      │
│                 ▼                      │
│           TRUSTED ZONE                 │
│    (FFI functions, external oracles)   │
│                                        │
└────────────────────────────────────────┘
```

### What Must Be Trusted

| Component | Trust Assumption |
|-----------|------------------|
| FFI functions | Correctly implement their specification |
| Mode checking | Correctly identifies ground terms |
| Value conversion | Correctly maps terms ↔ JS values |
| Verification | Correctly checks FFI results |

### Mitigation Strategies

1. **Verification**: Always verify FFI results when possible
   ```javascript
   // Cheap for arithmetic
   verify: (a, b, c) => a + b === c
   ```

2. **Type checking**: Ensure inputs match expected types
   ```javascript
   if (typeof a !== 'number') throw new Error(...);
   ```

3. **Sandboxing**: Run FFI in restricted context
   ```javascript
   // No access to filesystem, network, etc.
   ```

4. **Whitelisting**: Only allow pre-approved FFI functions
   ```javascript
   const ALLOWED_FFI = ['arithmetic.plus', 'arithmetic.times', ...];
   ```

5. **Logging**: Record all FFI calls for auditing
   ```javascript
   console.log(`FFI: plus(${a}, ${b}) = ${result}`);
   ```

### The "Just Trust" Model

For your specific use case:
> "mark this rule in the implementation as ffi and write a js function `plus(a,b) { return [a,b, a+b]; }` with correct security checks"

This is the **pragmatic** approach:
- Define which predicates are FFI
- Implement them in JS
- Trust the implementations
- Optionally verify results

The security model is: **"I wrote this FFI, I trust it."**

This is similar to:
- Prolog's built-in `is/2`
- CLP's constraint solvers
- Agda's COMPILE pragmas

---

## Sources

### Mode Checking and Logic Programming

- [Pfenning: Mode and Termination Checking for Higher-Order Logic Programs (ESOP 1996)](https://www.cs.cmu.edu/~fp/papers/esop96.pdf)
- [Twelf User's Guide - Modes](https://www.cs.cmu.edu/~twelf/guide-1-4/twelf_7.html)
- [SWI-Prolog Argument Mode Indicators](https://www.swi-prolog.org/pldoc/man?section=argmode)

### Constraint Logic Programming

- [CLP Wikipedia](https://en.wikipedia.org/wiki/Constraint_logic_programming)
- [SWI-Prolog CLP Documentation](https://www.swi-prolog.org/pldoc/man?section=clp)

### Proof Assistants and FFI

- [Agda FFI Documentation](https://agda.readthedocs.io/en/latest/language/foreign-function-interface.html)
- [Agda Postulates](https://agda.readthedocs.io/en/latest/language/postulates.html)
- [VeriFFI: Verified FFI between Coq and C](https://www.cs.princeton.edu/~appel/papers/VeriFFI.pdf)
- [Coq Evaluation Mechanisms](https://gallium.inria.fr/blog/coq-eval/)

### Oracle-Based Approaches

- [Necula & Lee: Oracle-based Checking of Untrusted Software (POPL 2001)](https://dl.acm.org/doi/10.1145/360204.360216)
- [Trusted Theorem Proving: SLD-Resolution Case Study](https://link.springer.com/chapter/10.1007/978-3-540-88479-8_56)

### Linear Logic Programming

- [Celf System Description](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28)
- [Ceptre: Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf)
- [Forward and Backward Chaining in Linear Logic](https://www.researchgate.net/publication/242793303)

### Trusted Computing Base

- [CompCert TCB Analysis](https://arxiv.org/abs/2201.10280)
- [TCB Wikipedia](https://en.wikipedia.org/wiki/Trusted_computing_base)

## Cross-References

See also in this knowledge base:
- [[nomos]] — Session types (different approach to external state)
- [[QTT]] — Semiring-graded types could inform quantity handling
- [[bibliography]] — Full citations

---

*Last updated: 2026-01-27*
