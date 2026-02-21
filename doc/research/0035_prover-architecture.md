---
title: "Prover Architecture: LCF, Tactics, and Proof Orchestration"
created: 2026-02-10
modified: 2026-02-10
summary: Theorem prover architectures including LCF trusted kernel, tactic languages, Sledgehammer parallel orchestration, and monad hierarchies for proof automation.
tags: [prover-architecture, LCF, tactics, Sledgehammer, automation]
category: "Implementation"
---

# Prover Architecture: LCF, Tactics, and Proof Orchestration

Comprehensive research on theorem prover architectures: LCF style, tactics, Sledgehammer, and how they apply to CALC.

> **See also:** [[ffi-logics]] for oracle/external prover integration, [[backward-prover-optimization]] for proof search optimization, [[clf-celf-ceptre]] for forward chaining patterns.

---

## Table of Contents

1. [LCF Architecture and de Bruijn Criterion](#lcf-architecture-and-de-bruijn-criterion)
2. [Lazy Resource Management for Linear Logic](#lazy-resource-management-for-linear-logic)
3. [Tacticals and Composition](#tacticals-and-composition)
4. [Sledgehammer: Parallel Prover Orchestration](#sledgehammer-parallel-prover-orchestration)
5. [Monad Hierarchies (Lean4, Coq)](#monad-hierarchies)
6. [Architecture Options for CALC](#architecture-options-for-calc)
7. [CALC's Current Implementation](#calcs-current-implementation)
8. [References](#references)

---

## LCF Architecture and de Bruijn Criterion

Two fundamental approaches to proof assistant correctness.

### LCF Architecture

The LCF (Logic for Computable Functions) architecture, developed by Robin Milner in the 1970s, is the foundation of most modern proof assistants.

**Key insight**: Theorems are an **abstract data type**. The only way to create a value of type `theorem` is through the trusted kernel's inference rules.

```
┌─────────────────────────────────────────────────────────────────┐
│                    Untrusted Code                                │
│         User tactics, automation, heuristics                     │
│                                                                  │
│    Can be arbitrarily complex and buggy                          │
│    But can ONLY produce theorems via the kernel                  │
└───────────────────────────┬─────────────────────────────────────┘
                            │ Creates theorem values
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Trusted Kernel                                │
│              Small, verified, implements inference rules         │
│                                                                  │
│    abstract type theorem                                         │
│    val assume : formula -> theorem       (* A ⊢ A *)            │
│    val mp : theorem -> theorem -> theorem  (* modus ponens *)   │
│    ...                                                           │
└─────────────────────────────────────────────────────────────────┘
```

**Why It Works:**
> "However complicated and potentially buggy your code is, if a value of type `theorem` is produced, it has been created through the small trusted interface."

**Memory Efficiency:**
- Theorems store only the proven formula, not full proof objects
- Trust comes from the type system, not proof storage

### de Bruijn Criterion

An alternative approach emphasized by Nicolaas de Bruijn (Automath):

**Definition:** A proof assistant satisfies the de Bruijn criterion if it generates proofs that can be checked independently using a simple program that a skeptical user can write themselves.

| Aspect | LCF Architecture | de Bruijn Criterion |
|--------|-----------------|---------------------|
| **Trust model** | Architecture-based (type system) | Certificate-based (proof objects) |
| **Memory** | Low (no proof storage) | High (full proof objects) |
| **Independent verification** | Requires trusting the kernel | Skeptic writes own checker |
| **Systems** | HOL Light, Isabelle | Coq, Lean (stores proof terms) |

### HOL Light: Minimal Trusted Kernel

HOL Light exemplifies the LCF approach with extreme minimalism:
- **~400 lines** of OCaml for the trusted kernel
- Only **3 axioms** and **10 primitive inference rules**
- **Candle**: Fully verified clone compiled to machine code via CakeML

---

## Lazy Resource Management for Linear Logic

### The Problem: Generic vs Optimized Provers

A **generic structural prover** is simple and correct:
- Pattern-match rules against goals
- Generate premises via substitution
- Backtrack on failure

But it's slow because for context-splitting rules like `Tensor_R: ?X, ?Y |- A * B`, it tries ALL 2^n ways to split the context.

An **optimized prover** (like CALC's focused prover) uses domain knowledge but is complex.

### The Hodas-Miller Approach

From "Logic Programming in a Fragment of Intuitionistic Linear Logic" (1994):

> "The nondeterminism that results from the need to split contexts in order to prove a multiplicative conjunction can be handled by viewing proof search as a **process that takes a context, consumes part of it, and returns the rest**."

### Input/Output Contexts

Instead of guessing how to split upfront:

```
NAIVE (exponential):
  Goal: A, B, C |- D * E
  Try: {} | {A,B,C}     → prove |- D and A,B,C |- E
  Try: {A} | {B,C}      → prove A |- D and B,C |- E
  ... 2^n possibilities

LAZY (linear):
  Goal: A, B, C |- D * E
  delta_in = {A, B, C}   # Available resources

  Step 1: Prove first premise with ALL resources
    A, B, C |- D         # Try to prove D
    delta_out = {B, C}   # A was consumed, B,C left over

  Step 2: Prove second premise with LEFTOVER
    B, C |- E            # delta_out becomes delta_in
    delta_out = {}       # All consumed
```

**Key**: The split is DISCOVERED during proof, not GUESSED upfront.

### Split vs Copy Modes

| Connective | Mode | Behavior |
|------------|------|----------|
| `Tensor_R` | split | First premise gets all, leftover to second |
| `Loli_L` | split | Same |
| `With_R` | copy | Both premises get full context (additive) |

---

## Tacticals and Composition

Tacticals are **functional combinators** for building complex tactics from simpler ones.

### Basic Tacticals (Isabelle)

| Tactical | ML Syntax | Description |
|----------|-----------|-------------|
| Sequence | `tac1 THEN tac2` | Apply tac1, then tac2 to all resulting goals |
| Choice | `tac1 ORELSE tac2` | Try tac1; if it fails, try tac2 |
| Try | `TRY tac` | Try tac; if it fails, do nothing |
| Repeat | `REPEAT tac` | Apply tac as many times as possible |

**Derived tacticals:**
```ml
fun TRY tac = tac ORELSE all_tac;
fun REPEAT tac st = ((tac THEN REPEAT tac) ORELSE all_tac) st;
```

### Potential Tacticals for CALC

```javascript
const THEN = (tac1, tac2) => goal => {
  const result1 = tac1(goal);
  if (!result1.success) return result1;
  return tac2(result1.newGoal);
};

const ORELSE = (tac1, tac2) => goal => {
  const result1 = tac1(goal);
  if (result1.success) return result1;
  return tac2(goal);
};

const REPEAT = (tac) => goal => {
  let current = goal;
  while (true) {
    const result = tac(current);
    if (!result.success) return { success: true, goal: current };
    current = result.newGoal;
  }
};
```

---

## Sledgehammer: Parallel Prover Orchestration

Sledgehammer is Isabelle's integration with external automated theorem provers.

### Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                    User Goal (Isabelle/HOL)                      │
└────────────────────────────┬────────────────────────────────────┘
                             │
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Relevance Filter (MePo/MaSh)                  │
│              Select ~100-500 lemmas from library                 │
└────────────────────────────┬────────────────────────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        ▼                    ▼                    ▼
   ┌─────────┐          ┌─────────┐          ┌─────────┐
   │    E    │          │  SPASS  │          │ Vampire │
   └────┬────┘          └────┬────┘          └────┬────┘
        └────────────────────┼────────────────────┘
                             ▼ First success wins
┌─────────────────────────────────────────────────────────────────┐
│                    Proof Reconstruction (Metis)                  │
│              Verify proof locally in Isabelle                    │
└─────────────────────────────────────────────────────────────────┘
```

**Key insight:**
> "The external provers are essentially used as very precise relevance filters."

Rather than translating ATP proofs directly, Sledgehammer:
1. Extracts which lemmas the ATP used
2. Calls Isabelle's built-in Metis prover with those lemmas
3. Metis finds its own proof using the suggested lemmas

### Relevance Filters

- **MePo** (Meng-Paulson): Symbol-based iterative selection
- **MaSh** (Machine learning): Naive Bayes + k-nearest neighbors
- **MeSh**: Combines MePo and MaSh

### Empirical Results

> "Running E, SPASS, and Vampire in parallel for five seconds solves as many problems as running a single theorem prover for two minutes."

---

## Monad Hierarchies

### Lean4's TacticM Hierarchy

```
TacticM  ←  TermElabM  ←  MetaM  ←  CoreM
   │            │            │         │
   │            │            │         └─ Environment (declarations, imports)
   │            │            └─ Metavariable context (unification variables)
   │            └─ Elaboration state (expected types, pending tactics)
   └─ Goal list (current proof obligations)
```

**Core operations:**
```lean
getMainGoal : TacticM MVarId
getGoals : TacticM (List MVarId)
setGoals : List MVarId → TacticM Unit
closeMainGoal : Expr → TacticM Unit
```

### Coq: Ltac2

Ltac2 is a redesign following the ML tradition with:
- **Hindley-Milner** type inference
- **Call-by-value** evaluation (predictable, unlike Ltac1)
- First-class backtracking via `zero`, `plus`, `case`

---

## Architecture Options for CALC

### Option A: LCF-Style (Proof Trees)

**ILL prover** produces complete proof tree.
**Generic prover** verifies each step.

```
┌─────────────────────────────────────────────────────┐
│              ILL PROVER (Tactic)                     │
│                                                      │
│  Input: Goal sequent                                 │
│  Output: {                                           │
│    success: true,                                    │
│    proofTree: PT { type, premisses, ... },          │
│    delta_out: { resources not consumed },           │
│    theta: [ substitutions ]                         │
│  }                                                   │
└───────────────────────────┬─────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────┐
│            GENERIC PROVER (Kernel)                   │
│                                                      │
│  verifyProofTree(pt):                               │
│    For each node:                                    │
│      1. Check rule name is valid                     │
│      2. Check conclusion matches rule schema         │
│      3. Check premises are correct for rule          │
│      4. Check resources flow correctly               │
│    Return: valid / invalid                           │
└─────────────────────────────────────────────────────┘
```

### Option B: Trust Levels (Recommended)

```javascript
class GenericProver {
  constructor(calculus, options = {}) {
    this.trustLevel = options.trustLevel;  // 'full' | 'verify' | 'none'
    this.oracle = options.oracle;           // ILL prover
  }

  prove(goal) {
    if (this.oracle && this.trustLevel !== 'none') {
      let result = this.oracle.prove(goal);

      if (this.trustLevel === 'full') {
        return result;  // Trust completely
      } else {
        if (this.verifyProofTree(result.proofTree)) {
          return result;
        }
        // Verification failed - fall back
      }
    }
    return this.enumerativeProve(goal);
  }
}
```

**Trust levels:**
- `'full'`: Trust oracle completely (fastest, for production)
- `'verify'`: Check every rule application (medium, for testing)
- `'none'`: Don't use oracle (slowest, for validation)

### Option C: Parallel Provers

```javascript
async function prove(goal) {
  return Promise.race([
    genericProver.prove(goal),
    focusedProver.prove(goal),
    // future: externalATP.prove(goal)
  ]);
}
```

---

## CALC's Current Implementation

CALC already implements key patterns from the research:

### Focusing (lib/prover.js)

```javascript
class FocusedProver {
  // Inversion phase: apply invertible rules eagerly
  getInvertibleRule(pt) { ... }

  // Focus phase: choose a formula to focus on
  chooseFocus(pt) { ... }

  // Identity rules for atoms
  tryIdentityPositive(pt, state) { ... }
  tryIdentityNegative(pt, state) { ... }
}
```

### Proof Search State

```javascript
class ProofSearchState {
  constructor(opts = {}) {
    this.phase = opts.phase || 'inversion';  // 'inversion' | 'focus'
    this.focusPosition = opts.focusPosition || null;  // 'L' | 'R'
    this.focusId = opts.focusId || null;
  }

  focus(position, id) { ... }
  blur() { ... }
  isFocused() { ... }
}
```

### Resource Threading (lib/proofstate.js)

```javascript
let delta = Proofstate.copyMS(pt.delta_in);
let propagate = pt.type === "With_R";

for (let j = 0; j < pt.premisses.length; j++) {
  if (propagate)
    delta = Proofstate.copyMS(pt.delta_in);  // Additive: copy

  let ptp = pt.premisses[j];
  Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);
  let result = Proofstate.auto(ptp, o);

  delta = result.delta_out;  // Multiplicative: leftover
}

pt.delta_out = delta;
```

### Mapping to Research Concepts

| Concept | Research System | CALC Equivalent |
|---------|-----------------|-----------------|
| Trusted kernel | LCF `thm` type | (future) `GenericProver.verify()` |
| Untrusted tactics | Isabelle tactics | `FocusedProver` |
| Metavariables | Lean MetaM | Free variables in sequents |
| Goal list | Lean TacticM | `pt.premisses` |
| Proof state monad | TacticM | `ProofSearchState` |
| Polarity | Andreoli focusing | `lib/polarity.js` |
| Context modes | Split/copy | `inferAllContextModes()` |

---

## References

### LCF and Proof Architectures

- [From LCF to Isabelle/HOL](https://arxiv.org/pdf/1907.02836)
- [de Bruijn criterion vs LCF (Paulson)](https://lawrencecpaulson.github.io/2022/01/05/LCF.html)
- [HOL Light GitHub](https://github.com/jrh13/hol-light)
- [Candle: Verified HOL Light](https://cakeml.org/itp22-candle.pdf)

### Linear Logic Resource Management

- [Hodas & Miller: Logic Programming in ILL](https://www.sciencedirect.com/science/article/pii/S0890540184710364)
- [Cervesato, Hodas, Pfenning: Efficient Resource Management](https://www.cs.cmu.edu/~fp/papers/elp96.pdf)

### Sledgehammer

- [Sledgehammer User's Guide](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf)
- [Three Years of Experience with Sledgehammer](https://www.cl.cam.ac.uk/~lp15/papers/Automation/paar.pdf)

### Monad Hierarchies

- [Lean4 Metaprogramming Book - Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)
- [Ltac2 Documentation](https://rocq-prover.org/doc/V8.19.0/refman/proof-engine/ltac2.html)

### Proof Certificates

- [Foundational Proof Certificates](https://dl.acm.org/doi/10.1145/2503887.2503894)
- [Verified Proof Checking (CakeML)](https://cakeml.org/checkers.html)

---

*Created: 2026-02-10 (merged from proof-search-oracles.md and interactive_proving.md)*
