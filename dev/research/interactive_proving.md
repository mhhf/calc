# Interactive Proving: Tactics, Sledgehammer, and Prover Orchestration

Research on how mature theorem provers handle interactive proving, tactics, and prover orchestration.

---

## Table of Contents

1. [LCF Architecture](#lcf-architecture)
2. [Isabelle: Tacticals and Sledgehammer](#isabelle-tacticals-and-sledgehammer)
3. [Lean4: Tactic Monad](#lean4-tactic-monad)
4. [Coq: Ltac and Ltac2](#coq-ltac-and-ltac2)
5. [Prover Orchestration Patterns](#prover-orchestration-patterns)
6. [Implications for CALC](#implications-for-calc)

---

## LCF Architecture

### The Core Idea

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

### Why It Works

> "However complicated and potentially buggy your code is, if a value of type `theorem` is produced, it has been created through the small trusted interface. Therefore the statement really holds."

The abstract data type guarantees:
- Only the kernel can construct theorem values
- All theorems are derived from axioms via inference rules
- Soundness depends only on the kernel, not on tactics

### Memory Efficiency

The LCF approach eliminates the need to store full proof terms:
- Theorems can optionally store proof objects
- Or just store the proven formula
- Trust comes from the type system, not proof storage

### Systems Using LCF Architecture

- **HOL Family**: HOL4, HOL Light, HOL88
- **Isabelle/HOL**: Successor of HOL
- **Lean**: Dependent type theory with LCF-style kernel
- **Coq**: Uses a variant (proof terms are checked, not generated)

### Sources

- [LCF Architecture - PLS Lab](https://www.pls-lab.org/LCF_architecture)
- [From LCF to Isabelle/HOL (arXiv)](https://arxiv.org/pdf/1907.02836)
- [Logic for Computable Functions - Wikipedia](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)

---

## Isabelle: Tacticals and Sledgehammer

### Tacticals (Tactic Combinators)

Tacticals are **functional combinators** for building complex tactics from simpler ones.

**Basic tacticals:**

| Tactical | ML Syntax | Description |
|----------|-----------|-------------|
| Sequence | `tac1 THEN tac2` | Apply tac1, then tac2 to all resulting goals |
| Choice | `tac1 ORELSE tac2` | Try tac1; if it fails, try tac2 |
| Append | `tac1 APPEND tac2` | Try tac1 and tac2, combine all outcomes |
| Try | `TRY tac` | Try tac; if it fails, do nothing |
| Repeat | `REPEAT tac` | Apply tac as many times as possible |

**Derived tacticals:**
```ml
fun TRY tac = tac ORELSE all_tac;
fun REPEAT tac st = ((tac THEN REPEAT tac) ORELSE all_tac) st;
```

**Block-structured versions:**
```ml
EVERY [tac1, ..., tacn]  ≡  tac1 THEN ... THEN tacn
FIRST [tac1, ..., tacn]  ≡  tac1 ORELSE ... ORELSE tacn
```

**Goal-addressing:**
```ml
ALLGOALS tac   ≡  tac n THEN ... THEN tac 1    (* all goals *)
SOMEGOAL tac   ≡  tac n ORELSE ... ORELSE tac 1  (* any goal *)
FIRSTGOAL tac  ≡  tac 1 ORELSE ... ORELSE tac n  (* first goal *)
```

### Sledgehammer: Parallel Prover Orchestration

Sledgehammer is Isabelle's integration with external automated theorem provers.

**How it works:**
1. User invokes sledgehammer (single mouse gesture)
2. Sledgehammer **translates** the goal to ATP formats (TPTP, SMT-LIB)
3. Sledgehammer **selects relevant lemmas** from the library
4. Multiple provers are invoked **in parallel**
5. **First successful prover wins**, others are terminated
6. Sledgehammer **reconstructs** the proof in Isabelle's native language

**Parallel execution:**
```
┌──────────────┐   ┌──────────────┐   ┌──────────────┐
│      E       │   │    SPASS     │   │   Vampire    │
└──────┬───────┘   └──────┬───────┘   └──────┬───────┘
       │                  │                  │
       └──────────────────┼──────────────────┘
                          │
                          ▼
                  First success wins
                  Others terminated
```

**Configuration:**
```isabelle
sledgehammer [prover = e spass vampire z3] (5 seconds)
```

**Default behavior:**
- E, SPASS, Z3 run locally
- Vampire, SInE run remotely via SystemOnTPTP
- Maximum 5 parallel prover processes
- "Slicing": Different heuristic configurations in parallel

**Empirical results:**
> "Running E, SPASS, and Vampire in parallel for five seconds solves as many problems as running a single theorem prover for two minutes."

### Sources

- [Sledgehammer User's Guide](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf)
- [Three Years of Experience with Sledgehammer](https://www.cl.cam.ac.uk/~lp15/papers/Automation/paar.pdf)
- [Theory Tactic (Isabelle Implementation)](https://proofcraft.systems/isabelle/dist/library/Doc/Implementation/Tactic.html)

---

## Lean4: Tactic Monad

### Monad Hierarchy

Lean4's metaprogramming is organized around a hierarchy of monads:

```
TacticM  ←  TermElabM  ←  MetaM  ←  CoreM
   │            │            │         │
   │            │            │         └─ Environment (declarations)
   │            │            └─ Metavariable context
   │            └─ Elaboration state
   └─ Goal list
```

Each monad extends the ones below it:
- **CoreM**: Access to environment (declarations, imports)
- **MetaM**: Access to metavariables (unification variables)
- **TermElabM**: Elaboration state (expected types, etc.)
- **TacticM**: Current goals

### TacticM Monad

A tactic is a function that processes syntax and updates goals:

```lean
-- A tactic is: Syntax → TacticM Unit
def myTactic : Syntax → TacticM Unit := fun stx => do
  let goal ← getMainGoal
  -- ... manipulate goal ...
  setGoals [newGoal1, newGoal2]
```

**Key operations:**
```lean
getMainGoal : TacticM MVarId        -- Get current goal
getGoals : TacticM (List MVarId)    -- Get all goals
setGoals : List MVarId → TacticM Unit
closeMainGoal : Expr → TacticM Unit -- Prove goal with term
```

### Lifting Between Monads

To use functions from lower monads:
```lean
-- Use MetaM function in TacticM
liftMetaTactic : (MVarId → MetaM (List MVarId)) → TacticM Unit

-- Example: apply a function from MetaM
liftMetaTactic1 fun goal => do
  let (newGoals, _) ← goal.apply expr
  return newGoals
```

### Sources

- [Lean4 Metaprogramming Book - Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)
- [Lean4 Metaprogramming Book - MetaM](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html)
- [Mathlib4 Metaprogramming Wiki](https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-for-dummies)

---

## Coq: Ltac and Ltac2

### Ltac1 (Original)

Ltac1 is Coq's original tactic language. It's dynamically typed and has unusual semantics.

**Problems with Ltac1:**
- Dynamic typing (type errors at runtime)
- Inconsistent semantics
- Tactic Notation is not composable
- Hard to debug

### Ltac2 (Modern Replacement)

Ltac2 is a redesign following the ML tradition:

> "The main goal of Ltac2 is to serve as a meta-language for Coq. As such, it naturally fits in the ML lineage."

**Key features:**
- Static typing (Hindley-Milner)
- Call-by-value evaluation
- Proper exception handling
- Composable syntax extensions

```coq
(* Ltac2 example *)
Ltac2 my_tactic () :=
  match! goal with
  | [ |- ?a = ?b ] => reflexivity
  | [ |- _ ] => fail
  end.
```

### The `constr` Type

Ltac2 has a `constr` type for Coq terms:
- Full access to kernel representation
- Syntactic sugar for term manipulation
- **Well-typedness is checked dynamically** (design choice for compatibility)

### FFI Between Ltac1 and Ltac2

For incremental migration:
```coq
(* Call Ltac1 from Ltac2 *)
Ltac2 call_ltac1 () := ltac1:(my_old_tactic).

(* Call Ltac2 from Ltac1 *)
Ltac my_tactic := ltac2:(my_new_tactic ()).
```

### Sources

- [Ltac2 Documentation (Coq 8.19)](https://rocq-prover.org/doc/V8.19.0/refman/proof-engine/ltac2.html)
- [Ltac2: Tactical Warfare (CoqPL 2019)](https://www.xn--pdrot-bsa.fr/articles/coqpl2019.pdf)
- [Ltac2 Tutorial (GitHub)](https://github.com/tchajed/ltac2-tutorial)

---

## Prover Orchestration Patterns

### Pattern 1: Parallel Race

Run multiple provers in parallel, first success wins.

```
goal ─┬─→ Prover A ─┐
      ├─→ Prover B ─┼─→ First success
      └─→ Prover C ─┘
```

**Used by:** Sledgehammer, CoqHammer

**Implementation:**
```javascript
// Conceptual JavaScript
async function prove(goal) {
  const provers = [proverA, proverB, proverC];
  return Promise.race(provers.map(p => p.prove(goal)));
}
```

### Pattern 2: Tactic Composition

Combine small tactics into larger ones using tacticals.

```
THEN  : tac × tac → tac    -- Sequential
ORELSE: tac × tac → tac    -- Choice
REPEAT: tac → tac          -- Iteration
```

**Used by:** All major proof assistants

### Pattern 3: Translation and Reconstruction

1. Translate goal to external format
2. Call external prover
3. Reconstruct proof in native language

**Used by:** Sledgehammer (translates to TPTP, reconstructs in Isar)

### Pattern 4: Reflection/Computation

Instead of proof search, **compute** the answer and verify.

```
1. Construct a decision procedure as a Coq/Lean program
2. Run it (trusted by kernel's computation rules)
3. Result is a proof by computation
```

**Used by:** Coq's `ring`, `omega`, `lia` tactics

---

## Implications for CALC

### What We Can Learn

1. **LCF Architecture**: Our GenericProver.verify() is the trusted kernel
   - ILLProver produces proof trees (untrusted)
   - GenericProver verifies them (trusted)

2. **Tacticals**: Could implement tactic combinators
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
   ```

3. **Parallel Provers**: Could run GenericProver and ILLProver in parallel
   ```javascript
   async function prove(goal) {
     return Promise.race([
       genericProver.prove(goal),
       illProver.prove(goal)
     ]);
   }
   ```

4. **Monad Structure**: TacticM-style monad for proof state
   ```typescript
   type TacticM<A> = (state: ProofState) => { result: A; newState: ProofState } | null;
   ```

### What We Should NOT Do (Yet)

- **Don't over-engineer**: We have one specialized prover (ILL)
- **Don't add complexity**: YAGNI applies
- **Don't implement Ltac**: Our use case is simpler

### Near-Term Actions

1. Keep GenericProver and ILLProver as separate implementations
2. Add `GenericProver.verify(proofTree)` for checking ILLProver output
3. Consider parallel execution if/when we add more provers

### Long-Term Possibilities

1. Tactic language for user-defined proof strategies
2. External prover integration (E, Vampire via TPTP)
3. Proof reconstruction from external provers

---

## Key Takeaways

| Concept | Description | CALC Relevance |
|---------|-------------|----------------|
| LCF architecture | Trusted kernel + untrusted tactics | GenericProver = kernel, ILLProver = tactic |
| Tacticals | Tactic combinators (THEN, ORELSE) | Could add for composability |
| Sledgehammer | Parallel prover race | Future multi-prover support |
| TacticM monad | Proof state transformation | Possible architecture for tactics |
| Ltac2 | Typed tactic language | Overkill for our needs |

---

*Created: 2026-01-28*
