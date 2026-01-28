# Interactive Proving: Tactics, Sledgehammer, and Prover Orchestration

Deep research on how mature theorem provers handle interactive proving, tactics, and prover orchestration.

---

## Table of Contents

1. [LCF Architecture and de Bruijn Criterion](#lcf-architecture-and-de-bruijn-criterion)
2. [Isabelle: Tacticals and Sledgehammer](#isabelle-tacticals-and-sledgehammer)
3. [Lean4: Tactic Monad and Metaprogramming](#lean4-tactic-monad-and-metaprogramming)
4. [Coq: Ltac and Ltac2](#coq-ltac-and-ltac2)
5. [Twelf: Logic Programming and Totality Checking](#twelf-logic-programming-and-totality-checking)
6. [Prover Orchestration Patterns](#prover-orchestration-patterns)
7. [Relation to CALC Codebase](#relation-to-calc-codebase)
8. [Key Takeaways](#key-takeaways)

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
> "However complicated and potentially buggy your code is, if a value of type `theorem` is produced, it has been created through the small trusted interface. Therefore the statement really holds."

**Memory Efficiency:**
- Theorems store only the proven formula, not full proof objects
- Trust comes from the type system, not proof storage
- This was crucial for 1970s memory constraints; still valuable for large proofs

### de Bruijn Criterion

An alternative approach emphasized by Nicolaas de Bruijn (Automath):

**Definition:** A proof assistant satisfies the de Bruijn criterion if it generates proofs that can be checked independently using a simple program that a skeptical user can write themselves.

**Key difference from LCF:**
- **LCF**: Proofs are correct by construction (abstract type enforcement)
- **de Bruijn**: Proofs are certificates that can be independently verified

### Comparison

| Aspect | LCF Architecture | de Bruijn Criterion |
|--------|-----------------|---------------------|
| **Trust model** | Architecture-based (type system) | Certificate-based (proof objects) |
| **Memory** | Low (no proof storage) | High (full proof objects) |
| **Independent verification** | Requires trusting the kernel | Sceptic writes own checker |
| **Systems** | HOL Light, Isabelle | Coq, Lean (stores proof terms) |

### HOL Light: Minimal Trusted Kernel

HOL Light exemplifies the LCF approach with extreme minimalism:
- **~400 lines** of OCaml for the trusted kernel
- Only **3 axioms** and **10 primitive inference rules**
- **Candle**: Fully verified clone compiled to machine code via CakeML

### Systems Using Each Approach

**LCF Architecture:**
- HOL Light, HOL4, HOL88
- Isabelle/HOL

**de Bruijn Criterion (proof terms stored):**
- Coq (Calculus of Inductive Constructions)
- Lean (dependent type theory)
- Agda

**Both (hybrid):**
- Modern Lean stores proof terms but also has a small trusted kernel

### Sources

- [LCF Architecture - PLS Lab](https://www.pls-lab.org/LCF_architecture)
- [de Bruijn criterion vs LCF (Paulson)](https://lawrencecpaulson.github.io/2022/01/05/LCF.html)
- [From LCF to Isabelle/HOL (arXiv)](https://arxiv.org/pdf/1907.02836)
- [Logic for Computable Functions - Wikipedia](https://en.wikipedia.org/wiki/Logic_for_Computable_Functions)
- [HOL Light GitHub](https://github.com/jrh13/hol-light)
- [Candle: Verified HOL Light](https://cakeml.org/itp22-candle.pdf)

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

**Architecture Overview:**
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
                             ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Translation to TPTP/SMT-LIB                   │
│              HOL → First-Order Logic                             │
└────────────────────────────┬────────────────────────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
   ┌─────────┐          ┌─────────┐          ┌─────────┐
   │    E    │          │  SPASS  │          │ Vampire │
   └────┬────┘          └────┬────┘          └────┬────┘
        │                    │                    │
        └────────────────────┼────────────────────┘
                             │
                             ▼ First success wins
┌─────────────────────────────────────────────────────────────────┐
│                    Proof Reconstruction (Metis)                  │
│              Verify proof locally in Isabelle                    │
└─────────────────────────────────────────────────────────────────┘
```

**How it works:**
1. **Relevance Filtering**: Heuristically select relevant lemmas
2. **Translation**: Convert goal to first-order logic (TPTP format)
3. **Parallel Execution**: Run multiple ATPs simultaneously
4. **First Success Wins**: Terminate other provers when one succeeds
5. **Proof Reconstruction**: Re-prove using Metis with found lemmas

**Relevance Filters:**
- **MePo** (Meng-Paulson): Symbol-based iterative selection
  - Starts with goal's symbols, expands iteratively
  - Weights unusual constants higher for discrimination
- **MaSh** (Machine learning): Naive Bayes + k-nearest neighbors
  - Learns from previous successful proofs
- **MeSh**: Combines MePo and MaSh

**Proof Reconstruction:**
> "The external provers are essentially used as very precise relevance filters."

Rather than translating ATP proofs directly, Sledgehammer:
1. Extracts which lemmas the ATP used
2. Calls Isabelle's built-in Metis prover with those lemmas
3. Metis finds its own proof using the suggested lemmas

**Slicing Technique:**
Run the same prover with different heuristic configurations in parallel. Different configurations excel on different problems.

**Empirical Results:**
> "Running E, SPASS, and Vampire in parallel for five seconds solves as many problems as running a single theorem prover for two minutes."

### Sources

- [Sledgehammer User's Guide](https://isabelle.in.tum.de/dist/doc/sledgehammer.pdf)
- [Three Years of Experience with Sledgehammer](https://www.cl.cam.ac.uk/~lp15/papers/Automation/paar.pdf)
- [Sledgehammer: Some History, Some Tips (Paulson)](https://lawrencecpaulson.github.io/2022/04/13/Sledgehammer.html)
- [Extending Sledgehammer with SMT Solvers](https://www.cl.cam.ac.uk/~lp15/papers/Automation/jar-smt.pdf)

---

## Lean4: Tactic Monad and Metaprogramming

### Monad Hierarchy

Lean4's metaprogramming is organized around a hierarchy of monads:

```
TacticM  ←  TermElabM  ←  MetaM  ←  CoreM
   │            │            │         │
   │            │            │         └─ Environment (declarations, imports)
   │            │            └─ Metavariable context (unification variables)
   │            └─ Elaboration state (expected types, pending tactics)
   └─ Goal list (current proof obligations)
```

Each monad extends the ones below it via transformer stacking.

### CoreM: Environment Access

```lean
CoreM -- Access to:
  - Environment (all declared constants, theorems)
  - Options (configuration)
  - Name generation (fresh names)
```

### MetaM: Metavariable Context

Metavariables are the central concept:
- **As holes**: Placeholders in expressions (like `?x` in unification)
- **As goals**: Proof obligations to be filled

```lean
MetaM -- Access to:
  - Metavariable assignments
  - Local context (hypotheses in scope)
  - Unification (isDefEq)

-- Key operations:
mkFreshExprMVar : Expr → MetaM MVarId    -- Create new metavariable
assign : MVarId → Expr → MetaM Unit       -- Fill in a metavariable
isDefEq : Expr → Expr → MetaM Bool        -- Unification
```

**Metavariable Kinds:**
- **Natural**: Freely assignable
- **Synthetic**: Assignment-avoiding (for certain elaboration patterns)
- **Synthetic Opaque**: Never assignable

### TermElabM: Elaboration State

```lean
TermElabM -- Access to:
  - Expected types
  - Pending elaboration problems
  - Pending tactics to execute
```

Used for writing term elaborators (`elab` methods for custom syntax).

### TacticM: Goal Manipulation

```lean
-- TacticM is essentially: ReaderT Context $ StateRefT State TermElabM

-- Core operations:
getMainGoal : TacticM MVarId           -- Get current goal
getGoals : TacticM (List MVarId)       -- Get all goals
setGoals : List MVarId → TacticM Unit  -- Set goal list
closeMainGoal : Expr → TacticM Unit    -- Prove goal with term
replaceMainGoal : List MVarId → TacticM Unit
```

**Accessing Hypotheses:**
```lean
Lean.Elab.Tactic.withMainContext do
  let ctx ← Lean.MonadLCtx.getLCtx
  ctx.forM fun decl: Lean.LocalDecl => do
    let declType ← Lean.Meta.inferType decl.toExpr
    -- ... use declType ...
```

**Error Handling:**
```lean
Lean.Meta.throwTacticEx `tacticName goal
  (m!"error message with delaboration support")
```

### Lifting Between Monads

```lean
-- Use MetaM function in TacticM
liftMetaTactic : (MVarId → MetaM (List MVarId)) → TacticM Unit

-- Example: apply a term to the goal
liftMetaTactic1 fun goal => do
  let (newGoals, _) ← goal.apply expr
  return newGoals
```

### Backtracking

All three main monads (MetaM, TermElabM, TacticM) support backtracking:
```lean
saveState : MetaM SavedState
restoreState : SavedState → MetaM Unit
observing? : MetaM α → MetaM (Option α)  -- Auto-backtrack on failure
```

### Implementing Custom Tactics

**Three approaches:**
1. **macro_rules**: Syntax-to-syntax translation
2. **elab_rules**: Direct tactic elaboration with TacticM
3. **elab**: Shorthand combining syntax + elab_rules

```lean
-- Using elab
elab "my_tactic" : tactic => do
  let goal ← getMainGoal
  -- manipulate goal...
  replaceMainGoal [newGoal]
```

### Sources

- [Lean4 Metaprogramming Book - Tactics](https://leanprover-community.github.io/lean4-metaprogramming-book/main/09_tactics.html)
- [Lean4 Metaprogramming Book - MetaM](https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html)
- [Mathlib4 Metaprogramming Wiki](https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-for-dummies)
- [Mathlib4 Monad Map](https://github.com/leanprover-community/mathlib4/wiki/Monad-map)

---

## Coq: Ltac and Ltac2

### Ltac1 (Original)

Ltac1 is Coq's original tactic language. It's dynamically typed and has unusual semantics.

**Problems with Ltac1:**
- Dynamic typing (type errors at runtime)
- Inconsistent, heuristic-based evaluation semantics
- Tactic Notation is not composable
- Hard to debug

### Ltac2 (Modern Replacement)

Ltac2 is a redesign following the ML tradition:

> "The main goal of Ltac2 is to serve as a meta-language for Coq. As such, it naturally fits in the ML lineage."

**Type System:**
- **Hindley-Milner** type inference
- Strict typing (no runtime type casts)
- Built-in types: `int`, `string`, `'a array`, `exn`, `constr`, `pattern`, `ident`
- Algebraic datatypes, records, open variants

**Evaluation Semantics:**
- **Call-by-value** (like OCaml), not call-by-need
- Requires explicit thunks for delayed computation
- Predictable, unlike Ltac1's heuristic evaluation

**Effects Model:**

Three categories of effects:
1. **Non-backtracking IO**: Mutable fields, array mutation, printing
2. **Fatal errors**: Non-recoverable exceptions via `throw`
3. **Backtracking**: First-class via `zero`, `plus`, `case`

```coq
(* Backtracking example *)
Ltac2 my_choice () :=
  Control.plus
    (fun () => (* first alternative *))
    (fun () => (* second alternative *)).
```

**Quotations (Meta/Object Level Separation):**
- `'[term]` → Open constructor terms (holes allowed)
- `constr:(expr)` → Closed terms
- `pat:(pattern)` → Term patterns for matching
- `@ident` → Identifier quotation

**Key Differences from Ltac1:**

| Feature | Ltac1 | Ltac2 |
|---------|-------|-------|
| **Type System** | Dynamic | Static (Hindley-Milner) |
| **Evaluation** | Heuristic | Call-by-value |
| **Parsing** | Implicit meta/object | Explicit quotations |
| **Data Structures** | Limited | Full ML-style |
| **Debugging** | Difficult | Proper exceptions |

### The `constr` Type

Ltac2 has a `constr` type for Coq terms:
- Full access to kernel representation
- Syntactic sugar for seamless manipulation
- **Well-typedness checked dynamically** (design choice for Ltac1 compatibility)

### FFI Between Ltac1 and Ltac2

```coq
(* Call Ltac1 from Ltac2 *)
Ltac2 call_ltac1 () := ltac1:(my_old_tactic).

(* Call Ltac2 from Ltac1 *)
Ltac my_tactic := ltac2:(my_new_tactic ()).
```

### CoqHammer

Like Sledgehammer, CoqHammer integrates external ATPs with Coq:

**Architecture:**
1. **sauto**: General proof search based on CIC inhabitation
2. **ATP translation**: Goal → first-order logic
3. **Proof reconstruction**: Specialized tactics rebuild proofs

**Performance:**
- 39.1% success rate on Coq libraries
- 25.6% on CompCert
- 87-97% reconstruction success rate (from ATPs that succeed)

**Limitations:**
- Poor on non-first-order features (HOF, boolean reflection, dependent types)
- Never performs induction automatically

### Sources

- [Ltac2 Documentation (Coq 8.19)](https://rocq-prover.org/doc/V8.19.0/refman/proof-engine/ltac2.html)
- [Ltac2: Tactical Warfare (CoqPL 2019)](https://www.xn--pdrot-bsa.fr/articles/coqpl2019.pdf)
- [CoqHammer GitHub](https://github.com/lukaszcz/coqhammer)
- [Hammer for Coq (JAR)](https://link.springer.com/article/10.1007/s10817-018-9458-4)

---

## Twelf: Logic Programming and Totality Checking

Twelf takes a fundamentally different approach from LCF-style provers.

### Core Idea

Twelf encodes logics in the LF (Logical Framework) type theory. Proofs are:
1. **Encoded** as LF terms (judgments-as-types)
2. **Executed** as logic programs (backward chaining)
3. **Verified** via totality checking (coverage + termination + mode)

### Logic Programming Interpretation

Twelf signatures are interpreted as logic programs:

```twelf
nat : type.
z : nat.
s : nat -> nat.

plus : nat -> nat -> nat -> type.
plus/z : plus z N N.
plus/s : plus (s M) N (s P) <- plus M N P.
```

**Operational semantics:** Backward chaining with unification
- Each `<-` introduces a subgoal
- Each `Π` introduces dynamic parameters

**Key differences from Prolog:**
- **Clause selection**: Local assumptions first, then global (most recent → oldest)
- **Subgoal selection**: Inside-out, not left-to-right
- **No cut**: Uses `%deterministic` declarations instead

### Mode Checking

Mode declarations specify information flow:
```twelf
%mode plus +M +N -P.
```
- `+` = input (must be ground when called)
- `-` = output (will be ground after success)
- `*` = unrestricted

Mode checking verifies that all calls respect these constraints.

### Totality Checking

The `%total` declaration verifies that a relation is total:

```twelf
%total M (plus M N P).
```

**Three components:**
1. **Input coverage**: Every possible ground input has at least one matching case
2. **Output coverage**: Outputs are sufficiently general (no spurious pattern matching)
3. **Termination**: Recursive calls are on structurally smaller inputs

**Key insight:**
> "Twelf can be thought of as a 'theorem prover' in the limited sense that it proves that a relation is total by doing program analysis."

### Theorem Prover (∀∃-Statements)

For metatheorems that don't fit totality checking:

```twelf
%theorem plus-comm :
  forall* {N1: nat}{N2: nat}{N3: nat}
  forall {D1: plus N1 N2 N3}
  exists {D2: plus N2 N1 N3}
  true.

%prove 5 D1 (plus-comm D1 D2).
```

**Note:** The theorem prover is "buggy, sometimes does not terminate" — totality checking is preferred.

### Effectiveness Lemmas

When automatic totality checking fails:
1. Write an explicit **effectiveness lemma** (LF type family)
2. Prove it satisfies totality manually
3. Use it as a building block for more complex proofs

### Sources

- [Twelf Theorem Prover Wiki](https://twelf.org/wiki/theorem-prover/)
- [Twelf Logic Programming Guide](https://www.cs.cmu.edu/~twelf/guide-1-4/twelf_5.html)
- [Coverage Checking Wiki](https://twelf.org/wiki/coverage-checking/)
- [System Description: Twelf (CADE'99)](https://www.cs.cmu.edu/~fp/papers/cade99.pdf)

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
async function prove(goal) {
  const provers = [proverA, proverB, proverC];
  const controller = new AbortController();

  try {
    return await Promise.race(
      provers.map(async p => {
        const result = await p.prove(goal, controller.signal);
        controller.abort(); // Cancel others
        return result;
      })
    );
  } catch (e) {
    controller.abort();
    throw e;
  }
}
```

### Pattern 2: Tactic Composition (Tacticals)

Combine small tactics into larger ones:

```
THEN  : tac × tac → tac    -- Sequential
ORELSE: tac × tac → tac    -- Choice (backtracking)
REPEAT: tac → tac          -- Iteration
TRY   : tac → tac          -- Optional (never fails)
```

**Used by:** All major proof assistants

### Pattern 3: Translation and Reconstruction

1. Translate goal to external format (TPTP, SMT-LIB)
2. Call external prover
3. Reconstruct proof in native language

**Key insight from Sledgehammer:**
Don't try to translate the external proof directly. Instead:
- Use the ATP as a "lemma finder"
- Extract which facts the ATP used
- Re-prove locally with a native prover (Metis)

### Pattern 4: Relevance Filtering

Before calling external provers, filter the knowledge base:
- Symbol-based (MePo): Follow constant references
- Machine learning (MaSh): Learn from past proofs
- Hybrid: Combine both

### Pattern 5: Slicing

Run the same prover with different heuristic configurations:
- Different timeout slices
- Different search strategies
- Different lemma selections

### Pattern 6: Reflection/Computation

Instead of proof search, **compute** the answer:
1. Define a decision procedure as a program
2. Run it (trusted by kernel's computation rules)
3. Result is a proof by computation

**Used by:** Coq's `ring`, `omega`, `lia` tactics

---

## Relation to CALC Codebase

### Current Architecture

CALC already implements key patterns from the research:

**1. Focusing (Andreoli) in `lib/prover.js`:**
```javascript
// From prover.js - FocusedProver class
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

This corresponds to Lean's tactic phases but is specialized for linear logic.

**2. Proof State Monad in `lib/prover.js`:**
```javascript
// ProofSearchState - tracks phase and focus
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

This is analogous to Lean's `TacticM` — a monad tracking proof state.

**3. Unification in `lib/mgu.js`:**
```javascript
// Most general unifier - like MetaM's isDefEq
const mgu = function (G) {
  var theta = [];
  while (G.length > 0) {
    let [t0, t1] = G.pop();
    // ... standard unification algorithm ...
  }
  return theta;
}
```

**4. Multi-Type Context in `lib/sequent.js`:**
```javascript
class Sequent {
  constructor(params) {
    this.persistent_ctx = params?.persistent_ctx || {};  // Cartesian type (!)
    this.linear_ctx = params?.linear_ctx || {};          // Linear type
    this.succedent = params?.succedent || {};
  }
}
```

This implements Benton's LNL (Linear/Non-Linear) calculus — already multi-type!

### Mapping Research Concepts to CALC

| Concept | Research System | CALC Equivalent |
|---------|-----------------|-----------------|
| Trusted kernel | LCF `thm` type | (future) `GenericProver.verify()` |
| Untrusted tactics | Isabelle tactics | `FocusedProver` |
| Metavariables | Lean MetaM | Free variables in sequents |
| Goal list | Lean TacticM | `pt.premisses` |
| Proof state monad | TacticM | `ProofSearchState` |
| Backtracking | Ltac2 `plus`/`zero` | Nondeterministic choice in `auto()` |
| Polarity | Andreoli focusing | `lib/polarity.js` |
| Context modes | Split/copy | `inferAllContextModes()` |

### Future Directions Informed by Research

**1. LCF-Style Verification (from HOL Light):**
```javascript
// Add to GenericProver
verify(proofTree) {
  // For each node, check:
  // 1. Rule name is valid
  // 2. Conclusion matches rule conclusion (under substitution)
  // 3. Premises match rule premises
  // 4. Resource flow is valid (delta_in ⊇ delta_out)
}
```

**2. Tacticals (from Isabelle):**
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

**3. Parallel Provers (from Sledgehammer):**
```javascript
async function prove(goal) {
  return Promise.race([
    genericProver.prove(goal),
    focusedProver.prove(goal),
    // future: externalATP.prove(goal)
  ]);
}
```

**4. Monad Hierarchy (from Lean4):**

If we formalize the architecture:
```typescript
// Core layer - environment access
type CoreM<A> = (env: Calculus) => A | null;

// Meta layer - metavariable context
type MetaM<A> = (state: { env: Calculus, subst: Substitution[] }) => A | null;

// Tactic layer - goal manipulation
type TacticM<A> = (state: ProofSearchState) => { result: A, newState: ProofSearchState } | null;
```

### What We Should NOT Do (Yet)

- **Don't implement Ltac**: Our use case is simpler
- **Don't add SMT integration**: YAGNI until needed
- **Don't over-engineer monad stack**: Current ProofSearchState is sufficient
- **Don't add proof reconstruction**: Only when we have external provers

---

## Key Takeaways

| Concept | Description | CALC Relevance |
|---------|-------------|----------------|
| **LCF architecture** | Trusted kernel via abstract type | Future GenericProver.verify() |
| **de Bruijn criterion** | Independent proof checking | Alternative to LCF if we store proof terms |
| **Tacticals** | Tactic combinators (THEN, ORELSE) | Could add for composability |
| **Sledgehammer** | Parallel prover race + reconstruction | Future multi-prover support |
| **TacticM monad** | Proof state transformation | Already have ProofSearchState |
| **MetaM / unification** | Metavariable management | Already have mgu.js |
| **Ltac2** | Typed tactic language | Overkill for our needs |
| **Twelf totality** | Verification by program analysis | Interesting alternative to proof search |
| **Relevance filtering** | Lemma selection for ATPs | Future external prover integration |

### Key Architectural Insights

1. **Separate concerns**: Kernel (correctness) vs. tactics (usability)
2. **Don't reinvent**: Use external ATPs as "lemma finders"
3. **Parallel wins**: Multiple provers beat any single prover
4. **Backtracking matters**: All major systems support it
5. **Polarity/focusing**: Reduces proof search dramatically (we have this!)
6. **Multi-type DC**: Natural fit for ! modality (we have this!)

---

*Created: 2026-01-28*
*Updated: 2026-01-28 (extended with deep research)*
