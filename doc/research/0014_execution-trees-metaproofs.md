---
title: Execution Trees, Metaproofs, and Coinduction
created: 2026-02-11
modified: 2026-02-11
summary: Research on branching execution, metaproof techniques, and fixpoints in linear logic
tags: [research, execution, metaproofs, coinduction, fixed-points]
category: "Related Paradigms"
status: active
---

# Execution Trees, Metaproofs, and Coinduction

Research on three related topics for extending CALC's proof capabilities.

---

## 1. Execution Trees (Proofs Despite Choice)

### Problem Statement

Current forward chaining in CALC runs until **quiescence** (no rules fire) or a **choice** (additive &). At additive choice, forward chaining stops because the consumer picks which branch to take.

**Goal:** Instead of stopping at choice, **branch** and explore all paths, building an **execution tree**.

### Theoretical Background

**Additive Choice (&) Semantics:**
- `A & B` gives **consumer** the choice of A or B
- In focused proof search: negative polarity, invertible
- In forward chaining: non-deterministic branch point

**Related Work:**

1. **Ceptre** (Chris Martens, CMU) - Linear logic programming for games
   - Uses **stages** to structure execution phases
   - Stage ends at **quiescence** (no rules fire)
   - Can run in **interactive mode** (human picks) or **random mode** (engine picks)
   - Generates **trace graphs** showing execution paths

2. **Symbolic Execution** - Explores all program paths
   - At branch: fork execution with separate path constraints
   - Build **computation tree** of all paths
   - Used in model checking, testing, verification

3. **Computation Tree Logic (CTL)** - Branching time logic
   - Models time as tree (multiple futures)
   - Quantifiers: A (all paths), E (exists path)
   - Operators: X (next), F (future), G (globally), U (until)

### Design for CALC

**Execution Tree Structure:**
```
Tree = Leaf State                     -- quiescent state
     | Branch Choice [(Option, Tree)]  -- choice point with subtrees
     | Seq Rule Tree                   -- rule application
```

**Algorithm:**
```
forward_tree(state, rules, opts):
  match findMatch(state, rules):
    | None -> Leaf(state)  -- quiescent
    | Some(rule, theta, consumed) ->
        if rule produces choice (A & B):
          leftBranch = forward_tree(apply(state, left), rules, opts)
          rightBranch = forward_tree(apply(state, right), rules, opts)
          Branch(rule, [(left, leftBranch), (right, rightBranch)])
        else:
          Seq(rule, forward_tree(apply(state, rule, theta), rules, opts))
```

**Key Questions:**
- How to detect choice production? (consequent contains &)
- How to handle resource splitting across branches?
- Memory: branches can explode (exponential)
- Cycle detection: infinite trees from loops

### Implementation Plan

1. **Detect choice in consequent**: Pattern match for `with(A, B)` in rule output
2. **Fork state**: Create copies of state for each branch
3. **Build tree**: Recursive structure with branch metadata
4. **Rendering**: GraphViz dot output (like Ceptre's trace)
5. **Analysis**: Extract all leaf states, check properties

### References

- [Ceptre: A Language for Modeling Generative Interactive Systems](https://ojs.aaai.org/index.php/AIIDE/article/view/12784) (AAAI 2015)
- [Ceptre GitHub/Tutorial](https://github.com/chrisamaphone/interactive-lp/blob/master/tutorial.md)
- [Computation Tree Logic](https://en.wikipedia.org/wiki/Computation_tree_logic)
- [Symbolic Execution Survey](https://arxiv.org/pdf/1610.00502)

---

## 2. Metaproofs (Properties of Linear Logic Programs)

### Problem Statement

What can we prove **about** our linear logic programs, beyond just finding proofs?

**Examples:**
- **Conservation**: Total token supply preserved across all executions
- **Progress**: System can always make a move (no deadlocks)
- **Safety**: Bad states never reachable
- **Termination**: Forward chaining always reaches quiescence
- **Confluence**: Different execution orders same result

### Theoretical Background

**Logical Frameworks (Twelf, Abella):**
- Encode object logic in meta-logic (LF)
- Prove theorems about the encoded logic
- **Adequacy**: encoding is faithful
- **Totality checking**: proves metatheorems

**Linear Logic and Petri Nets:**
- Linear logic formulas ↔ Petri net markings
- Proof search ↔ reachability analysis
- Invariants in linear logic = place invariants in Petri nets

**Key Insight from Girard:**
> "Linear logic allows us to use purely propositional provable sequents to directly formalise the reachability relations in a net."

### Types of Metaproofs for CALC

**1. Conservation Laws:**
```
∀ execution e. total_supply(initial(e)) = total_supply(final(e))
```
Proof technique: Show each rule preserves total (induction on rules).

**2. No Counterfeiting:**
```
∀ token t. t ∈ final(e) → t was minted or t ∈ initial(e)
```
Proof technique: Track provenance through execution.

**3. Reachability:**
```
∃ execution e. initial(e) = S₁ ∧ final(e) = S₂
```
Proof technique: Forward chaining finds witness, or exhaustive search proves unreachable.

**4. Safety (Invariants):**
```
∀ e, s ∈ states(e). invariant(s)
```
Proof technique: Show initial satisfies invariant, each rule preserves it.

### Design for CALC

**Approach 1: Reachability Analysis**
- Build execution tree (Section 1)
- Extract all leaf states
- Check property on each leaf

**Approach 2: Inductive Invariants**
- User specifies invariant I(state)
- Verify: I(initial) ∧ ∀rule. (I(pre) → I(post))
- If verified, I holds on all reachable states

**Approach 3: External Formalization**
- Export CALC rules to Twelf/Abella
- Prove metatheorems in proof assistant
- High assurance but manual effort

### Implementation Plan

1. **State property DSL**: Language to express invariants
2. **Invariant checker**: Verify initial + preservation
3. **Reachability queries**: "Can state S be reached?"
4. **Counter-example generation**: If property fails, show trace

### References

- [Mechanizing Metatheory in a Logical Framework](https://www.cs.cmu.edu/~rwh/papers/mech/jfp07.pdf) (JFP 2007)
- [Formalized Meta-Theory of Sequent Calculi for Linear Logics](https://www.sciencedirect.com/science/article/pii/S030439751930129X)
- [Application of Linear Logic to Backward Reachability Analysis](https://www.academia.edu/6214134/Application_of_linear_logic_to_Backward_Reachability_Analysis_of_Colored_Petri_Nets)
- [The Twelf Proof Assistant](https://link.springer.com/chapter/10.1007/978-3-642-03359-9_7)

---

## 3. Induction and Coinduction in Linear Logic

### Problem Statement

How to handle **unbounded** and **infinite** behavior in CALC?

- **Induction**: Finite iteration, well-founded recursion
- **Coinduction**: Infinite streams, productive corecursion

### Theoretical Background

**μMALL: Linear Logic with Fixed Points**

Baelde & Miller (2007) extended MALL with least (μ) and greatest (ν) fixed points:

```
μX. F(X)   -- least fixed point (inductive)
νX. F(X)   -- greatest fixed point (coinductive)
```

**Key properties:**
- Cut-elimination holds
- Complete focused proof system
- Decidability: undecidable in general (Π⁰₁-hard)

**Cyclic Proofs:**
- Allow proof trees with back-edges
- Global correctness condition: "progressing criterion"
- Trades inductive invariant complexity for richer proof structure
- Facilitates automation

**Induction/Coinduction Duality:**

| Induction | Coinduction |
|-----------|-------------|
| Least fixed point μ | Greatest fixed point ν |
| Finite structures | Infinite structures |
| Elimination rule | Introduction rule |
| Termination | Productivity |

### Applications to CALC

**1. Recursive Contract Definitions:**
```
streaming_payment P A B =
  νX. (pay P A B ⊗ delay ⊗ X)
```
Coinductive: infinite stream of payments.

**2. Termination Proofs:**
For EVM execution:
```
∀ program p. terminates(p) ∨ loops_forever(p)
```
Need induction on gas/step count.

**3. Invariant Induction:**
```
invariant(s) = μI. (initial(s) ∨ (∃rule. prev(s) ∧ I(prev)))
```
Inductively define "reachable states satisfy invariant."

**4. Bisimulation for Equivalence:**
Two contracts equivalent if bisimilar:
```
contract₁ ≈ contract₂ iff ν(bisimulation relation)
```

### Design for CALC

**Approach 1: Explicit Fixed Points in Logic**
- Add μ, ν connectives to formula language
- Extend proof search for fixed points
- Use focusing to guide unfolding

**Approach 2: Cyclic Proof Engine**
- Allow proofs with back-edges
- Check global progress condition
- More automation-friendly

**Approach 3: Bounded Model Checking**
- Unfold fixed points to depth k
- Find bugs without full proof
- Incomplete but practical

### Implementation Plan

1. **Cycle detection**: Detect when forward chaining revisits state
2. **Bounded exploration**: Limit tree depth, report if bound reached
3. **Fixed point syntax**: Add μ, ν to formula grammar
4. **Progress checking**: Verify cyclic proofs are valid

### References

- [Least and Greatest Fixed Points in Linear Logic](https://dl.acm.org/doi/abs/10.1145/2071368.2071370) (ACM TOCL 2012)
- [Non-well-founded Deduction for Induction and Coinduction](https://link.springer.com/chapter/10.1007/978-3-030-79876-5_1)
- [Cyclic Proofs, Hypersequents, and Transitive Closure Logic](https://link.springer.com/chapter/10.1007/978-3-031-10769-6_30)
- [Bedwyr System for Model Checking](https://link.springer.com/chapter/10.1007/978-3-540-75560-9_9)
- [Practical Coinduction](https://www.cs.cornell.edu/~kozen/Papers/Structural.pdf)

---

## Connections and Synthesis

These three topics are deeply connected:

1. **Execution trees** provide the **raw data** for metaproofs
2. **Metaproofs** establish **properties** that hold across all branches
3. **Coinduction** handles **infinite** execution trees (productive streams)

**Unified View:**

```
                    ┌─────────────────┐
                    │  CALC Program   │
                    │   (LL rules)    │
                    └────────┬────────┘
                             │
              ┌──────────────┼──────────────┐
              │              │              │
              ▼              ▼              ▼
        ┌──────────┐   ┌──────────┐   ┌──────────┐
        │ Execution │   │  Fixed   │   │   Meta   │
        │   Tree    │   │  Points  │   │  Proofs  │
        │ (finite)  │   │ (μ, ν)   │   │ (about)  │
        └──────────┘   └──────────┘   └──────────┘
              │              │              │
              │              │              │
              ▼              ▼              ▼
        ┌──────────┐   ┌──────────┐   ┌──────────┐
        │  Model   │   │ Infinite │   │ Safety   │
        │ Checking │   │ Behavior │   │ Proofs   │
        └──────────┘   └──────────┘   └──────────┘
```

**Proposed Implementation Order:**

1. **Execution trees** (most concrete, builds on current forward chaining)
2. **Simple metaproofs** (reachability, invariant checking)
3. **Cycle detection** (prerequisite for coinduction)
4. **Fixed points** (extends the logic itself)

---

## Open Questions

1. **Memory efficiency**: How to represent exponentially branching trees?
   - Incremental/lazy exploration?
   - Sharing common prefixes?
   - BDDs for state sets?

2. **Cycle detection**: What equivalence for "same state"?
   - Exact hash equality?
   - Modulo permutation of resources?
   - Bisimulation?

3. **Fixed point syntax**: How to integrate with current parser?
   - New connectives μ, ν?
   - Recursive rule definitions?
   - Both?

4. **Verification vs exploration**:
   - Bounded model checking (find bugs)?
   - Full verification (prove absence of bugs)?
   - Hybrid?
