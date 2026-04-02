---
title: "Granularity in Petri Nets and Multiset Rewriting: Fine-Grained vs Coarse-Grained Rules"
created: 2026-04-02
modified: 2026-04-02
summary: "Theory and practical tradeoffs between fine-grained (many small transitions) and coarse-grained (one big transition) rule designs in Petri nets and linear logic multiset rewriting, with application to EVM symbolic execution."
tags: [linear-logic, multiset-rewriting, Petri-nets, forward-chaining, evm, symbolic-execution, concurrency, category-theory, quiescence]
category: "Forward Chaining"
---

# Granularity in Petri Nets and Multiset Rewriting

## The Question

In an EVM symbolic execution model, two designs exist:

**Fine-grained (A):** Separate resources for each state component — `pc PC`, `gas GAS`, `stack S`, `mem M`, `bytecode BC`. Each EVM rule mentions only what it needs (e.g., `evm/add` touches `pc`, `gas`, `stack` but not `mem`).

**Coarse-grained (B):** One resource `step(PC, GAS, STACK, MEM, BYTECODE)` containing everything. Every rule replaces the entire step tuple.

Why not use design B?

---

## 1. Petri Net Theory: Place Refinement

### 1.1 What the literature says

The correspondence between linear logic and Petri nets (Engberg & Winskel 1990; Kanovich 1995; Meseguer & Montanari 1990) maps:
- linear facts → tokens on places
- forward rules → transitions
- multiset states → markings

In this framework, **place granularity** is directly the question: how many distinct places should exist?

**Murata (1989, "Petri Nets: Properties, Analysis and Applications")** states the fundamental principle: "The degree to which transitions in a net are independent is determined by the structure of the pre- and post-sets." Two transitions are **independent** (can fire concurrently in any order — the diamond property) iff their pre-sets are disjoint (they consume no shared places). Coarse-graining places merges pre-sets, turning independent transitions into sequential ones.

**Place refinement** (also called "place splitting") is the operation of decomposing a single place `P` into multiple places `P₁, P₂, ...`. The inverse is **place fusion**. Berthelot (1987, "Transformations and Decompositions of Nets") establishes:
- Place fusion preserves reachability but can destroy liveness and boundedness properties.
- Place refinement preserves liveness if the refinement respects the invariants of the original net.

### 1.2 The Concurrency Measure

The **concurrency degree** of a Petri net (Karp & Miller 1969) is the maximum number of transitions that can fire simultaneously in any reachable marking. Fine-grained places maximize this:

- In design A: `evm/add` and a storage rule can potentially fire on different resources concurrently (if the EVM model is extended to interleaving steps). The pre-sets are disjoint when the rules touch different components.
- In design B: every transition consumes `step(...)`, so at most one transition can fire at a time. The net is **sequential** by construction.

For single-threaded EVM execution this doesn't matter operationally. But it matters for **compositional reasoning**: if two independent contracts are placed in the same state, fine-grained resources allow their rules to be composed without interference (disjoint pre-sets). Coarse-grained resources force artificial serialization.

---

## 2. State Space and the Reachability Graph

### 2.1 Does granularity affect the state space size?

**Claim:** Granularity does not directly change the number of *distinct reachable states* (assuming the same program logic). What it changes is the *shape of the reachability graph* — specifically, whether independent transitions produce a diamond or a chain.

**Fine-grained diamond property:**
```
State s = { pc PC, gas GAS, stack S, mem M }

Rule r1: pc PC -o { pc PC' }        (only modifies pc)
Rule r2: gas GAS -o { gas GAS' }    (only modifies gas)

r1 and r2 are independent: both can fire from s.
s --r1--> s' = { pc PC', gas GAS, stack S, mem M }
s --r2--> s'' = { pc PC, gas GAS', stack S, mem M }
s' --r2--> t = { pc PC', gas GAS', stack S, mem M }
s'' --r1--> t   (same t — diamond closes)
```

The reachability graph has 4 states and 4 edges. The states `s'` and `s''` are genuinely distinct intermediate states, but they both lead to the same terminal state `t`.

**Coarse-grained:** Both modifications must be bundled into a single rule touching `step(...)`. There is no intermediate state. The reachability graph has 2 states and 1 edge. *The intermediate states disappear.*

Consequence for exhaustive exploration: **fine-grained models produce larger exploration trees** due to intermediate states that exist only because of the ordering of rule applications. The coarse-grained model produces a smaller tree by eliminating this order-of-application nondeterminism.

This is the key tradeoff: the fine-grained tree overapproximates the true state space with redundant intermediate states; the coarse-grained tree eliminates them. However, **both models produce the same set of terminal states** if the rules are equivalent.

### 2.2 The Diamond Property as Confluence

The diamond property (Meseguer & Montanari 1990) says: for concurrent multiset rewriting, if two rules fire independently on disjoint resources, the order doesn't matter. The reachability graph contains diamonds, not just chains.

For symbolic execution, these diamonds are **redundant paths** to the same state. CALC's `explore()` already handles this via cycle detection (`pathVisited`), but the intermediate states still appear as nodes in the tree, causing branching overhead.

The coarse-grained model collapses all diamonds by removing the intermediate states entirely, yielding a smaller tree. This is a genuine practical advantage for exhaustive exploration.

---

## 3. Composability and Modularity

### 3.1 The conservative extension argument

Adding a new state dimension in design A (e.g., `storage K V`) requires:
1. Adding the new resource type declaration
2. Adding rules that use `storage`

**No existing rules change.** Rules that don't touch storage simply don't mention it. This is a **conservative extension** in the sense of RES_0099: the new types are purely additive; existing rules remain valid.

In design B:
1. The `step` type must be extended to `step(PC, GAS, STACK, MEM, BYTECODE, STORAGE)`
2. **Every existing rule must be updated** to thread the new `STORAGE` component through, even rules that never touch storage. The rules change even though their semantics is unchanged.

This is the **frame problem** in disguise. Fine-grained resources solve it at the resource level (no rule needs to mention what it doesn't touch). Coarse-grained resources require every rule to explicitly carry through the frame.

### 3.2 The $-sugar as frame shorthand

CALC's `$P` (preserved resource sugar) partially recovers composability for coarse-grained patterns:

```ill
evm/add:
  $bytecode BC * pc PC * ...
```

The `$bytecode` says "pass this through unchanged." But this is syntactic — the rule still mentions `bytecode` in both antecedent and consequent. If a new component is added, every `$`-decorated rule still requires updating.

Fine-grained resources make `$` unnecessary: a rule that doesn't touch `bytecode` simply omits it. The "pass-through" is automatic.

### 3.3 The categorical argument

From RES_0099's multicategory perspective: forward rules are morphisms `(A₁,...,Aₙ) → B`. **Compositionality** means morphisms compose by connecting matching input/output types, and unrelated types just pass through.

In the multicategory picture:
- Fine-grained: `evm/add` is a morphism `(pc, gas, stack) → (pc', gas', stack')`. The `bytecode` wire is not in its type signature — it passes through the box as an independent wire.
- Coarse-grained: `evm/add` is a morphism `(step) → (step')`. The `bytecode` wire is bundled inside `step`, so the morphism must extract and re-pack it even though it doesn't change it.

The coarse-grained model *encapsulates* the state but loses the **interface information** needed for modular reasoning. You can no longer say "`evm/add` only modifies `pc`, `gas`, and `stack`" — the type says it could modify anything inside `step`.

---

## 4. Partial Evaluation / Compile-Time Composition

### 4.1 The intermediate type approach from RES_0099

RES_0099 shows that abstract intermediate types like `dispatch BC PC OP PC'` serve as **internal wires** in the multicategory. They carry only the interface needed between producer and consumer rules. Cut elimination composes them away at compile time.

The `dispatch` type carries `(BC, PC, OP, PC')` — exactly the information needed by EVM instruction rules. It does **not** carry `gas`, `stack`, or `mem` because these are independent resources that different rules handle independently.

Compare:
- A `step` type carrying everything is the *opposite* of an intermediate type: it's a coarse-grained bundle that is never partially consumed.
- A `dispatch` type carrying only the bytecode-dispatch interface is an *internal wire* that is fully consumed in one step after composition.

### 4.2 What happens to composition when the intermediate carries everything

If the intermediate type carries the full state `step(PC, GAS, STACK, MEM, BC)`, then:

1. **Composition via cut** (RES_0099): composing `step/make` with `evm/add` via cut on `step` yields a rule that consumes `(pc, gas, stack, mem, bytecode)` and produces `(pc', gas', stack, mem, bytecode)`. This is the fine-grained rule — the composition *undoes* the bundling.

2. **The composition is correct** but produces the same rules as design A. The coarse-grained intermediate is transparently folded away by cut elimination. So design B with `step` as an internal type is equivalent to design A — it's just a verbose way of writing design A.

3. **If `step` is kept at runtime** (not eliminated by cut), then every rule match requires unpacking and repacking the full tuple. This is more expensive than matching only the fields each rule needs.

### 4.3 The SELL/subexponential angle

When resources have different lifetimes or scopes (RES_0097), fine-grained resources allow different subexponential modalities:
- `bytecode` might be `!` (persistent, never consumed, read-only) under SELL
- `pc` is linear (consumed and reproduced each step)
- `storage` is linear with persistence semantics across calls

Coarse-grained `step` cannot express these distinctions internally — the entire step must be the same modality, or the system must unpack it immediately. Fine-grained resources allow the type system to track these distinctions directly.

---

## 5. The Ceptre Perspective

Martens (2015) consistently uses fine-grained predicates in Ceptre examples. The block-stacking example:

```ceptre
pickup : arm_free * clear B * on B Table -o arm_holding B * clear Table.
```

`arm_free`, `clear`, and `on` are separate predicates. The rule does not mention `table` predicates for other blocks — they are implicitly preserved. Martens does not discuss a "coarse-grained" alternative explicitly, but the design principle is clear: **predicates = independent state dimensions; rules touch only what they modify**.

The only discussion approaching coarse-graining in Ceptre is **stages**: a stage bundles *rules*, not resources. All rules in a stage run to quiescence, but the resources remain fine-grained. This is the right factoring: coarse-grained control flow, fine-grained resources.

---

## 6. Summary: Concrete Tradeoffs

| Property | Fine-Grained (A) | Coarse-Grained (B) |
|---|---|---|
| **Adding a new state component** | Add type + rules only for it | Update every existing rule |
| **Rule matches** | Match only needed fields | Unpack entire state tuple |
| **Concurrency / independence** | Independent rules have disjoint pre-sets | All rules share the `step` place; fully sequential |
| **Reachability tree size** | Larger (intermediate states from independent firings) | Smaller (no intermediate states) |
| **Terminal state set** | Same as B (equivalent logic) | Same as A |
| **Type-level documentation** | Rule type signature = exact dependencies | Rule type signature = entire state |
| **Compose intermediate type away** | Already fine-grained; no need | Composition yields fine-grained rules (= design A) |
| **SELL/subexponential precision** | Each resource can have its own modality | Entire state is one modality |
| **Frame problem** | Solved at the type level | Requires explicit threading |
| **Invariant analysis** | Can reason about `pc` invariants independently | Must project out of `step` first |
| **Partial matching (SELL Tiers)** | Natural: rule filters by predicate | Requires unpack-then-filter |

### The one genuine advantage of coarse-grained

For **exhaustive exploration**, coarse-grained transitions eliminate the combinatorial explosion from independent rule orderings. If two rules modify `pc` and `gas` independently, fine-grained execution generates two paths (apply `pc-rule` first, or `gas-rule` first) that both lead to the same state. Coarse-grained execution has one path.

For deterministic sequential execution (EVM is deterministic given the bytecode), this advantage vanishes: there is only one applicable rule at each step anyway (the rule for the current instruction). The independence between `pc`, `gas`, and `stack` is real but only matters if multiple rules could fire simultaneously — which doesn't happen in EVM's sequential model.

### The practical verdict for EVM

EVM execution is **deterministic per instruction**: at each step, exactly one rule fires (the rule for the current opcode). There is no genuine concurrency to exploit or eliminate. The fine-grained model (design A) is therefore correct, and:

1. The frame problem is solved automatically (rules don't mention what they don't touch).
2. Adding new state components (e.g., storage, logs) requires no changes to existing rules.
3. Type signatures document exact dependencies.
4. The reachability tree is of the same size as design B because at most one rule fires per state (no diamonds to collapse).

The coarse-grained model offers no benefit for EVM and imposes ongoing maintenance costs on every rule change.

---

## References

### Petri Net Theory
- Murata, T. (1989). "Petri Nets: Properties, Analysis and Applications." *Proceedings of the IEEE*, 77(4):541-580. — foundational survey; place refinement, concurrency, liveness.
- Berthelot, G. (1987). "Transformations and Decompositions of Nets." *Advances in Petri Nets 1986*, LNCS 254, pp. 359-376. — series-place reduction, place fusion, structural transformations.
- Karp, R.M. & Miller, R.E. (1969). "Parallel Program Schemata." *JCSS*, 3(2):147-195. — Karp-Miller tree; concurrency measure.
- Reisig, W. (1985). *Petri Nets: An Introduction.* Springer. — standard reference; place/transition systems.
- Esparza, J. (1998). "Decidability and Complexity of Petri Net Problems." *Lectures on Petri Nets I*, LNCS 1491. — survey of decidability; place refinement and net equivalences.

### Linear Logic and Petri Nets
- Engberg, U. & Winskel, G. (1990). "Petri Nets as Models of Linear Logic." *CAAP'90*, LNCS 431, pp. 147-161. — systematic correspondence.
- Kanovich, M.I. (1995). "Petri Nets, Horn Programs, Linear Logic, and Vector Games." *Annals of Pure and Applied Logic*, 75(1-2):107-135. — definitive equivalence result.
- Meseguer, J. & Montanari, U. (1990). "Petri Nets Are Monoids." *Information and Computation*, 88(2):105-155. — categorical view; concurrency = diamond property.
- Cervesato, I. & Scedrov, A. (2009). "Relating State-Based and Process-Based Concurrency through Linear Logic." *Inf. Comput.*, 207(10):1044-1077.

### Concurrency and Independence
- Best, E. & Fernández, C. (1988). "Nonsequential Processes: A Petri Net View." *EATCS Monographs*. — concurrency degree; causal independence.
- Nielsen, M., Plotkin, G. & Winskel, G. (1981). "Petri Nets, Event Structures and Domains." *TCS*, 13(1):85-108. — unfolding; diamond property and event structures.

### Compile-Time Composition / Cut Elimination
- See RES_0099 (compile-time cut elimination for forward rule composition)
- See RES_0100 (termination of iterated rule composition)

### Multiset Rewriting
- Cervesato, I. (2001). "Typed MSR: Syntax and Examples." *MMM-ACNS 2001*. — multiset rewriting formalism.
- Durgin, N., Lincoln, P., Mitchell, J. & Scedrov, A. (2004). "Multiset Rewriting and the Complexity of Bounded Security Protocols." *JCS*, 12(2):247-311.

### Ceptre
- Martens, C. (2015). "Programming Interactive Worlds with Linear Logic." PhD Thesis, CMU. — fine-grained predicates as design principle.
- Martens, C. (2015). "Ceptre: A Language for Modeling Generative Interactive Systems." *AIIDE'15*.
