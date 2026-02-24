---
title: "HVM and Interaction Nets: Optimal Reduction, Linear Logic, and CALC"
created: 2026-02-24
modified: 2026-02-24
summary: "Deep analysis of the Higher-order Virtual Machine (HVM), its foundation in interaction combinators and optimal lambda reduction, the connection to linear logic proof nets, and the relationship to CALC's architecture."
tags: [HVM, interaction-nets, interaction-combinators, optimal-reduction, linear-logic, proof-nets, parallelism, Lafont, Lamping, geometry-of-interaction]
category: "Related Paradigms"
---

# HVM and Interaction Nets: Optimal Reduction, Linear Logic, and CALC

---

## 1. What HVM Is

### 1.1 Overview

HVM (Higher-order Virtual Machine) is a runtime for the Interaction Calculus (IC), a term rewriting system based on Lafont's interaction combinators (1997). It compiles functional programs (lambda calculus, pattern matching) into interaction nets and reduces them using local graph rewriting rules. The key claims:

- **Optimal beta-reduction**: no redundant work, in the sense of Levy (1978).
- **Automatic parallelism**: local interaction rules require no global synchronization.
- **No garbage collector**: linear resource management at the graph level.

HVM is developed by Higher Order Company (formerly Kindelia), founded by Victor Taelin.

### 1.2 Version History

| Version | Year | Key Advance |
|---|---|---|
| **Optlam** | ~2012 | JavaScript proof-of-concept of Lamping's algorithm |
| **Absal** | ~2015 | Abstract algorithm subset, removed oracle, 10x speedup |
| **FM-Net** | ~2018 | C implementation for Formality proof language (Ethereum era) |
| **HVM1** | 2022 | Rust. Compact encoding (128-bit nodes, tags on pointers). ~30% of GHC single-core, surpassed GHC with parallelism |
| **HVM2** | 2023 | Correct mass parallelizer. Near-ideal speedup per core. ~12x on 16 cores, ~20000x on GPU. Compilation target for Bend |
| **HVM3** | 2024 | First low-level compiler. Identifies compilable fragments, uses C backend. 10x-100x speedup in some cases, approaching Rust/C single-core |
| **HVM4** | 2025 | General compilation of IC functions to zero-overhead machine code, including functions with superpositions |

The atomic linker (the parallel synchronization mechanism) evolved from slow locks (HVM1) to AtomicCAS (HVM1.5) to AtomicSwap (HVM2) to a polarized atomic linker (HVM3) that eliminates the separate substitution map, reducing memory overhead by ~1/3.

### 1.3 The Bend Language

Bend is a high-level programming language that compiles to HVM. It offers Python/Haskell-like syntax with higher-order functions, pattern matching, recursion, and continuations. The key property: "if your code can run in parallel, it will run in parallel" -- no explicit threading, locks, or atomics. Bend achieved 57x speedup on GPU for bitonic sort vs sequential.

### 1.4 The Kindelia Blockchain

The original motivation for HVM was Kindelia, a blockchain ("cryptocomputer, not cryptocurrency") that replaces the EVM with HVM. The idea: formally verified smart contracts written in functional languages (Kind, Idris, Agda) can execute natively on a peer-to-peer functional computer. Kindelia claims 867x throughput over Ethereum due to HVM and reversible heap snapshots. The project was deprioritized in favor of Bend as a go-to-market strategy, but the blockchain motivation explains why HVM targets both correctness and performance.

---

## 2. Theoretical Foundation: Interaction Nets

### 2.1 Lafont's Interaction Nets (1990)

Interaction nets are a graphical model of computation defined by Yves Lafont in 1990 as a generalization of linear logic proof structures. An interaction net system consists of:

- **Agents** (nodes): each has a fixed arity (number of auxiliary ports) and one distinguished **principal port**.
- **Nets**: graphs built by connecting ports of agents with wires. Each port connects to exactly one other port (linearity).
- **Interaction rules**: when two agents connect via their principal ports (an **active pair**), they are rewritten according to a deterministic rule.

Key properties:
- **Determinism**: each active pair has at most one applicable rule.
- **Locality**: rewriting affects only the two interacting agents and their immediate neighbors.
- **Strong confluence**: any two reduction sequences from the same net yield the same normal form (when one exists).
- **No garbage collection**: every node is either part of an active pair or reachable from the interface; consumed nodes are immediately freed.

### 2.2 Interaction Combinators (Lafont 1997)

Lafont showed that a system of only **three agents** and **six rules** is universal for all interaction net systems:

**Agents:**
- **CON** (constructor): arity 2. Encodes lambda/application and multiplicative connectives.
- **DUP** (duplicator): arity 2. Encodes copying/sharing and the exponential modality.
- **ERA** (eraser): arity 0. Encodes garbage collection/weakening.

**Rules** (when two agents meet at their principal ports):

| Active Pair | Rule Type | Effect |
|---|---|---|
| CON - CON | Annihilation | Cancel; cross-connect auxiliary ports |
| DUP - DUP (same label) | Annihilation | Cancel; cross-connect auxiliary ports |
| DUP - DUP (different label) | Commutation | Pass through each other, creating 4 new nodes |
| CON - DUP | Commutation | Duplicate the constructor: 2 CON + 2 DUP |
| CON - ERA | Erasure | Erase constructor, propagate ERA to children |
| DUP - ERA | Erasure | Erase duplicator, propagate ERA to children |

**Universality theorem** (Lafont 1997): any interaction net system can be encoded in the interaction combinators. This means the three agents are a universal basis for deterministic distributed computation, analogous to how NAND is universal for Boolean circuits.

### 2.3 Symmetric Interaction Combinators

Mazza (2007) studied the **symmetric** variant where CON and DUP are treated symmetrically (both are binary agents with labels, distinguished only by label equality/inequality during interaction). The symmetric combinators enjoy a weaker universality property but are equally expressive and admit cleaner denotational semantics inspired by the relational model of linear logic.

HVM uses a variant closer to the symmetric combinators, with labeled nodes where same-label interactions annihilate and different-label interactions commute.

### 2.4 The Interaction Calculus (IC)

Victor Taelin's Interaction Calculus is a textual notation for interaction combinators, designed for practical programming:

**Six term types:**
- `VAR` (variable), `LAM`/`APP` (abstraction/application), `ERA` (erasure), `SUP` (superposition = labeled pair), `DUP` (duplication = labeled projection)

**Five interaction rules:**
1. `APP-LAM`: standard beta-reduction
2. `APP-SUP`: distribute application over superposition
3. `DUP-LAM`: duplicate a lambda (incremental copying)
4. `DUP-SUP` (same label): direct pair elimination
5. `DUP-SUP` (different label): nested duplication

Key departures from lambda calculus:
- **Affine variables**: each variable appears at most once (linearity).
- **Global scope**: variables can occur anywhere in the program (no scope boundaries).
- **First-class superpositions**: enable optimal sharing without bookkeeping oracles.

---

## 3. The Linear Logic Connection

This is the deepest and most important section for understanding HVM's relationship to CALC.

### 3.1 Proof Nets as Interaction Nets

Girard's proof nets (1987) are a graph representation of proofs in linear logic that quotients away irrelevant rule permutations. Lafont's interaction nets (1990) were explicitly designed as a **generalization** of proof nets:

- Each linear logic connective corresponds to an agent type.
- Each inference rule in the sequent calculus corresponds to how agents are wired.
- **Cut elimination in linear logic = interaction (reduction) in interaction nets.**

This is not a metaphor. The correspondence is formal:

| Linear Logic (Proof Nets) | Interaction Nets |
|---|---|
| Formula | Wire (connecting two ports) |
| Connective introduction | Agent node |
| Cut link (two formulas identified) | Active pair (principal ports connected) |
| Cut elimination step | Interaction rule application |
| Cut-free proof | Normal form (no active pairs) |

When two proof net nodes are connected at a cut link, the cut elimination procedure rewrites them according to the logical rules. This rewriting IS interaction. The proof net in normal form (all cuts eliminated) IS an interaction net in normal form.

### 3.2 The Multiplicative Fragment

The multiplicative connectives (tensor and par, or in ILL: tensor and loli) correspond directly to the **CON** agent:

- `A ⊗ B` (tensor): a CON node with wires to A and B, principal port facing the conclusion.
- `A ⅋ B` (par): the dual -- a CON node with wires to A and B, principal port facing the hypotheses.
- `A ⊸ B` (loli): syntactic sugar for `A^⊥ ⅋ B`.

When a tensor meets a par at a cut (i.e., a tensor-right proof meets a tensor-left proof), cut elimination cross-connects the sub-formulas. In interaction net terms: CON-CON annihilation. The auxiliary ports are reconnected, the two CON nodes disappear.

This is why CALC's `tensor_l` rule (which decomposes `A ⊗ B` on the left into separate `A` and `B`) corresponds to the annihilation interaction: the tensor node on one side meets the destructor on the other and both vanish, leaving the components connected directly.

### 3.3 The Exponential Fragment

The exponentials (`!` and `?`) are where interaction nets depart most strikingly from flat sequent calculus, and where the connection to optimal reduction lives.

- `!A` (of course / bang): controlled duplication. A proof of `!A` can be used zero or more times.
- `?A` (why not): the dual.

In interaction nets, `!A` is encoded using **DUP** (duplication) and **ERA** (erasure) agents:
- **Dereliction** (`!A ⊢ A`): unwrap one copy. Corresponds to a DUP-CON commutation.
- **Contraction** (`!A ⊢ !A ⊗ !A`): duplicate. Corresponds to DUP nodes that copy the subnet.
- **Weakening** (`!A ⊢ 1`): discard. Corresponds to ERA nodes that erase the subnet.

The DUP agent in interaction combinators IS the exponential modality made operational. When DUP meets CON (commutation rule), it duplicates the constructor -- this is exactly what happens when a banged proof is used: the proof structure gets copied incrementally, one constructor at a time.

**This is the key insight connecting HVM to CALC**: CALC's `!A` (persistent resources, can be copied freely) and HVM's DUP nodes (controlled duplication agents) are two operational interpretations of the same logical concept. CALC implements `!` via the persistent/linear context split; HVM implements `!` via explicit DUP/ERA agents in the interaction net.

### 3.4 Girard's Geometry of Interaction (GoI)

The Geometry of Interaction (Girard 1989) provides the mathematical foundation connecting linear logic to computation:

- Formulas are interpreted as Hilbert spaces (not sets).
- Proofs are interpreted as partial isometries (not morphisms A -> B, but operators on A + B).
- Cut elimination is interpreted via the **execution formula**, which computes the composed operator from two interacting operators using a fixed-point construction.

GoI was revolutionary because it interpreted proofs as **dynamic objects** (operators with internal dynamics) rather than static maps. This dynamic interpretation is precisely what interaction nets realize concretely: a proof net is a graph with internal dynamics (active pairs that interact), and normalization (cut elimination) is the execution of those dynamics.

GoI had direct influence on:
- Game semantics for linear logic (Abramsky, Hyland, Ong)
- Optimal reduction theory (the "GoI-style" readback in Lamping's algorithm)
- HVM's design (interaction rules ARE the GoI execution formula made discrete)

### 3.5 Abramsky's Computational Interpretations

Abramsky (1993) established two computational readings of linear logic:

1. **Intuitionistic linear logic -> refined lambda calculus**: finer control over evaluation order and storage allocation, while maintaining the Curry-Howard correspondence. This is the path CALC follows -- ILL as a refinement of functional programming with resource control.

2. **Classical linear logic -> concurrent processes**: the "proofs as processes" paradigm. Linear logic proofs correspond to processes in a synchronous pi-calculus. Tensor = parallel composition, loli = input/output, bang = replication.

The second reading connects to HVM's parallelism: interaction net reduction IS concurrent computation. Each active pair can be reduced independently. The interaction rules ARE the communication/synchronization primitives of a concurrent system.

### 3.6 Why Interaction Nets Are Inherently Parallel

The parallelism of interaction nets follows from linearity:

1. Each wire connects exactly two ports (linearity of resources).
2. Each interaction involves exactly two agents connected at their principal ports.
3. Two active pairs that don't share wires can be reduced simultaneously without interference.
4. After reduction, the new wires connect only to the neighbors of the original agents.

This is **locality = linearity**. In a linear system, there are no hidden aliases, no shared mutable state, no need for synchronization (except at the wire level). HVM's atomic linker exploits this: it uses atomic swaps on individual wires to coordinate parallel reduction, and the linearity of the net guarantees that conflicts are local and resolvable.

CALC's linear logic has the same property in principle: linear resources are used exactly once, so independent rule applications don't interfere. CALC's forward engine applies rules sequentially, but the exhaustive exploration tree has **embarrassingly parallel branches** -- each branch is independent after forking.

---

## 4. Optimal Reduction

### 4.1 Levy's Optimality

Levy (1978) defined optimality for lambda calculus reduction: two beta-redexes are **equivalent** if they arise from copying the same original redex. An optimal reduction strategy never reduces two equivalent redexes separately -- it reduces them once, sharing the result. Levy proved a lower bound on the number of reduction steps needed, but gave no algorithm achieving it.

### 4.2 Lamping's Algorithm (1990)

Lamping gave the first algorithm achieving Levy-optimal reduction using **sharing graphs**: a graphical representation where common subexpressions are shared rather than copied. The key ideas:

- Lambda terms are represented as graphs with explicit sharing nodes (fans).
- Beta-reduction is a local graph rewrite (like interaction net reduction).
- When a shared subexpression needs to be duplicated, fans propagate through the graph incrementally -- copying happens lazily, one constructor at a time.
- **Bookkeeping** nodes (brackets, croissants) track the scope of sharing to prevent incorrect interactions.

The algorithm is "well suited to parallel implementations, consisting of a fixed set of local graph rewrite rules" (Lamping 1990).

### 4.3 From Lamping to Interaction Combinators

Gonthier, Abadi, and Levy (1992) simplified Lamping's algorithm using insights from linear logic:

- The sharing graph IS a proof net for the lambda term (via the Curry-Howard correspondence extended through linear logic).
- The bookkeeping nodes correspond to managing the exponential modality.
- Reduction steps correspond to cut elimination in proof nets.
- Danos and Regnier discovered that Lamping's algorithm is an instance of Girard's Geometry of Interaction.

Lafont's interaction combinators (1997) completed the picture: the three agents (CON, DUP, ERA) with their six rules are sufficient to implement Lamping's algorithm without external bookkeeping. The labels on DUP nodes (superposition labels in HVM's IC) play the role of Lamping's brackets -- tracking scope of duplication.

### 4.4 What "Optimal" Means in Practice

- **No redundant beta-reductions**: if `(λx. x x)(M)` duplicates `M`, and both copies of `M` contain a redex `R`, then `R` is reduced once (in the shared representation) rather than twice.
- **Exponential speedups**: for certain terms (e.g., lambda-encoded Church numerals), optimal reduction is exponentially faster than normal-order reduction. HVM multiplies lambda-encoded numbers exponentially faster than GHC.
- **Not always faster**: optimal reduction has overhead from managing sharing nodes. For terms with little sharing, it can be slower than simple strategies. Asperti (2017) showed that certain terms require exponentially many bookkeeping steps despite having only linearly many beta-steps.
- **Practical sweet spot**: HVM3/HVM4 identify fragments that can be compiled to zero-overhead machine code and use the interaction net evaluator only where sharing/optimality matters.

---

## 5. How HVM Works (Technical)

### 5.1 Memory Model

HVM represents interaction nets as arrays of 64-bit or 128-bit cells. Each cell encodes a node (agent) with:
- A **tag** indicating the agent type (CON, DUP, ERA, or extensions like NUM, OP, etc.).
- **Pointers** to connected ports (other cells in the array).
- A **label** for DUP/SUP nodes (tracking scope of duplication).

Tags are stored on pointers rather than nodes (HVM1 innovation), halving the memory footprint and enabling pointer-tag tricks for fast dispatch.

### 5.2 Reduction Engine

The reduction engine maintains a **redex queue** of active pairs (two agents connected at their principal ports). Each reduction step:

1. Pop an active pair from the queue.
2. Dispatch on the tag combination (CON-CON, CON-DUP, CON-ERA, etc.).
3. Apply the interaction rule: rewrite the local neighborhood.
4. If new active pairs are created, push them to the queue.

### 5.3 Parallel Execution

Multiple threads consume the redex queue simultaneously. The **atomic linker** handles the synchronization:

- Memory is organized with **polarized** terms (positive and negative) that must respect pairing rules.
- When a thread rewrites an active pair, it uses atomic swap operations on the affected wires.
- If two threads try to interact with the same wire, the polarization scheme resolves the conflict: the displaced term is moved to the conflicting location, automatically serializing access.
- No locks, no global synchronization, no separate substitution map (HVM3+).

This achieves near-ideal speedup: 12x on 16 CPU cores, ~20000x on ~32384 GPU cores (HVM2 benchmarks).

### 5.4 Compilation (HVM3+)

HVM3 and HVM4 identify "compilable fragments" -- IC functions that can be translated to direct machine code without the interaction net overhead. The fragment analysis:

- If a function is first-order and doesn't use superpositions, compile it to direct C/machine code.
- If it uses superpositions (higher-order sharing), use the interaction net evaluator.
- HVM4 extends this to compile even functions with superpositions to zero-overhead code.

---

## 6. Relationship to CALC

### 6.1 Shared Foundation: Linear Logic

Both CALC and HVM are built on linear logic, but they use different **presentations**:

| | CALC | HVM |
|---|---|---|
| **Presentation** | Sequent calculus | Proof nets / interaction nets |
| **Objects** | Sequents `Gamma |- A` | Nets (graphs of agents) |
| **Proof steps** | Inference rules | Interaction rules |
| **Cut elimination** | Not primary (used in verification) | Primary computation mechanism |
| **Connectives** | tensor, loli, with, oplus, bang, one | CON (tensor/loli), DUP (bang), ERA (weakening) |

These are different presentations of the **same logic**. A sequent calculus proof can be translated to a proof net, and vice versa (for the multiplicative-exponential fragment). Cut elimination in the sequent calculus corresponds to interaction in the proof net.

### 6.2 Complementary Roles: Search vs Execution

CALC and HVM serve fundamentally different purposes:

- **CALC searches for proofs**: given a goal (sequent), find a derivation. Backward chaining decomposes the goal; forward chaining builds up from axioms. The result is a proof tree (or execution tree).
- **HVM executes proofs**: given a proof (lambda term / interaction net), reduce it to normal form. The result is a value.

These compose naturally: **CALC finds the proof, HVM runs it.**

A concrete scenario: CALC proves that a linear logic program is correct (e.g., a smart contract satisfies a specification). The proof term is a lambda term. HVM executes the lambda term optimally. The proof net representation serves as the shared intermediate format.

### 6.3 Different Computation Models

| | CALC Forward Engine | HVM |
|---|---|---|
| **State** | Multiset of linear formulas | Graph of interaction net agents |
| **Step** | Multiset rewriting (consume antecedents, produce consequents) | Graph rewriting (annihilate/commute active pair) |
| **Granularity** | One rule application = many graph rewrites | One interaction = one local graph rewrite |
| **Nondeterminism** | Don't-know (explore all rule selections) | Deterministic (each active pair has one rule) |
| **Result** | Execution tree (all possible traces) | Single normal form |

CALC's forward engine is a **multiset rewriting system** where the state is a bag of formulas and rules consume/produce formulas. HVM is a **graph rewriting system** where the state is a net of agents and interactions annihilate/rearrange agents. Both are Turing-complete, both arise from linear logic, but they operate at different abstraction levels.

### 6.4 Content Addressing vs Graph Nodes

CALC's Store implements **hash consing**: terms are content-addressed hashes, structural equality is O(1), and identical subterms are shared automatically. HVM's interaction nets use **graph structure** for sharing: identical subterms are literally the same node in the graph, connected by wires.

| | CALC Store | HVM Interaction Net |
|---|---|---|
| **Identity** | Hash comparison (`a === b`) | Pointer comparison (same node) |
| **Sharing** | Implicit (hash deduplication) | Explicit (DUP nodes, wire aliasing) |
| **Duplication** | Free (O(1), just copy the hash) | Controlled (DUP propagation, incremental) |
| **Garbage collection** | None (terms persist forever) | Automatic (ERA propagation) |
| **Mutability** | Immutable (content-addressed) | In-place rewriting (active pairs consumed) |

CALC optimizes for **read-heavy** workloads (proof search inspects terms repeatedly). HVM optimizes for **write-heavy** workloads (reduction rewrites the graph continuously).

### 6.5 The Exponential Modality

CALC's `!A` (bang) = persistent resources that can be copied freely. The operational semantics:
- `state.persistent[hash] = true` -- the fact is always available.
- Persistent facts are never consumed by forward rules.
- `provePersistentGoals` resolves persistent antecedents via state lookup or backward proving.

HVM's DUP nodes = controlled duplication agents. The operational semantics:
- A DUP meeting a CON duplicates the constructor incrementally.
- A DUP meeting an ERA erases the duplication request.
- A DUP meeting a DUP with the same label annihilates (sharing resolved).

Both are operational readings of the same logical concept: the `!` modality permits structural rules (contraction and weakening) that are forbidden for linear resources. CALC handles this at the **state level** (persistent vs linear zones). HVM handles this at the **graph level** (DUP/ERA agents).

### 6.6 Parallelism

**HVM's parallelism** comes from the locality of interaction rules. Two active pairs sharing no wires can be reduced simultaneously. This is a fine-grained parallelism at the individual interaction level.

**CALC's potential parallelism** is coarser-grained:
- **Exhaustive exploration**: each branch of the execution tree (THY_0001) is independent after forking. Branches can be explored in parallel -- this is embarrassingly parallel.
- **Forward rule independence**: when multiple rules can fire on disjoint subsets of the state, they could fire in parallel. CALC currently serializes this, but the linearity of resource consumption guarantees safety.
- **Backward proof search**: independent subgoals (from tensor-right context splitting) could be searched in parallel.

The difference: HVM's parallelism is **automatic** (inherent in the reduction model). CALC's parallelism requires **explicit scheduling** (fork branches, distribute work, merge results).

### 6.7 Exhaustive vs Optimal

CALC and HVM have opposite goals in a precise sense:

- **CALC explores ALL possible executions**: the execution tree (THY_0001) enumerates every reachable state. This is **universal quantification** over rule selections.
- **HVM finds THE ONE optimal reduction**: sharing ensures each redex is reduced exactly once. This is **existential computation** -- finding the single normal form.

These are complementary:
- CALC needs all paths to verify properties (safety, conservation, deadlock-freedom).
- HVM needs one path to compute a result efficiently.
- A system that can both verify all paths AND execute one path optimally would combine their strengths.

### 6.8 Composition Scenarios

**Scenario 1: CALC proves, HVM executes.** CALC's backward prover finds a proof that a program satisfies a specification. The proof term is a lambda term (via Curry-Howard). HVM executes the lambda term optimally. The proof guarantees correctness; HVM guarantees efficiency.

**Scenario 2: Proof net as intermediate representation.** CALC's content-addressed formulas could be translated to interaction net nodes. The proof net representation captures sharing structure that content-addressed hashing misses (beta-equivalent terms have different hashes but the same proof net normal form).

**Scenario 3: HVM as CALC's reduction backend.** When CALC needs to normalize terms (e.g., for the QTT definitional equality gap in RES_0056 D.7), HVM's optimal reducer could serve as the normalization engine. CALC constructs terms; HVM normalizes them; CALC checks equality by comparing normal forms.

---

## 7. What CALC Could Learn from HVM

### 7.1 Parallel Reduction of Independent Proof Branches

CALC's exhaustive exploration (symexec.js) is currently single-threaded DFS with mutation+undo. HVM's atomic linker technique demonstrates that fine-grained parallel graph rewriting is achievable with minimal synchronization. CALC could:
- Fork independent branches to separate threads/workers.
- Use CALC's content-addressed hashes as natural synchronization points (if two branches produce the same hash, they converge).
- The linearity of CALC's state guarantees no aliasing between branches.

### 7.2 Interaction Net Representation

CALC currently represents formulas as content-addressed hashes (Merkle DAG). An alternative: represent proof states as interaction nets. This would:
- Make cut elimination (normalization) a first-class operation.
- Enable sharing analysis not possible with hash consing alone.
- Potentially simplify the backward prover by making proof construction = net construction.

The trade-off: interaction nets are mutable (in-place rewriting), while CALC's Store is immutable (append-only). The immutability is valuable for proof search (easy backtracking). A hybrid approach -- build immutable proof terms, translate to interaction nets for execution -- may capture both benefits.

### 7.3 Optimal Sharing for the Exponential Modality

CALC's persistent facts (`!A`) are duplicated eagerly: every rule that needs `!A` gets a full copy of A. HVM's DUP nodes duplicate lazily, one constructor at a time. For large persistent facts (e.g., the EVM code table with hundreds of entries), lazy duplication could avoid copying structure that is never inspected.

### 7.4 The Atomic Linker for Lock-Free Parallel Computation

HVM3's polarized atomic linker achieves lock-free parallel reduction by:
- Assigning polarities to nodes (positive/negative).
- Using atomic swaps on individual wires.
- Resolving conflicts via polarization (displaced terms move to the conflict location).

If CALC ever moves to parallel exploration, this technique -- or an adaptation to multiset rewriting -- could enable lock-free parallel forward chaining.

---

## 8. What HVM Could Learn from CALC

### 8.1 Proof Search

HVM only **reduces** -- it takes a term and computes its normal form. It cannot **search** for proofs. If you need to find a program that satisfies a specification, HVM cannot help. CALC's backward and forward provers fill this gap: given a specification (sequent), CALC finds a proof (program).

### 8.2 Exhaustive Exploration

HVM computes one result (the normal form). CALC computes all possible results (the execution tree). For verification, testing, and model checking, exhaustive exploration is essential. HVM's interaction nets are deterministic (confluent); CALC's forward engine is nondeterministic (multiple rules can fire). Exhaustive exploration of nondeterministic interaction net systems is an unexplored direction.

### 8.3 Resource-Aware Verification

CALC tracks linear resource consumption throughout execution. Every forward step accounts for which resources are consumed and produced. This enables verification that resources are conserved (no creation from nothing, no silent destruction). HVM's ERA nodes can silently erase arbitrary subterms; there is no accounting for whether this erasure is intentional or a bug.

### 8.4 Forward Chaining for Logic Programming

HVM's computation model is pure reduction (goal: normal form). CALC's forward engine implements a different paradigm: multiset rewriting driven by pattern matching on the state. This is closer to Prolog/Datalog/CHR than to lambda calculus reduction. The forward chaining paradigm enables encoding of state machines, protocols, and reactive systems that are awkward to express as lambda reductions.

---

## 9. Open Questions

### 9.1 Can Interaction Net Reduction Be Used Inside CALC's Proof Search?

CALC's backward prover constructs proof trees by decomposing goals. Could proof net construction (building interaction nets) replace or complement sequent calculus proof search? Proof nets have better complexity for some operations (no commutative cases), but sequent calculus has better control (focusing, invertibility). A hybrid where focusing guides proof net construction might be tractable.

### 9.2 Could CALC's Execution Trees Be Represented as Interaction Nets?

THY_0001's execution tree has nodes (step, fork, branch, leaf, cycle). Could this tree structure be encoded as an interaction net where:
- `step` = a CON node connecting the state to the continuation
- `fork` (from oplus) = a CON node with two auxiliary ports (additive)
- `branch` (from nondeterminism) = a DUP-like node (explore both)
- `leaf` = an ERA-like node (terminal)

The tree would then be "reducible" -- reducing it would correspond to executing the program. But the execution tree represents ALL paths, not one path. Interaction nets are confluent (one normal form). Encoding universal quantification over paths in a confluent system requires care.

### 9.3 Is There a Useful Compilation from CALC Programs to HVM?

CALC's `.ill` programs are sets of forward rules. Each rule is a linear implication `A1 * ... * An -o { B1 * ... * Bm }`. These are proof net fragments: the antecedents wire to a cut link with the consequents. The full program is the parallel composition of all applicable rule instances. Whether this encoding leads to efficient execution depends on whether HVM's interaction rules can simulate multiset rewriting without losing the locality property.

### 9.4 Can HVM's Parallelism Accelerate CALC's Exhaustive Exploration?

CALC's symexec explores a tree of states. Independent branches (after a `branch` or `fork` node) are embarrassingly parallel. HVM's parallel evaluator could potentially:
- Represent the exploration tree as an interaction net.
- Let different threads reduce different subtrees.
- Use the atomic linker for shared-state access (e.g., cycle detection via `pathVisited`).

Challenge: CALC's mutation+undo pattern (optimized for sequential DFS) would need to be replaced by a fork-join pattern (each branch gets its own state copy). Content-addressed hashing makes state copying O(1) for shared structure.

### 9.5 How Do QTT Grades Interact with Interaction Net Duplication?

RES_0056 explores QTT (Quantitative Type Theory) for CALC. QTT grades control how many times a variable can be used. In interaction net terms:
- Grade 0 = ERA (erase, never use)
- Grade 1 = direct wire (use exactly once, no DUP)
- Grade omega = DUP (unlimited copying)
- Grade n = bounded DUP (copy exactly n times, then ERA)

Bounded duplication (grade n) is not directly supported by Lafont's interaction combinators (DUP duplicates unboundedly). Encoding bounded duplication would require counting DUP nodes or using a graded variant of interaction combinators. This connects to bounded linear logic (Girard, Scedrov, Scott 1992) and the graded exponential modality.

### 9.6 Can CALC's Content-Addressed Store Be Unified with Interaction Net Representation?

CALC's Store uses FNV-1a hashing for O(1) equality. Interaction nets use pointer identity. A unified representation might:
- Use content-addressed hashing for **stable subterms** (atoms, types, ground terms).
- Use interaction net wiring for **dynamic subterms** (terms under active reduction).
- Switch representations at the boundary: hash ground terms, wire open terms.

This mirrors how HVM3/HVM4 compile "compilable fragments" to direct code while using interaction nets for dynamic parts.

---

## 10. Bibliography

### Interaction Nets and Combinators
- Lafont, Y. (1990). "Interaction Nets." POPL 1990, pp. 95-108. [ACM DL](https://dl.acm.org/doi/10.1145/96709.96718) -- Original interaction nets paper.
- Lafont, Y. (1997). "Interaction Combinators." Information and Computation 137(1):69-101. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/S0890540197926432) -- Universality of three agents.
- Mazza, D. (2007). "A Denotational Semantics for the Symmetric Interaction Combinators." MSCS 17(3). [PDF](https://lipn.univ-paris13.fr/~mazza/papers/CombSem-MSCS.pdf)
- Mazza, D. (2006). "Interaction Nets: Semantics and Concurrent Extensions." PhD thesis, Univ. Paris 13. [PDF](https://lipn.fr/~mazza/papers/Thesis-1.0.pdf)
- Mackie, I. and Pinto, J.S. "Encoding Linear Logic with Interaction Combinators." [Semantic Scholar](https://www.semanticscholar.org/paper/Encoding-Linear-Logic-with-Interaction-Combinators-Mackie-Pinto/1158b58bc4a67772b15758f81907b0e193f936ba)

### Optimal Reduction
- Levy, J.-J. (1978). "Reductions Correctes et Optimales dans le Lambda-Calcul." PhD thesis, Univ. Paris VII. -- Optimality definition.
- Lamping, J. (1990). "An Algorithm for Optimal Lambda Calculus Reduction." POPL 1990, pp. 16-30. [ACM DL](https://dl.acm.org/doi/10.1145/96709.96711)
- Gonthier, G., Abadi, M., Levy, J.-J. (1992). "The Geometry of Optimal Lambda Reduction." POPL 1992, pp. 15-26. [ACM DL](https://dl.acm.org/doi/10.1145/143165.143172)
- Asperti, A. (2017). "About the Efficient Reduction of Lambda Terms." [arXiv:1701.04240](https://arxiv.org/pdf/1701.04240) -- Bookkeeping overhead analysis.

### Linear Logic and Proof Nets
- Girard, J.-Y. (1987). "Linear Logic." TCS 50(1):1-102. -- The foundation.
- Girard, J.-Y. (1989). "Geometry of Interaction I: Interpretation of System F." Logic Colloquium 1988, pp. 221-260. -- GoI foundation.
- Girard, J.-Y. (1995). "Geometry of Interaction III: Accommodating the Additives." Advances in Linear Logic, pp. 329-389. [Cambridge](https://www.cambridge.org/core/books/abs/advances-in-linear-logic/geometry-of-interaction-iii-accommodating-the-additives/27C4B983ECC98FF0F50021569EBA34FE)
- Lafont, Y. (1995). "From Proof Nets to Interaction Nets." Advances in Linear Logic, pp. 225-247. [Cambridge](https://www.cambridge.org/core/books/abs/advances-in-linear-logic/from-proof-nets-to-interaction-nets/8C2C748AFE97D1E5B7310AB855CCB51B) -- The bridge paper.
- Girard, J.-Y., Scedrov, A., Scott, P.J. (1992). "Bounded Linear Logic." TCS 97(1):1-66. -- Bounded exponentials.

### Computational Interpretations
- Abramsky, S. (1993). "Computational Interpretations of Linear Logic." TCS 111(1-2):3-57. [Academia](https://www.academia.edu/2781700/Computational_Interpretations_of_Linear_logic) -- Lambda calculus and process calculus readings.
- Abramsky, S. (1994). "Proofs as Processes." TCS 135(1):5-9. [Semantic Scholar](https://www.semanticscholar.org/paper/Proofs-as-Processes-Abramsky/838f4532ae4765d2cda50bf5994ff399d35a92b5)
- Caires, L. and Pfenning, F. (2010). "Session Types as Intuitionistic Linear Propositions." CONCUR 2010. -- Linear logic / session types correspondence.

### HVM and Bend
- Taelin, V. (2023). "HVM2: A Parallel Evaluator for Interaction Combinators." [Paper](https://raw.githubusercontent.com/HigherOrderCO/HVM/main/paper/HVM2.pdf)
- Taelin, V. (2024). "HVM3's Optimal Polarized Atomic Linker." [Gist](https://gist.github.com/VictorTaelin/2aba162f2b04478dc53e5615f482db7b)
- Taelin, V. (2025). "Interaction Calculus." [GitHub](https://github.com/VictorTaelin/Interaction-Calculus)
- HigherOrderCO. HVM4. [GitHub](https://github.com/HigherOrderCO/HVM4)
- HigherOrderCO. Bend. [GitHub](https://github.com/HigherOrderCO/Bend)
- HigherOrderCO. Kindelia. [GitHub](https://github.com/HigherOrderCO/Kindelia)

### Cross-References
- THY_0001 -- Exhaustive Forward Chaining in MALL with the Lax Monad
- RES_0056 -- Quantitative Type Theory: Sequent Calculus and Gap Analysis for CALC
- RES_0026 -- Linear Logic Connectives: Par, Why Not, and Polarity
