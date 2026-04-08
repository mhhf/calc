---
title: "Tabling, Datalog Stratification, Magic Sets, SLD Completeness, findall, Partial Evaluation, and EVM Dead Code"
created: 2026-04-07
modified: 2026-04-07
summary: "Research-grade survey of SLG resolution/tabling algorithms, Datalog stratification, magic set transformation, SLD completeness for enumerating all solutions, findall implementation, partial evaluation in logic programming, and EVM dead code decidability."
tags: [tabling, datalog, logic-programming, partial-evaluation, evm, prolog, sld-resolution, forward-chaining, optimization, termination]
category: "Implementation"
---

## 1. SLG Resolution / Tabling in Logic Programming

### 1.1 The Problem with SLD

Standard SLD resolution (Prolog's algorithm) has two failure modes for collecting all solutions:

1. **Infinite positive loops**: `p :- p.` causes non-termination.
2. **Redundant recomputation**: `fib(N,F)` called twice from different rules recomputes the whole tree, giving exponential complexity.

SLG resolution (Chen & Warren, JACM 1996) addresses both by maintaining a table of subgoals and their answers.

### 1.2 The SLG Forest-of-Trees Model

SLG evaluation is represented as a **forest of SLG trees**, one tree per distinct tabled subgoal. Each tree is rooted at a node `S :- S` and grows by applying resolution steps. The state of evaluation is the entire forest.

Key definitions:
- **Generator**: the tree root for a tabled subgoal; it drives clause resolution.
- **Consumer**: a node in another tree that called a variant of an already-tabled subgoal; it suspends instead of recursing.
- **Answer table**: the accumulated set of answers for each subgoal, built incrementally.

### 1.3 The Seven SLG Transformations (Chen & Warren 1996)

For definite (Horn clause) programs, the core operations are:

1. **New_Subgoal**: When a literal `G` is selected that matches a tabled predicate and no table entry for `G` exists yet, create a new SLG tree rooted at `G`. Register `G` in the table with an empty answer set.

2. **Program_Clause_Resolution**: Apply a matching program clause to a generator node, producing child nodes for the body literals. Standard SLD step within the generator tree.

3. **Answer_Return**: When a generator node reaches an empty goal (refutation), record the computed answer substitution in `G`'s answer table. If it is new, trigger Answer_Clause for all consumers of `G`.

4. **Answer_Clause**: Resume a suspended consumer node by unifying with a new answer from the table, creating a new branch for each answer.

5. **Completion**: When no further transformations can apply to any node in a set of mutually dependent subgoals (an SCC of the Subgoal Dependency Graph), mark those subgoals as **complete**. A complete subgoal's answer table is final; future calls resolve directly against it.

6. **Delaying** (for negation/general programs): When a literal `not G` is selected and `G`'s table is incomplete, delay the resolution rather than fail; resume when `G` completes.

7. **Simplification** (for well-founded semantics): After completion, simplify delayed literals using three-valued logic to produce final truth values.

For definite programs, only transformations 1–5 are needed.

### 1.4 How All Solutions Are Collected

The algorithm is a **least-fixed-point computation** over the answer tables:

```
Repeat:
  For each non-complete subgoal G:
    Apply Program_Clause_Resolution to expand its tree
    For each new answer A derived:
      Add A to table(G)
      Resume all consumers of G with A (Answer_Clause)
Until: no new answers are derived for any subgoal
Then: mark all subgoals in the current SCC as complete
```

**Termination**: For programs with the **bounded term-depth property** (no function symbols, or bounded depth), this loop terminates. Datalog (function-free) always terminates; the answer table is a finite subset of ground atoms.

**Completeness**: SLG resolution is **sound and search-space complete** with respect to the well-founded partial model for all non-floundering queries. For definite (Horn) programs, it computes the **least Herbrand model** — all and only the logical consequences of the program.

### 1.5 SCC-Based Completion in the SLG-WAM

XSB's SLG-WAM implementation uses a **Completion Stack** tracking the current SCC of mutually dependent tabled subgoals. The invariant: a subgoal `G` is complete only when all subgoals in the SCC containing `G` are complete (no new answers possible).

The algorithm detects SCCs on-the-fly using a DFS-based approach analogous to Tarjan's algorithm. When the SCC leader (the first subgoal of the component on the stack) finishes its expansion with no new answers produced, the entire SCC is marked complete simultaneously.

**Answer Completion** (for programs with negation through failure): an additional post-processing pass over a completed SCC's delayed answers using well-founded semantics. For definite programs, this step is vacuous.

### 1.6 Key Complexity Results (Swift & Warren, TPLP 2012)

- Positive Datalog: **PTIME** data complexity, EXPTIME combined complexity.
- Stratified Datalog with negation: **PTIME** data complexity.
- Well-founded semantics: **PTIME** data complexity.
- SLG-WAM overhead over standard WAM for non-tabled predicates: ~25% for call-subsumption mode; lower for call-variance mode.

### 1.7 Call Subsumption vs Call Variance

- **Call variance** (default): two calls `G1`, `G2` are the same if they are variants (identical up to variable renaming). Each variant gets its own table entry.
- **Call subsumption**: if `G1` is more general than `G2`, answers to `G1` subsume answers to `G2`. Significant efficiency gains for programs with partially instantiated calls (e.g., path(a, Y) subsumes path(X, Y)).

---

## 2. Datalog Stratification

### 2.1 Predicate Dependency Graph

Given a Datalog program `P` with negation, construct a directed graph `G_P`:
- **Nodes**: all predicate symbols (IDB + EDB).
- **Positive edge** `p → q` (unlabeled): rule in `P` with `p` as head and `q` in a positive body literal.
- **Negative edge** `p → q` (labeled `¬`): rule in `P` with `p` as head and `q` in a negated body literal (`not q(...)`).

### 2.2 Stratifiability Criterion

`P` is **stratifiable** iff `G_P` contains no cycle that includes a negative edge.

Equivalently: no SCC of `G_P` contains a negative edge internal to it (a predicate cannot negatively depend on itself, directly or transitively).

### 2.3 Algorithm: Computing the Stratification

**Input**: Datalog program `P` with negation.
**Output**: A stratification function `stratum: Pred → ℕ`, or FAIL.

```
1. Build G_P (O(|rules|) time).

2. Compute SCCs of G_P using Tarjan's algorithm (O(|nodes| + |edges|)).

3. Check: for each negative edge p → q, p and q must be in DIFFERENT SCCs.
   If any negative edge is intra-SCC, return FAIL (program not stratifiable).

4. Topologically sort the SCCs (O(|SCC| + |edges between SCCs|)).
   Let SCC_0, SCC_1, ..., SCC_k be the topological order (SCC_0 has no incoming edges).

5. Assign strata:
   - For each predicate p in SCC_i:
     stratum(p) = max over all edges q → p of:
       - stratum(q)      if the edge is positive
       - stratum(q) + 1  if the edge is negative
   This assignment is consistent because negative edges go strictly downward.
```

**Complexity**: O(|predicates| + |rules|) — linear in program size.

### 2.4 Stratified Evaluation Algorithm

```
For i = 0, 1, ..., k:
  Treat all predicates in strata < i as EDB (frozen/complete).
  Compute the least fixpoint of the rules for strata-i predicates
    (they form a semi-positive Datalog program — no negation within stratum).
  Freeze the strata-i results.
```

**Correctness**: For stratifiable programs, this produces the **perfect model semantics** — the unique minimal model that respects stratification. Equivalent to the well-founded model when the program is stratifiable.

### 2.5 Modular Stratification (Ross & Topor 1988; Ullman)

**Modular stratification** (also called local stratification) is a strict generalization: instead of a global predicate-level partition, assigns strata to ground atoms. A program is locally stratifiable if the ground instantiation's dependency graph is acyclic through negation. Every globally stratifiable program is locally stratifiable; the converse fails (e.g., `p(X) :- not q(X), r(X)` can be locally stratifiable when r is bounded even if p and q seem to mutually depend).

### 2.6 Complexity Bounds Summary

| Datalog variant | Data complexity | Combined complexity |
|---|---|---|
| Positive Datalog | PTIME-complete | EXPTIME-complete |
| Stratified Datalog¬ | PTIME-complete | EXPTIME-complete |
| Well-founded semantics | PTIME-complete | EXPTIME-complete |
| Stable model semantics | PTIME (for stratified) / NP-complete (general) | — |

Source: Abiteboul, Hull, Vianu, "Foundations of Databases" (1995), Chapter 15; also Dalmau & Kolaitis, complexity survey.

---

## 3. Magic Set Transformation

### 3.1 Problem: Demand-Driven Evaluation

Bottom-up Datalog evaluation computes all facts in all predicates, even those irrelevant to the query. The magic set transformation rewrites the program to restrict evaluation to only query-relevant tuples — simulating top-down propagation within a bottom-up framework.

### 3.2 The Transformation Algorithm

**Phase 1: Adornment computation** (Beeri & Ramakrishnan 1987)

An **adornment** for a predicate `p/n` is a string of `b` (bound) and `f` (free) characters, length `n`. For a query `?- q(a, X)`, the seed adornment is `bf` (first argument bound, second free).

The adornment propagation uses the **Sideways Information Passing Strategy (SIPS)**:
```
Start: query predicate gets its adornment from the query pattern.
For each rule with head p with adornment a:
  Process body atoms left-to-right (or per chosen SIPS order).
  An argument is "bound" if:
    - it appears as a bound argument of the head, OR
    - it appears in a body literal already processed and marked bound.
  Assign adornments to IDB body atoms based on which of their arguments are bound.
  Recursively adorn those IDB predicates.
```

**Phase 2: Magic predicate generation**

For each adorned IDB atom `p^a` appearing in a rule body:
```
magic_p^a(bound_args(p)) :- magic_h^ah(bound_args(h)), body_literals_before_p
```

This creates a predicate encoding "demand": `magic_p^a(X)` means the value `X` is a requested input for `p^a`.

**Phase 3: Rule rewriting**

Each original rule `h^a :- B1, ..., Bn` is rewritten to:
```
h^a :- magic_h^a(bound_args(h)), B1, ..., Bn
```

The magic guard restricts the rule to fire only when the head predicate has been demanded.

**Phase 4: Seed fact**

Add `magic_q^a(query_constants).` as the initial demand fact.

### 3.3 Correctness Theorem

**Theorem (Beeri & Ramakrishnan 1987)**: For a Datalog program `P` and query `q(t)`, let `P'` be the magic-set transformed program. Then:
```
P ∪ facts ⊨ q(t)  iff  P' ∪ facts ⊨ q(t)
```
The transformation is **query-equivalent**: the set of answers to the query is identical in both programs.

Moreover, `P'` computes **only** those facts relevant to answering the query (in the sense that it generates the minimal set required by any sound top-down evaluation strategy). This corresponds to the **minimax SLD tree** for the query.

### 3.4 Magic Sets vs Tabling

Tabling (SLG) and magic sets are **equivalent in expressive power** for Datalog query answering:
- Magic sets: a **static program transformation** (compile-time); bottom-up evaluation of the transformed program.
- Tabling: a **dynamic runtime mechanism**; memoizes subgoal answers as they are computed top-down.

For programs where the query pattern is known at compile time, magic sets can be more efficient (no runtime tabling overhead). For programs with unknown query patterns, tabling is more flexible.

**Key result (Tekle & Liu 2010)**: Subsumptive tabling (call subsumption in XSB) can be strictly more efficient than magic sets for queries with partially-bound patterns, because subsumption dynamically detects that a more specific call's answers are already covered by a more general tabled entry.

### 3.5 Limitations

The standard magic sets transformation does not handle:
- Negation (stratified extensions exist: Ross 1991, Alviano et al. 2012)
- Aggregation (extensions exist: Greco et al.)
- Functors (requires termination analysis)

Extended magic for stratified negation (Tekle & Liu 2019) preserves query equivalence and produces optimal bottom-up evaluation matching top-down evaluation's footprint precisely.

---

## 4. Completeness of SLD Resolution for Definite Clauses

### 4.1 The SLD Tree

For a definite program `P` and goal `G`, the **SLD tree** (also called the search tree) is the full non-deterministic resolution tree. Each node is a goal sequence; branching corresponds to choosing which program clause to apply to the selected literal.

- **Success branches**: leaves with empty goal (refutation found); the sequence of substitutions along the branch gives a computed answer.
- **Failure branches**: leaves where no clause applies.
- **Infinite branches**: possible when the program has recursive rules.

### 4.2 Completeness Theorem (Lloyd 1987, Clark 1979)

**Theorem (Refutation Completeness of SLD)**:
Let `P` be a definite program, `G` a goal, and `θ` a correct answer substitution for `G` (i.e., `P ⊨ G θ`). Then there exists a **computed answer substitution** `σ` in some SLD refutation for `G`, such that `θ` is an instance of `σ`: `θ = σ μ` for some `μ`.

Formally: *every correct answer is an instance of some computed answer.*

**Independence of the Computation Rule**: The set of computed answers does not depend on which literal is selected at each step (the computation rule / selection function). Any computation rule gives the same set of computed answers (up to variable renaming).

### 4.3 Critical Limitation: Depth-First Search is Incomplete

Although the SLD **tree** contains all computed answers, Prolog's **depth-first left-to-right** traversal can **fail to enumerate all of them** if the tree has infinite branches to the left of success branches.

Example:
```prolog
loop :- loop.
p(a).
```
Query `?- p(X).`: The SLD tree has an infinite leftmost branch (`loop` via itself) and a success branch `p(a)`. DFS follows the infinite branch first and never finds `p(a)`.

**Breadth-first** (or iterative deepening) traversal of the SLD tree IS complete — it finds every success branch in finite time, provided the tree is finitely branching. But BFS has high space overhead.

### 4.4 Fair Selection Strategies

A computation rule is **fair** if it eventually selects every literal in every infinite derivation. Fair selection guarantees finding all solutions. BFS is fair; DFS is not. Iterative deepening DFS is fair.

**Theorem**: If the computation rule is fair and the SLD tree is finitely branching, the SLD procedure is complete — it enumerates all computed answers.

For standard Prolog (DFS), completeness holds only when there are no infinite branches to the left of desired solutions. In practice, programmers must order clauses to avoid left-infinite loops.

### 4.5 Tabling as a Complete Strategy

SLG resolution restores completeness even for left-recursive programs by detecting loops and treating them as fixpoints. For programs with bounded term depth, SLG is both terminating and complete (computes all correct answers).

---

## 5. findall/3 in Prolog

### 5.1 Standard Semantics

```prolog
findall(Template, Goal, Bag)
```

`Bag` is the list of all instances of `Template` for which `Goal` succeeds, in order of derivation. If `Goal` has no solutions, `Bag = []` (findall always succeeds). All variables in `Goal` not shared with `Template` are treated as existentially quantified.

ISO standard (ISO/IEC 13211-1): `findall(T, G, B)` succeeds iff `B` unifies with the list of values of `T` from "successive re-executions of `call(G)`" after replacing all variables by fresh copies.

### 5.2 Implementation Mechanism

findall requires **copy_term semantics** for each solution: when a solution is found, a copy of `Template` is made with all variables **renamed** (so later backtracking does not corrupt earlier solutions). The copies are accumulated on a separate list/stack.

**Core algorithm**:
```
1. Save current choice point (or create one).
2. Call Goal using standard SLD backtracking.
3. On each success:
   a. copy_term(Template, Copy)   -- fresh copy of the current instantiation
   b. Add Copy to Bag_accumulator
   c. Fail to force backtracking (continue searching)
4. When Goal has no more solutions (no more choice points within Goal):
   Return Bag_accumulator as Bag.
5. Restore state to before step 1.
```

The key: **independent backtracking** within findall's Goal does not affect external bindings. findall creates an isolated environment.

### 5.3 WAM-Level Implementation

In the Warren Abstract Machine, findall is implemented using a **mark** on the heap and choice point stack. On each solution, `copy_term` copies the current Template into a private accumulator area. On final exit, the heap is reset to the mark. The implementation does **not** use a separate sub-interpreter — it reuses the main WAM's backtracking machinery within a protected stack frame.

This is a **non-declarative** primitive: it cannot be defined in pure Prolog without access to the continuation/failure mechanism. However, it CAN be defined in Prolog extended with delimited continuations (using `shift/reset` or `call/cc`):

```prolog
findall(T, G, Bag) :-
    reset(collect(T, G), done(Bag), _).

collect(T, G) :-
    call(G),
    shift(solution(T)),
    fail.
collect(_, _).
```

(With appropriate `reset` handler that accumulates `solution(T)` shifts.)

### 5.4 Relationship to SLD Resolution

findall does NOT use tabling. It uses standard SLD backtracking with an isolation mechanism. The distinction:

- **SLD + backtracking**: produces answers one at a time, interleaved with the outer computation.
- **findall**: produces ALL answers atomically, before returning to the outer computation.

findall is NOT complete if Goal has infinite solutions — it diverges. It is complete for finite answer sets.

### 5.5 bagof/3 and setof/3 Differences

- **bagof/T, G, B)**: Free variables in `G` not in `T` are implicitly universally quantified; `bagof` backtracks over their bindings, yielding one `B` per combination. Fails if `G` has no solutions.
- **setof/T, G, B)**: Like `bagof` but sorts `B` and removes duplicates via `sort/2`. Same backtracking behavior over free variables.
- **findall/T, G, B)**: All free variables in `G` existentially quantified; produces one unified `B`. Never fails.

---

## 6. Partial Evaluation and Binding-Time Analysis in Logic Programming

### 6.1 The Partial Evaluation / Partial Deduction Framework

**Partial evaluation** (PE) of a logic program `P` with respect to a partial input (static data `s`, dynamic data `d` unknown) produces a **residual program** `P_s` specialized for `s`, such that for any dynamic input `d`:
```
P(s, d) computes same result as P_s(d)
```

In logic programming, this is called **partial deduction** (Komorowski 1982; Lloyd & Shepherdson 1991). The specializer constructs a finite SLD-tree for `P` and static goal `G_s`, then extracts **resultants** (clauses) from the non-failed leaves.

### 6.2 Online vs Offline Partial Evaluation

**Online (ECCE system, Leuschel)**: Decisions about whether to unfold a goal are made dynamically based on the current program state. ECCE builds a **conjunctive partial deduction** tree that models Prolog's left-to-right evaluation. It uses abstract interpretation (e.g., depth-k abstraction) to ensure termination.

**Offline (LOGEN system, Leuschel)**: A separate **binding-time analysis (BTA)** phase first annotates each call as `unfold` (static, compute at specialization time) or `residualize` (dynamic, keep in residual program). Then the specializer executes annotated-unfold calls and generates residual code for annotated-residualize calls.

### 6.3 Binding-Time Analysis

The BTA problem: given which arguments of the top-level call are static (known at compile time), propagate "staticness" through the program.

Standard approach (two-point domain: `Static` / `Dynamic`):
```
Atom p(a1,...,an) is Static if all arguments a_i are Static AND
  p is annotated unfold (its clauses will be executed at PE time).
An argument is Static if it is:
  - a constant (always static), OR
  - a variable bound to a static value in the current clause, OR
  - a term all of whose subterms are static.
```

A **fast BTA** (Leuschel & Bruynooghe 2002) integrates size-change analysis to ensure that unfolded calls terminate — preventing infinite loops during specialization.

### 6.4 How Compile-Time Values Are Enumerated

For offline PE, if a goal `p(static_val)` is marked `unfold`, the specializer executes `p(static_val)` using standard SLD resolution (full Prolog interpreter). This computes all solutions for the static goal (via backtracking + findall if needed).

For online PE (ECCE), the specializer builds an SLD-tree for each static call, stopping when:
- A leaf is reached (residualize), OR
- A global termination condition is triggered (the call is too deep / would loop).

**Tabling in partial evaluation**: LOGEN supports tabling for the static computation phase. Tabling prevents infinite loops when the static data contains recursive structures that would cause non-termination under standard SLD. The specializer effectively becomes a Datalog-style bottom-up evaluator for static facts.

### 6.5 Correctness of Partial Deduction

**Theorem (Lloyd & Shepherdson 1991)**: Let `P` be a definite program, `A` a set of atoms. If `R` is a set of resultants obtained from a finite SLD-tree for each atom in `A`, and the tree covers all calls that arise, then `P` and `P_s` (the residual program) have the **same computed answer semantics** for any goal subsumed by atoms in `A`.

This is an instance of the SLD completeness result applied to PE trees: the residual program is correct iff the PE tree includes all relevant success branches.

### 6.6 Binding-Time Analysis Without Tabling: Incompleteness Risk

Without tabling, online PE can **fail to enumerate all static solutions** if:
- The SLD tree for a static goal is infinite (left recursion in the static fragment).
- The termination check halts before exploring all branches.

This is a standard incompleteness trade-off: PE of non-terminating static computations may produce residual programs that are less specialized than optimal (some static computations are left as dynamic). Tabling the static fragment removes this issue for Datalog-style static data (no function symbols).

---

## 7. Dead Code Elimination Decidability in EVM

### 7.1 EVM Fundamentals

The EVM (Ethereum Virtual Machine) is a **stack-based bytecode interpreter**. Control flow is determined by:
- Linear execution (most instructions).
- `JUMP`: unconditional jump to an address popped from the stack (dynamically computed).
- `JUMPI`: conditional jump to a stack address.
- `JUMPDEST`: marks valid jump targets.

### 7.2 The Halting Problem vs. Gas-Bounded Termination

The EVM is **quasi-Turing-complete**: every execution is bounded by the gas limit, making all executions finite. Thus:
- **Every EVM execution terminates** (in at most O(gas) steps).
- The question "does this bytecode terminate?" is trivially YES (due to gas). The halting problem does not apply in the usual sense.

However, **reachability** (does execution ever reach instruction at address X?) is still undecidable in the classical sense because:
- Jump targets are computed from the stack, which depends on input data.
- For arbitrary inputs, determining all reachable addresses requires solving an arbitrary constraint satisfaction problem.

The EVM is functionally equivalent to a finite-state machine (finite gas, finite memory) but the state space is astronomically large (2^256 stack words), making exact reachability analysis infeasible in practice.

### 7.3 The CFG Construction Problem

The core challenge: resolving `JUMP` targets. Unlike static jumps (as in x86 with `JMP imm`), EVM jumps take their target from the top of the stack, which is computed at runtime.

**Sound CFG construction** must over-approximate: include all possible jump targets (possibly including unreachable ones). An unsound analysis might miss edges and falsely identify reachable code as dead.

**Undecidability**: For a Turing-complete language, determining the exact set of reachable program addresses is undecidable. Since the EVM is gas-bounded (finite computation), it is technically decidable — but the decision procedure would require exploring the full state space (doubly exponential in gas).

### 7.4 Abstract Interpretation Approach (EVMLiSA, EtherTrust)

The standard approach is **abstract interpretation** over an abstract domain for the EVM stack:

**Abstract domain**: Each stack position holds either a concrete value (known) or `⊥` (unknown). Most arithmetic operations on unknowns yield `⊥`. The PUSH opcode always yields a concrete value.

**CFG construction** (EVMLiSA, Arceri et al. 2025):
1. Symbolically execute each basic block with the abstract stack.
2. At `JUMP`/`JUMPI`: if top of abstract stack is concrete value `v`, add edge to `v`; if `⊥`, add edges to ALL `JUMPDEST` instructions (over-approximation).
3. Detect loops using weakest-precondition analysis; fold back when invariant is found.
4. Minimize the resulting CFG using partition-based bisimulation.

**Soundness**: The analysis is provably sound — every concrete execution is captured by some abstract execution. Therefore, if a code block has no incoming CFG edges in the over-approximated CFG, it is **truly unreachable** and can be safely eliminated as dead code.

**Completeness**: Not guaranteed. The analysis may include spurious edges (false positives — code deemed potentially reachable that is actually dead). There is no sound and complete (exact) algorithm for the general case.

### 7.5 Horn-Clause Encoding (EtherTrust, Grishchenko et al. 2018)

EtherTrust translates EVM bytecode into a system of **Horn clauses** encoding the operational semantics:
```
step(PC, Stack, Mem, ...) :- instr(PC, PUSH, V), PC' is PC+1, step(PC', [V|Stack], Mem, ...).
step(PC, [Addr|Stack], Mem, ...) :- instr(PC, JUMP), is_jumpdest(Addr), step(Addr, Stack, Mem, ...).
```

The system of Horn clauses is then solved by Datalog-style bottom-up evaluation or CHC (Constrained Horn Clauses) solvers (Z3/SPACER). The solver computes an over-approximation of all reachable states.

**Soundness guarantee**: If the solver determines a state is unreachable (the corresponding Horn clause has no proof), then no concrete EVM execution can reach that state. Dead code detection follows: if no reachable state has `PC = address`, then `address` is dead.

**Decidability with Horn clauses**: The Horn-clause reachability problem for EVM (with finite domains / bounded arithmetic) is decidable by Datalog fixpoint computation over the abstract domain. However, it is PSPACE-hard in the worst case (Horn clause satisfiability over finite domains).

### 7.6 Practical Soundness vs. Precision

State-of-the-art results:

| Tool | Approach | Soundness | Precision | Dead Code? |
|---|---|---|---|---|
| EVMLiSA | Abstract interpretation + abstract stacks | Sound | High for real contracts | Yes (sound) |
| EtherTrust | Horn clauses + SPACER | Sound | Moderate | Yes (sound) |
| hevm | Symbolic execution (SMT) | Sound (for bounded depth) | High | Partial |
| Oyente/Mythril | Heuristic | Unsound | — | No |

### 7.7 Theoretical Status Summary

- **Exact dead code elimination**: Undecidable in general (reduces to program reachability); practically infeasible even for gas-bounded EVM due to state explosion.
- **Sound dead code elimination**: Decidable via abstract interpretation over-approximation. Any code block with no incoming edges in the sound CFG is provably dead.
- **EIP-3779 / EOF (EVM Object Format)**: Proposed EVM improvements that statically embed jump tables, making CFG construction decidable in linear time for conforming contracts. Adopted in some EVM versions.

---

## References

- Chen, W., Warren, D.S. "Tabled Evaluation with Delaying for General Logic Programs." JACM 43(1):20–74, 1996.
- Swift, T., Warren, D.S. "XSB: Extending Prolog with Tabled Logic Programming." TPLP 12(1-2):157–187, 2012.
- Abiteboul, S., Hull, R., Vianu, V. "Foundations of Databases." Addison-Wesley, 1995. (Chapter 15: Negation in Datalog)
- Lloyd, J.W. "Foundations of Logic Programming." Springer, 1987 (2nd ed.).
- Beeri, C., Ramakrishnan, R. "On the Power of Magic Sets for Bottom-Up Evaluation." PODS 1987.
- Tekle, K.T., Liu, Y.A. "More Efficient Datalog Queries: Subsumptive Tabling Beats Magic Sets." SIGMOD 2011.
- Tekle, K.T., Liu, Y.A. "Extended Magic for Negation: Efficient Demand-Driven Evaluation of Stratified Datalog with Precise Complexity Guarantees." arXiv 1909.08246, 2019.
- Leuschel, M. "The ECCE Partial Deduction System." PEPM 2004. (GitHub: leuschel/ecce)
- Leuschel, M., Bruynooghe, M. "Logic Program Specialisation through Partial Deduction: Control Issues." TPLP 2002.
- Lloyd, J.W., Shepherdson, J.C. "Partial Evaluation in Logic Programming." JLP 11(3-4):217–242, 1991.
- Grishchenko, I., Maffei, M., Schneidewind, C. "EtherTrust: Sound Static Analysis of Ethereum Bytecode." Presented at HCVS, 2018.
- Schneidewind, C., Grishchenko, I., et al. "eThor: Practical and Provably Sound Static Analysis of Ethereum Smart Contracts." CCS 2020.
- Arceri, V., et al. "EVMLiSA: Sound Static Control-Flow Graph Construction for EVM Bytecode." Blockchain Research and Applications, 2025.
- EIP-3779: "Safer Control Flow for the EVM." https://eips.ethereum.org/EIPS/eip-3779
