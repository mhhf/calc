---
title: "Anti-Unification and Most Specific Generalization: Algorithm, Theory, and Applications to State Merging"
created: 2026-02-27
modified: 2026-02-27
summary: "Deep survey of Plotkin's MSG algorithm, anti-unification over multisets, and state merging techniques in symbolic execution (Kuznetsov QCE, veritesting, supercompilation)"
tags:
  - anti-unification
  - generalization
  - symexec
  - symbolic-execution
  - state-merging
  - supercompilation
  - unification
  - memoization
  - performance
  - optimization
  - forward-chaining
  - multiset
category: "Symbolic Execution"
---

# RES_0066: Anti-Unification (Most Specific Generalization)

## 1. Plotkin's Algorithm (1970)

### Formal Definition

Given first-order terms t1 and t2, a term g is a **generalization** (or anti-unifier) of t1 and t2 if there exist substitutions s1, s2 such that g*s1 = t1 and g*s2 = t2. The **least general generalization** (lgg), also called **most specific generalization** (MSG), is the most specific such g: for any other generalization g', there exists a substitution s such that g = g'*s.

Plotkin (1970) and Reynolds (1970) independently showed that the lgg always exists and is unique (up to variable renaming) for first-order terms.

### Algorithm

The algorithm requires an **injective mapping** phi: T x T -> V that assigns a unique variable to each pair of subterms. Two rewrite rules applied exhaustively:

**Rule 1 (Decomposition):** If both terms have the same root symbol and arity:
```
f(s1,...,sn) |_| f(t1,...,tn)  =>  f(s1 |_| t1, ..., sn |_| tn)
```

**Rule 2 (Abstraction):** If the previous rule does not apply (different root symbols, different arities, or one is a variable):
```
s |_| t  =>  phi(s, t)
```
where phi(s,t) is a fresh variable, with the constraint that phi is injective: phi(s1,t1) = phi(s2,t2) iff s1=s2 and t1=t2.

The injective mapping ensures that if the **same pair** of disagreements appears at multiple positions, the **same variable** is used. This is essential for preserving shared structure.

### Worked Example

```
msg(f(a, g(b, c)), f(a, g(d, c)))
  = f(msg(a,a), msg(g(b,c), g(d,c)))     -- Rule 1: same root f/2
  = f(a, g(msg(b,d), msg(c,c)))           -- Rule 1: a=a, same root g/2
  = f(a, g(X, c))                          -- Rule 2: b!=d -> X; c=c
  where X = phi(b,d)
```

Another example showing variable sharing:
```
msg(f(a, a), f(b, b))
  = f(msg(a,a), msg(a,a))  -- WRONG: this would give f(a,a)
```
Wait -- correct computation:
```
msg(f(a, b), f(c, c))
  = f(phi(a,c), phi(b,c))  = f(X, Y)     -- two different disagreements

msg(f(a, a), f(b, b))
  = f(phi(a,b), phi(a,b))  = f(X, X)     -- SAME disagreement pair -> same var
```

The variable sharing captures that "both arguments are the same" -- a structural property preserved by the generalization.

### Handling Different Arities

When terms have different root symbols OR different arities, Rule 2 applies immediately: the entire disagreeing subterms are replaced by a single fresh variable.

```
msg(f(a, b), g(c))  =>  X           -- different root symbols
msg(f(a, b), f(c))  =>  X           -- same root, different arity (ranked setting)
```

In the **ranked** (fixed-arity) setting, function symbols have fixed arities, so different arities means different symbols. In the **unranked** setting (Kutsia, Levy, Villaret, RTA 2011), function symbols can have variable arity, and anti-unification uses **hedge variables** that stand for sequences of subterms:

```
msg(f(a, b, c), f(a, d))  =>  f(a, H)   -- H is a hedge variable
```

The unranked case introduces a combinatorial alignment problem (which subsequences to match), solved via a **rigidity function** parameter.

### Complexity

- **Time: O(|t1| + |t2|)** -- linear in the combined size of the input terms. The algorithm traverses both terms in lockstep, doing O(1) work per node.
- **Space: O(|t1| + |t2|)** for the result term plus the phi mapping.
- **Parallel complexity: NC** (in the class NC, parallelizable). Kuperberg et al. (1992) show an O(log^2 N) parallel algorithm using N/log^2 N processors on an EREW PRAM.
- **Contrast with unification:** Unification is P-complete (inherently sequential). Anti-unification is in NC (highly parallelizable). This is because anti-unification never needs to propagate constraints (no occurs check, no equation solving).

### Recursive/Cyclic Structures

Plotkin's algorithm assumes **tree-structured** (finite, acyclic) terms. For DAG-represented terms (with sharing), the algorithm still works but must handle shared subterms. The key result: anti-unification of terms represented as labeled DAGs can be done efficiently, and the output is also a DAG.

For **cyclic terms** (rational trees, as in Prolog without occurs check), anti-unification is more complex. The standard approach is to unfold cycles to a sufficient depth, but this can produce infinite generalizations. Cerna and Kutsia's survey (IJCAI 2023) notes that anti-unification for infinite terms is a less-studied area.

### N-way Generalization

The definition extends naturally: msg(t1, ..., tn) is the most specific term generalizing all ti simultaneously. Notation: t1 |_| t2 |_| ... |_| tn.

**Pairwise computation works but may lose precision:**
```
msg(msg(t1, t2), t3)  may differ from  msg(t1, msg(t2, t3))
```
Example:
```
t1 = f(a, b),  t2 = f(b, a),  t3 = f(a, a)
msg(t1, t2) = f(X, Y)              -- X=phi(a,b), Y=phi(b,a), X != Y
msg(f(X,Y), t3) = f(X', Y')        -- different vars because X!=a, Y!=a

True n-way: msg(t1, t2, t3) = f(Z, W)  -- same result here
```

In general, pairwise iterated MSG is **at least as general as** the true n-way MSG (it loses information). The true n-way MSG requires maintaining an n-way mapping phi: T^n -> V.

**Practical approach:** For n-way with small n (2-8 alternatives in oplus), pairwise iteration is usually acceptable. The information loss is in variable identity: pairwise may introduce two distinct variables where n-way would use one.

---

## 2. Anti-Unification over Multisets (The Pairing Problem)

### Problem Statement

When generalizing two **goals** (conjunctions/multisets of atoms), the key difficulty is **alignment**: which atoms in goal 1 should be paired with which atoms in goal 2 for anti-unification?

For ordered sequences, alignment is determined by position. For **unordered** multisets (as in linear logic states), alignment is a combinatorial choice.

### Yernaux & Vanhoof (CSL 2022): Anti-Unification of Unordered Goals

Two notions of generalization for unordered goals:

1. **Largest Common Generalization (LCG):** Maximize the number of atoms in the generalization (even if each is very general).
2. **Most Specific Generalization (MSG):** Maximize the specificity (structural detail) of the generalization (even if fewer atoms are included).

**Complexity results:**
- Computing LCG and MSG: **polynomial time** in the basic formulation.
- Minimizing the number of variables in the generalization: **NP-hard**.

### Reduction to Bipartite Matching

The pairing problem reduces to a **weighted bipartite matching** (assignment problem):

- Left vertices: atoms of goal 1
- Right vertices: atoms of goal 2
- Edge weight: a measure of structural similarity between atoms (e.g., size of their pairwise MSG)
- Objective: maximize total weight (most structure preserved)

The assignment problem is solvable in O(n^3) by the Hungarian algorithm.

**Complication:** When goals have different numbers of atoms with the same predicate, some atoms are left unpaired. Unpaired atoms are either dropped (in LCG) or replaced by a very general variable (in MSG).

### The k-Swap Stability Heuristic

Yernaux & Vanhoof propose **k-swap stability** as a polynomial-time approximation for the NP-hard variable-minimization problem. A generalization is k-swap stable if no swap of k or fewer atom pairings improves the objective. This is computable in O(n^{k+1}) time.

For k=1 (1-swap stability), this is equivalent to local search with single swaps, running in O(n^2). In practice, 1-swap stability already produces near-optimal results.

### Practical Approach for CALC

CALC states are multisets of facts grouped by predicate tag. A pragmatic algorithm:

```
mergeStates(S1, S2):
  for each predicate tag T present in both S1 and S2:
    facts1 = S1.factsWithTag(T)
    facts2 = S2.factsWithTag(T)
    if |facts1| != |facts2|: FAIL (different shape)
    if |facts1| == 1:
      // unambiguous pairing
      merged[T] = [msg(facts1[0], facts2[0])]
    else:
      // multiple facts with same tag: solve assignment problem
      weights[i][j] = similarity(facts1[i], facts2[j])
      pairing = hungarian(weights)
      merged[T] = [msg(facts1[i], facts2[pairing[i]]) for i]
  return merged
```

For EVM states, most predicates have exactly one instance (one `pc`, one `sh`, one `gas`, etc.). Only `stack` and `mem` may have multiple, but stack depth is already ordered. So the pairing problem is typically trivial.

---

## 3. Anti-Unification in Symbolic Execution

### 3.1 State Merging (Kuznetsov et al., PLDI 2012)

**Key insight:** Symbolic execution sits on a spectrum between "never merge" (pure forking, exponential states, simple queries) and "always merge" (linear states, complex queries). The optimal point depends on the program.

**Merging operation:** Two states at the same program point with different symbolic stores are merged:
```
state1: x = e1, path: P1
state2: x = e2, path: P2
merged: x = ITE(P1, e1, e2), path: P1 v P2
```

**Query Count Estimation (QCE):** A static preprocessing step that estimates the cost of merging. For each variable v at each potential merge point p:

```
QCE(v, p) = count of downstream branch conditions referencing v
```

Parameters:
- Each query takes 1 time unit
- An ITE expression increases query cost by factor zeta > 1
- Branch feasibility probability: fraction of branches that trigger solver calls
- Iteration bound: limits the CFG traversal depth

**Decision rule:** Merge states only when the estimated cost saving (fewer states) exceeds the estimated cost increase (harder queries due to ITE expressions).

**Dynamic State Merging (DSM):** Integrates QCE into the exploration scheduler. Instead of statically identifying merge points, DSM dynamically groups "similar" states (same QCE-relevant variables are concrete) and fast-forwards them to check if they converge.

**Results on CoreUtils (82 programs):** QCE+DSM improves path coverage by orders of magnitude (up to 10^11x) compared to pure forking.

### 3.2 Veritesting (Avgerinos et al., ICSE 2014)

**Hybrid approach:** Dynamically switches between:
- **DSE mode** (dynamic symbolic execution): fork at every branch, concrete execution
- **SSE mode** (static symbolic execution): compute a single formula over an entire CFG region, merging all paths

**Transition criterion:** Enter SSE when the CFG ahead is a DAG with no system calls, indirect jumps, or complex memory operations. Exit SSE at "transition nodes" where complications arise.

**State merging mechanism:** In SSE mode, veritesting converts the CFG region to a single disjunctive formula. Branch outcomes become disjuncts in the merged formula. This is equivalent to unconditional merging within the region.

**Results:** 2x more bugs found, 27% more code coverage, tested 33,248 Debian programs. The key insight: most code is "easy" (suitable for SSE/merging), with occasional "hard" spots requiring forking.

**Relevance to CALC:** Veritesting's SSE/DSE switching is analogous to choosing between eager branching (current symexec) and speculative merge at oplus points. The "easy region" concept maps to committed-choice segments between oplus points.

### 3.3 MultiSE / Value Summaries (Sen et al., ESEC/FSE 2015)

**Value summaries:** Each variable maps to a set of guarded expressions `{(guard_i, value_i)}`. The program counter itself is a guarded value. Merging happens incrementally at every assignment, not just at join points.

**Advantages over ITE-based merging:**
- No auxiliary symbolic variables introduced
- Works with solver-opaque operations (function pointers, dynamic dispatch)
- Concrete values remain concrete (guards collapse when ground)
- No nested ITE expressions (guards are factored out)

**Relevance to CALC:** Value summaries are conceptually close to what MSG+evars achieves. An evar produced by MSG is essentially a value summary with the guard implicit in the branch that produced it.

### 3.4 Lattice Model (Scheurer, Hahnle, Bubel, ICFEM 2016)

**Formal framework:** State merging is a join in a lattice:
- **Abstract domain A:** a join-semilattice of possible values
- **Merge operator:** the join, applied pointwise to all variables
- **Soundness criterion:** merged state is a sound overapproximation (every concrete execution of originals is a concrete execution of merged state)

**Key theorem:** Merging is sound if the merge operator forms a Galois connection with the concrete domain (i.e., it is an abstract interpretation).

**Instantiations:**

| Lattice | Precision | Solver cost |
|---|---|---|
| Full symbolic (ITE) | Exact | High |
| Predicate abstraction | Medium | Medium |
| Sign/interval | Coarse | None |

**Result:** Predicate abstraction merging produces proof obligations 15-25% smaller than ITE merging or no merging.

---

## 4. Anti-Unification in Supercompilation

### The Supercompilation Loop

Turchin's supercompilation (1986) builds a **process tree** of configurations (program states with symbolic inputs). Three operations:

1. **Driving:** Unfold one computation step, extending the tree.
2. **Folding:** If the current configuration is a renaming of a previous node, create a back-edge (tree becomes graph). Detects exact structural equivalence.
3. **Generalization:** If the homeomorphic embedding whistle fires (current config is "growing" relative to a previous one), compute MSG of the two configs and restart from the generalized configuration.

### Homeomorphic Embedding (The Whistle)

The relation s <| t (s is homeomorphically embedded in t):
```
s <| f(t1,...,tn)        if s <| ti for some i            (diving)
f(s1,...,sn) <| f(t1,...,tn)  if si <| ti for all i       (coupling)
```

**Kruskal's Tree Theorem** guarantees: in any infinite sequence of terms, there exist i < j with ti <| tj. So the whistle always eventually fires, ensuring termination.

### MSG in Supercompilation

When the whistle fires (ti <| tj), the supercompiler computes msg(ti, tj):
- If msg produces meaningful shared structure: **generalize** and continue from the generalized config.
- If msg produces just a variable (completely disjoint terms): **split** the configuration into independent parts.
- If tj is a direct instance of ti: **fold** (create back-edge).

The implementation from Gluck & Sorensen uses two sub-rules applied iteratively:
1. **Common functor:** Extract matching function applications from substitution bindings.
2. **Common substitution:** When two distinct variables bind identical terms, merge them.

These iterate until no more generalizations apply (fixed point).

### Relevance to CALC

The supercompilation framework maps directly:

| Supercompilation | CALC Forward Chaining |
|---|---|
| Configuration | State (linear + persistent multiset) |
| Driving | Applying one forward rule |
| Folding | Memo hit (exact state match) |
| Generalization | MSG of states at oplus branches |
| Whistle | Homeomorphic embedding on state terms |

The current structural memo in CALC (`controlHash`) is a crude **folding** criterion. MSG-based merging would add a proper **generalization** criterion, handling cases where states are similar but not identical.

---

## 5. Equational Anti-Unification

Standard anti-unification is **syntactic** (literal term structure). For richer theories, generalizations must respect equational axioms.

### Associative-Commutative (AC) Anti-Unification

For operators that are associative and/or commutative (like multiset union, addition):
- **Commutative (C):** Baader showed anti-unification is unitary in restricted settings.
- **AC and ACU:** Alpuente et al. provide complete algorithms, proving the problem is **finitary** (the minimal complete set of generalizations is finite but may contain more than one element).

### Relevance to Linear Logic

Linear logic states are multisets (commutative monoids under tensor). Anti-unification of states should respect commutativity:
```
msg({a, b, c}, {a, d, c})  should give  {a, X, c}
```
not depend on the ordering of elements. This is exactly **AC anti-unification** where the operation is multiset union.

The NP-hardness of variable minimization (Yernaux & Vanhoof) arises precisely because commutativity introduces exponentially many possible alignments.

---

## 6. Precision vs Performance Tradeoffs

### When Merging Helps

- **Symmetric branching:** Multiple alternatives lead to structurally identical continuations. Merging eliminates redundant exploration. (The multisig member-check pattern.)
- **Data-independent control flow:** When downstream branching is independent of the merged-away values.
- **Low QCE variables:** Variables rarely referenced in future branch conditions can be safely merged.

### When Merging Hurts

- **Data-dependent branching:** If downstream code branches on the merged-away value, the merged state explores both branches even when only one was feasible in each original state. This creates **spurious paths**.
- **ITE explosion:** Merged expressions accumulate nested ITE terms. SMT solvers struggle with deeply nested ITEs (exponential case splits).
- **Loss of concreteness:** Merging turns concrete values into symbolic ones, disabling concrete execution optimizations (constant folding, memoization).
- **Solver query amplification:** Each ITE in a branch condition multiplies the solver's case analysis.

### Empirical Evidence

From Kuznetsov PLDI 2012:
- Most CoreUtils programs benefit from selective merging (QCE+DSM).
- A few programs slow down due to ITE expressions.
- A few crash (presumably solver timeouts from ITE explosion).

From veritesting:
- SSE (aggressive merging) does not always find every bug that DSE finds. Some bugs are masked by the disjunctive formula.
- Overall, the net effect is strongly positive (2x more bugs, 27% more coverage).

### MSG vs ITE Merging

MSG (Plotkin-style) differs from ITE merging in a crucial way:

| Property | MSG (evars) | ITE merging |
|---|---|---|
| Result type | Fresh unconstrained variable | ITE(cond, v1, v2) expression |
| Condition tracking | Lost | Preserved |
| Downstream precision | May explore spurious paths | Exact (no precision loss) |
| Implementation cost | Low (just anti-unify) | High (need symbolic expression type, solver) |
| Solver interaction | None (evars are opaque) | Heavy (ITE in queries) |

MSG is a **lossy** approximation of ITE merging. It is cheaper but may introduce false positives (spurious paths). ITE merging is **exact** but requires a symbolic expression language and solver support.

For CALC, MSG is the pragmatic choice: it works with the existing content-addressed store and evar mechanism, without requiring architectural changes (see TODO_0056).

---

## 7. Open Research: Linear Logic + Anti-Unification

No published work directly combines linear logic proof search with anti-unification for state merging. The closest connections:

- **Simmons & Pfenning (PEPM 2009):** Linear logical approximations for abstract interpretation. Uses contraction/weakening approximations of linear logic programs to overapproximate reachable states. This is abstract interpretation, not anti-unification, but addresses the same goal (state space reduction in forward chaining).

- **CLF monadic encapsulation (Watkins et al. 2002):** CLF identifies forward-chaining computations that differ only in rule ordering. This is permutation equivalence, which is a form of structural equivalence but not anti-unification.

- **DPOR for linear logic (Flanagan & Godefroid 2005, applied to forward chaining):** Partial-order reduction eliminates redundant interleavings of independent rule applications. Complementary to MSG-based merging: DPOR reduces branching from rule ordering, MSG reduces branching from symmetric data.

The combination of linear logic states (multisets of resources) with MSG-based generalization appears to be novel territory. The key challenge is that linear resource consumption makes the pairing problem context-dependent: which facts to pair depends on which rules will consume them, which is unknown at merge time.

---

## Key References

- Plotkin, G.D. *A Note on Inductive Generalization*. Machine Intelligence 5, pp. 153-163, 1970.
- Reynolds, J.C. *Transformational Systems and the Algebraic Structure of Atomic Formulas*. Machine Intelligence 5, pp. 135-151, 1970.
- Kutsia, T., Levy, J., Villaret, M. *Anti-Unification for Unranked Terms and Hedges*. RTA 2011 / J. Automated Reasoning 2014.
- Yernaux, G., Vanhoof, W. *Anti-Unification of Unordered Goals*. CSL 2022.
- Cerna, D.M., Kutsia, T. *Anti-Unification and Generalization: A Survey*. IJCAI 2023.
- Kuznetsov, V., Kinder, J., Bucur, S., Candea, G. *Efficient State Merging in Symbolic Execution*. PLDI 2012.
- Avgerinos, T., Rebert, A., Cha, S.K., Brumley, D. *Enhancing Symbolic Execution with Veritesting*. ICSE 2014.
- Sen, K., Necula, G., Gong, L., Choi, W. *MultiSE: Multi-Path Symbolic Execution using Value Summaries*. ESEC/FSE 2015.
- Scheurer, D., Hahnle, R., Bubel, R. *A General Lattice Model for Merging Symbolic Execution Branches*. ICFEM 2016.
- Turchin, V.F. *The Concept of a Supercompiler*. TOPLAS 1986.
- Sorensen, M.H., Gluck, R. *An Algorithm of Generalization in Positive Supercompilation*. 1995.
- Kuperberg, G., et al. *A Note on the Parallel Complexity of Anti-Unification*. J. Automated Reasoning 1992.
- Baader, F. *Unification in Commutative Theories*. J. Symbolic Computation, 1989.
- Alpuente, M., et al. *A Modular Order-Sorted Equational Generalization Algorithm*. Information and Computation, 2014.
- Simmons, R.J., Pfenning, F. *Linear Logical Approximations*. PEPM 2009.
