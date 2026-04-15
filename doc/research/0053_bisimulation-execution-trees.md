---
title: "Bisimulation via Execution Trees"
created: 2026-02-24
modified: 2026-02-24
summary: "Survey of bisimulation theory, algorithms, and up-to techniques applied to exhaustive linear logic execution trees, with connections to process interpretations, session types, and coinduction"
tags: [bisimulation, execution-trees, coinduction, partition-refinement, up-to, session-types, process-algebra, linear-logic]
category: "Proof Theory"
---

# Bisimulation via Execution Trees

CALC produces **exhaustive execution trees** via forward chaining over linear logic programs. Two programs can be compared by checking whether their execution trees exhibit the same branching structure --- this is bisimulation. This document surveys the theory, algorithms, and linear-logic-specific connections that make this viable.

---

## 1. What Bisimulation Means for Execution Trees

### 1.1 The Standard Definition

Given two labeled transition systems (LTSs) `(S1, Act, ->1)` and `(S2, Act, ->2)`, a **bisimulation** is a relation R on S1 x S2 such that whenever `(s1, s2) in R`:

- If `s1 --a--> s1'`, then there exists `s2'` with `s2 --a--> s2'` and `(s1', s2') in R`.
- Symmetrically: if `s2 --a--> s2'`, then there exists `s1'` with `s1 --a--> s1'` and `(s1', s2') in R`.

Two states are **bisimilar** (`s1 ~ s2`) if there exists a bisimulation containing `(s1, s2)`. Bisimilarity is the largest bisimulation --- the greatest fixed point of the bisimulation functional (Sangiorgi 2012).

### 1.2 CALC's Execution Trees as LTSs

A CALC execution tree is directly an LTS:

| LTS component | CALC equivalent |
|---|---|
| State | Multiset of linear + persistent facts (content-addressed hash) |
| Action | Rule application `(rule_name, substitution)` |
| Transition | `mutateState`: consume linear facts, produce new facts |
| Terminal | `leaf` (quiescent), `cycle` (back-edge), `bound` (depth limit) |

The execution tree already enumerates **all** transitions from every reachable state. Branch nodes = all applicable rules; fork nodes = all disjunctive alternatives (oplus). The tree IS the unfolding of the LTS.

### 1.3 What Bisimulation Captures

Two CALC programs P1, P2 with initial states S1, S2 are bisimilar when:

1. **Same branching structure** --- at every state, the same rules are applicable.
2. **Same observable effects** --- each rule application produces equivalent successor states.
3. **Same terminal behavior** --- the same leaf states (quiescent multisets) are reachable.

This is strictly stronger than trace equivalence (same set of execution traces). Bisimulation preserves the **branching structure** --- it distinguishes a program that can choose between A-then-B and A-then-C from one that must commit to A-then-B before knowing about C.

### 1.4 Bisimulation as Coinduction

Bisimilarity is defined coinductively: `~ := nu R. F(R)` where `F` is the bisimulation functional. This connects directly to TODO_0009 (coinduction/fixed points). In muMALL:

```
Bisim(P1, P2) := nu R. forall action.
  (Step(P1, action) -o exists P1'. Step(P1', action) tensor R(P1', P2'))
  & (Step(P2, action) -o exists P2'. Step(P2', action) tensor R(P1', P2'))
```

The coinductive definition means: two systems are bisimilar if, after any finite number of observations, they remain indistinguishable.

---

## 2. How CALC's Exhaustive Trees Enable Automatic Bisimulation

### 2.1 The Key Advantage

Classical bisimulation checking requires exploring the joint state space of two LTSs on-the-fly. CALC's `explore()` already builds the complete tree for each program. With both trees materialized, bisimulation checking becomes a **structural comparison** --- no further state-space exploration is needed.

### 2.2 Naive Algorithm (Structural Tree Comparison)

For finite trees (bounded gas, bounded depth):

```javascript
function checkBisimulation(tree1, tree2) {
  // Terminal cases
  if (tree1.type === 'leaf' && tree2.type === 'leaf')
    return statesEquivalent(tree1.state, tree2.state);
  if (tree1.type !== tree2.type) return false;

  // Branch: both must offer the same rules
  if (tree1.type === 'branch') {
    const s1 = [...tree1.children].sort(byRule);
    const s2 = [...tree2.children].sort(byRule);
    if (s1.length !== s2.length) return false;
    return s1.every((c1, i) =>
      c1.rule === s2[i].rule &&
      checkBisimulation(c1.child, s2[i].child));
  }
  return false;
}
```

**Complexity:** O(|T1| + |T2|) --- linear in tree size. State comparison is O(1) via content-addressed hashing.

### 2.3 Refined Notion: Observational Equivalence

The naive algorithm checks **strong bisimulation** (every rule matched exactly). For practical program comparison, weaker notions suffice:

| Equivalence | What it checks | CALC application |
|---|---|---|
| **Strong bisimulation** | Same rules, same branching | Exact equivalence |
| **Weak bisimulation** | Ignores internal (tau) steps | Ignoring auxiliary rules |
| **Branching bisimulation** | Preserves branching under tau | Internal optimization steps |
| **Trace equivalence** | Same set of leaf states | Same observable outcomes |
| **Barbed congruence** | Same observations in all contexts | Full contextual equivalence |

For CALC's EVM programs, **strong bisimulation on leaf states** is the most useful: two programs are equivalent if they produce the same set of final states regardless of rule ordering.

### 2.4 Content-Addressed Hashing Advantage

CALC's content-addressed store gives O(1) state equality. Two states with identical multisets of facts produce identical hashes. This eliminates the expensive state-matching step that dominates classical bisimulation algorithms. The Paige-Tarjan algorithm is O((m+n) log n); CALC's tree comparison is O(n) because state equality is free.

---

## 3. Algorithms

### 3.1 Partition Refinement (Paige-Tarjan)

The classical algorithm for computing the coarsest bisimulation on an LTS:

1. Start with partition P = {S} (all states in one block).
2. For each block B and action a, compute the **splitter**: states in B that can do a to reach B vs. those that cannot.
3. Split blocks until stable.
4. The stable partition defines the bisimulation equivalence classes.

**Complexity:** O((m+n) log n) where n = states, m = transitions (Paige & Tarjan, SIAM J. Computing 1987). Lower bound: Omega((m+n) log n) (Groote, CONCUR 2021).

**For CALC:** Partition refinement applies when comparing a single program against itself (quotienting the execution tree by bisimulation to find the minimal equivalent tree). This is useful for:
- **State-space reduction:** Merge bisimilar subtrees.
- **Symmetry detection:** Identify rule orderings that produce equivalent behavior.
- **Quotient trees:** Compress the execution tree modulo bisimulation.

### 3.2 On-the-Fly Comparison (Two Trees)

For comparing two different programs, a **synchronized BFS/DFS** over both trees suffices:

```
CompareQueue = [(root1, root2)]
Visited = {}

while CompareQueue is not empty:
  (n1, n2) = dequeue(CompareQueue)
  if (n1, n2) in Visited: continue   // coinductive success
  Visited.add((n1, n2))

  if terminal(n1) and terminal(n2):
    check stateEquiv(n1.state, n2.state)
  elif branch(n1) and branch(n2):
    match children by rule name
    enqueue corresponding child pairs
  else:
    report divergence at (n1, n2)
```

The `Visited` set implements **coinduction**: revisiting a pair means the trees are structurally recursive at that point, which is success (not failure). This is exactly Bedwyr's tabling strategy applied to bisimulation.

### 3.3 Bisimulation Minimization of Tree Automata

CALC's execution trees are tree-structured, not graph-structured (modulo back-edges). Tree automata minimization via bisimulation (Hogberg, Maletti & May, 2006) applies:

- View the execution tree as a tree automaton where states are tree nodes and transitions are edges.
- Minimize by merging bisimilar subtrees.
- Result: the smallest tree automaton accepting the same tree language.

This produces a **canonical representative** for each bisimulation class of programs.

---

## 4. Up-To Techniques

### 4.1 The Problem

Proving bisimulation directly requires exhibiting a relation R that is a post-fixed point of the bisimulation functional. For complex systems, R can be enormous. **Up-to techniques** allow proving bisimulation with a smaller relation by closing it under additional operations.

### 4.2 Bisimulation Up-To Equivalence

Instead of requiring `(s1', s2') in R` after matching transitions, allow `(s1', s2') in ~.R.~` (compose R with bisimilarity). This means: the successors need not be directly related by R, only bisimilar to something in R.

### 4.3 Bisimulation Up-To Context (Congruence)

For CALC: if two programs differ only in a subexpression, establish bisimulation only for the differing part and close under the shared context. This is **compositional bisimulation**.

Bonchi & Pous (POPL 2013) showed that bisimulation up-to congruence can exponentially reduce the number of pairs to check. Their NFA equivalence checker based on this technique outperforms classical algorithms by orders of magnitude.

### 4.4 Fibrational Framework (Bonchi, Petrisan, Pous & Rot 2014)

The most general treatment: bisimulation up-to in a fibrational setting. They prove soundness of up-to techniques for a large class of coinductive predicates modeled as coalgebras. The framework systematically derives sound up-to techniques from the structure of the coalgebra.

**Applicability to CALC:** CALC's execution trees form a coalgebra (each state maps to its set of successors). The fibrational framework guarantees soundness of up-to techniques for this coalgebra, including up-to equivalence, up-to context, and up-to union.

### 4.5 Practical Up-To for CALC

Three up-to techniques are immediately useful:

1. **Up-to state equivalence:** Two states with the same content-addressed hash are equivalent. Already built into CALC's O(1) comparison.

2. **Up-to persistent context:** If two states differ only in persistent facts (which are monotonic --- never consumed), they are equivalent modulo the persistent context. This factors out the growing persistent store.

3. **Up-to rule ordering:** If two branch nodes have the same children (modulo permutation), they are bisimilar regardless of the order in which rules were tried. CALC already normalizes by sorting children by rule name.

---

## 5. Connection to Linear Logic

### 5.1 Proofs as Processes (Abramsky 1994, Bellin & Scott 1994)

The foundational observation: cut elimination in classical linear logic corresponds to communication in the pi-calculus. Proofs ARE processes; proof normalization IS process reduction.

- **Abramsky (1994)** observed that linear cut elimination resembles reduction in CCS and pi-calculus.
- **Bellin & Scott (1994)** gave the detailed translation from proof nets to a synchronous pi-calculus, with soundness and completeness results for fragments of CLL.

**Consequence:** Bisimulation of processes = bisimulation of proofs (modulo the translation). Two linear logic proofs are "behaviorally equivalent" if their corresponding processes are bisimilar.

### 5.2 Propositions as Sessions (Caires & Pfenning 2010, Wadler 2012)

The modern incarnation: linear logic propositions correspond to session types.

- **Caires & Pfenning (2010):** Intuitionistic linear logic propositions = session types for pi-calculus processes. Type preservation ensures session fidelity; the logic ensures deadlock freedom.
- **Wadler (2012):** Classical linear logic propositions = session types in CP/GV. Cut elimination = process reduction. Deadlock freedom follows from the correspondence.
- **Perez, Caires & Pfenning (2012):** Linear logical relations for session-based concurrency. Adapted barbed bisimulation to the linear setting. Reductions on linear channels induce a "partial confluence" of process behaviors.

**Connection to CALC:** CALC's loli continuations (`A -o B` in state) are linear channels --- they consume A and produce B, exactly like a session-typed channel offering input A and output B. Bisimulation of CALC programs with loli continuations = bisimulation of session-typed processes.

### 5.3 Linearity and Bisimulation (Yoshida, Honda & Berger 2002)

Linear types strengthen bisimulation by restricting the observer:

> Linear typing guarantees that certain channels are used exactly once. An observer constrained by linearity cannot duplicate or discard communications, yielding a coarser (larger) bisimulation that still captures all observable behavior.

Their result: the linear bisimulation is **strictly coarser** than standard bisimulation while remaining sound. This means linearity makes equivalence EASIER to establish --- fewer distinctions to check.

**For CALC:** Linear facts are used exactly once (consumed by a rule). This is inherently a linear-typed discipline. CALC's bisimulation benefits from this: two programs that differ only in how they internally manage linear resources are identified as equivalent, because an external observer cannot distinguish them.

### 5.4 The Deng-Cervesato-Simmons Result (MSCS 2016)

The key bridge between linear logic proof theory and process-theoretic bisimulation:

> For a CCS-like calculus obtained from the formula-as-process interpretation of linear logic, the proof-theoretic logical preorder coincides with the process-theoretic contextual preorder.

The proof uses coinductively defined simulation as a stepping stone. This means: if two CALC programs are "logically equivalent" (one entails the other in ILL), they are also "process-equivalent" (bisimilar as concurrent systems). The converse holds too.

### 5.5 Petri Net Bisimulation

Since CALC's forward engine is a Petri net (RES_0050 Section 1), Petri net bisimulation theory applies:

- **Bisimilarity of Petri nets is undecidable** for labeled nets (Jancar, 1995). However:
- **Bisimilarity is decidable for BPP** (Basic Parallel Processes --- Petri nets without synchronization). Decidable in polynomial time.
- **Resource bisimulation** (Vogler): two markings are resource-bisimilar if substituting one for the other doesn't change net behavior. Undecidable in general, but decidable for restricted classes.

For CALC's ground programs (like EVM), the finite state space makes all bisimulation questions decidable.

---

## 6. Connection to Coinduction and TODO_0009

### 6.1 Bisimulation IS Coinduction

Bisimilarity is the canonical example of a coinductively defined property. The bisimulation functional F maps a relation R to the set of pairs that can match one step and remain in R. Bisimilarity = nu R. F(R) = the greatest fixed point of F.

TODO_0009 proposes three implementation paths for coinduction in CALC:
- **Option C (tabling):** State memoization. For bisimulation: if a pair (s1, s2) has been visited, it's coinductively bisimilar.
- **Option B (cyclic proofs):** The bisimulation proof has back-edges (revisiting a pair). The global trace condition validates the proof.
- **Option A (muMALL):** Express `Bisim` as a nu-formula directly in the logic.

### 6.2 Bisimulation via Tabling (Bedwyr-Style)

Bedwyr checks coinductive predicates by tabling: revisiting a goal on the current path = success. For bisimulation:

1. `check_bisim(s1, s2)`: if `(s1, s2)` is tabled, return success (coinductive hypothesis).
2. Otherwise, table `(s1, s2)` and check all one-step successors.
3. If all successor pairs are bisimilar (recursively), succeed.

CALC already has the infrastructure: `pathVisited` in `symexec.js` implements path-based tabling via content-addressed hashing. Extending it to pairs `(hash1, hash2)` is straightforward.

### 6.3 Bisimulation via Cyclic Proofs

A cyclic proof of bisimulation has the structure:

```
  (s1, s2) |-  Bisim(s1, s2)
    |
    v
  For each action a:
    s1 --a--> s1'  matched by  s2 --a--> s2'
    Bisim(s1', s2')   -- recursive goal
      |
      v
    ... eventually reaches (s1, s2) again (back-edge)
```

The global trace condition (GTC) ensures that every infinite path through the unfolded proof exhibits infinite progress through the nu-unfolding. Since bisimulation is a nu-formula, progress = unfolding nu = one step of the bisimulation check. Every infinite path that keeps checking one step is valid.

---

## 7. What Bisimulation Lets You Verify

### 7.1 Compiler/Optimizer Correctness

> "The optimized program behaves like the reference implementation."

Given:
- `P_ref`: reference implementation (simple, obviously correct).
- `P_opt`: optimized version (complex, faster).
- Explore both: `T_ref = explore(P_ref)`, `T_opt = explore(P_opt)`.
- Check: `checkBisimulation(T_ref, T_opt)`.

If bisimilar: `P_opt` is a correct optimization.

### 7.2 Refactoring Safety

> "Splitting a rule into two sub-rules doesn't change behavior."

Example from TODO_0009 Section 3.4: direct transfer vs. two-step transfer (debit then credit). Bisimulation checks that the decomposed version reaches the same final states.

### 7.3 Protocol Conformance

> "The implementation conforms to the specification."

For smart contracts: the specification defines allowed state transitions. The implementation's execution tree must be bisimilar (or simulated by) the specification's tree.

### 7.4 Regression Testing

> "The new version behaves identically to the old version."

Run `explore()` on both versions, compare trees. Any behavioral difference is detected, with the divergence point identified.

### 7.5 Confluence Checking (Weaker Than Bisimulation)

Two branch children that lead to the same leaf sets are **confluent** (rule order doesn't matter). This is a special case of bisimulation where both trees come from the same program at the same state.

---

## 8. Implementation Sketch for CALC

### 8.1 Module: `lib/engine/bisim.js` (~80 LOC)

```javascript
// Core: compare two execution trees
function bisimilar(t1, t2, opts = {}) {
  const visited = new Set();
  const equiv = opts.stateEquiv || defaultStateEquiv;

  function go(n1, n2) {
    // Coinductive guard
    const key = pairKey(n1, n2);
    if (visited.has(key)) return true;
    visited.add(key);

    // Terminal cases
    if (n1.type === 'leaf' && n2.type === 'leaf')
      return equiv(n1.state, n2.state);
    if (n1.type === 'cycle' && n2.type === 'cycle')
      return equiv(n1.state, n2.state);
    if (n1.type !== n2.type) return false;

    // Branch: match children by rule name
    if (n1.type === 'branch') {
      const c1 = groupByRule(n1.children);
      const c2 = groupByRule(n2.children);
      if (!sameKeys(c1, c2)) return false;
      for (const rule of Object.keys(c1)) {
        if (!go(c1[rule], c2[rule])) return false;
      }
      return true;
    }
    return false;
  }
  return go(t1, t2);
}

// Weaker: same leaf state sets (trace equivalence)
function traceEquivalent(t1, t2) {
  const leaves1 = getAllLeaves(t1).map(l => stateHashStr(l.state)).sort();
  const leaves2 = getAllLeaves(t2).map(l => stateHashStr(l.state)).sort();
  return arraysEqual(leaves1, leaves2);
}

// State equivalence: default uses stateHashStr
function defaultStateEquiv(s1, s2) {
  return stateHashStr(s1) === stateHashStr(s2);
}
```

### 8.2 Integration Points

| Existing module | How bisim.js uses it |
|---|---|
| `symexec.js: explore()` | Produces the two trees to compare |
| `symexec.js: stateHashStr()` | O(1) state equality |
| `symexec.js: getAllLeaves()` | Leaf enumeration for trace equivalence |
| `show.js: show()` | Human-readable divergence reporting |

### 8.3 API

```javascript
const { bisimilar, traceEquivalent } = require('./bisim');

const t1 = explore(state1, rules1, { calc, maxDepth: 200 });
const t2 = explore(state2, rules2, { calc, maxDepth: 200 });

bisimilar(t1, t2);        // => true/false
traceEquivalent(t1, t2);  // => true/false (weaker check)
```

### 8.4 Divergence Reporting

When bisimulation fails, report the first divergence point:

```javascript
function findDivergence(t1, t2) {
  // Returns { path, reason, state1, state2 }
  // path = sequence of (rule, choice) from root to divergence
  // reason = 'different_type' | 'different_leaves' | 'missing_rule' | ...
}
```

---

## 9. Open Questions and Research Directions

### 9.1 Weak Bisimulation for CALC

Strong bisimulation requires every rule to be matched exactly. For optimization verification, some rules are "internal" (auxiliary computations) and should be treated as tau-steps. Defining which CALC rules are "internal" requires a notion of **observable vs. internal** actions --- not yet defined for CALC.

### 9.2 Symbolic Bisimulation

CALC's symbolic execution produces trees with symbolic values (metavariables). Two symbolic trees might be bisimilar under all ground instantiations but structurally different. **Symbolic bisimulation** (Hennessy & Lin, 1995) extends bisimulation to symbolic transition systems. Adapting this to CALC requires integrating with constraint propagation (TODO_0005).

### 9.3 Bisimulation for Infinite Trees

CALC's `cycle` nodes represent potentially infinite behavior. Bisimulation of trees with back-edges requires coinduction. The tabling approach (Section 6.2) handles this, but formal soundness needs the muMALL coinduction framework (TODO_0009 Phase 4).

### 9.4 Quotient Trees and Canonical Forms

Given a single execution tree, compute its **bisimulation quotient** (merge bisimilar subtrees). This produces a minimal representation. Questions:
- Can the quotient be computed incrementally (during exploration, not post-hoc)?
- Does the quotient have a canonical form (unique representative per equivalence class)?
- Can the quotient be used for **memoization** (if two states have bisimilar subtrees, compute once)?

### 9.5 Bisimulation Metrics

For approximate equivalence: define a **bisimulation distance** between trees. Two programs that are "almost bisimilar" (differ in few branches) have small distance. This connects to behavioral metrics (Desharnais et al., 2004) and quantitative bisimulation (Giacalone et al., 1990).

### 9.6 Connection to CHR Operational Equivalence

Abdennadher & Fruhwirth (1999) gave a decidable syntactic condition for operational equivalence of confluent, terminating CHR programs. This is a restricted form of bisimulation (only for well-behaved programs). CALC could implement this check for its forward rules, complementing full bisimulation.

### 9.7 Resource Bisimulation

Vogler's resource bisimulation for Petri nets asks: can one marking be substituted for another without changing net behavior? In CALC terms: can one multiset of facts be replaced by another while preserving all future executions? This is relevant for state abstraction and symmetry reduction.

---

## 10. Bibliography

### Bisimulation Theory (Foundational)
- Sangiorgi, D. *Introduction to Bisimulation and Coinduction.* Cambridge University Press, 2012. ISBN 978-1-107-00363-7.
- Sangiorgi, D. & Rutten, J. (eds.) *Advanced Topics in Bisimulation and Coinduction.* Cambridge Tracts in Theoretical Computer Science 52, 2012.
- Park, D. "Concurrency and automata on infinite sequences." LNCS 104, pp. 167--183, 1981.
- Milner, R. "A calculus of communicating systems." LNCS 92, Springer, 1980.

### Algorithms
- Paige, R. & Tarjan, R.E. "Three partition refinement algorithms." SIAM J. Computing 16(6), pp. 973--989, 1987.
- Groote, J.F. "Bisimulation by partitioning is Omega((m+n) log n)." CONCUR 2021, LIPIcs 203, 31:1--31:16.
- Hogberg, J., Maletti, A. & May, J. "Bisimulation minimization of tree automata." Int. J. Foundations of Computer Science 20(4), pp. 699--722, 2009.

### Up-To Techniques
- Bonchi, F. & Pous, D. "Checking NFA equivalence with bisimulations up to congruence." POPL 2013, pp. 457--468. doi:10.1145/2429069.2429124.
- Bonchi, F., Petrisan, D., Pous, D. & Rot, J. "Coinduction up to in a fibrational setting." LICS 2014, pp. 20:1--20:10. doi:10.1145/2603088.2603149.
- Pous, D. & Sangiorgi, D. "Enhancements of the bisimulation proof method." In *Advanced Topics in Bisimulation and Coinduction*, CUP, 2012.
- Sangiorgi, D. "Bisimulation and coinduction enhancements: a historical perspective." Formal Aspects of Computing 31, pp. 733--749, 2019.

### Linear Logic and Process Algebra
- Abramsky, S. "Proofs as processes." Theoretical Computer Science 135(1), pp. 5--9, 1994.
- Bellin, G. & Scott, P.J. "On the pi-calculus and linear logic." Theoretical Computer Science 135(1), pp. 11--65, 1994.
- Caires, L. & Pfenning, F. "Session types as intuitionistic linear propositions." CONCUR 2010, LNCS 6269, pp. 222--236.
- Wadler, P. "Propositions as sessions." ICFP 2012 / JFP 24(2--3), pp. 384--418, 2014.
- Perez, J.A., Caires, L. & Pfenning, F. "Linear logical relations for session-based concurrency." ESOP 2012, LNCS 7211, pp. 539--558.

### Linearity and Bisimulation
- Yoshida, N., Honda, K. & Berger, M. "Linearity and bisimulation." FoSSaCS 2002, LNCS 2303, pp. 417--433. Extended: JLAP 72(1), pp. 19--37, 2007.
- Deng, Y., Cervesato, I. & Simmons, R.J. "Relating reasoning methodologies in linear logic and process algebra." MSCS 26(5), pp. 868--906, 2016. doi:10.1017/S0960129514000218.

### Petri Net Bisimulation
- Jancar, P. "Undecidability of bisimilarity for Petri nets and some related problems." Theoretical Computer Science 148(2), pp. 281--301, 1995.
- Vogler, W. "Bisimulation and action refinement." Theoretical Computer Science 114(1), pp. 173--200, 1993.

### Coinduction and Fixed Points
- Baelde, D. & Miller, D. "Least and greatest fixed points in linear logic." ACM TOCL 13(1), Article 2, 2012.
- Doumane, A. "On the infinitary proof theory of logics with fixed points." PhD thesis, Universite Sorbonne Paris Cite, 2017.
- Baelde, D., Gacek, A., Miller, D., Nadathur, G. & Tiu, A. "The Bedwyr system for model checking over syntactic expressions." CADE 2007, LNCS 4603, pp. 391--397.

### CHR Equivalence
- Abdennadher, S. & Fruhwirth, T. "Operational equivalence of CHR programs and constraints." CP 1999.
- Abdennadher, S., Fruhwirth, T. & Meuss, H. "Confluence and semantics of constraint simplification rules." Constraints 4(2), pp. 133--165, 1999.

### CALC Internal References
- THY_0001 --- Exhaustive forward chaining (execution tree judgment)
- RES_0050 --- Metaproof & verification landscape
- RES_0051 --- Induction, coinduction, termination survey
- TODO_0008 --- Metaproofs (program property verification)
- TODO_0009 --- Induction/coinduction (bisimulation, Section 7)
- TODO_0042 --- Completeness of exhaustive exploration
- TODO_0045 --- Execution tree judgment (formal tree constructors)
- DEF_0020 --- Execution tree judgment definition
