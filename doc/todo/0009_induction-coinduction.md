---
title: "Induction and Coinduction (Fixed Points)"
created: 2026-02-18
modified: 2026-02-23
summary: "Handle unbounded/infinite behavior via fixed point connectives — induction for termination and safety proofs, coinduction for bisimulation and liveness, cyclic proofs for automation. Includes concrete examples, implementation options, and connection to existing CALC infrastructure."
tags: [fixed-points, induction, coinduction, cyclic-proofs, termination, bisimulation, muMALL, ranking-functions]
type: research
cluster: Theory
status: planning
priority: 5
depends_on: [TODO_0008]
required_by: []
starred: true
---

# Induction and Coinduction (Fixed Points)

Handle unbounded/infinite behavior: recursive contracts, streaming payments, termination proofs, bisimulation equivalence, safety invariants. This document answers the core design question — **what does CALC need, and how little can we get away with?**

## Table of Contents

1. [The Core Question: Do You Need Higher-Order Logic?](#1-the-core-question)
2. [What CALC Already Has](#2-what-calc-already-has)
3. [Four Proof Techniques with Concrete Examples](#3-four-proof-techniques)
4. [muMALL: Fixed Points in Linear Logic](#4-mumall-fixed-points)
5. [Cyclic Proofs: Automation Without Invariant Guessing](#5-cyclic-proofs)
6. [Termination Analysis](#6-termination-analysis)
7. [Bisimulation and Program Equivalence](#7-bisimulation)
8. [Implementation Options](#8-implementation-options)
9. [Recommended Architecture](#9-recommended-architecture)
10. [Implementation Roadmap](#10-implementation-roadmap)
11. [Connection to Other TODOs](#11-connections)
12. [References](#12-references)

---

## 1. The Core Question: Do You Need Higher-Order Logic? {#1-the-core-question}

**No.** First-order logic with (co)inductive definitions suffices for all practical CALC properties. You do not need second-order quantification, full type theory, or higher-order unification.

What you DO need:

| Property | Proof Technique | Logic Required |
|----------|----------------|---------------|
| Termination | Ranking functions | First-order (no induction needed) |
| Safety invariants | Induction over rule steps | First-order induction schema |
| Conservation laws | Induction over multiset transformations | First-order + multiset axioms |
| Liveness | Coinduction or model checking | First-order coinductive definitions |
| Bisimulation | Coinduction | First-order coinductive definitions |
| Temporal properties | Fixed points (mu/nu) | muMALL (propositional suffices) |

**Key insight from Berardi & Tatsuta (LICS 2017):** In first-order logic with inductive definitions plus arithmetic, cyclic proofs and explicit induction are equivalent. Since CALC already has arithmetic via FFI (inc, plus, neq, mul), the two approaches have the same power. But cyclic proofs are more automation-friendly because they avoid invariant guessing.

**The omega-rule** (if P(0), P(1), P(2), ... each provable, conclude forall n.P(n)) is strictly stronger than first-order induction but rarely needed for program properties.

---

## 2. What CALC Already Has {#2-what-calc-already-has}

### 2.1 Cycle Detection in Forward Chaining

`lib/engine/symexec.js` implements path-based back-edge detection:

```javascript
// pathVisited = Set of numeric hashes on current DFS path
if (pathVisited.has(ctx.stateHash)) {
  return { type: 'cycle', state: snapshotState(state) };
}
pathVisited.add(ctx.stateHash);
// ... explore children ...
pathVisited.delete(ctx.stateHash);
```

**Properties:**
- Detects when a state recurs on the current root-to-node path
- Uses `computeNumericHash(state)` — incremental XOR-based fingerprint (O(changed facts) per step)
- `hashStateString(state)` gives deterministic string hash for exact comparison
- `pathVisited` contains only current-path hashes (not global), preventing false positives at join points

### 2.2 Bounded Exploration

```javascript
const maxDepth = opts.maxDepth ?? 100;
if (depth >= maxDepth) {
  return { type: 'bound', state: snapshotState(state) };
}
```

### 2.3 Four Terminal Node Types

| Node | Meaning | Interpretation |
|------|---------|----------------|
| `leaf` | No rules fire (quiescent) | Normal termination |
| `bound` | Depth limit exceeded | Exploration truncated |
| `cycle` | State seen earlier on this path | Back-edge (potential infinite loop) |
| `branch` | Multiple rules applicable | Nondeterministic choice point |

### 2.4 Content-Addressed State Equality

State comparison is O(1) via content-addressed hashing. Two states with the same multiset of facts produce the same hash. This is the foundation for:
- Cycle detection (back-edge = same hash on path)
- Memoization/tabling (reuse subtrees at equivalent states)
- Bisimulation checking (state equality without traversal)

### 2.5 Structural Recursion via Backward Chaining

CALC already supports structural recursion in backward-chaining clauses:

```ill
% Recursive arithmetic on binary numbers
plus/z1: plus e e e.
plus/s1: plus (o M) (o N) (o R) <- plus M N R.
plus/s4: plus (i M) (i N) (o R) <- plus M N Q <- inc Q R.
```

Termination is guaranteed by decreasing constructor depth. But this is only for computing values — NOT for proving properties about forward-chaining programs.

### 2.6 What's Missing

- **No fixed-point connectives** (mu, nu) in the formula language
- **No induction principle** for proving "for all reachable states, P holds"
- **No coinduction** for proving "two programs behave the same forever"
- **No progress checking** for validating cyclic proofs
- **No ranking function infrastructure** for automated termination proofs

---

## 3. Four Proof Techniques with Concrete Examples {#3-four-proof-techniques}

### 3.1 Induction: "Every number is even or odd"

**The property:** For all natural numbers n, either n is even or n is odd.

**In muMALL:** Natural numbers are `Nat := mu X. 1 oplus X` (zero or successor).

**Step-by-step proof:**

```
Goal: |- Nat -o (Even oplus Odd)
where Even := mu X. 1 oplus (1 oplus X)    % 0, 2, 4, ...
      Odd  := mu X. 1 oplus (1 oplus X)    % 1 shifted

1. Apply mu-left (induction) on Nat.
   Invariant S := Even oplus Odd.
   Must show: S is closed under the body of Nat.

2. Base case (n = 0):
   Zero = 1 (the unit).
   Show: 1 implies Even oplus Odd.
   Choose left: 1 implies Even (zero is even). Done.

3. Inductive case (n = succ(m)):
   Given: predecessor m satisfies Even oplus Odd.
   Show:  succ(m) satisfies Even oplus Odd.

   Case m is Even: succ(Even) is Odd. Choose right.
   Case m is Odd:  succ(Odd) is Even. Choose left.
```

**In CALC pseudocode** (what it would look like with forward rules):

```ill
% Forward rules for checking even/odd
check_even/z:  nat(0) -o { even(0) }.
check_odd/z:   nat(1) -o { odd(1) }.
check_even/s:  nat(N) * !plus 2 M N -o { even(N) }.  % if N-2 is even
check_odd/s:   nat(N) * !plus 2 M N -o { odd(N) }.   % if N-2 is odd
```

**But the induction principle IS the metaproof** — we need to prove that these rules correctly classify ALL naturals, not just run them on specific inputs. This is exactly what TODO_0008's invariant checker does: verify the property holds at every node of the execution tree.

### 3.2 Coinduction: Stream Bisimulation

**The property:** Two infinite streams that both produce `1` forever are bisimilar.

**In muMALL:** Streams are `Stream(A) := nu X. A tensor X`.

**Step-by-step proof:**

```
Goal: Bisim(ones, ones')
where ones  = 1 :: 1 :: 1 :: ...
      ones' = 1 :: ones

Bisim(s1, s2) := nu R. (head(s1) = head(s2)) & R(tail(s1), tail(s2))

1. Apply nu-right (coinduction).
   Coinvariant S := {(ones, ones')}.
   Must show: S is a post-fixed point (bisimulation).

2. Check one step for the pair (ones, ones'):
   head(ones) = 1 = head(ones')     -- heads match
   tail(ones) = ones                 -- by definition
   tail(ones') = ones                -- by definition (ones' = 1 :: ones)
   (ones, ones) must be in S.
   Since ones = ones' (by coinductive hypothesis),
   (ones, ones) = (ones, ones') in S.

3. S is a bisimulation, so Bisim(ones, ones') holds by coinduction.
```

**Why coinduction works:** We don't prove the streams are equal by examining all (infinitely many) elements. We prove that any finite observation yields the same result — the coinductive argument says "if you can always make one more matching step, the objects are equivalent."

**In CALC terms:** Coinduction corresponds to cycle detection. If the symexec tree visits a state that was already seen, and the property held at that state, then the property holds forever along that cycle. This is exactly Bedwyr's tabling strategy:
- **Inductive predicate + loop = failure** (no finite evidence)
- **Coinductive predicate + loop = success** (consistent observation)

### 3.3 Termination: Gas-Bounded EVM Execution

**The property:** EVM execution always terminates (reaches STOP, REVERT, or out-of-gas).

**Ranking function:**

```
rank(state) = value of gas fact in state.linear
```

**Proof:**

```
1. Every EVM instruction rule consumes gas(N) and produces gas(N')
   where N' = N - cost(opcode) and cost >= 1.

2. rank strictly decreases: rank(post) = N - cost < N = rank(pre).

3. gas is a natural number (non-negative integer).

4. Natural numbers under > are well-founded.

5. Therefore: no infinite sequence of rule applications exists.
   Execution must reach a terminal state (STOP/REVERT/out-of-gas).
```

**This does NOT require fixed points or induction in the logic.** It's a meta-level argument about the rules. The Dershowitz-Manna multiset ordering (CACM 1979) generalizes this to arbitrary multiset-decreasing systems.

### 3.4 Bisimulation: Two Transfer Programs Are Equivalent

**The property:** Two implementations of token transfer produce the same final states.

```ill
% Implementation A: direct transfer
transfer_a: token(A, N) * request(A, B, M) * !geq(N, M) * !sub(N, M, R)
  -o { token(A, R) * token(B, M) }.

% Implementation B: two-step transfer (debit then credit)
debit_b: token(A, N) * request(A, B, M) * !geq(N, M) * !sub(N, M, R)
  -o { token(A, R) * credit(B, M) }.
credit_b: credit(B, M) -o { token(B, M) }.
```

**Bisimulation proof:**

```
Define relation R:
  (state_a, state_b) in R iff
    state_b = state_a with some token(B, M) replaced by credit(B, M)

1. Initial states: identical -> (S0, S0) in R.

2. If state_a steps via transfer_a to state_a':
   state_b can step via debit_b then credit_b to reach state_b'.
   After both steps: (state_a', state_b') in R.

3. If state_b steps via debit_b:
   state_a can step via transfer_a (does both at once).
   After: (state_a', state_b_intermediate) in R.

4. R is a bisimulation -> programs A and B are equivalent.
```

**In CALC:** This could be checked by exploring both programs' execution trees and comparing leaf state sets. Content-addressed hashing makes state comparison O(1).

---

## 4. muMALL: Fixed Points in Linear Logic {#4-mumall-fixed-points}

### 4.1 The System

muMALL (Baelde & Miller, LPAR 2007, TOCL 2012) extends MALL with:

```
A ::= ... | mu X. B(X) | nu X. B(X)
```

- **mu X. B(X)** — least fixed point (inductive). Like "nat = zero | succ(nat)".
- **nu X. B(X)** — greatest fixed point (coinductive). Like "stream = head * stream".

De Morgan duality: `(mu X. B(X))^bot = nu X. B^bot(X)`.

### 4.2 Proof Rules

**Unfolding** (derivable from induction/coinduction):
```
  |- Gamma, B(mu X. B)          |- Gamma, B(nu X. B)
  --------------------  muR     --------------------  nuR
   |- Gamma, mu X. B             |- Gamma, nu X. B
```

**Induction** (mu on left): requires an **invariant** S (any closed formula):
```
  |- Gamma, B(S)    |- S^bot, mu X.B
  ------------------------------------ muL
          |- Gamma, (mu X.B)^bot
```

**Coinduction** (nu on right): requires a **coinvariant** S:
```
  |- Gamma, B(S)    |- S, (nu X.B)^bot
  ------------------------------------ nuR (coinduction)
          |- Gamma, nu X.B
```

### 4.3 Focusing and Polarity

In Andreoli-style focusing (which CALC's L3 already implements):

- **mu is positive** (synchronous): decomposed eagerly on the right, requires invariant on the left
- **nu is negative** (asynchronous): decomposed eagerly on the left, requires coinvariant on the right

This extends CALC's existing polarity table:

| Connective | Polarity | Invertible side | Focusable side |
|-----------|----------|----------------|----------------|
| tensor, one, bang, oplus, **mu** | Positive | Left | Right |
| loli, with, **nu** | Negative | Right | Left |

### 4.4 Key Properties

- **Cut elimination** holds (weak normalization) — Baelde 2012
- **Complete focused system** — focusing doesn't lose completeness
- **Invariant problem:** The invariant S can be ANY closed formula. Proof search undecidable (Pi^0_1-hard for non-wellfounded, PSPACE for circular — Das, De & Saurin, FSCD 2022)
- **Exponentials as fixed points:** `!A = nu X. A & X`, `?A = mu X. A oplus X` — fixed points are strictly more expressive than exponentials

### 4.5 Data Type Encodings

```
Nat       := mu X. 1 oplus X            % Natural numbers
List(A)   := mu X. 1 oplus (A tensor X) % Finite lists
Tree(A)   := mu X. A oplus (X tensor X) % Binary trees
Stream(A) := nu X. A tensor X           % Infinite streams
CoList(A) := nu X. 1 & (A tensor X)     % Possibly-infinite lists
```

### 4.6 What Fixed Points Give CALC

| Capability | Mechanism | CALC Application |
|-----------|-----------|------------------|
| Inductive data types | mu X. F(X) | Token lists, approval chains |
| Coinductive processes | nu X. F(X) | Streaming payments, services |
| Exponentials as sugar | !A := nu X. A & X | Simplifies core logic |
| Inductive reasoning | mu-left rule | Conservation, safety |
| Coinductive reasoning | nu-right rule | Bisimulation, equivalence |
| Temporal properties | CTL via mu/nu | Safety = nu X. safe & AX(X) |

---

## 5. Cyclic Proofs: Automation Without Invariant Guessing {#5-cyclic-proofs}

### 5.1 The Invariant Problem

The induction rule requires guessing an invariant S — any closed formula. This makes proof search undecidable. The invariant is not a subformula of the conclusion (subformula property fails).

**Cyclic proofs avoid this:** Instead of guessing S, allow the proof tree to have back-edges (cycles) and check a global correctness condition.

### 5.2 How Cyclic Proofs Work

A **circular pre-proof** is a finite proof graph with:
- **Buds** — leaves linked to earlier nodes (companions)
- **Global trace condition (GTC):** on every infinite path through the unfolded tree, there exists an infinitely progressing trace

A **trace** follows a formula through rule applications. It **progresses** when passing through a mu-unfolding (on the left) or a nu-unfolding (on the right). Progress = descent in the fixed-point hierarchy.

**Soundness:** An infinite path with infinite progress would yield an infinite descending chain of ordinals, contradicting well-foundedness.

### 5.3 Connection to Size-Change Termination

The GTC is deeply related to the Size-Change Principle (Lee, Jones, Ben-Amram, POPL 2001):

| Size-Change Termination | Cyclic Proof Validity |
|------------------------|---------------------|
| Size-change graphs | Trace transitions |
| Infinite call sequences | Infinite proof paths |
| Infinite descent in data | Infinite progress through mu-unfoldings |
| PSPACE-complete | PSPACE-complete |

Doumane's thesis establishes this formally. Nollet, Saurin & Tasson (FoSSaCS 2019) proved PSPACE-completeness of thread-validity for muMALL via reduction to/from SCT.

### 5.4 Checking Algorithms

| Algorithm | Complexity | Notes |
|-----------|-----------|-------|
| Buchi automata (standard) | EXPTIME | Path automaton included in trace automaton |
| Doumane's local criterion | PSPACE | Compositional, suitable for modular reasoning |
| E-Cyclist (Stratulat 2021) | Polynomial | Multiset path orderings, 5x faster than Cyclist |
| Ramsey-based (Das & Girlando, MSCS 2024) | — | Conceptually simpler soundness argument |

### 5.5 Why Cyclic Proofs Are Better for CALC

1. **No invariant guessing** — the proof structure encodes the (co)inductive argument
2. **Automation-friendly** — proof search explores cyclic structure naturally, validity is a separate decidable post-check
3. **CALC's content-addressed store** enables O(1) cycle detection (state equality by hash comparison)
4. **Connects to forward chaining** — cycle detection during forward chaining IS the operational analogue of cyclic proof construction
5. **Manual proof UI** — user "closes a cycle" by pointing to an earlier sequent, more intuitive than constructing an invariant formula
6. **Curry-Howard correspondence** — cyclic proofs = typed goto programs (Kuperberg, Pinault & Pous, POPL 2021)

### 5.6 The Curry-Howard Content

Kuperberg, Pinault & Pous (POPL 2021) established:

| System | Functions Captured |
|--------|-------------------|
| Cyclic proofs (with contraction) | System T (provably total functions of PA) |
| Cyclic proofs (affine, no contraction) | Primitive recursive functions |

**Implications for CALC:**
- Cyclic proofs ARE programs (typed goto programs)
- The trace condition IS termination checking
- CALC's linear discipline (no implicit duplication) keeps execution primitive recursive
- `!` (bang) enables contraction, which unlocks full recursion
- From a cyclic validity proof, one can extract a System T witness

---

## 6. Termination Analysis {#6-termination-analysis}

### 6.1 When Does CALC Need Termination Proofs?

| Scenario | Terminates? | Why |
|----------|------------|-----|
| Ground EVM execution | Always | Gas decreases strictly |
| Symbolic EVM execution | Always (per branch) | Gas still decreases |
| Token transfer (bounded requests) | Yes | Each rule consumes a request |
| Streaming payments | Never (by design) | Coinductive — infinite by intent |
| Self-spawning rules | Maybe | Depends on rule structure |

### 6.2 Ranking Functions

A **ranking function** maps states to a well-founded domain such that each rule application strictly decreases the rank.

**Formal setup:**

```
rank: State -> N (natural numbers)
For each rule r: consumed_r -o { produced_r }
  Require: weight(consumed_r) > weight(produced_r)
```

**Example — EVM gas:**

```
weight(gas(N)) = N
weight(everything_else) = 0
rank(state) = sum of weights = gas value

Every instruction: gas(N) consumed, gas(N-k) produced (k >= 1)
rank decreases by k >= 1 per step.
```

**Example — Token transfer:**

```
weight(request(_, _, _)) = 1
weight(everything_else) = 0
rank(state) = count of request facts

transfer rule: consumes 1 request, produces 0 requests
rank decreases by 1 per step.
```

### 6.3 Dershowitz-Manna Multiset Ordering

For more complex programs, the **multiset ordering** (Dershowitz & Manna, CACM 1979) lifts any well-founded order on elements to a well-founded order on multisets:

> M >> N iff M != N and for every x in (N - M), there exists y in (M - N) with y > x.

Intuitively: you can replace elements with finitely many smaller elements, and the multiset still decreases.

**Key theorem:** If `>` is well-founded on S, then `>>` is well-founded on finite multisets over S.

**Application to CALC:** Linear facts form a multiset. Forward rules replace consumed facts with produced facts. If we assign weights such that consumed >> produced in the multiset ordering, termination follows.

### 6.4 CHR Termination Techniques

CHR (CALC's closest relative) has three termination analysis approaches:

1. **Ranking-based** (Fruhwirth 2000): Map constraint stores to well-founded domain. For simplification rules: rank(head) > rank(body).

2. **Transformational** (Pilozzi & De Schreye, WST 2007): Transform CHR to Prolog, apply LP termination provers.

3. **Self-sustainability** (Voets et al., ICLP 2012): Check whether a rule can re-enable itself. For CALC: does a rule's output contain predicates that match its own input?

### 6.5 Implementation Sketch

```javascript
// lib/engine/termination.js (~80 LOC)

function checkTermination(rules) {
  // Build predicate dependency graph
  const deps = buildDependencyGraph(rules);

  // Check for self-sustaining cycles
  const cycles = findCycles(deps);
  if (cycles.length === 0)
    return { terminates: true, reason: 'no self-sustaining rules' };

  // Try ranking function: predicate count
  const weights = tryCountRanking(rules);
  if (weights) return { terminates: true, ranking: weights };

  // Try gas-based ranking
  const gasRanking = tryGasRanking(rules);
  if (gasRanking) return { terminates: true, ranking: gasRanking };

  return { terminates: 'unknown', cycles };
}

function buildDependencyGraph(rules) {
  // Rule r depends on predicate p if r produces p and some rule consumes p
  const graph = {};
  for (const rule of rules) {
    const produced = rule.consequent.linear.map(getPredicateHead);
    for (const p of produced) {
      if (!graph[p]) graph[p] = [];
      for (const r2 of rules) {
        if (r2.antecedent.linear.map(getPredicateHead).includes(p))
          graph[p].push(r2.name);
      }
    }
  }
  return graph;
}
```

### 6.6 Practical Termination Checkers

| Tool | Approach | CALC Relevance |
|------|----------|----------------|
| AProVE | Dependency pairs + polynomial interp. | High — automated TRS termination |
| TTT2 | Similar, different heuristics | High |
| Maude MTT | Transform to TRS, apply backends | Medium |
| K Framework | Reachability logic | High — KEVM for EVM |

---

## 7. Bisimulation and Program Equivalence {#7-bisimulation}

### 7.1 What Bisimulation Means for CALC

Two CALC programs are **bisimilar** if they produce equivalent execution trees: same branching structure, same leaf states (up to some equivalence relation).

**Formalized coinductively:**

```
Bisim(P1, P2) := nu R. forall action.
  (Step(P1, action) -o exists P1'. Step(P1', action) tensor R(P1', P2'))
  & (Step(P2, action) -o exists P2'. Step(P2', action) tensor R(P1', P2'))
```

### 7.2 Deng-Cervesato-Simmons Result (MSCS 2016)

> For a CCS-like calculus from the formula-as-process interpretation of linear logic, the proof-theoretic logical preorder coincides with the process-theoretic contextual preorder.

The proof uses coinductively defined simulation as a stepping stone.

### 7.3 Practical Bisimulation Checking for CALC

For finite-state CALC programs (bounded execution trees):

```javascript
// lib/engine/bisim.js (~60 LOC)
function checkBisimulation(tree1, tree2) {
  if (tree1.type === 'leaf' && tree2.type === 'leaf')
    return statesEquivalent(tree1.state, tree2.state);
  if (tree1.type !== tree2.type) return false;
  if (tree1.type === 'branch') {
    if (tree1.children.length !== tree2.children.length) return false;
    const s1 = [...tree1.children].sort((a, b) => a.rule.localeCompare(b.rule));
    const s2 = [...tree2.children].sort((a, b) => a.rule.localeCompare(b.rule));
    return s1.every((c1, i) =>
      c1.rule === s2[i].rule && checkBisimulation(c1.child, s2[i].child)
    );
  }
  return false;
}
```

For infinite-state programs: use coinduction with tabling (cycle at equivalent states = bisimilar).

### 7.4 Applications

1. **Compiler correctness:** Optimized program bisimilar to unoptimized
2. **Refactoring safety:** Two rule sets produce equivalent behavior
3. **Implementation equivalence:** Direct transfer vs. two-step transfer (Section 3.4)
4. **Protocol conformance:** Implementation matches specification

---

## 8. Implementation Options {#8-implementation-options}

### 8.1 Three Approaches

#### Option A: muMALL Fixed-Point Connectives

Add `mu X. B(X)` and `nu X. B(X)` to the formula grammar.

**What changes:**
- Parser: extend tree-sitter grammar for mu/nu syntax
- Store: new tag IDs for mu/nu (in dynamic tag range, above PRED_BOUNDARY)
- Rule interpreter: mu-left (induction) and nu-right (coinduction) rules
- Focusing: mu is positive, nu is negative (extend focusing.js)
- Bundle: regenerate ill.json

**Pros:** Full theoretical power. Native syntax. Connects to rich theory.
**Cons:** Parser changes. Invariant problem (undecidable proof search). Requires user to supply invariants.

**Estimated effort:** ~400 LOC

#### Option B: Cyclic Proofs with GTC Checking

Allow proof trees with back-edges. Validate via global trace condition.

**What changes:**
- Proof tree representation: add `back-edge(target)` node type
- GTC checker: validate that every infinite path has infinite progress
- Manual proof UI: "close cycle" action linking bud to companion
- Automated search: bounded DFS with cycle detection (already exists)

**Pros:** No invariant guessing. Automation-friendly. Builds on existing cycle detection.
**Cons:** GTC checking is PSPACE (practical with E-Cyclist-style polynomial heuristic).

**Estimated effort:** ~200 LOC

#### Option C: Tabling / Memoization (Bedwyr-Style)

Add state memoization to proof search and forward chaining. Loops = success or failure depending on predicate polarity.

**What changes:**
- symexec: add memo table (Map from state hash to subtree)
- prove.js: add tabling for backward chaining goals
- Polarity annotation: mark predicates as inductive (loop = fail) or coinductive (loop = succeed)

**Pros:** Simplest implementation. Direct speedup (100x reported by QCHR). Maps to existing infrastructure.
**Cons:** Less expressive than full mu/nu. Can't express arbitrary inductive properties.

**Estimated effort:** ~80 LOC

### 8.2 Comparison

| Criterion | Option A (muMALL) | Option B (Cyclic) | Option C (Tabling) |
|-----------|------------------|-------------------|-------------------|
| Expressiveness | Full muMALL | Full (with arithmetic) | Limited to ground checking |
| Automation | Poor (need invariants) | Good (GTC decidable) | Good (fully automatic) |
| Implementation cost | High (~400 LOC) | Medium (~200 LOC) | Low (~80 LOC) |
| Parser changes | Yes | No | No |
| Theory connection | Strong (Baelde 2012) | Strong (Doumane 2017) | Medium (Bedwyr 2007) |
| Handles infinite | Yes (coinductive types) | Yes (cyclic structure) | Partially (loop detection) |
| UI integration | Complex | Natural | Invisible |

### 8.3 Recommendation: C then B then A (Bottom-Up)

Start with **Option C** (tabling) — immediate practical benefit, minimal changes, builds foundation.

Then **Option B** (cyclic proofs) — for the manual proof UI, user closes cycles interactively; GTC validation is a post-check.

Finally **Option A** (muMALL) — when CALC needs inductive data types or coinductive process definitions in the object logic.

---

## 9. Recommended Architecture {#9-recommended-architecture}

### 9.1 Module Structure

```
lib/engine/
  termination.js    # Ranking functions, dependency graphs
  bisim.js          # Execution tree bisimulation
  (extend symexec.js with tabling)

lib/prover/
  (extend pt.js with back-edge node type)
  (extend focused.js with mu/nu polarity, Phase 3)
```

### 9.2 Separation of Concerns

```
                    +------------------------+
                    |   Property to Check    |
                    |  (from TODO_0029 DSL)  |
                    +----------+-------------+
                               |
              +----------------+----------------+
              |                |                |
              v                v                v
     +----------------+  +------------+  +-------------+
     |  Termination   |  |  Invariant |  | Bisimulation|
     |  (ranking fn)  |  | (induction)|  |(coinduction)|
     | termination.js |  |  TODO_0030 |  |  bisim.js   |
     +-------+--------+  +-----+------+  +------+------+
             |                  |                |
             v                  v                v
     +----------------+  +------------+  +-------------+
     |  Dependency    |  | Tree Walk  |  |   Tree      |
     |  Graph         |  | (TODO_0030)|  | Comparison  |
     |  Analysis      |  |            |  |             |
     +----------------+  +------------+  +-------------+
```

Termination, invariant checking, and bisimulation are three independent analysis passes that share:
- The execution tree (from symexec)
- The property DSL (from TODO_0029)
- State hashing (from content-addressed store)

### 9.3 What Goes Where

| Analysis | Module | Depends On | Technique |
|----------|--------|-----------|-----------|
| Termination | termination.js | Rule descriptors only | Ranking functions, dependency graphs |
| Safety invariants | verify.js (TODO_0030) | Execution tree | Induction over tree nodes |
| Conservation | invariants.js (TODO_0008) | Rule descriptors | P-invariant linear algebra |
| Bisimulation | bisim.js | Two execution trees | Coinductive tree comparison |
| Liveness | Future (mu/nu) | Tree + fixed points | Model checking |
| Temporal | Future (mu/nu) | Tree + fixed points | CTL via mu/nu encoding |

---

## 10. Implementation Roadmap {#10-implementation-roadmap}

### Phase 1: Tabling + Termination Analysis (~160 LOC, no dependencies)

**Tabling (~80 LOC):** Add state memoization to `explore()`:

```javascript
const memo = new Map();  // hashStateString -> subtree
function go(depth, ctx) {
  const key = hashStateString(state);
  if (memo.has(key)) return { type: 'memo', ref: memo.get(key) };
  // ... normal exploration ...
  memo.set(key, result);
  return result;
}
```

**Termination analysis (~80 LOC):** Build predicate dependency graph from `calc.forwardRules`. Detect self-sustaining cycles. Try simple ranking functions (predicate count, gas value).

### Phase 2: Bisimulation Checker (~60 LOC)

Structural comparison of two execution trees. Sort children by rule name for canonical comparison. Report first divergence point if not bisimilar.

### Phase 3: Cyclic Proof Support (~200 LOC, depends on manual proof UI)

Add `back-edge` node type to proof trees. Implement GTC checking (E-Cyclist-style polynomial algorithm). Integrate with manual proof UI — user "closes a cycle" by linking to an earlier sequent.

### Phase 4: muMALL Fixed Points (~400 LOC, major feature)

Extend formula grammar with mu/nu. Add mu-left (induction) and nu-right (coinduction) rules to the prover. Extend focusing discipline. This is a significant feature that changes the logic itself.

| Phase | LOC | Value | Dependencies |
|-------|-----|-------|-------------|
| 1a: Tabling | ~80 | High (performance + correctness) | None |
| 1b: Termination | ~80 | Medium (automated analysis) | None |
| 2: Bisimulation | ~60 | Medium (program equivalence) | None |
| 3: Cyclic proofs | ~200 | High (induction without invariants) | Manual proof UI |
| 4: muMALL | ~400 | Very High (full fixed point logic) | Parser, rule interpreter |
| **Total** | **~820** | | |

---

## 11. Connection to Other TODOs {#11-connections}

### Direct Dependencies

- **TODO_0008** (Metaproofs) — induction/coinduction provides the proof techniques for invariant checking, reachability, and temporal properties. Phase 1 of 0009 (tabling) directly supports 0008's memoization (Section 9.4).

- **TODO_0029** (State Property DSL) — temporal properties (safety = nu, liveness = mu) need fixed points. Phase 4 of 0009 enables temporal extensions to the DSL.

- **TODO_0030** (Invariant Checker) — Strategy B (per-rule preservation) is an induction proof. Phase 3 of 0009 (cyclic proofs) provides an automated alternative.

### Related Tasks

- **TODO_0042** (Completeness) — completeness of exploration is needed for soundness of "property holds at all leaves" arguments.
- **TODO_0043** (CHR Soundness) — the CHR soundness theorem (Theorem 4.8) provides the logical foundation. Termination and confluence analysis build on this.
- **TODO_0045** (Execution Tree Judgment) — the tree judgment formalizes what Phases 1-3 check operationally. Cycle nodes correspond to back-edges in cyclic proofs.
- **TODO_0005** (Constraint Propagation) — constraint propagation enables symbolic invariant checking.

### Connection to Research Documents

- **RES_0031** (muMALL) — comprehensive survey of the theory, directly informing Phase 4
- **RES_0050** (Verification Landscape) — positions induction/coinduction among other techniques
- **RES_0051** (Induction/Coinduction/Termination) — detailed survey with step-by-step proofs
- **THY_0001** (Exhaustive Forward Chaining) — execution tree judgment, Q5/Q6

---

## 12. References {#12-references}

### Foundational (muMALL)
- Baelde & Miller. "Least and greatest fixed points in linear logic." LPAR 2007
- Baelde. "Least and greatest fixed points in linear logic." ACM TOCL 13(1), 2012
- Baelde, Miller & Snow. "Focused inductive theorem proving." IJCAR 2010

### Cyclic Proofs
- Fortier & Santocanale. "Cuts for circular proofs." CSL 2013
- Baelde, Doumane & Saurin. "Infinitary proof theory: the mult. add. case." CSL 2016
- Doumane. PhD thesis, 2017 (Gilles Kahn Prize)
- Nollet, Saurin & Tasson. "PSPACE-completeness of thread criterion." FoSSaCS 2019
- Acclavio, Curzi & Guerrieri. "Infinitary cut-elimination via finite approximations." CSL 2024

### Curry-Howard for Cyclic Proofs
- Kuperberg, Pinault & Pous. "Cyclic proofs, system T, and the power of contraction." POPL 2021
- Curzi & Das. "Computational expressivity of circular proofs with fixed points." LICS 2023

### Termination
- Dershowitz & Manna. "Proving termination with multiset orderings." CACM 22(8), 1979
- Lee, Jones & Ben-Amram. "The size-change principle." POPL 2001
- Arts & Giesl. "Termination using dependency pairs." TCS 236, 2000
- Fruhwirth. *Constraint Handling Rules.* CUP, 2009

### Bisimulation
- Deng, Cervesato & Simmons. "Relating reasoning in LL and process algebra." MSCS 26(5), 2016
- Sangiorgi. *Introduction to Bisimulation and Coinduction.* CUP, 2012

### Model Checking and Tabling
- Baelde, Gacek, Miller, Nadathur & Tiu. "The Bedwyr system." CADE 2007
- Gacek, Miller & Nadathur. "A two-level logic approach." JAR 49(2), 2012
- Barichard & Stephan. "Quantified CHR." ACM TOCL 26(3), 2025

### Decision Problems
- Das, De & Saurin. "Decision problems for muMALL." FSCD 2022
- Brotherston & Simpson. "Sequent calculi for induction and infinite descent." JLC 21(6), 2011

### Practical Systems
- Clavel et al. "All About Maude." Springer, 2007
- Rosu. "K: A semantic framework." Marktoberdorf 2017
- Giesl et al. "AProVE." RTA 2004

### CALC Internal
- RES_0031 — muMALL survey
- RES_0050 — Metaproof verification landscape
- RES_0051 — Induction, coinduction, termination survey
- THY_0001 — Exhaustive forward chaining (judgment, Q5-Q6)
- TODO_0008 — Metaproofs (program property verification)
- TODO_0042 — Completeness of exhaustive exploration
- TODO_0043 — CHR soundness mapping
- TODO_0045 — Execution tree judgment
