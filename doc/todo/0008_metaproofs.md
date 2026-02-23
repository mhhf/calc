---
title: "Metaproofs — Program Property Verification"
created: 2026-02-18
modified: 2026-02-23
summary: "Prove properties about CALC programs: conservation, safety, termination, confluence. Includes Petri net invariant discovery, state property DSL, invariant checker, reachability queries, counter-example generation, and advanced model-checking techniques."
tags: [metaproofs, verification, safety, invariants, Petri-nets, model-checking, CEGAR, confluence]
type: design
cluster: Theory
status: planning
priority: 8
depends_on: [TODO_0042]
required_by: [TODO_0009]
---

# Metaproofs — Program Property Verification

Prove properties **about** CALC programs, beyond just running them. Given a set of forward rules and an initial state, answer questions like:

- **Conservation:** Is the total token supply preserved across all executions?
- **Safety:** Can the system reach a "bad" state (e.g., balance < 0)?
- **Progress:** Is the system deadlock-free?
- **Termination:** Does execution always reach quiescence?
- **Confluence:** Does rule application order matter?
- **Equivalence:** Do two programs behave identically?

## Subtasks (exported as standalone TODOs)

- [ ] TODO_0008.Task_0 — P-invariant discovery: see [Section 3](#3-p-invariant-discovery-task_0)
- [ ] TODO_0008.Task_1 — State property DSL: see [TODO_0029](0029_state-property-dsl.md) and [Section 4](#4-state-property-dsl-task_1)
- [ ] TODO_0008.Task_2 — Invariant checker: see [TODO_0030](0030_invariant-checker.md) and [Section 5](#5-invariant-checker-task_2)
- [ ] TODO_0008.Task_3 — Reachability queries: see [TODO_0031](0031_reachability-queries.md) and [Section 6](#6-reachability-queries-task_3)
- [ ] TODO_0008.Task_4 — Counter-example generation: see [TODO_0032](0032_counterexample-generation.md) and [Section 7](#7-counter-example-generation-task_4)
- [ ] TODO_0008.Task_5 — Confluence analysis: see [Section 8](#8-confluence-analysis-task_5)

---

## 1. Theoretical Foundations

### 1.1 The Metaproof Landscape

Three fundamental paradigms apply to verifying properties of linear logic forward-chaining programs:

| Paradigm | Question | Technique | Theory |
|----------|----------|-----------|--------|
| **Reachability** | Can state S be reached? | Forward/backward search | Petri net reachability |
| **Invariants** | Does property P hold everywhere? | Initial + preservation | Inductive invariants |
| **Model checking** | Does temporal property φ hold? | CTL over execution tree | Kripke structures |

### 1.2 The Petri Net Correspondence

CALC's forward engine IS a Petri net:

| Petri Net | CALC | ILL |
|-----------|------|-----|
| Place | Predicate type (e.g., `token`, `pc`) | Atomic formula |
| Token | Linear fact instance | Linear resource |
| Transition | Forward rule | `A -o {B}` |
| Marking | Multiset of linear facts (`state.linear`) | Linear context Δ |
| Read arc (test) | Persistent antecedent (`!P`) | Banged formula |
| Firing | `mutateState` (consume + produce) | Cut / loli-left |

This correspondence was established by:
- **Girard:** "Linear logic allows us to use purely propositional provable sequents to directly formalise the reachability relations in a net."
- **Engberg & Winskel (1990):** Petri nets as models of ILL — systematic correspondence between individual nets, linear logic theories, and commutative quantales.
- **Kanovich (1995):** The !-Horn fragment of MELL is equivalent to Petri net reachability.

### 1.3 Decidability Results

CALC's state space (multisets of content-addressed hashes) forms a **well-structured transition system (WSTS)** under multiset inclusion (Finkel & Schnoebelen, 2001). This immediately gives:

| Problem | Decidable? | Complexity | Notes |
|---------|-----------|------------|-------|
| **Coverability** | Yes | EXPSPACE-complete | "Can a state *containing* X be reached?" (Rackoff, 1978) |
| **Boundedness** | Yes | EXPSPACE | "Is the token count bounded?" |
| **Exact reachability** | Yes | Non-elementary | Ackermann-hard (Czerwinski et al., 2019) |
| **Safety** | Yes (reducible to coverability) | EXPSPACE | "Is bad state never reachable?" |
| **Termination** | Yes (for bounded systems) | EXPSPACE | Gas-bounded EVM programs |
| **Confluence** | Yes (for terminating programs) | Decidable via critical pairs | Abdennadher et al., 1996 |

For practical verification: **coverability** is the right target for safety properties — much cheaper than exact reachability. CALC's finite-state programs (e.g., bounded-gas EVM execution) have finite state spaces, making all properties decidable.

### 1.4 What CALC Already Has

The symexec engine (`lib/engine/symexec.js`) already provides exhaustive exploration, which is the computational foundation for all metaproof techniques:

- **Execution tree:** `explore()` builds a complete tree of all possible executions
- **Leaf enumeration:** `getAllLeaves(tree)` returns all terminal states
- **Cycle detection:** `pathVisited` hash set detects back-edges (prevents infinite exploration)
- **Depth bounding:** `maxDepth` option limits tree depth (bounded model checking)
- **State hashing:** Content-addressed `computeNumericHash(state)` for O(1) cycle detection
- **State inspection:** `show(hash)`, `classifyLeaf(state)`, `showInteresting(state)` in `lib/engine/show.js`

What's missing: a structured way to express properties and check them against the tree.

---

## 2. Concrete Minimal Example

To ground the discussion, consider a simple token transfer program:

```ill
% Two-party token transfer
transfer: token(A, N) * request(A, B, M) * !geq(N, M) * !sub(N, M, R)
  -o { token(A, R) * token(B, M) }.

% Initial state
token(alice, 100) * token(bob, 50).
```

### Properties we want to verify:

**Conservation:** `sum(token(_, N)) = 150` across all reachable states.

This is a **P-invariant** in Petri net terms: a weighted sum of tokens that is constant. The incidence matrix for `transfer` has:
- `token(A, N)`: consumed 1, produced 1 (net: 0 for A's token with different value)
- `token(B, M)`: produced 1

Wait — this doesn't work directly because token values change. The correct formulation: the *sum of amounts* is constant, not the *count of token facts*. This requires a **weighted P-invariant** where the weight is the second argument of `token`.

**Safety:** `token(_, N)` implies `N >= 0` (no negative balances). This holds because `!geq(N, M)` guards the rule.

**No counterfeiting:** Every token in a final state is traceable to the initial supply. This follows from linearity — facts can only be produced by rules, and rules consume existing facts.

---

## 3. P-Invariant Discovery (Task_0)

### 3.1 What Are P-Invariants?

Given a Petri net with **incidence matrix C** (rows = places, columns = transitions):

- **P-invariant:** integer vector **y** such that **y · C = 0**
- Meaning: the weighted sum `Σ y_i · M(p_i)` is constant for all reachable markings M
- This is an automatic **conservation law** requiring zero user annotation

### 3.2 Building the Incidence Matrix from CALC Rules

Each compiled forward rule contributes one column to C. For each rule:
- Consumed linear fact of predicate `p` → entry `C[p, rule] -= 1`
- Produced linear fact of predicate `p` → entry `C[p, rule] += 1`
- Persistent antecedents (`!P`) are **read arcs** — they don't affect the incidence matrix

```
Example: transfer rule
  consumes: token(A, N), request(A, B, M)
  produces: token(A, R), token(B, M)

  Incidence column (by predicate):
    token:   -1 + 2 = +1  (net gain of 1 token fact)
    request: -1            (net loss of 1 request fact)
```

For the token-count invariant: **y = (1, 0)** satisfies `y · C = 1·1 + 0·(-1) = 1 ≠ 0`. So token count is NOT preserved (the rule creates a new token fact for B). This is correct — the rule *splits* one token into two (different amounts).

For the **amount-sum invariant**, we need a refined analysis that tracks argument values, not just predicate counts. This requires the **parameterized P-invariant** approach.

### 3.3 Simple vs Parameterized Invariants

**Simple P-invariants** track fact counts per predicate. Useful for:
- "The number of `pc` facts is always 1" (single program counter)
- "The total number of `stack` + `consumed_stack` facts is constant"

**Parameterized P-invariants** track weighted sums where the weight depends on fact arguments. Useful for:
- "The sum of all `token(_, amount)` amounts is constant"
- "The sum of all `gas(N)` values N is non-increasing"

Parameterized invariants require inspecting the content-addressed structure of facts (via `Store.child(hash, argIndex)`) to extract argument values.

### 3.4 Algorithm

```
1. Extract predicate set P from calc.forwardRules
2. Build incidence matrix C[|P| × |rules|]:
   For each rule r:
     For each consumed linear fact with predicate p: C[p, r] -= 1
     For each produced linear fact with predicate p: C[p, r] += 1
3. Solve homogeneous system y · C = 0 over integers
4. Each non-trivial solution y is a conservation law:
   "Σ y_p · count(p) is constant across all reachable states"
```

For the integer nullspace computation: use the **Farkas/Martinez-Silva** algorithm (adapted Fourier-Motzkin elimination for non-negative integer solutions). Complexity: polynomial for finding one invariant; exponential worst case for all minimal invariants.

### 3.5 Implementation

```javascript
// In lib/engine/invariants.js (~100 LOC)
function buildIncidenceMatrix(rules) {
  const predicates = new Set();
  for (const rule of rules) {
    for (const p of rule.antecedent.linear) predicates.add(getPredicateHead(p));
    for (const p of rule.consequent.linear) predicates.add(getPredicateHead(p));
  }
  const predList = [...predicates];
  const C = Array.from({ length: predList.length }, () =>
    new Array(rules.length).fill(0));
  for (let j = 0; j < rules.length; j++) {
    for (const p of rules[j].antecedent.linear) {
      const i = predList.indexOf(getPredicateHead(p));
      C[i][j] -= 1;
    }
    for (const p of rules[j].consequent.linear) {
      const i = predList.indexOf(getPredicateHead(p));
      C[i][j] += 1;
    }
  }
  return { predicates: predList, matrix: C };
}

function findPInvariants(C) {
  // Solve y · C = 0 — integer nullspace via Hermite Normal Form or Farkas
  // Return array of basis vectors
}
```

**Data source:** `calc.forwardRules` from `mde.load()` — these are the compiled rules with `antecedent.linear`, `consequent.linear` arrays of pattern hashes.

**Verification:** For each discovered invariant `y`, check `Σ y_p · count(p, initial_state) = k`, then verify the invariant holds at each leaf via `getAllLeaves(tree)`.

### 3.6 Estimated Effort

~150 LOC. No dependencies on other TODO_0008 tasks. Can be implemented independently. The lowest-hanging fruit.

### 3.7 References

- Martinez & Silva (1982) — "A Simple and Fast Algorithm to Obtain All Invariants of a Generalised Petri Net"
- Colom & Silva (1991) — Decomposition-based P-invariant computation
- Desel (1998) — "Basic Linear Algebraic Techniques for Place/Transition Nets"
- Kanovich (1995) — "Petri Nets, Horn Programs, Linear Logic, and Vector Games"
- Engberg & Winskel (1990) — "Petri Nets as Models of Linear Logic"

---

## 4. State Property DSL (Task_1)

### 4.1 Design Goals

A language to express properties over execution states. Must be:
- **Composable:** Build complex properties from simple predicates
- **Evaluable:** Check against a concrete state (multiset of hashes)
- **Expressible:** Cover conservation, safety, reachability, absence
- **Minimal:** No features beyond what's needed

### 4.2 Design Options

#### Option A: Predicate Functions (JavaScript)

Properties as JavaScript functions `(state) => boolean`:

```javascript
// Conservation: total supply = 150
const conservation = (state) => {
  let sum = 0;
  for (const h in state.linear) {
    if (getPredicateHead(Number(h)) === 'token') {
      sum += extractAmount(Number(h)) * state.linear[h];
    }
  }
  return sum === 150;
};
```

**Pros:** Zero new syntax. Full expressiveness. Composable via `&&`, `||`.
**Cons:** Not serializable. Not analyzable (opaque functions). No static checking.

#### Option B: Declarative Property Language (DSL)

Custom syntax parsed from `.prop` files or inline annotations:

```
@invariant token_supply:
  sum(token(_, N), N) = 150

@safety no_negative:
  forall token(_, N). N >= 0

@reachability target:
  exists token(bob, N). N >= 50

@absence no_overflow:
  not exists token(_, N). N > 1000
```

**Pros:** Serializable. Analyzable. Self-documenting. Can be statically checked.
**Cons:** New parser. Design overhead. Less flexible than raw JS.

#### Option C: ILL Formulas as Properties

Express properties in ILL itself (metaproofs as proofs):

```ill
% Conservation as a provable sequent
conservation: token(A, N) * token(B, M) |- !sum_eq(N, M, 150).

% Safety as absence of bad state
safety: token(_, N) * !lt(N, 0) |- false.
```

**Pros:** Uses existing parser/prover. Deeply integrated with the logic.
**Cons:** ILL may not be expressive enough for all properties (quantification over all states is meta-level). Mixing object/meta levels is confusing.

### 4.3 Recommended: Option A + B (Hybrid)

Start with **Option A** (JS predicates) for implementation. Design **Option B** (declarative syntax) as a future sugar layer that compiles to Option A.

The JS predicate approach requires:

```javascript
// Property combinators
const forall = (pred, statePred) => (state) => {
  for (const h in state.linear) {
    if (matchPredicate(Number(h), pred)) {
      if (!statePred(Number(h), state)) return false;
    }
  }
  return true;
};

const exists = (pred, statePred) => (state) => {
  for (const h in state.linear) {
    if (matchPredicate(Number(h), pred)) {
      if (statePred(Number(h), state)) return true;
    }
  }
  return false;
};

const sum = (pred, extractWeight) => (state) => {
  let total = 0;
  for (const h in state.linear) {
    if (matchPredicate(Number(h), pred)) {
      total += extractWeight(Number(h)) * (state.linear[h] || 0);
    }
  }
  return total;
};

const count = (pred) => sum(pred, () => 1);
```

### 4.4 Property Types

| Type | Quantification | Example |
|------|---------------|---------|
| **Point property** | One state | `count('pc', state) === 1` |
| **Universal** | All leaves | `forall leaves. count('pc') === 1` |
| **Existential** | Some leaf | `exists leaf. has('token', {addr: bob})` |
| **Path** | Root-to-leaf trace | `along every path, gas decreases` |
| **Temporal** | CTL-like | `AG(safe)`, `EF(goal)` |

For the initial implementation, **point properties** checked universally over leaves are sufficient. Temporal properties come with muMALL fixed points (TODO_0009).

### 4.5 Temporal Extensions (Future)

When CALC adds mu/nu fixed points (TODO_0009), properties become expressible in the logic itself:

```
% Safety as greatest fixed point: "safe at every reachable state"
nu X. (safe(state) & after_every_step(X))

% Liveness as least fixed point: "goal eventually reached"
mu X. (goal(state) | after_some_step(X))
```

This connects metaproofs to **Bedwyr-style model checking** (Baelde, Gacek, Miller, 2007): tabling during proof search detects loops — inductive loops = failure (safety violated), coinductive loops = success (invariant holds).

---

## 5. Invariant Checker (Task_2)

### 5.1 Inductive Invariant Method

An **inductive invariant** I(state) satisfies two conditions:

1. **Initial:** I(state₀) holds
2. **Preservation:** For every rule r and every state s where I(s) holds: if r fires on s producing s', then I(s') holds

If both hold, I(s) holds for ALL reachable states (by induction on derivation length).

### 5.2 Two Implementation Strategies

#### Strategy A: Check Over Execution Tree (Post-Hoc)

After `explore()` builds the full tree, check I at every node:

```javascript
function checkInvariantOverTree(tree, invariant) {
  const violations = [];
  function walk(node, path) {
    if (node.state && !invariant(node.state)) {
      violations.push({ state: node.state, path: [...path] });
    }
    if (node.type === 'branch') {
      for (const child of node.children) {
        path.push({ rule: child.rule, choice: child.choice });
        walk(child.child, path);
        path.pop();
      }
    }
  }
  walk(tree, []);
  return { holds: violations.length === 0, violations };
}
```

**Pros:** Simple. Works for any computable property. Gets counterexample traces for free.
**Cons:** Requires full tree exploration (expensive for large state spaces). Only works for finite trees.

#### Strategy B: Rule-Level Preservation (Static)

Check preservation per rule WITHOUT exploring the tree:

```javascript
function checkPreservationPerRule(rules, invariant) {
  for (const rule of rules) {
    // For each rule: symbolically check that if invariant holds
    // before rule fires, it holds after.
    // This requires reasoning about what the rule consumes/produces.
    const consumed = rule.antecedent.linear;
    const produced = rule.consequent.linear;
    // Check: if I(state) and state contains consumed, then I(state - consumed + produced)
  }
}
```

**Pros:** O(|rules|) — independent of state space size. Proves invariant for ALL executions.
**Cons:** Harder to implement (symbolic reasoning about state transformations). May require SMT for non-trivial invariants.

### 5.3 Recommended: Strategy A First, Strategy B Later

Strategy A is simple and sufficient for finite-state programs (EVM with bounded gas). Strategy B is needed for programs with unbounded state spaces (streaming payments, unbounded nonces).

### 5.4 Connection to Ceptre's Invariant Framework

Martens (2015, thesis Chapter 6) defines two invariant types for linear logic programs:

- **Consumptive invariants:** "After rule r fires, resource A must NOT be in state" (absence property)
- **Generative invariants:** "After rule r fires, resource B must BE in state" (presence property)

**Key result:** Invariant checking is decidable for the propositional fragment because ground linear logic programs form a WSTS (connecting to Finkel-Schnoebelen).

Ceptre's framework maps directly to CALC — but Ceptre never implemented the checker. CALC can be the first system to have an actual invariant checker for linear logic programs.

### 5.5 Worked Example

For the token transfer example:

**Invariant:** `count('token') + count('request') >= 2`

**Initial check:** State has `token(alice, 100), token(bob, 50)`. Count = 2. `2 >= 2`. ✓

**Preservation for `transfer` rule:**
- Consumes: 1 token, 1 request (count decreases by 2)
- Produces: 2 tokens (count increases by 2)
- Net: 0 change. ✓

**P-invariant verification:** The incidence matrix column for `transfer` is `[+1, -1]` (token: +1, request: -1). The vector `y = [1, 1]` gives `y · C = 1·1 + 1·(-1) = 0`. ✓ This is the P-invariant `count(token) + count(request) = const`.

---

## 6. Reachability Queries (Task_3)

### 6.1 Forward Reachability (Tree Search)

Given a target property P, find a leaf of the execution tree satisfying P:

```javascript
function findReachable(tree, property) {
  if (tree.type === 'leaf' && property(tree.state)) {
    return { reachable: true, state: tree.state, path: [] };
  }
  if (tree.type === 'branch') {
    for (const child of tree.children) {
      const result = findReachable(child.child, property);
      if (result.reachable) {
        result.path.unshift({ rule: child.rule, choice: child.choice });
        return result;
      }
    }
  }
  return { reachable: false };
}
```

This uses the existing `explore()` tree. The path from root to matching leaf is the **witness** (execution trace proving reachability).

### 6.2 Backward Reachability (Coverability)

For larger state spaces, **backward reachability** is more efficient:

1. Start from the target state set S_bad
2. Compute **predecessors**: Pre(S_bad) = { s | ∃ rule r. r(s) ∈ S_bad }
3. Iterate: Pre*(S_bad) = S_bad ∪ Pre(S_bad) ∪ Pre²(S_bad) ∪ ...
4. If initial state ∈ Pre*(S_bad): reachable (bad!). Otherwise: safe.

This is the standard backward set-saturation algorithm for WSTS. For Petri nets, it computes the **upward-closed** set of predecessors using the well-quasi-ordering.

**Implementation considerations:**
- Predecessor computation requires inverting rules: given a target state, which states could produce it?
- For CALC, this means: for each rule, find states where the rule's antecedent matches and the consequent produces the target facts
- Upward-closed sets can be represented as **minimal elements** (antichain representation)
- Complexity: EXPSPACE in the worst case (matching the theoretical lower bound)

### 6.3 Bounded vs Unbounded

| Mode | Guarantee | Cost |
|------|-----------|------|
| **Bounded (depth k)** | "Not reachable within k steps" | O(|tree|) |
| **Unbounded (full)** | "Not reachable ever" | Decidable but expensive (EXPSPACE) |
| **Symbolic** | "Not reachable (with constraint pruning)" | Depends on TODO_0005 |

For practical use: bounded reachability (via `explore()` with `maxDepth`) is sufficient for EVM programs (bounded gas). Unbounded reachability is needed for programs with potentially infinite execution.

---

## 7. Counter-Example Generation (Task_4)

### 7.1 Trace Extraction

When a property violation is found (either by invariant checking or reachability), extract a **minimal witness trace**:

```javascript
function extractTrace(tree, violatingLeaf) {
  // DFS to find path from root to violating leaf
  function findPath(node, target, path) {
    if (node === target) return path;
    if (node.type === 'branch') {
      for (const child of node.children) {
        path.push({ rule: child.rule, choice: child.choice });
        const found = findPath(child.child, target, path);
        if (found) return found;
        path.pop();
      }
    }
    return null;
  }
  return findPath(tree, violatingLeaf, []);
}
```

### 7.2 Trace Minimization

A trace may contain steps irrelevant to the violation. Minimize by:

1. **Backward slicing:** From the violating fact, trace backward through the execution, keeping only steps that contribute to producing it
2. **Delta-debugging:** Binary search on trace prefixes to find the shortest prefix that still produces the violation
3. **Dependency analysis:** Use the undo log to identify which facts were consumed/produced at each step; prune independent steps

### 7.3 Human-Readable Formatting

```javascript
function formatTrace(trace, tree) {
  const lines = [];
  let node = tree;
  for (const step of trace) {
    // Find child matching step
    const child = node.children.find(c =>
      c.rule === step.rule && c.choice === step.choice);
    // Show state diff
    const diff = computeStateDiff(node.state, child.child.state);
    lines.push(`${step.rule}${step.choice !== undefined ? ` (alt ${step.choice})` : ''}:`);
    for (const h of Object.keys(diff.consumed)) {
      lines.push(`  - ${show(Number(h))} ×${diff.consumed[h]}`);
    }
    for (const h of Object.keys(diff.produced)) {
      lines.push(`  + ${show(Number(h))} ×${diff.produced[h]}`);
    }
    node = child.child;
  }
  return lines.join('\n');
}
```

**State diffs** are computable from the undo log returned by `mutateState()`, or reconstructed from parent/child state snapshots. The undo log format is `[type, hash, oldValue, ...]` (see symexec.js).

### 7.4 Integration with CLI Tool

Extend `tools/symexec-inspect.js` to accept property specifications:

```bash
node tools/symexec-inspect.js --check "count('pc') === 1" programs/evm.ill
node tools/symexec-inspect.js --invariant "sum('token', 1) === 150" programs/transfer.ill
node tools/symexec-inspect.js --reachable "has('error')" programs/contract.ill
```

---

## 8. Confluence Analysis (Task_5)

### 8.1 What Confluence Means for CALC

A CALC program is **confluent** if for every state, applying any applicable rule leads to the same final state (modulo rule application order). Confluence means the execution tree collapses to a single outcome.

### 8.2 Critical Pair Analysis

Two rules are in a **critical pair** when they can both fire on the same state (their linear antecedents overlap). The critical pair tests whether applying rule A then rule B yields the same result as B then A.

Algorithm (adapted from CHR, Abdennadher et al., 1999):

```
1. For each pair of rules (r1, r2):
   a. Compute overlap: can r1 and r2 both match the same multiset of facts?
   b. If yes: construct the minimal overlapping state
   c. Apply r1 first, then r2 → state S12
   d. Apply r2 first, then r1 → state S21
   e. If S12 ≡ S21: joinable (confluent for this pair)
   f. If not: report critical pair

2. If all critical pairs are joinable: program is confluent
```

### 8.3 CALC-Specific Analysis

For EVM rules:

- **Ground execution is confluent** (trivially — deterministic opcode dispatch, at most one rule fires per state)
- **Symbolic execution is NOT confluent** (by design — ⊕ creates choice points, different branches lead to different leaves)
- **Helper rules** (concatMemory, calldatacopy) are confluent (guards are mutually exclusive)

### 8.4 Post-Hoc Confluence from Execution Tree

The execution tree already explores all orderings. Confluence can be checked by comparing branch outcomes:

```javascript
function checkConfluence(tree) {
  if (tree.type !== 'branch') return { confluent: true };
  // All children should lead to equivalent leaf sets
  const leafSets = tree.children.map(c => {
    const leaves = getAllLeaves(c.child);
    return new Set(leaves.map(l => hashStateString(l.state)));
  });
  // Check: do all children produce the same set of reachable leaves?
  const first = leafSets[0];
  for (let i = 1; i < leafSets.length; i++) {
    if (!setsEqual(first, leafSets[i])) {
      return { confluent: false, rule1: tree.children[0].rule, rule2: tree.children[i].rule };
    }
  }
  // Recurse into children
  for (const child of tree.children) {
    const sub = checkConfluence(child.child);
    if (!sub.confluent) return sub;
  }
  return { confluent: true };
}
```

### 8.5 References

- Abdennadher, Frühwirth, Meuss (1999) — "Confluence and Semantics of Constraint Simplification Rules"
- Duck, Stuckey, Sulzmann (2007) — "Observable Confluence for CHR"
- See RES_0007 §8.1 for CHR confluence theory

---

## 9. Advanced Techniques (Future Work)

### 9.1 CEGAR (Counterexample-Guided Abstraction Refinement)

For large state spaces where full exploration is impractical:

1. **Abstract:** Collapse the multiset state space (e.g., merge all `token(addr, amount)` into a single `token_count` place)
2. **Model-check:** Check property on abstract Petri net (simple linear algebra on abstract incidence matrix)
3. **Counterexample check:** Simulate counterexample trace on concrete CALC system
4. **Refine:** If trace is spurious (can't happen in concrete system), split abstracted places

CALC's content-addressed hashing provides a natural **refinement lattice**: tag-level abstraction (all `token` facts → one place) → hash-level (each `token(x,y)` → separate place).

**Key references:**
- Clarke et al. (2003) — "Counterexample-Guided Abstraction Refinement for Symbolic Model Checking"
- König & Kozioura (2006, TACAS) — CEGAR for graph transformation systems via Petri net over-approximation (Augur tool)

### 9.2 muMALL Fixed Points for Property Specification

When TODO_0009 adds mu/nu connectives, properties become expressible in the logic:

```
% Safety as greatest fixed point
Safe(P) := nu X. P(state) & forall_step(X)
  -- "P holds at this state AND after every possible step, P still holds"

% Liveness as least fixed point
Live(P) := mu X. P(state) | exists_step(X)
  -- "P holds at this state OR there exists a step after which P will hold"

% Invariant as induction
Inv(I) := mu X. I(initial) & (I(s) => forall_rule(I(s')))
```

This connects to **Bedwyr** (Baelde, Gacek, Miller, 2007) which implements model checking via focused proof search with tabling. Bedwyr's approach: loops on inductive predicates = failure (property violated), loops on coinductive predicates = success (property holds forever).

### 9.3 Nomos-Style Resource Typing

Das, Balzer, Hoffmann, Pfenning (2021) created **Nomos** for digital contracts: linear session types + automatic amortized resource analysis. Key idea: annotate predicates with resource **weights** that must be conserved across rule application:

```
@weight(token, arg=1)  % weight = second argument of token
@invariant total_supply: sum_weight(token) = CONST
```

This is the P-invariant computation expressed as a type system: each rule is type-checked for weight conservation. Linear-time checking. No execution required.

### 9.4 State Memoization (Tabling)

Enhance symexec with **state memoization**: if a state has been seen before (even on a different path), reuse the subtree. This is QCHR's tabling mechanism (Barichard & Stéphan, 2025).

```javascript
const memo = new Map();  // hashStateString → subtree

function explore(state, depth) {
  const key = hashStateString(state);
  if (memo.has(key)) return memo.get(key);  // reuse
  // ... normal exploration ...
  memo.set(key, result);
  return result;
}
```

**Benefits:** Dramatic speedup when multiple paths converge to the same state (common in programs with commutative rule interactions). QCHR reports 100x speedup from tabling on game benchmarks.

**Risk:** Memory growth (all explored states cached). Mitigate with LRU eviction or depth-bounded memoization.

---

## 10. Implementation Architecture

### 10.1 Module Structure

```
lib/engine/
├── verify.js            # Top-level API: checkInvariant, findReachable, checkConfluence
├── invariants.js         # P-invariant discovery (incidence matrix, nullspace)
├── property.js           # Property combinators (forall, exists, sum, count)
└── trace.js              # Trace extraction, minimization, formatting
```

### 10.2 API Design

```javascript
const { explore } = require('./symexec');
const { checkInvariant, findReachable, checkConfluence } = require('./verify');
const { count, sum, forall, has } = require('./property');

// Build tree
const tree = explore(initialState, rules, { maxDepth: 200, calc });

// Check invariant
const inv = checkInvariant(tree, state => count('pc')(state) === 1);
// → { holds: true } or { holds: false, violations: [...], traces: [...] }

// Reachability
const reach = findReachable(tree, state => has('error')(state));
// → { reachable: false } or { reachable: true, trace: [...] }

// Confluence
const conf = checkConfluence(tree);
// → { confluent: true } or { confluent: false, criticalPair: {...} }
```

### 10.3 Extension Points in Existing Code

The symexec engine already provides the necessary hooks:

| Need | Existing hook | Location |
|------|-------------|----------|
| Leaf enumeration | `getAllLeaves(tree)` | tree-utils.js |
| State inspection | `state.linear`, `state.persistent` | symexec.js |
| Fact display | `show(hash)`, `classifyLeaf(state)` | show.js |
| Tree traversal | `countNodes`, `maxDepth`, `toDot` | tree-utils.js |
| Rule metadata | `calc.forwardRules` | mde.load() |
| State hashing | `hashStateString(state)` | symexec.js |

No changes needed to the core engine — verification is a pure **read-only analysis** of the tree.

---

## 11. Implementation Roadmap

### Phase 1: P-Invariant Discovery (~150 LOC, no dependencies)

Build incidence matrix from `calc.forwardRules`, solve integer nullspace, report conservation laws. This is purely algebraic — no tree exploration needed. Can be a CLI tool.

### Phase 2: Property Combinators + Tree Checker (~100 LOC)

Implement `count`, `sum`, `forall`, `exists`, `has` combinators. Implement `checkInvariantOverTree`. Extend `tools/symexec-inspect.js` with `--check` flag.

### Phase 3: Trace Extraction (~80 LOC)

Implement `extractTrace`, `formatTrace`. When invariant check fails, produce a human-readable execution trace showing each step from initial state to violation.

### Phase 4: Confluence Checker (~60 LOC)

Implement `checkConfluence` as post-hoc analysis of the execution tree. Report non-confluent rule pairs.

### Phase 5: Backward Reachability (~200 LOC, advanced)

Implement predecessor computation and backward set-saturation. Needed for programs where full forward exploration is too expensive.

### Phase 6: State Memoization (~50 LOC)

Add tabling to `explore()`. Cache explored states. Reuse subtrees for repeated states.

| Phase | LOC | Value | Dependencies |
|-------|-----|-------|-------------|
| 1: P-invariants | ~150 | High (automatic conservation laws) | None |
| 2: Property + tree check | ~100 | High (user-defined properties) | None |
| 3: Trace extraction | ~80 | Medium (debugging) | Phase 2 |
| 4: Confluence | ~60 | Medium (rule analysis) | None |
| 5: Backward reachability | ~200 | High (large state spaces) | Phase 2 |
| 6: Memoization | ~50 | High (performance) | None |
| **Total** | **~640** | | |

---

## 12. Theoretical Connections

### 12.1 Execution Tree as Proof Object

CALC's execution tree is a **proof object** in Stéphan's ω_l sequent calculus (ICLP 2018):

- Each root-to-leaf path = one ω_l proof
- Branch nodes (multiple rules fire) = different &L choices
- Fork nodes (⊕ in consequent) = CHR∨ disjunction

The full tree is best understood via QCHR (Stéphan & Barichard, TOCL 2025): a game tree where ∀-branching = exhaustive rule exploration and ∃-branching = ⊕ disjunction.

See: THY_0001 §Q5-Q6, TODO_0045, TODO_0043 §7-8

### 12.2 Soundness Foundation

By the CHR∨ soundness theorem (Betz & Frühwirth, TOCL 2013, Theorem 4.8):

```
S₀ ↦* S  ⟹  S₀^L ⊢_{Σ_R ∪ Σ_CT} S^L
```

Every reachable state is logically entailed by the initial state. This means any property that is "stable under logical entailment" (like conservation) is automatically preserved.

See: TODO_0043 §2

### 12.3 Completeness Foundation

For completeness of the execution tree (does it contain ALL reachable states?), we need:

1. `findAllMatches` returns all applicable rules ✓ (TODO_0041 fixed priority bug)
2. Strategy stack doesn't miss rules ✓ (fingerprint + disc-tree + predicate layers)
3. State hash has no false cycle detections (hash collision → missed states)

See: TODO_0042

### 12.4 Connection to Constraint Propagation

When TODO_0005 adds constraint propagation (equality resolution, FFI re-check), it enables **symbolic invariant checking**: verify properties even on branches with symbolic values by propagating constraints and pruning infeasible branches.

---

## 13. Key References

### Foundational
- Girard (1987) — Linear Logic, TCS 50(1):1-102
- Engberg & Winskel (1990) — "Petri Nets as Models of Linear Logic", CAAP'90
- Kanovich (1995) — "Petri Nets, Horn Programs, Linear Logic, and Vector Games"

### Model Checking
- Finkel & Schnoebelen (2001) — "Well-Structured Transition Systems Everywhere!", TCS 256
- Czerwinski et al. (2019) — "Reachability Not Elementary", STOC'19
- Cervesato, Durgin, Lincoln, Mitchell, Scedrov (1999) — "MSR for Protocol Analysis"

### Invariants
- Martinez & Silva (1982) — "P-invariant Algorithm for Petri Nets"
- Desel (1998) — "Basic Linear Algebraic Techniques for Place/Transition Nets"
- Martens (2015) — "Ceptre: Consumptive/Generative Invariants", PhD thesis Chapter 6

### CHR Analysis
- Abdennadher, Frühwirth, Meuss (1999) — "Confluence and Semantics of CHR"
- Sneyers et al. (2010) — "CHR Survey", TPLP 10(1)
- Frühwirth (2009) — *Constraint Handling Rules*, Cambridge University Press

### CHR ↔ Linear Logic
- Betz & Frühwirth (2013) — "CHR with Disjunction", TOCL 14(1) — soundness
- Stéphan (2018) — "Proof-Theoretical Linear Semantics for CHR", ICLP — ω_l
- Barichard & Stéphan (2025) — "Quantified CHR", TOCL 26(3) — ω_l^{∃∀}

### Fixed Points and Model Checking
- Baelde & Miller (2012) — "muMALL: Fixed Points in Linear Logic", TOCL 13(1)
- Baelde, Gacek, Miller et al. (2007) — "Bedwyr: Model Checking", CADE
- Doumane (2017) — "Circular Proofs in muMALL", PhD thesis

### Resource Types
- Das, Balzer, Hoffmann, Pfenning (2021) — "Nomos: Resource-Aware Session Types", CSF
- Caires & Pfenning (2010) — "Session Types as Intuitionistic Linear Propositions", CONCUR

### CEGAR
- Clarke et al. (2003) — "CEGAR for Symbolic Model Checking", JACM 50(5)
- König & Kozioura (2006) — "CEGAR for Graph Transformation", TACAS

### CALC Internal
- RES_0007 — CHR ↔ Linear Logic survey
- RES_0014 — Execution Trees, Metaproofs, and Coinduction
- RES_0031 — muMALL: Fixed Points in Linear Logic
- RES_0050 — Metaproof & Verification Landscape
- THY_0001 — Exhaustive Forward Chaining (judgment, Q5-Q6)
- TODO_0042 — Completeness of Exhaustive Exploration
- TODO_0043 — CHR∨ Soundness Mapping
- TODO_0045 — Execution Tree Judgment
- TODO_0005 — Constraint Propagation (enables symbolic invariant checking)
- TODO_0009 — Induction/Coinduction (muMALL fixed points for temporal properties)
