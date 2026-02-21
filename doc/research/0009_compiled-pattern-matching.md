---
title: "Compiled Pattern Matching"
created: 2026-02-21
modified: 2026-02-21
summary: "Maranget's decision tree compilation for pattern matching: column heuristic, DAG conversion, and application to CALC's rule selection at 1000+ rules."
tags: [pattern-matching, compilation, decision-trees, Maranget, performance]
category: "Performance"
---

# Compiled Pattern Matching

Compiling multiple rule patterns into a single decision tree that selects matching rules by testing term positions in optimal order.

**Cross-references:** Stage 9 in [[forward-optimization-roadmap]], [[term-indexing]], [[de-bruijn-indexed-matching]]

---

## The Problem

CALC currently selects rules via:
1. Strategy stack → candidate rules (O(1) for opcode rules, O(R) for predicate layer)
2. `tryMatch()` per candidate → full pattern matching (O(pattern_size × facts))

For 1000 rules, step 1 produces many candidates, and step 2 tries each sequentially. Compiled pattern matching eliminates both steps: compile ALL patterns into a single decision tree that tests term positions in optimal order and directly yields matching rules.

---

## Decision Tree Compilation (Maranget, 2008)

### Core Algorithm

Given a set of patterns P1..Pn, the compiler:

1. **Select column** — choose which term position to test first (the "column heuristic")
2. **Branch** — for each possible value at that position, recursively compile the sub-patterns
3. **Leaf** — when patterns are fully discriminated, emit rule reference(s)

### Example: EVM Rules

Consider three rules with trigger patterns:

```
R1: code(_PC, i(e))          -- opcode 0x01 (ADD)
R2: code(_PC, o(i(e)))       -- opcode 0x02 (MUL)
R3: code(_PC, i(i(e)))       -- opcode 0x03 (SUB)
```

**Decision tree (testing child[1] first):**

```
test Store.tag(child(fact, 1)):
  case 'i':
    test Store.tag(child(child(fact, 1), 0)):
      case 'atom' (= 'e'): → R1 (ADD)
      case 'i':
        test Store.tag(child(child(child(fact, 1), 0), 0)):
          case 'atom' (= 'e'): → R3 (SUB)
          default: → no match
      default: → no match
  case 'o':
    test Store.tag(child(child(fact, 1), 0)):
      case 'i':
        test Store.tag(child(child(child(fact, 1), 0), 0)):
          case 'atom' (= 'e'): → R2 (MUL)
          ...
  default: → no match
```

Each term position is tested **at most once**. The tree branches on symbol values. Wildcards (metavars) match any branch.

### Column Heuristic

The key to good decision trees: which position to test first? Maranget proposes the **"necessity"** heuristic:

- A column is **necessary** if it contains at least one non-wildcard pattern
- Score each column by how many patterns it can discriminate
- Select the column with the highest score

For CALC's EVM rules: `child[1]` (the opcode) is maximally discriminating (44 distinct values). `child[0]` (the PC) is all-wildcard (metavar `_PC` in every rule). So the compiler would test `child[1]` first — exactly what `opcodeLayer` does manually.

**Insight:** CALC's hand-crafted `opcodeLayer` IS a manually compiled decision tree with:
- Column selection: `child[1]` of `code` facts
- Branch: hash-map lookup by opcode
- Leaf: single rule

Maranget's algorithm automates this for arbitrary patterns.

### DAG Conversion

Decision trees can have exponential size in the worst case (overlapping patterns with many wildcards). **DAG conversion** (sharing identical subtrees) mitigates this:

- If two branches of the tree lead to the same set of remaining patterns, share the subtree
- In practice, DAG size is O(R × D) where R = rules, D = max term depth

For CALC's flat terms (D=2-3): DAG size ≈ R × 3 ≈ 130 nodes for 44 rules. Negligible.

### Wildcards and Variables

When a pattern has a metavar at a tested position, it matches ANY value. The decision tree includes the pattern in ALL branches at that node.

```
R1: f(a, _X)    — concrete at pos 1, wildcard at pos 2
R2: f(_Y, b)    — wildcard at pos 1, concrete at pos 2
R3: f(a, b)     — concrete at both

Decision tree:
test pos 1:
  case 'a': → candidates {R1, R2, R3}
    test pos 2:
      case 'b': → {R1, R2, R3}   (all match)
      default:  → {R1, R2}        (R3 excluded)
  default: → candidates {R2}
    test pos 2:
      case 'b': → {R2}
      default:  → {}               (no match)
```

With many wildcards, patterns appear in many branches → tree blowup. DAG sharing limits this.

---

## Le Fessant & Maranget (2001)

### The "Necessity" Column Heuristic

A column c is necessary for row r if pattern P(r,c) is not a wildcard. The necessity score of column c = number of rows where c is necessary.

**Ties:** When multiple columns have the same necessity score, prefer:
1. The column with the most distinct values (more branching = more discrimination)
2. The leftmost column (stable ordering)

### Column Scoring for CALC

For EVM forward rules indexed by first linear antecedent:

| Position | Necessity | Distinct values | Notes |
|----------|-----------|----------------|-------|
| root tag | 44/44 | ~8 (pc, code, sh, stack, gas, ...) | All rules have concrete root |
| child[0] | ~40/44 | ~40 (ground PCs) | Most are metavar `_PC` |
| child[1] | ~40/44 | ~40 (opcodes) | Highly discriminating |

Root tag is necessary for all rules but has few distinct values (8 predicates). `child[1]` is necessary for 40 rules with 40 distinct opcode values → most discriminating. This confirms the opcodeLayer strategy.

### Comparison to Naive Compilation

Naive (left-to-right) compilation: test positions in declaration order. For CALC: test root tag → child[0] → child[1]. This first branches on predicate (8 ways), then on PC (all wildcard — no discrimination), then on opcode (40 ways).

Optimal (Maranget): test root tag → child[1] → skip child[0]. Two levels of branching instead of three. The useless child[0] test is eliminated.

---

## Relationship to Discrimination Trees

| Aspect | Discrimination Tree | Compiled Decision Tree |
|--------|--------------------|-----------------------|
| **Construction** | Insert patterns one by one | Compile all patterns simultaneously |
| **Column order** | Fixed (preorder traversal) | Optimized (necessity heuristic) |
| **Branching** | At every position | Only at discriminating positions |
| **Wildcards** | Separate wildcard branch | Pattern appears in all branches |
| **Runtime** | Trie traversal (pointer chasing) | Flat switch cascade (branch prediction friendly) |
| **Update** | O(pattern_size) per insert/remove | Full recompilation |

**Key difference:** Discrimination trees follow a fixed traversal order (preorder). Compiled decision trees choose the BEST position to test first. For patterns where the discriminating position is deep (e.g., CALC's opcodes at child[1]), discrimination trees waste time testing non-discriminating positions.

**When compiled wins:**
- Fixed rule set (CALC's case — rules don't change at runtime)
- Patterns with deep discriminating positions
- Many overlapping wildcards (discrimination tree duplicates, decision tree shares via DAG)

**When discrimination trees win:**
- Dynamic rule sets (frequent insertion/removal)
- Simple patterns where preorder IS the optimal order
- When you need the data structure for other operations (generalization retrieval, subsumption checking)

---

## Application to CALC

### Two Use Cases

**1. Rule selection (Stage 9):** Given a changed fact, which rules could fire?

This is the discrimination tree use case. Compile trigger patterns into a decision tree. At each step, evaluate the decision tree on the changed fact → get candidate rules.

**2. Pattern matching within tryMatch:** Given a rule and a state, does the rule match?

This is more complex: tryMatch must match MULTIPLE antecedent patterns against MULTIPLE facts, with cross-pattern variable sharing. A single decision tree can't handle this directly — it handles single-pattern-to-single-term matching.

### Compiled tryMatch (Future)

For a specific rule like `evm/add`, compile the entire match sequence:

```javascript
// Compiled from evm/add's antecedent:
function tryMatchEvmAdd(state, index) {
  // 1. Find pc fact (most selective with codeByPC)
  const pcFacts = index['pc'];
  if (!pcFacts || pcFacts.length === 0) return null;
  const pcFact = pcFacts[0];
  const _PC = Store.child(pcFact, 0);  // bind _PC

  // 2. Find code fact via codeByPC (O(1))
  const codeFact = index.codeByPC[_PC];
  if (!codeFact) return null;
  // Check opcode = i(e)
  if (Store.child(codeFact, 1) !== IE_HASH) return null;

  // 3. FFI: inc(_PC) → _PC'
  const ffiResult = ffi.inc(_PC);
  if (!ffiResult) return null;
  const _PC_PRIME = ffiResult;

  // 4. Find sh fact
  const shFacts = index['sh'];
  // ... match sh(s(s(_SH)))

  // ... etc.

  return { theta: [_PC, _PC_PRIME, _SH, _A, _B, _C], consumed: {...} };
}
```

This is a **compiled match function** — the generic `tryMatch` loop is replaced by a rule-specific function that:
- Accesses state index directly (no candidate iteration)
- Matches patterns in optimal order (selectivity-based, not declaration order)
- Binds variables to local variables (no theta scan)
- Inlines FFI calls

**Estimated improvement:** 2-5x per tryMatch call. For 44 rules × 63 steps: 10-30% total symexec improvement.

**Complexity:** ~20 LOC per compiled rule × 44 rules = ~880 LOC of generated code. Needs a code generator (~300 LOC).

### Incremental Compilation

Rules are loaded once at `mde.load()` time. Compilation to decision trees / match functions can happen at load time:

```javascript
// In compileRule():
compiled.compiledMatch = generateMatchFunction(compiled);
```

The generated function is a closure over Store and index operations. No eval() needed — generate function objects directly.

---

## Implementation Strategy

### Phase 1: Decision Tree for Rule Selection (= discrimination tree, optimized column order)

Replace `predicateLayer.getCandidateRules()` with a compiled decision tree:

1. Analyze all trigger patterns for column necessity scores
2. Build decision tree with optimal column ordering
3. Compile to a flat array of `{ position, value, then_idx, else_idx }` entries
4. At runtime: walk the flat array, branch on term positions

**Effort:** ~200 LOC. Moderate complexity. Directly replaces Stage 9 discrimination tree.

### Phase 2: Per-Rule Compiled Match Functions

For each rule, generate a specialized match function:

1. Analyze antecedent patterns for match ordering (selectivity)
2. Generate code that accesses state index directly
3. Inline FFI calls for persistent antecedents
4. Use de Bruijn slots for variable binding (Stage 6)

**Effort:** ~300 LOC for generator + ~880 LOC generated. High complexity. Depends on Stage 6.

### Phase 3: Cross-Rule Match DAG

Merge per-rule match functions into a single DAG that shares common prefixes:

1. Many EVM rules share `pc(_PC) * code(_PC, OP)` prefix
2. After matching this prefix, branch on `OP` to rule-specific code
3. Eliminates redundant state index lookups across rules

**Effort:** ~500 LOC. Very high complexity. Future.

---

## Research Directions

### Optimality Criteria

Maranget's heuristic optimizes for **minimum number of tests** in the worst case. Other criteria:

- **Average case with known distributions:** If some patterns fire more often, weight the decision tree toward those paths.
- **Minimum code size:** DAG sharing + branch elimination.
- **Cache-friendliness:** Flat array layout vs pointer-based tree.

For CALC: the distribution is highly skewed (EVM opcodes at different PCs follow program structure). Profile-guided optimization could significantly improve average case.

### Partial Evaluation

Compiled match functions are essentially **partial evaluation** of `tryMatch()` with respect to a fixed rule. The Futamura projections suggest:

- **1st projection:** Specialize tryMatch for a fixed rule → compiled match function
- **2nd projection:** Specialize the specializer → compiler from rules to match functions
- **3rd projection:** Specialize the compiler-compiler → self-applicable code generator

CALC only needs the 1st projection. The code generator is the 2nd projection.

### Multi-Head Pattern Matching

Standard compiled pattern matching handles ONE pattern matched against ONE term. CALC needs MULTIPLE patterns matched against a MULTISET of facts.

This connects to:
- **Rete/TREAT:** Beta network handles multi-pattern joins
- **Conjunctive queries:** Multi-pattern matching as a database join
- **Relational e-matching (Zhang et al., 2022):** Pattern matching as conjunctive queries with worst-case optimal joins

**Todo:** Investigate whether relational e-matching can be applied to CALC's multi-pattern matching.

---

## References

- Le Fessant, F. & Maranget, L. (2001). *Optimizing pattern matching.* In ICFP '01.
- Maranget, L. (2008). *Compiling pattern matching to good decision trees.* In ML '08.
- Scott, K. & Ramsey, N. (2000). *When do match-compilation heuristics matter?* UVa TR CS-2000-13.
- Sestoft, P. (1996). *ML pattern match compilation and partial evaluation.* In Dagstuhl Seminar on Partial Evaluation.
- Voronkov, A. (1995). *The anatomy of Vampire.* J. Automated Reasoning 15(2).
- Zhang, Y. et al. (2022). *Relational e-matching.* In POPL '22.
