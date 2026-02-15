# Term Indexing for Rule Selection

Techniques for efficiently selecting which forward rules can match against a given state, replacing linear scan with sub-linear lookup.

**Cross-references:** Stage 9 in [[forward-optimization-roadmap]], [[de-bruijn-indexed-matching]], [[prover-optimization]]

---

## The Problem

When a fact changes (added/consumed), which rules could potentially fire? Currently CALC answers this with two layers:

1. **opcodeLayer** (EVM-specific): `PC → code → opcode → rule`. O(1). Covers 40/44 EVM rules.
2. **predicateLayer** (catch-all): iterates all unclaimed rules, checks if trigger predicates exist in state. O(rules).

For 44 rules, this is fine — the opcode layer handles almost everything, and 4 rules go to the predicate catch-all. But for 100-1000 rules without EVM-style structure, the predicate layer degenerates to linear scan.

The standard solution in automated reasoning: **term indexing** — build a trie-like data structure over rule patterns, query it with facts, retrieve only matching rules.

---

## CALC's Current Indexing Architecture

### State Index (`buildStateIndex`, forward.js:85-113)

Groups facts by predicate head: `stateIndex['pc']` → all `pc(...)` facts. Secondary index `codeByPC` for O(1) code lookup.

This is a **1-level discrimination tree**: branch on predicate tag, leaf = fact list. Effective when predicates are discriminating (many distinct predicates, few facts per predicate).

### Rule Index (`buildRuleIndex`, forward.js:361-376)

Groups rules by trigger predicates: `ruleIndex['pc']` → all rules with `pc` in their antecedent. Used by `findMatch()` in `run()` (committed-choice single-step execution).

Also 1-level: branch on trigger predicate, leaf = rule list.

### Strategy Stack (symexec.js:451-489)

Layered architecture: each layer claims rules it can index, unclaimed rules cascade to the next layer.

```
rules → opcodeLayer (claims 40 rules, O(1) per step)
           │
     remaining → predicateLayer (claims 4 rules, O(4) per step)
```

A discrimination tree layer would slot into this stack between opcode and predicate:

```
rules → opcodeLayer (EVM rules, O(1))
           │
     remaining → discriminationTreeLayer (general rules, O(term_depth))
           │
     remaining → predicateLayer (catch-all, O(remaining))
```

### What Triggers Rule Re-evaluation?

In `findAllMatches()` (symexec.js:507-524), **every** candidate rule is tried via `tryMatch()` at every step. There's no delta tracking — when a fact changes, all candidate rules are re-evaluated.

For 44 rules this is acceptable. For 1000 rules: need per-fact rule selection (which rules could be affected by fact X changing?).

---

## 1. Discrimination Trees

**Key references:**
- McCune, W. (1992). "Experiments with discrimination-tree indexing and path indexing for term retrieval." J. Automated Reasoning 9(2), 147-167.
- Voronkov, A. (2001). "Term indexing." In Handbook of Automated Reasoning, Vol. 2, Ch. 26, pp. 1853-1964. (Section on discrimination trees, pp. 1877-1897)
- Christian, J. (1993). "Flatterms, discrimination nets, and fast term rewriting." J. Automated Reasoning 10(1), 95-113.
- Ganzinger, H., Nieuwenhuis, R., Hillenbrand, T. (2003). "Note on McCune's article on discrimination trees." J. Automated Reasoning.

### Core Data Structure

A discrimination tree is a **trie** (prefix tree) built over the **preorder traversal** (depth-first, left-to-right) of first-order terms. Each path from root to leaf corresponds to a flattened term representation.

**Flatterm encoding.** A term `f(g(a), b)` is traversed preorder to produce the string `[f, g, a, b]`. Because function symbols have fixed arities, the arity determines how many successors to expect — the flat string is unambiguous and uniquely reconstructs the term. Variables are encoded as a special wildcard symbol `*`.

**Example.** Given terms to index:
```
t1 = f(g(a), b)    → flat: [f, g, a, b]
t2 = f(g(x), a)    → flat: [f, g, *, a]
t3 = f(a, b)        → flat: [f, a, b]
t4 = h(a)            → flat: [h, a]
```

The discrimination tree (trie):
```
root
├── f
│   ├── g
│   │   ├── a → b → {t1}
│   │   └── * → a → {t2}
│   └── a → b → {t3}
└── h
    └── a → {t4}
```

Each internal node branches on the symbol at that position in the preorder string. Leaves store the set of indexed terms (or rules).

**Node structure:**
```
DiscTreeNode {
  children: Map<Symbol, DiscTreeNode>   // branches for function symbols and constants
  wildcard: DiscTreeNode | null          // branch for variable positions (*)
  data: Set<Rule> | null                 // non-null only at leaves
}
```

### Insertion Algorithm

```
INSERT(node, flatterm[], position, rule):
  if position == len(flatterm):
    node.data.add(rule)
    return
  sym = flatterm[position]
  if sym == '*':
    if node.wildcard == null: node.wildcard = new DiscTreeNode()
    INSERT(node.wildcard, flatterm, position + 1, rule)
  else:
    if sym not in node.children: node.children[sym] = new DiscTreeNode()
    INSERT(node.children[sym], flatterm, position + 1, rule)
```

**Build time:** O(R x D) where R = number of rules, D = max flatterm length (= term size).

### Retrieval Algorithms

There are four retrieval operations. The critical distinction: what is in the **index** vs what is the **query**.

#### (a) Find Generalizations (pattern in index, ground term as query)

This is the CALC use case: rules contain patterns (with variables), facts are ground.

```
FIND_GENERALIZATIONS(node, query_flat[], pos, results):
  if pos == len(query_flat):
    if node.data != null: results.addAll(node.data)
    return
  sym = query_flat[pos]
  // Follow the concrete branch matching the query symbol
  if sym in node.children:
    FIND_GENERALIZATIONS(node.children[sym], query_flat, pos + 1, results)
  // Also follow the wildcard branch (variable in pattern matches anything)
  if node.wildcard != null:
    skip = arity_subtree_size(sym)  // skip the whole subterm the variable covers
    FIND_GENERALIZATIONS(node.wildcard, query_flat, pos + skip, results)
```

**Key insight:** When the query is ground (no variables), the wildcard-follow at each node is the ONLY source of branching. The concrete-branch follow is deterministic. This means: number of branches = number of variable positions in indexed patterns. For shallow patterns with few variables, retrieval is nearly linear.

**Complexity:** O(|query| x branching_factor). Worst case (all patterns are single variables): O(R). Typical case with structured patterns: O(|query|) per matching pattern.

#### (b) Find Instances (ground terms in index, pattern as query)

Dual operation: query has variables, index has only ground terms.

```
FIND_INSTANCES(node, query_flat[], pos, results):
  if pos == len(query_flat):
    if node.data != null: results.addAll(node.data)
    return
  sym = query_flat[pos]
  if sym == '*':
    // Variable in query: follow ALL children (any ground symbol matches)
    for child_sym in node.children:
      skip = arity_subtree_size(child_sym)
      FIND_INSTANCES(node.children[child_sym], query_flat, pos + skip, results)
  else:
    // Concrete symbol: follow matching branch only
    if sym in node.children:
      FIND_INSTANCES(node.children[sym], query_flat, pos + 1, results)
```

#### (c) Find Unifiable (both may have variables)

Most expensive: at each node, must follow both the matching concrete branch AND the wildcard branch AND (if query has variable) all concrete children. This is the general case used in resolution theorem provers.

#### (d) Find Variants (exact match up to variable renaming)

Follow only branches where symbols match or both are variables. Simplest retrieval.

### Perfect vs Imperfect Discrimination Trees

**Imperfect (non-deterministic) discrimination trees** (McCune 1992): Variables in the trie are collapsed to a single `*` node. Different variable occurrences (`X`, `Y`) are not distinguished. This means two patterns `f(X, X)` and `f(X, Y)` share a single trie path `[f, *, *]`. The trie returns BOTH as candidates, and a post-filter (full unification/matching) is needed to distinguish them.

**Perfect discrimination trees**: Each path encodes the full binding structure. Variables are tracked: the first occurrence of `X` gets `*_new`, subsequent occurrences get `*_back(ref)` pointing back to the first. This eliminates false positives entirely — every candidate returned truly matches. But the trie can grow exponentially in pathological cases.

**Trade-off:**
- Imperfect: smaller trie, fast build, but needs post-filter. Used when post-filter (unification) is cheap.
- Perfect: larger trie (potentially exponential), no post-filter needed. Used in E prover (Schulz) for rewriting and unit forward subsumption where the volume of candidates matters.

**For CALC:** Imperfect discrimination trees suffice. The patterns are small (2-3 levels), variable sharing is rare in forward rules, and `tryMatch()` is already fast (O(term_size) with content-addressed equality).

### Complexity Summary

| Operation | Time | Space |
|-----------|------|-------|
| Build index | O(R x D) | O(R x D) nodes worst case |
| Insert one rule | O(D) | O(D) new nodes |
| Delete one rule | O(D) | — |
| Query: generalizations (ground query) | O(D) per match, O(D x matches) total | — |
| Query: instances (pattern query) | O(D x branching) | — |
| Query: unifiable | O(D x branching^2) worst case | — |

R = number of rules/patterns, D = max term size (flatterm length).

### Strengths
- Simple to implement (~100-150 LOC)
- O(D) per query for generalization retrieval with ground queries
- Perfect filtering possible (no false positives)
- Well-understood, battle-tested in E, Waldmeister, Otter, Prover9

### Weaknesses
- Poor discrimination when patterns share long prefixes (all EVM rules start with `pc(...)`)
- Perfect variant can have exponential space
- Fixed traversal order (preorder) may not be optimal for all pattern shapes
- No substitution sharing (each match restarts from scratch)

### When to Use
- 50-500 rules with diverse top-level structure
- Generalization retrieval (patterns in index, ground facts as queries)
- When post-filter is acceptable (imperfect) or patterns are linear (perfect)

---

## 2. Path Indexing

**Key references:**
- Stickel, M.E. (1989). "The path-indexing method for indexing terms." Technical Report 473, AI Center, SRI International.
- McCune, W. (1992). "Experiments with discrimination-tree indexing and path indexing for term retrieval." (comparative study)
- Riazanov, A. & Voronkov, A. (2003). "Efficient instance retrieval with standard and relational path indexing."

### Core Data Structure

Instead of a single preorder traversal, path indexing decomposes a term into **all root-to-leaf paths**. Each path is a sequence of (position, symbol) pairs. These paths are stored in **separate inverted indices** (one per position sequence).

**Example.** For `f(g(a), b)`:
- Path 1: position `ε.1.1`, symbols along the way: `f, g, a`
- Path 2: position `ε.2`, symbols: `f, b`

Each unique position path maintains a set of terms containing that path. Retrieval computes the **intersection** of all path sets matching the query.

### How It Differs from Discrimination Trees

| Aspect | Discrimination Trees | Path Indexing |
|--------|---------------------|---------------|
| Decomposition | Single preorder string | Multiple root-to-leaf paths |
| Storage | One trie | Multiple inverted lists |
| Retrieval | Follow one trie path | Intersect multiple lists |
| Variable handling | Wildcard branches in trie | Absent paths in lists |
| Filtering | Single traversal | Set intersection |

### Algorithm

**Insertion:** For each root-to-leaf path in the term, add the term to the inverted list for that path.

**Retrieval (find instances):** For each path in the query pattern (non-variable paths only), look up the inverted list. Intersect all lists. The result contains all terms that have the query's concrete structure at all non-variable positions.

**Retrieval (find generalizations):** For each path in the query, look up terms that either (a) have the same concrete path, or (b) have a variable at some prefix position of that path. Union the filtered lists.

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Build | O(R x P) where P = paths per term | O(R x P) |
| Query | O(P x log(list_size)) for intersection | — |

### Strengths
- Better than discrimination trees for **backward subsumption** (finding all indexed clauses subsumed by a query) — the intersection naturally handles multi-position constraints
- Works well with large databases of ground terms (1000+ indexed terms)
- Each path index is independent — easy to parallelize
- Evaluated by Isabelle/ML: "path indexing is significantly faster when 200 or more terms are indexed" (for certain query types)

### Weaknesses
- Set intersection cost: O(P x min_list_size) per query. For terms with many paths, this dominates.
- Not a perfect filter — still needs post-unification
- More complex implementation than discrimination trees (multiple indices, intersection logic)
- For generalization retrieval (CALC's use case), discrimination trees are typically faster

### When to Use
- Instance retrieval / backward subsumption (finding indexed terms that are instances of a query)
- Large ground-term databases (200+ terms per predicate)
- NOT recommended for CALC's forward-chaining use case (patterns in index, ground queries)

---

## 3. Substitution Trees

**Key references:**
- Graf, P. (1994). "Substitution tree indexing." MPI Technical Report MPI-I-94-251. Max Planck Institute.
- Graf, P. (1995). "Substitution tree indexing." In Proc. RTA '95, LNCS 914, pp. 117-131.
- Graf, P. (1996). *Term Indexing.* LNAI 1053, Springer. (monograph covering all techniques)
- Pientka, B. (2003). "Higher-order substitution tree indexing." In IJCAR '03.

### Core Data Structure

A substitution tree stores terms by factoring out their **most specific common generalization** (msg). Internal nodes hold substitution fragments; the composition of substitutions along a root-to-leaf path reconstructs the original term.

**Example.** Index three patterns:
```
t1 = f(a, b)
t2 = f(a, c)
t3 = f(d, b)
```

A discrimination tree stores three separate paths: `[f,a,b]`, `[f,a,c]`, `[f,d,b]`.

A substitution tree factors out shared structure:
```
root: f(X, Y)
├── {X→a}: f(a, Y)
│   ├── {Y→b}: f(a, b) → t1
│   └── {Y→c}: f(a, c) → t2
└── {X→d, Y→b}: f(d, b) → t3
```

Each edge carries a **substitution fragment**. The full substitution from root to leaf reconstructs the original term. Siblings share their parent's substitution, so common structure is stored once.

### Insertion Algorithm

To insert a new term `t`:
1. Start at root. Apply the inverse of the root substitution to `t`.
2. At each node, compute the **msg** (most specific common generalizer) of the current residual and the node's substitution.
3. If the msg differs from the node's substitution, split the node: create a new parent with the msg, and two children (old node with residual, new term with residual).
4. If the msg equals the node's substitution, recurse into the appropriate child.

The msg computation uses anti-unification (dual of unification): find the most specific term that generalizes both inputs.

### Retrieval Algorithm

**Find generalizations** (pattern in tree, ground query): Traverse from root, at each node apply the edge substitution. If the substitution is compatible with the query (all concrete symbols match, variables can be anything), continue. Collect all leaf terms reached.

**Key advantage:** Substitutions computed during traversal can be **reused**. When the tree branches, the parent's partial substitution is shared — you don't recompute it for each branch. This is the central benefit over discrimination trees, where matching restarts from scratch for each candidate.

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Build | O(R x D x anti-unify) | O(shared) — significantly less than O(R x D) |
| Insert one | O(D + anti-unify) | O(delta from msg) |
| Query | O(D x matches) with shared substitution work | — |

The space advantage is the main selling point: for R patterns of size D, if they share structure, the tree stores O(R x delta) where delta is the average deviation from the common generalizer. In the worst case (no sharing) it's O(R x D), same as a discrimination tree.

### Strengths
- **Space efficiency**: Maximal sharing of common term structure. For rule sets with many structural variants (e.g., `f(a,b)`, `f(a,c)`, `f(a,d)`), space is O(R) instead of O(R x D).
- **Substitution reuse**: Partial substitutions computed during traversal carry forward to children. Avoids redundant matching work.
- **Outperforms discrimination trees** in Graf's experiments on large rule sets (1000+) with high structural similarity.
- Works for terms AND substitutions (can index idempotent substitutions directly).

### Weaknesses
- **Implementation complexity**: Anti-unification, substitution composition, and node splitting are significantly more complex than trie insertion (~300-500 LOC).
- **Overhead for small rule sets**: The msg computation overhead is not amortized for < 100 rules.
- **Traversal cost**: Each node requires substitution application, which involves variable lookups. For shallow patterns, this overhead exceeds the simpler tag-comparison of discrimination trees.

### When to Use
- 500+ rules with high structural similarity (many rules differ in only a few positions)
- When substitution results are needed (not just candidate sets)
- Memory-constrained environments where sharing matters
- NOT recommended for CALC at current scale (44 rules, minimal sharing)

---

## 4. Code Trees

**Key references:**
- Voronkov, A. (1995). "The anatomy of Vampire: Implementing bottom-up procedures with code trees." J. Automated Reasoning 15(2), 237-265.
- Riazanov, A. & Voronkov, A. (2001). "Partially adaptive code trees." In JELIA '01, LNCS 2258, pp. 209-220.
- Tammet, T. (1998). "Towards efficient subsumption." In CADE-15.

### Core Idea

Code trees compile the discrimination tree structure into a **linear bytecode program**. Instead of following trie pointers at runtime, the system executes a sequence of instructions that encode the branching logic.

### Instruction Set

The abstract machine operates on a **query term** (the fact to match against) and a set of **registers** (for variable bindings). Instructions:

| Instruction | Semantics |
|-------------|-----------|
| `CHECK(pos, sym)` | Assert that the symbol at position `pos` in the query equals `sym`. Fail if not. |
| `COMPARE(pos1, pos2)` | Assert that subterms at `pos1` and `pos2` are equal. (For non-linear patterns like `f(X,X)`.) |
| `BIND(pos, reg)` | Bind the subterm at `pos` to register `reg`. |
| `BRANCH(pos, {sym1→pc1, sym2→pc2, ...})` | Switch on the symbol at `pos`, jump to the corresponding program counter. |
| `YIELD(rule)` | The current rule matched. Add to result set. |
| `BACKTRACK` | Return to the last choice point. |

### Compilation

All rule patterns are compiled into a single code tree (bytecode program). The compiler:
1. Takes all patterns, computes their preorder flattenings
2. Builds a discrimination-tree-like structure
3. Linearizes the tree into bytecode, with `BRANCH` instructions at trie forks and `YIELD` at leaves
4. Optimizes: common prefix checking is shared, dead branches eliminated

**Example.** For patterns `f(a, X)` and `f(b, Y)`:
```
0: BRANCH(root, {f→1, *→FAIL})
1: BRANCH(1, {a→2, b→4, *→FAIL})
2: BIND(2, R0)           // X bound to second arg
3: YIELD(rule1)
4: BIND(2, R1)           // Y bound to second arg
5: YIELD(rule2)
```

### Relationship to Compiled Pattern Matching (Maranget 2008)

Code trees and Maranget's compiled decision trees solve the same problem: multi-pattern matching compiled to efficient code. Key connections:

- Maranget focuses on **algebraic datatypes** in ML; code trees focus on **first-order terms** in logic.
- Both produce decision trees where internal nodes test positions and branch on constructors.
- Maranget's "necessity" heuristic (test the column that eliminates the most patterns) corresponds to code tree **column selection** optimization.
- Code trees additionally handle **variable binding** and **non-linear patterns** (repeated variables), which Maranget's setting does not require.

The partially adaptive code trees of Riazanov & Voronkov (2001) combine compiled code with runtime adaptation: the instruction sequence is fixed, but some branch targets are updated when new clauses are added. This gives near-compiled performance with incremental updates.

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Compile | O(R x D x optimization) — can be O(R^2 x D) with full optimization | O(R x D) bytecode |
| Query | O(D) — same as discrimination tree, but with lower constant factor (no pointer chasing) | — |
| Incremental update | O(D) for partially adaptive | — |

### Strengths
- **Fastest query execution**: Bytecode dispatch eliminates trie pointer indirection. 2-5x faster than pointer-based discrimination trees in Vampire benchmarks.
- **Locality**: Bytecode is a flat array — cache-friendly. Trie nodes may be scattered in memory.
- **Shared prefix optimization**: Common checks across rules are executed once.
- **Partially adaptive**: Can add/remove rules without full recompilation (Riazanov & Voronkov 2001).

### Weaknesses
- **Complex implementation**: ~500-800 LOC for the compiler, bytecode interpreter, and optimization passes.
- **Compilation cost**: Full optimization is O(R^2 x D). Acceptable for fixed rule sets; expensive for dynamic ones.
- **Debugging**: Bytecode is harder to inspect than a trie structure.

### When to Use
- Fixed rule sets compiled once at load time (CALC's model)
- Hundreds of rules where trie pointer overhead is measurable
- Provers doing millions of queries per second (Vampire, SPASS)
- NOT justified for < 100 rules (compilation overhead exceeds benefit)

---

## 5. Fingerprint Indexing

**Key references:**
- Schulz, S. (2012). "Fingerprint indexing for paramodulation and rewriting." In IJCAR '12, LNCS 7364, pp. 477-483.
- Schulz, S. (2013). "Simple and efficient clause subsumption with feature vector indexing." In PAAR-2012 (related technique for clause-level indexing).

### Core Idea

Sample K fixed positions in a term to produce a **fingerprint** (a K-element feature vector). Use fingerprints as a cheap pre-filter: if fingerprints are incompatible, the terms cannot match/unify. If fingerprints are compatible, do full matching.

### Feature Vector Construction

Choose K **sample positions** in the term tree. For each position, record the symbol found there (or a special value if the position does not exist in the term, or `*` if a variable occupies that position).

**Standard sample positions:**
- `p0 = ε` (root symbol)
- `p1 = 1` (first child of root)
- `p2 = 2` (second child of root)
- `p3 = 1.1` (first child of first child)
- etc.

**Example with K=3, positions = {ε, 1, 2}:**
```
f(g(a), b) → fingerprint: (f, g, b)
f(g(x), a) → fingerprint: (f, g, a)
f(x, y)    → fingerprint: (f, *, *)
h(a)       → fingerprint: (h, a, ⊥)    // ⊥ = position doesn't exist
```

### Trie Organization

Fingerprints are stored in a **K-level trie** where level `i` branches on the symbol at sample position `p_i`. Terms are stored at leaves.

Retrieval traverses the trie. At each level:
- **For matching (find instances):** If query has concrete symbol `s` at this position, follow only the `s` branch. If query has `*`, follow ALL branches.
- **For generalization (find patterns):** If query has concrete `s`, follow `s` branch AND `*` branch. If query has `*`, follow only `*` branch.
- **For unification:** Follow `s` branch, `*` branch, and (if query has `*`) all branches.

Since all terms at a leaf share the same fingerprint, they are stored once. This is a major advantage over coordinate indexing (which would require intersecting per-position lists).

### Configurations in E Prover

Schulz tested multiple configurations:

| Config | Sample Positions | K |
|--------|-----------------|---|
| FP1 | ε | 1 |
| FP2 | ε, 1 | 2 |
| FP3 | ε, 1, 2 | 3 |
| FP3D | ε, 1, 1.1 | 3 (depth-first) |
| FP4 | ε, 1, 2, 1.1 | 4 |
| FP4M | ε, 1, 2, 1.1 (multi-value) | 4 |
| FP7 | ε, 1, 2, 1.1, 1.2, 2.1, 2.2 | 7 |

### False Positive Analysis

Fingerprint indexing is an **imperfect filter**: it never misses a match (no false negatives) but may return non-matching candidates (false positives).

The false positive rate depends on:
- **K** (more sample positions = fewer false positives)
- **Vocabulary size V** (more distinct symbols = better discrimination)
- **Variable density** in patterns (more variables = more `*` entries = more false positives)

Rough model: for random terms with vocabulary V and patterns with w wildcard positions out of K samples:
```
P(false positive) ≈ (1/V)^(K - w)
```

For EVM terms with V~50 symbols:
- K=2, w=1: ~1/50 = 2% false positive rate
- K=3, w=1: ~1/2500 = 0.04%
- K=4, w=1: ~1/125000 ≈ 0%

In practice, Schulz found K=3 or K=4 sufficient to eliminate >99% of non-matching candidates, with FP7 providing near-perfect filtering.

### Feature Vector Indexing (Related Technique)

Also by Schulz (2004, 2013). For **clause subsumption** rather than term matching. Each clause is represented by a vector of feature counts (e.g., number of occurrences of each function symbol). Organized in a trie.

Key property: if clause C subsumes clause D, then for every feature, count(C) <= count(D). So subsumption retrieval follows branches with `<=` (or `>=`) comparisons at each level.

### Complexity

| Operation | Time | Space |
|-----------|------|-------|
| Build | O(R x K) | O(R x K) in trie |
| Query | O(K x branching) where branching = wildcard density | — |
| Pre-compute fingerprint | O(K) per term | O(K) per term |

### Strengths
- **Extremely simple**: ~50-80 LOC to implement
- **Low overhead**: O(K) per query (K is typically 3-7, a small constant)
- **Small index**: K-level trie with at most V^K leaves (but typically much sparser)
- **Uniform algorithm**: Same code handles matching, generalization, and unification
- **Good enough in practice**: K=4 eliminates >99% of false candidates in E prover benchmarks

### Weaknesses
- **Imperfect**: Always requires post-filter (full matching/unification)
- **Sampling bias**: If discriminating structure is at positions not sampled, filtering is poor
- **No substitution output**: Only filters candidates; doesn't produce bindings
- **Diminishing returns**: Beyond K=7, improvement is marginal (deep positions are rarely discriminating)

### When to Use
- Quick win for any rule set size (even 20 rules benefit if fingerprints are free)
- When full discrimination tree implementation is not justified
- As a **first-stage filter** before a more expensive second stage
- CALC's opcodeLayer is already a K=2 fingerprint index (sampling root and second argument)

---

## 6. Adaptive / Hybrid Indexing

**Key references:**
- Ramakrishnan, I.V., Sekar, R.C. & Voronkov, A. (2001). "Term indexing." In Handbook of Automated Reasoning, Ch. 26.
- Riazanov, A. & Voronkov, A. (2001). "Partially adaptive code trees." In JELIA '01.
- Nieuwenhuis, R., Hillenbrand, T., Riazanov, A. & Voronkov, A. (2001). "On the evaluation of indexing techniques for theorem proving." In IJCAR '01.

### Adaptive Automata (Handbook of Automated Reasoning)

The term indexing chapter in the Handbook surveys techniques along two axes:
- **Fixed vs adaptive traversal order**: Discrimination trees and path indexing use fixed preorder. Substitution trees and unification factoring use adaptive order (choosing the most discriminating position at each step).
- **Perfect vs imperfect filtering**: Perfect (discrimination tree, substitution tree) vs imperfect (path indexing, fingerprint indexing).

Adaptive traversal means: at each trie node, instead of always branching on the next preorder symbol, choose the position that maximizes discrimination (eliminates the most candidates). This is analogous to Maranget's column-selection heuristic for pattern matching.

### Hybrid Approaches in Practice

Real provers use **multiple indices** for different operations:

**E Prover (Schulz):** Uses perfect discrimination trees for forward rewriting + unit subsumption, and fingerprint indexing as a pre-filter for backward operations. Feature vector indexing for clause subsumption.

**Vampire (Voronkov):** Uses code trees (compiled) for forward subsumption and demodulation. Substitution trees for unification indexing.

**SPASS:** Uses discrimination trees with term hashing for forward chaining.

### Switching Strategy by Rule Count

Based on the literature and CALC's architecture:

| Rule Count | Recommended Strategy |
|------------|---------------------|
| < 20 | Linear scan (current predicateLayer). Overhead of building index exceeds benefit. |
| 20-100 | Fingerprint indexing (K=3-4). Cheap to build, good filtering. |
| 100-500 | Discrimination tree. Perfect filtering, moderate implementation cost. |
| 500-2000 | Substitution tree or code tree. Space sharing or compiled speed. |
| 2000+ | Code tree with adaptive compilation. Maximum throughput. |

CALC's strategy stack already supports this: each layer can decide at build time whether to claim rules based on count.

---

## 7. Hash-Consing Interaction

**Key references:**
- Conchon, S. & Filliatre, J.-C. (2006). "Type-safe modular hash-consing." In ACM SIGPLAN Workshop on ML, Portland, OR.
- Filliatre, J.-C. OCaml hash-consing library: https://github.com/backtracking/ocaml-hashcons

### How Content-Addressing Changes Indexing

In CALC, every term is content-addressed: `Store.put(tag, children)` returns a unique integer hash. Two terms with the same hash are structurally identical (`O(1)` equality via `===`).

This interacts with term indexing in several ways:

#### (a) O(1) Equality Enables Shortcuts

In a standard discrimination tree, checking whether a query symbol matches a trie branch requires string comparison. With content-addressing:
- `Store.tag(h)` returns the constructor tag (O(1) array read)
- `h1 === h2` determines structural equality (O(1) integer comparison)

This means trie branch comparison is always O(1), not O(symbol_length).

#### (b) Term Hashes as Trie Keys

Instead of branching on tag strings, branch on **Store indices** (integers). This is more discriminating:
- Tag-based: `pc(42)` and `pc(43)` both go to the `pc` branch
- Hash-based: `pc(42)` hash=1017 and `pc(43)` hash=1018 go to different branches

The trade-off: hash-based branching creates wider tries (one branch per unique term) but eliminates false positives at that position entirely. Useful for positions where the indexed pattern has a GROUND subterm.

#### (c) Memoized Traversal Results

Since the same fact hash always produces the same trie traversal, we can **cache** the result: `trie_cache[fact_hash] → Set<Rule>`. On repeated queries with the same fact: O(1) lookup.

This is particularly powerful in CALC's forward chaining where:
- Many facts persist across steps (only delta changes)
- Facts are frequently re-queried (same PC value at different branches)

#### (d) Hybrid: Hash for Ground Prefix, Trie for Variable Suffix

For a pattern like `code(PC, 0x60)` where the second argument is ground:
- First branch on tag `code` (trie)
- Second position has variable `PC`: wildcard branch
- Third position has ground `0x60` (hash 42): can use hash equality directly

The trie naturally does this: branch comparison uses `Store.tag`, which is O(1). Content-addressing doesn't change the trie structure — it just makes each comparison cheaper.

#### (e) Hash-Consed Substitution Trees

Conchon & Filliatre's hash-consing library assigns each value a unique integer `tag`. For substitution trees, this means:
- Anti-unification (msg computation) can use tag comparison instead of structural comparison
- Substitution application: `{X → hash_42}` is O(1) to store and compare
- Occurs-check: O(1) via tag sets instead of structural walk

In CALC's Store, this is already the case — substitution `{X → 42}` means "variable X maps to Store index 42". The substitution tree edges would carry `Map<Var, StoreIndex>` entries, with O(1) application and comparison.

#### (f) When Hash-Consing Makes Indexing Unnecessary

If facts are ground and rule trigger patterns are also ground (no variables), then:
- `ruleIndex[fact_hash] → Rule[]` is a perfect O(1) index
- No trie needed at all

This is rare in practice (most patterns have at least one variable), but CALC's `opcodeLayer` is close: it looks up `code(PC, OPCODE)` where OPCODE is the discriminating ground subterm, and PC is a variable.

---

## Detailed CALC Integration Design

### Discrimination Tree Layer for Strategy Stack

Fits into the existing strategy stack architecture:

```javascript
const discriminationTreeLayer = {
  claims: (rule) => true,  // claims all rules
  build: (rules) => {
    const root = buildDiscTree(rules);
    return {
      getCandidateRules(state, stateIndex) {
        // For each predicate in state, query the disc tree
        const candidates = new Set();
        for (const pred in stateIndex) {
          if (pred === 'codeByPC' || pred === '*') continue;
          for (const fact of stateIndex[pred]) {
            for (const rule of queryDiscTree(root, fact)) {
              candidates.add(rule);
            }
          }
        }
        return [...candidates];
      }
    };
  }
};
```

**Problem:** This queries ALL facts against the tree every step. For 100K facts, this is O(100K x term_depth). Need delta tracking to only query changed facts.

**Solution:** Semi-naive integration — only query facts that changed since last step. This connects to [[incremental-matching]] (Task #14).

### Build-Time vs Query-Time Trade-off

| Approach | Build | Query | Space | Perfect? |
|----------|-------|-------|-------|----------|
| Predicate filter | O(R) | O(R) per step | O(R) | No (imperfect) |
| Fingerprint K=2 | O(R) | O(R) per step | O(R x K) | No (imperfect) |
| Discrimination tree | O(R x D) | O(D) per fact | O(R x D) | Yes |
| Substitution tree | O(R x D) | O(D) per fact | O(shared) | Yes |
| Code tree | O(R^2 x D) | O(D) per fact | O(R x D) | Yes |

R = rules, D = max term depth. For CALC: R=44, D=2-3.

### Cross-Check Strategy

Same approach as other optimizations:
1. Run symexec with predicate layer only → collect candidate sets per step
2. Run symexec with discrimination tree layer → collect candidate sets per step
3. Assert: tree candidates ⊇ predicate candidates (tree may give more precise filtering)
4. Assert: all actually-matching rules appear in tree candidates (no false negatives)

---

## What's Needed vs What Exists

| Need | Current Solution | Gap | Stage |
|------|-----------------|-----|-------|
| Per-step rule selection | opcodeLayer + predicateLayer | OK for 44 rules | — |
| Per-fact rule selection | None (re-evaluate all candidates) | Needed at 100+ rules | 9 |
| Delta-aware matching | None (re-match all facts) | Needed at 100K facts | semi-naive |
| Deep pattern indexing | 1-level predicate head | Needed at depth 4+ | 9 |

---

## Research Directions

### Multi-Antecedent Indexing

Discrimination trees index one pattern per rule (the "trigger"). For rules with 5 antecedents, the trigger choice affects filtering quality. Options:

1. **Most selective trigger:** Choose the antecedent with the most concrete symbols. Requires selectivity estimation (count ground vs metavar positions).
2. **Multi-key index:** Index on multiple antecedents simultaneously. Like a multi-column database index. More discriminating but more complex.
3. **Join ordering:** Process antecedents in selectivity order (most selective first). Related to Rete beta network optimization.

### Incremental Trie Maintenance

When rules are added/removed dynamically (future: runtime calculus extension), the discrimination tree must be updated. Insertion is O(pattern_depth). Deletion requires reference counting at leaves.

For CALC's current model (rules fixed at load time): not needed. But for a meta-proof system that explores different rule sets: important.

### Trie Compression

**Patricia tries:** Compress single-child chains into single edges with multi-symbol labels. Reduces pointer chasing. Relevant when many rules share long common prefixes.

**Array-mapped tries (HAMT):** Use bitmap + compact array instead of Map for children. Better cache performance. Relevant for tries with many children per node.

### Persistent Tries for Backtracking

If the execution tree (symexec) needs to undo state changes, a persistent trie (path-copied) allows O(log N) snapshots. CALC's current undo mechanism (`undoIndexChanges`) is more efficient for linear-resource forward chaining, but persistent tries would be needed for speculative multi-rule exploration.

---

## Summary Comparison Table

| Technique | Query Time | Space | Perfect? | Impl. Complexity | Best For |
|-----------|-----------|-------|----------|-------------------|----------|
| **Discrimination tree** | O(D) | O(R x D) | Yes* | ~150 LOC | Generalization retrieval, 50-500 rules |
| **Path indexing** | O(P x log N) | O(R x P) | No | ~200 LOC | Instance retrieval, backward subsumption |
| **Substitution tree** | O(D) + subst | O(shared) | Yes | ~400 LOC | 500+ rules with structural sharing |
| **Code tree** | O(D), low const | O(R x D) | Yes | ~600 LOC | Fixed rule sets, max throughput |
| **Fingerprint index** | O(K) | O(R x K) | No | ~60 LOC | Quick wins, pre-filter stage |
| **Feature vector index** | O(K) | O(R x K) | No | ~80 LOC | Clause subsumption |

*Perfect with perfect discrimination variant; imperfect with standard variant.

D = max term depth/size, R = number of rules, P = paths per term, K = sample positions, N = indexed terms.

---

## References

- Christian, J. (1993). *Flatterms, discrimination nets, and fast term rewriting.* J. Automated Reasoning 10(1), 95-113.
- Conchon, S. & Filliatre, J.-C. (2006). *Type-safe modular hash-consing.* Workshop on ML.
- Graf, P. (1995). *Substitution tree indexing.* In RTA '95, LNCS 914.
- Graf, P. (1996). *Term Indexing.* LNAI 1053, Springer.
- Maranget, L. (2008). *Compiling pattern matching to good decision trees.* In ML '08.
- McCune, W. (1992). *Experiments with discrimination-tree indexing and path indexing for term retrieval.* J. Automated Reasoning 9(2), 147-167.
- Nieuwenhuis, R., Hillenbrand, T., Riazanov, A. & Voronkov, A. (2001). *On the evaluation of indexing techniques for theorem proving.* In IJCAR '01, LNCS 2083, 257-271.
- Ramakrishnan, I.V., Sekar, R.C. & Voronkov, A. (2001). *Term indexing.* In Handbook of Automated Reasoning, Vol. 2, Ch. 26, pp. 1853-1964.
- Rawson, M. — [discrimination-tree (Rust crate)](https://github.com/MichaelRawson/discrimination-tree). Reference implementation.
- Riazanov, A. & Voronkov, A. (2001). *Partially adaptive code trees.* In JELIA '01, LNCS 2258.
- Schulz, S. (2012). *Fingerprint indexing for paramodulation and rewriting.* In IJCAR '12, LNCS 7364, 477-483.
- Schulz, S. (2013). *Simple and efficient clause subsumption with feature vector indexing.* In PAAR-2012.
- Stickel, M.E. (1989). *The path-indexing method for indexing terms.* Technical Report 473, SRI International.
- Voronkov, A. (1995). *The anatomy of Vampire: Implementing bottom-up procedures with code trees.* J. Automated Reasoning 15(2), 237-265.
