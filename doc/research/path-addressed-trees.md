# Path-Addressed Trees vs Content-Addressed Trees

Research into tree data structures where node identity derives from structural position (path from root) rather than content (bottom-up hash).

---

## 1. Core Distinction

**Content-addressed (bottom-up):** A node's identity is a hash of its content and children's hashes. Two structurally identical subtrees anywhere in any tree share the same identity. This is hash consing / Merkle hashing.

**Path-addressed (top-down):** A node's identity is its path from the root -- a sequence of directions like `[1, 0, 2]` meaning "second child, first child, third child." Two nodes with identical content at different positions have different identities.

```
Content-addressed:  identity = H(tag, H(child1), H(child2))
Path-addressed:     identity = [0, 1, 0]  (root -> child0 -> child1 -> child0)
```

These are dual perspectives. Content addressing answers "what is this subtree?" Path addressing answers "where is this node in the tree?"

---

## 2. Formal Foundations: Positions in Terms

Term rewriting systems formalize positions extensively (Baader & Nipkow, *Term Rewriting and All That*, 1998):

**Definition.** A *position* in a term `t` is a finite sequence of positive integers. The empty sequence `epsilon` denotes the root. Position `p.i` denotes the i-th child at position `p`.

**Notation:**
- `t|_p` -- subterm of `t` at position `p`
- `t[s]_p` -- replace subterm at position `p` with `s`

**Example:** In `f(g(a, b), c)`:
- `epsilon` -> `f(g(a,b),c)` (root)
- `[0]` -> `g(a,b)` (first child of f)
- `[0,1]` -> `b` (second child of g)
- `[1]` -> `c` (second child of f)

A rewrite step: `t` rewrites to `t'` if there exists a rule `l -> r`, position `p`, and substitution `sigma` such that `t|_p = sigma(l)` and `t' = t[sigma(r)]_p`.

---

## 3. Related Concepts and Systems

### 3.1 Patricia Tries / Radix Trees

Patricia tries (Morrison, 1968) use key prefixes as paths through the tree. Each node represents a shared prefix; branching occurs where keys diverge. Path compression merges single-child chains into one edge.

**Relevance:** Patricia tries are path-addressed by construction -- a node's identity *is* its prefix path. No content hashing. Lookup/insert are O(k) where k = key length.

The Adaptive Radix Tree (ART, Leis et al. 2013) extends this with adaptive node sizes (4/16/48/256 children), achieving hash-table-competitive performance with sorted order.

### 3.2 Ethereum's Modified Merkle-Patricia Trie

A hybrid: keys are path-addressed (keccak256(address) determines the path through the trie), but each node is also content-hashed (Merkle) for authentication. The root hash summarizes the entire state.

This is the canonical example of combining both addressing schemes:
- **Path addressing** for lookup/update: navigate by key nibbles
- **Content addressing** for integrity: root hash authenticates all data
- Extension nodes compress common prefixes (Patricia optimization)

Trade-off: every state mutation requires O(log n) rehashing up to root.

### 3.3 Addressed Term Rewriting Systems

Dougherty, Lescanne, Liquori, and Lang (2004) developed **Addressed Term Rewriting Systems** where paths become first-class citizens inside terms rather than metalevel notation.

Key idea: paths (sequences of integers, possibly negative) are *part of the term language*, representing pointers between subterms. This generalizes:
- Classical positions in first-order terms
- De Bruijn indices in lambda calculus

Applications: operational semantics for languages with sharing, recursive computations, and cyclic data structures. Related to term-graph rewriting via explicit paths (Fernandez and Mackie).

### 3.4 De Bruijn Indices

De Bruijn indices (1972) are position-based variable representation: each bound variable is identified by a natural number counting the number of binders between the variable occurrence and its binding lambda.

This is path-addressing for *variables only*: the variable's identity is its structural position relative to its binder, not its name (content).

**Locally nameless representation** is a hybrid: de Bruijn indices for bound variables, names for free variables.

### 3.5 Zippers (Huet, 1997)

A zipper represents a position in a tree as a pair: (focused subtree, path context). The path context records "the way back to the root" -- reversed pointers from root to focus.

Zippers make path-addressed navigation first-class in functional programming. Updates at the focus are O(1); moving up/down is O(1). The path itself is the addressing mechanism.

### 3.6 Hash Array Mapped Tries (HAMT)

Bagwell's HAMT (2001) uses hash bits as path directions through a trie. Each 5-bit segment of the hash selects a child in a 32-way branching node with bitmap compression.

Used in Clojure/Scala persistent maps. Path copying enables persistence: updating one leaf copies O(log32 n) = O(1 in practice) nodes along the root-to-leaf path.

### 3.7 E-Graphs

E-graphs (egg, Willsey et al. 2021) are content-addressed: they maintain a hash-consing invariant where structurally identical e-nodes map to the same e-class. Union-find tracks equivalence classes.

E-graphs demonstrate the power of content addressing for equality saturation: rewrites only add information, and structural sharing is automatic. Path information is irrelevant -- only equivalence classes matter.

---

## 4. Term Indexing: Path Indexing vs Discrimination Trees

Automated theorem provers use term indexing for fast retrieval of unifiable/generalizable/instantiable terms. Two key methods:

### Path Indexing (Stickel, 1989)

A term is stored via **the set of all paths from root to leaves**. Each path records the function symbols and argument positions encountered.

For `f(g(a), b)`, the paths are:
- `f.1.g.1.a` (root -> first arg of f -> first arg of g -> leaf a)
- `f.2.b` (root -> second arg of f -> leaf b)

Each path is stored in a separate index (trie). To retrieve terms matching a query, intersect the candidate sets from each path's trie.

**Properties:** imperfect filter (candidates need post-verification), good for backward subsumption, decomposes the term structure by position.

### Discrimination Trees (McCune, 1992)

A term is stored via **a single path** from a fixed-order traversal (preorder). The entire term maps to one key in one trie.

For `f(g(a), b)`, the key is: `f, g, a, b` (preorder traversal).

**Properties:** better for forward subsumption, perfect filter for some operations, but harder for unification retrieval.

### Key Insight

Path indexing literally decomposes terms by their positional structure. It is the ATP community's answer to "how do you index terms by path?" The positions `f.1.g.1.a` and `f.2.b` *are* path addresses.

---

## 5. Trade-Off Analysis

### When Content-Addressing (Hash Consing) Wins

| Scenario | Why |
|----------|-----|
| Frequent equality checking | O(1) pointer comparison vs O(n) structural traversal |
| Structural sharing | Identical subtrees stored once, referenced many times |
| Memoization/caching | Hash serves as cache key; identical inputs reuse results |
| Immutable term manipulation | New terms share unchanged subtrees automatically |
| DAG representation | Natural deduplication of common subexpressions |

**Quantified benefits** (Conchon & Filliatre, 2006; Cheli et al., 2025):
- Equality: O(1) vs O(n)
- Memory: 2x reduction typical for symbolic computation
- Downstream speedups: 3-100x for operations that exploit sharing
- Prerequisite for e-graph equality saturation

**Costs:**
- Hash computation on every node creation
- Hash table lookup overhead
- Hash collisions require fallback to structural check
- Ineffective for mutable data (mutations would propagate through shared references)
- When few terms are structurally identical, overhead dominates

### When Path-Addressing Wins

| Scenario | Why |
|----------|-----|
| Frequent localized mutations | Update at position p without recomputing any hashes |
| Navigation-heavy operations | Zipper-style focus movement is O(1) |
| Position-dependent semantics | When "where" matters more than "what" (e.g., program counters) |
| Indexing for retrieval | Path indexing decomposes terms for fast candidate filtering |
| Stable structure, changing content | Path is stable even as leaf values change |

**Key advantage:** In a mutable tree where content changes frequently but structure stays the same, paths are stable identifiers. Content hashes change on every mutation and require O(depth) rehashing.

### Hybrid Approaches

1. **Ethereum MPT:** Path navigation for lookup + Merkle hashing for authentication
2. **HAMT:** Hash-derived paths for lookup + path copying for persistence
3. **Locally nameless:** De Bruijn (positional) for bound vars + names (content) for free vars
4. **Persistent trees with path copying:** Path identifies what to copy; structural sharing preserves unchanged subtrees

---

## 6. Term Graph Rewriting: The Sharing Dimension

Term *graph* rewriting (vs term *tree* rewriting) adds explicit sharing: if variable `x` appears twice in a rule's right-hand side, graph rewriting shares the matched subterm rather than copying it.

This is orthogonal to the path/content distinction but interacts with it:
- Content-addressed stores get sharing for free (same hash = same node)
- Path-addressed structures need explicit back-edges or let-bindings for sharing
- Ariola & Klop (1994, 1996) formalized cyclic term graphs with equational axioms

---

## 7. Application to CALC's Proof Search Engine

### Current Architecture

CALC uses content-addressed hash consing (Merkle-DAG):
- Store: global `Map<hash, {tag, children}>` with FNV-1a 32-bit hashing
- Equality: O(1) integer comparison
- Substitution: creates new hash-consed nodes (bottom-up rebuild)
- Contexts: multisets of hashes

### Would Path-Addressing Help?

Evaluating against CALC's specific workload:

**1. Equality checking is critical (identity axiom, unification)**

Content addressing wins decisively. The identity axiom `A |- A` is literally `hash1 === hash2`. Unification starts with hash comparison and short-circuits when equal. Path addressing would require O(n) structural comparison.

**Verdict: Content addressing is strictly better here.**

**2. Substitution creates new terms frequently**

Content addressing: `substitute(term, var, value)` walks the term top-down, creates new hash-consed nodes bottom-up. Each new node requires a hash computation and table lookup. But identical substitution results are automatically shared.

Path addressing: substitution could update leaf values without rehashing ancestors. But then equality checking becomes O(n) again, which is used far more frequently than substitution.

**Verdict: Content addressing wins because the O(1) equality payoff exceeds the substitution overhead.**

**3. Forward chaining rewrites state (linear resources consumed/produced)**

This is where path-addressing has a theoretical argument: linear resources are consumed/produced at specific positions, and the state structure (a multiset of formulas) doesn't change shape much. But CALC's state is a flat multiset of hashes, not a tree -- there's no meaningful "path" to a formula in a multiset.

The symexec optimizations already handle this via mutation+undo: state.linear is mutated in-place with an undo log, avoiding both copying and rehashing.

**Verdict: Not applicable. The state is a multiset, not a tree. Mutation+undo already solves the update problem.**

**4. The tree structure rarely changes shape**

This would favor path-addressing in a tree, but formulas in ILL are immutable once created. The "structure" that changes is the *context* (which formulas are present), not the formula trees themselves.

**Verdict: Content addressing is the right choice for immutable formula trees.**

### Where Path-Based Ideas Already Apply in CALC

- **Term indexing:** The opcode index (`codeByPC`) is essentially path indexing -- it indexes formulas by the PC value (a positional key) for O(1) lookup
- **Position in proof tree:** Proof tree nodes are implicitly path-addressed (the path through the proof tree identifies a subgoal)
- **Context splitting:** The distribution of linear resources among subgoals is a position-dependent operation

### Potential Path-Addressing Applications

- **Proof tree navigation:** A zipper over the proof tree would enable O(1) focus changes for interactive proving
- **Incremental rehashing:** If formulas were very large and mutations were localized, path-addressed subtrees with lazy rehashing could help. Not currently needed (formulas are small).
- **Path-based proof term extraction:** Recording the path through the proof tree as a term (like Curry-Howard proof terms)

---

## 8. Summary

| Dimension | Content-Addressed | Path-Addressed |
|-----------|-------------------|----------------|
| Identity | Hash of content | Position in tree |
| Equality | O(1) | O(n) |
| Sharing | Automatic (maximal) | Requires explicit management |
| Mutation | Requires rehashing O(depth) | O(1) at leaf |
| Navigation | Requires traversal from root | Zipper gives O(1) movement |
| Stable across mutations | No (hash changes) | Yes (path unchanged) |
| Best for | Immutable terms, frequent equality | Mutable trees, navigation-heavy |

For CALC's proof search engine, content addressing is the right choice. The workload is dominated by equality checking (identity axiom, unification, memoization), structural sharing (common subformulas), and immutable formula construction -- all of which content addressing handles optimally.

---

## References

- Baader & Nipkow, *Term Rewriting and All That*, Cambridge, 1998
- Morrison, "PATRICIA - Practical Algorithm To Retrieve Information Coded in Alphanumeric," JACM 15(4), 1968
- Leis et al., "The Adaptive Radix Tree: ARTful Indexing for Main-Memory Databases," ICDE 2013
- Huet, "The Zipper," J. Functional Programming 7(5), 1997
- Bagwell, "Ideal Hash Trees," EPFL Technical Report, 2001
- Conchon & Filliatre, "Type-Safe Modular Hash-Consing," ML Workshop, 2006
- Willsey et al., "egg: Fast and Extensible Equality Saturation," POPL 2021
- Stickel, "The Path-Indexing Method for Indexing Terms," SRI Technical Note, 1989
- McCune, "Experiments with discrimination-tree indexing and path indexing for term retrieval," J. Automated Reasoning 9(2), 1992
- Dougherty, Lescanne, Liquori, Lang, "Addressed Term Rewriting Systems," TERMGRAPH 2004
- Cervesato, Hodas, Pfenning, "Efficient Resource Management for Linear Logic Proof Search," TCS 1999
- De Bruijn, "Lambda Calculus Notation with Nameless Dummies," Indagationes Mathematicae 34, 1972
- Ariola & Klop, "Equational Term Graph Rewriting," Fundamenta Informaticae, 1996
- Cheli et al., "Efficient Symbolic Computation via Hash Consing," arXiv:2509.20534, 2025
- Ethereum Foundation, "Merkle Patricia Trie," ethereum.org/developers
