# Expression Simplification: Techniques from Proof Theory and Term Rewriting

Research survey for CALC's forward-chaining ILL engine. Focus: simplifying symbolic arithmetic expressions beyond what hevm/K/halmos do.

## 1. Congruence Closure / E-Graphs (egg / egglog)

### Mechanism

An e-graph is a union-find + hashcons hybrid. Each **e-class** contains a set of **e-nodes** (function applications whose children are e-class IDs). Asserting `a = b` merges their e-classes; **congruence closure** propagates: if `f(a) ~ f(b)` after merging `a ~ b`, those get merged too.

**Equality saturation** runs rewrite rules to completion (or a limit): every rule `l -> r` adds `r` to `l`'s e-class rather than destructively rewriting. The e-graph represents *all* equivalent forms simultaneously. **Extraction** then picks the cheapest term (AST-size, latency, etc.) via a bottom-up cost function.

**egglog** unifies this with Datalog. Rules are Datalog clauses over a database of partial functions. E-matching becomes relational join with worst-case-optimal guarantees. Semi-naive evaluation gives incrementality for free.

### What makes it fast

- **Deferred invariant maintenance** ("rebuild"): batch union-find operations, restore hashcons invariant once. Up to 87x faster than eager congruence closure.
- **Relational e-matching** (egglog): database-style query planning, seminaive evaluation. Avoids the exponential blowup of backtracking e-match.
- **Local cost functions** enable O(|e-graph|) greedy extraction.

### Applicability to CALC

CALC already has content-addressed terms (Store) with dedup — conceptually half an e-graph. The missing half is the union-find / equivalence classes.

**Concrete idea: E-graph layer for symbolic state.** Instead of a flat multiset of facts, wrap the state in a lightweight e-graph:
- When forward rules produce `plus(A,B) = C`, don't just add `C` — assert `plus(A,B) ~ C` in the e-graph.
- Symbolic terms like `plus(x, 0)` and `x` live in the same e-class after saturation with `plus(X, 0) -> X`.
- At branch points (JUMPI), extract the simplest representative for path conditions.

**Challenge:** Linear logic consumes facts. E-graphs are monotonic (you only add equalities). Need a "scoped e-graph" or colored e-graph (see below) that can fork/rollback for branching.

**Colored e-graphs** (Singher & Shacham, 2023) layer context-sensitive equalities on top of a shared base. Each JUMPI branch gets a "color" — equalities from that branch are visible only in that color. This maps well to symexec tree exploration.

**Implementation complexity:** ~500-800 LOC for a basic e-graph + rebuild. egglog-style relational matching would be 1500+ LOC. Colored extension adds another ~300 LOC.

## 2. Knuth-Bendix Completion

### Mechanism

Given equations E (e.g. `plus(X,0) = X`, `plus(X,Y) = plus(Y,X)`) and a reduction ordering >, KB completion:
1. Orient each equation into a rewrite rule (bigger side -> smaller side).
2. Find all **critical pairs** (overlapping rule applications).
3. Normalize each critical pair. If not equal, add as new rule.
4. Repeat until no new rules (success) or forever/failure.

When it succeeds, the resulting TRS is **confluent** and **terminating**: every term has a unique normal form, and rewriting always terminates.

### Failure cases

KB fails on **unorientable equations** (neither side is bigger), notably commutativity: `plus(X,Y) = plus(Y,X)`. Neither direction terminates. Extensions:
- **AC-completion** (Maude's mascott): completion modulo AC axioms, treating commutativity as a built-in theory rather than a rule.
- **Unfailing completion**: keeps unorientable equations as "demodulators," applies them only when they reduce under a ground ordering. Complete for equational theorem proving.
- **Multi-completion**: tries multiple orientations in parallel.

### Applicability to CALC

We could auto-generate simplification rules from equational axioms:
```
plus(X, 0) -> X                 (identity)
mul(X, 1) -> X                 (identity)
mul(X, 0) -> 0                 (annihilation)
plus(plus(X,Y), Z) -> plus(X, plus(Y,Z))  (right-associate)
```

For commutative operations, use AC-completion or ordered rewriting (only apply `plus(X,Y) -> plus(Y,X)` when `X > Y` in some term order, achieving a canonical sorted form).

**Practical for CALC:** We don't need the full algorithm. Our equational theory is small and fixed (plus, mul, mod 2^256). We can **hand-write the confluent TRS** and add it as a simplification pass. KB completion is more relevant if users define custom equational theories in .calc files.

**Implementation complexity:** Full KB completion: 1000+ LOC. Hand-written TRS for EVM arithmetic: ~100 LOC.

## 3. AC-Normalization (Maude-style)

### Mechanism

Associativity (A) and commutativity (C) are **equational axioms** declared on operators, not rewrite rules. The system rewrites *modulo* these axioms:
- **Flatten:** `plus(plus(a,b), c)` becomes the multiset `{a, b, c}` under `plus`.
- **Sort:** Apply a canonical ordering to the flattened arguments: `plus(a, b, c)` with `a < b < c`.
- **Match modulo AC:** Pattern `plus(X, Y)` matches any partition of the multiset into two non-empty sub-multisets.

Maude achieves near-constant-time AC rewriting for typical patterns via Eker's algorithms: AC argument lists are stored as sorted flat arrays; matching uses bipartite graph encodings.

### Applicability to CALC

CALC's `plus` and `mul` are AC. Currently they're binary: `plus(plus(a,b),c)`. AC-normalization would:
1. Flatten to a sorted list: `[a, b, c]` under `plus`.
2. Fold constants: `plus(3, x, 5)` -> `plus(8, x)`.
3. Cancel: `plus(x, neg(x))` -> `0` (if we add additive inverse).

**For content-addressed Store:** Introduce a new tag `ac_plus` / `ac_mul` with variadic children stored in sorted order. `Store.put('ac_plus', [child1, child2, ...])` with children sorted by hash value. Content-addressing then gives automatic structural equality for AC-equivalent terms.

**This is probably the single highest-value technique for arithmetic simplification.** It turns AC equivalence into syntactic identity via canonical representation.

**Implementation complexity:** ~200 LOC for flattened/sorted AC terms in Store. ~100 LOC for constant folding during construction. AC matching for forward rules: ~300 LOC additional.

## 4. Isabelle's Simplifier (simp)

### Mechanism

A conditional term rewriting system that applies rules bottom-up (innermost-first):
1. **Simpset**: a collection of rewrite rules `l = r [if P]`, congruence rules, and simprocs.
2. **Bottom-up traversal**: simplify subterms first, then try rules on the whole term.
3. **Conditional rewrites**: when `l = r if P`, the simplifier recursively tries to prove `P` using the same simpset (mutual recursion).
4. **Congruence rules**: control context. E.g., for `if P then A else B`, simplify `A` under assumption `P`, simplify `B` under assumption `not P`.
5. **Simprocs**: ML functions that generate rewrite rules on-the-fly for the current term (e.g., evaluate `3 + 5 -> 8`).
6. **Ordered rewriting**: permutative rules (like commutativity) only fire when the result is smaller under a lexicographic term order.
7. **Term net indexing**: discrimination-net-style indexing for fast rule lookup.

### What makes it effective

The architecture: simpset + conditional rewriting + congruence rules + simprocs. Each component is simple, but together they handle a huge range of simplifications. The simproc mechanism is especially powerful — it's the escape hatch for domain-specific computation (exactly what our FFI does).

### Applicability to CALC

Our forward engine already has the pieces:
- **Simpset** = forward rules + FFI definitions.
- **Simprocs** = FFI functions (arithmetic.js). Already called during forward chaining.
- **Missing: congruence rules.** Currently, simplifying inside a `plus(A, B)` doesn't propagate context. For path conditions in symexec, this matters: if we know `A = 5`, we should simplify `plus(A, 3)` to `8`.

**Concrete idea: Simplification pass after forward step.** After each forward rule fires and produces new facts, run a bottom-up simplifier on all newly produced terms. Use the current state (persistent facts) as the simpset context.

**Implementation complexity:** Bottom-up simplifier with rule indexing: ~300 LOC. Congruence rules: ~200 LOC. Connects to existing disc-tree + FFI infrastructure.

## 5. Coq's ring / omega Tactics

### Ring tactic (polynomial normalization)

**Mechanism:** Normalize polynomial expressions to **Horner form**: `f(x) = c` or `f(x) = c + x * g(x)`. This is a canonical representation for polynomials — two polynomials are equal iff their Horner forms are syntactically identical.

The tactic:
1. Reifies the goal expression into an abstract polynomial AST.
2. Normalizes to Horner form using a verified normalizer (associativity, commutativity, distributivity, constant folding).
3. Compares the two sides syntactically.

Uses **reflection**: the normalization computation happens inside the proof checker's reduction machinery, so the proof term is tiny (linear in the number of operations).

### Omega / lia (linear integer arithmetic)

**Mechanism:** Decision procedure for quantifier-free Presburger arithmetic (linear inequalities over integers).
1. Normalize all constraints to `a1*x1 + ... + an*xn >= 0`.
2. Eliminate variables one by one using **Fourier-Motzkin** (or the Omega test's dark/grey shadows).
3. If the empty system is infeasible, report UNSAT (the negation of the goal is false, so the goal holds).

The Omega test adds **dark shadows** (exact integer solutions) and **grey shadows** (approximate) beyond basic Fourier-Motzkin, handling divisibility constraints that arise from integer rounding.

### Applicability to CALC

**Polynomial normalization for EVM arithmetic.** EVM operates in Z/(2^256). We can normalize:
- `plus(plus(a, 3), 5)` -> `plus(a, 8)` (constant folding in Horner form)
- `mul(2, plus(a, b))` -> `plus(mul(2,a), mul(2,b))` (distribution, if it helps)
- Detect `plus(a, neg(a))` -> `0` (cancellation)

**Linear arithmetic for path condition pruning.** When symexec branches on `lt(gas, 100)`, the true-branch knows `gas < 100`. A linear arithmetic decision procedure could detect infeasible paths (e.g., `gas < 100` AND `gas > 200`).

**Practical approach:** Don't implement full omega. Instead:
1. **Constant folding** in Store.put: if both children of `plus` are binlits, compute eagerly. Already done via FFI.
2. **Horner normalization** as a rewrite pass: flatten `plus`/`mul` trees, collect constants, fold. ~200 LOC.
3. **Simple infeasibility check** for path conditions: maintain interval bounds per symbolic variable, prune when empty. ~150 LOC.

## 6. Lean4's simp Tactic

### Mechanism

Similar architecture to Isabelle's simplifier but with modern implementation:
1. **Discrimination tree indexing** for simp lemma lookup. Terms are encoded as preorder traversals; the disc tree finds all lemmas whose LHS pattern matches the current subterm.
2. **Bottom-up rewriting** with conditional lemmas.
3. **E-matching** for lemma instantiation: find substitutions that make a pattern match a subterm of the goal.
4. **Configurable reduction**: can enable/disable beta, zeta (let), delta (definition unfolding) reduction independently.

### What makes it fast

- Disc trees with **WHNF keys**: terms are reduced before indexing, so `f x` and `(fun y => f y) x` share the same key.
- `#discr_tree_simp_key` debugging command for inspecting lookup behavior.
- The aesop tactic (Lean's automation framework) uses **lazy discrimination trees** that avoid computing keys until needed.

### Applicability to CALC

CALC already has disc-tree indexing (Stage 9). The relevant new idea is:
- **Lazy disc trees for rule selection.** Currently we flatten every fact eagerly. For large states, lazy flattening (only flatten when the root tag has rules in the tree) could skip work.
- **WHNF-like normalization before indexing.** Before inserting a fact into the state index, normalize it (constant fold, AC-sort). Then the disc tree automatically deduplicates equivalent forms.

**Implementation complexity:** Lazy disc tree: ~50 LOC change to existing disc-tree.js. Pre-normalization: depends on normalization strategy (see section 3).

## 7. Maude's Rewriting Logic

### Mechanism

Maude implements rewriting logic: theories are `(Sigma, E, R)` where:
- `Sigma` = order-sorted signature (types with subtype relations)
- `E` = equational axioms (computed modulo, never as rules). Includes AC, identity, idempotency.
- `R` = rewrite rules (the actual computation steps)

Key features:
- **Order-sorted matching**: `nat < int`, so a rule for `int` automatically applies to `nat`.
- **Equational attributes**: AC, identity (`0` for plus), idempotency declared per operator. Matching is done modulo these attributes automatically.
- **Narrowing**: symbolic execution via unification instead of matching. Can explore all possible inputs.
- **Meta-level reflection**: Maude can rewrite its own rewrite theories.

Eker's algorithms for AC matching/normalization: O(log n) per rewrite step on flat sorted AC argument lists, vs O(n^k) for naive AC matching.

### Applicability to CALC

**Order-sorted types** are directly relevant. CALC's EVM calculus has implicit type structure: `uint256`, `address` (= uint160), `bool` (= {0,1}). If we had sort declarations:
```
sorts: bool < uint160 < uint256
op plus: uint256 uint256 -> uint256 [assoc comm id: 0]
```
Then `plus(x, 0) -> x` is automatic (identity attribute), and AC normalization is built into matching.

**Narrowing for symbolic execution** is exactly what CALC's symexec does (forward-chaining with symbolic terms). Maude's narrowing strategies could inform how we handle branching.

**Practical extraction:** The equational attribute approach. Instead of writing rules `plus(X, 0) -> X`, declare `plus` as `[assoc comm id: 0]` and let the matching engine handle it. This is the Maude philosophy: axioms are not rules, they're part of the matching logic.

**Implementation complexity:** Equational attributes on Store operations: ~400 LOC. Full narrowing integration: 1000+ LOC.

## 8. CHR (Constraint Handling Rules)

### Mechanism

CHR operates on a **constraint store** (multiset of constraints) using three rule types:
- **Simplification**: `H <=> G | B` — if head `H` matches and guard `G` holds, replace `H` with `B`.
- **Propagation**: `H ==> G | B` — if head `H` matches and guard `G` holds, add `B` (keep `H`).
- **Simpagation**: `H1 \ H2 <=> G | B` — keep `H1`, remove `H2`, add `B`.

This is **exactly** ILL forward chaining: simpagation = persistent head + linear head + guard + body. CHR's operational semantics IS multiset rewriting in linear logic.

### What makes it fast

CHR implementations (SWI-Prolog, JCHR) compile rules into host-language code:
- **Occurrence indexing**: each constraint occurrence in a rule head gets compiled to a lookup.
- **Join ordering**: multi-headed rules get optimized join plans (like database query optimization).
- **Propagation history**: prevents redundant rule firings (like CALC's pathVisited).
- **Late guard evaluation**: guards checked as early as possible during head matching.

### Applicability to CALC

The insight from the optimization roadmap is already noted: "CHR simpagation IS ILL forward rules." The 25+ years of CHR compilation research is directly applicable.

**Specific techniques to steal:**
1. **Optimal join ordering** for multi-antecedent rules. Currently CALC matches antecedents left-to-right. CHR compilers analyze selectivity and reorder. For a rule `A * B * !C -o D`, if `B` has fewer instances in the store, match `B` first.
2. **Guard scheduling**: Move cheap guards (like `neq(X,Y)`) before expensive pattern matches. CALC's FFI calls are guards — reorder them by cost.
3. **Constraint indexing**: Beyond disc-tree, CHR uses hash-based constraint stores keyed on first argument (like CALC's stateIndex by predicate). Multi-argument indexing (like `codeByPC[pc]`) is the CHR equivalent.

**Implementation complexity:** Join ordering: ~100 LOC in rule-analysis.js. Guard scheduling: ~50 LOC.

## Synthesis: Recommended Approach for CALC

Ordered by impact/effort ratio:

### Tier 1: Do now (~300 LOC total)

1. **AC-canonical Store.put** for plus/mul: flatten + sort children + fold constants during construction. Content-addressing then makes `plus(a,plus(b,c))` and `plus(b,plus(a,c))` the same hash.

2. **Eager constant folding** in Store.put: if all children of an arithmetic op are binlits, compute the result immediately. (Partially exists via FFI, but happens at match time, not construction time.)

3. **Simple simplification rules** as a post-step normalizer: `plus(X,0)->X`, `mul(X,1)->X`, `mul(X,0)->0`. Run on every newly produced fact. ~50 LOC.

### Tier 2: Next sprint (~500 LOC total)

4. **Interval tracking** for symbolic variables: maintain `[lo, hi]` bounds per symbolic var, updated on every arithmetic fact. Prune infeasible paths. ~200 LOC.

5. **Join ordering** for multi-antecedent rules: analyze antecedent selectivity at compile time, reorder matching. ~100 LOC.

6. **Guard scheduling**: evaluate cheap FFI guards (neq, lt) before expensive pattern matches. ~50 LOC.

### Tier 3: When scaling demands (~1500 LOC total)

7. **Scoped e-graph** for symbolic state: represent equivalent forms simultaneously, extract simplest at branch points. Use colored e-graphs for branching context.

8. **Horner normalization** for polynomial subexpressions: canonical form for complex arithmetic expressions involving multiple variables.

9. **Linear arithmetic decision procedure** for path feasibility: detect contradictory path conditions early. Could use a simplified Omega test or just Fourier-Motzkin elimination.

### Anti-patterns to avoid

- **Full KB completion at runtime**: too expensive, our theory is fixed. Pre-compute the confluent TRS offline.
- **Full AC matching in the forward engine**: the overhead of multiset matching in the hot loop would dominate. Better to canonicalize at construction time (Tier 1).
- **Unrestricted equality saturation**: e-graphs can blow up. Need size limits and extraction heuristics. The colored e-graph approach is more controlled.

## 9. CLP / Coroutining / Mercury Modes

### CLP(FD) Bounds Propagation

Each symbolic variable carries an interval domain `[lo, hi]`. Constraints between variables trigger propagation: `X + Y = Z` generates indexicals `X in min(Z)-max(Y)..max(Z)-min(Y)`. When a domain shrinks to a single value, the variable auto-binds. Bounds consistency (tracking only min/max) is cheap and sufficient for path feasibility.

### Coroutining = Loli Mechanism

Prolog's `freeze(X, Goal)` suspends `Goal` until X is bound. CALC's loli mechanism (`!P -o { body }`) is semantically identical. When FFI mode-mismatch occurs (e.g., `plus(X, 3, Y)` with X unbound), instead of failing, emit a loli watching for X's binding. When X becomes ground (through branching or constraint resolution), the loli fires and computes Y. Chains compose naturally: `loli(bind(X,_V), {plus(_V,3,Y) * loli(bind(Y,_W), {mul(_W,2,Z)})})`.

### Mercury Mode Formalization

Mercury requires explicit mode declarations with determinism categories. For FFIs: formalize `plus` as having modes `{+ + - det, - + + det}`. At rule compile time, analyze groundness flow to select the appropriate mode — or suspend if no mode matches. Enables reverse-mode computation automatically.

### Tabling (XSB Prolog)

Memoize subgoal calls and answers in a trie. For CALC: a simple hash table `(ffi_name, ground_inputs_hash) → output_hash` avoids redundant BigInt operations across symexec branches. Content-addressed Store makes lookup trivial. Pure FFIs never need cache invalidation.

### Applicability to CALC

These techniques target the **R2 (Loli/Evar) approach** specifically:
- **Loli-as-freeze** is already implemented; needs auto-emit on FFI mode mismatch (~20 LOC)
- **Bounds propagation** as domain facts `domain(eigen_id, lo, hi)` with narrowing forward rules (~200 LOC)
- **Mercury modes** formalize existing implicit FFI modes into selectable data (~100 LOC)
- **FFI result cache** eliminates redundant computation across branches (~30 LOC)

The key insight: CALC's forward engine already has all the architectural primitives for CLP-style constraint handling. The loli mechanism IS `freeze`, persistent facts ARE the constraint store, forward rules ARE propagators. The gap is in the FFI layer — mode mismatch should suspend rather than fail.

## Key Insight

The single most impactful technique is **normalization at construction time** (AC-canonical forms in Store.put). This is the Maude philosophy: don't rewrite what you can normalize. When `plus(a, plus(b, c))` and `plus(c, plus(a, b))` produce the same hash, every downstream operation — matching, indexing, state dedup — benefits automatically with zero per-step cost.

The second key insight: **CALC's loli mechanism already implements CLP-style coroutining**. Making FFI mode-mismatch auto-emit lolis (instead of failing) gives deferred computation with ~20 LOC change.

## References

- Willsey et al. (2021) — *egg: Fast and Extensible Equality Saturation* ([paper](https://arxiv.org/abs/2004.03082))
- Willsey (2023) — *Practical and Flexible Equality Saturation* (PhD thesis)
- Zhang et al. (2023) — *Better Together: Unifying Datalog and Equality Saturation* ([paper](https://arxiv.org/abs/2304.04332))
- Zhang et al. (2021) — *Relational E-Matching* ([paper](https://arxiv.org/abs/2108.02290))
- Singher & Shacham (2023) — *Colored E-Graph: Equality Reasoning with Conditions* ([paper](https://arxiv.org/abs/2305.19203))
- Eker (2003) — *Associative-Commutative Rewriting on Large Terms* ([paper](https://maude.cs.illinois.edu/papers/pdf/acSlides.pdf))
- Clavel et al. (2002) — *Maude: Specification and Programming in Rewriting Logic*
- Fruhwirth (2009) — *Constraint Handling Rules*
- Boutin (1997) — *Using Reflection to Build Efficient and Certified Decision Procedures* (ring tactic via reflection)
- Nipkow, Paulson & Wenzel — *Isabelle/HOL: A Proof Assistant for Higher-Order Logic* ([tutorial](https://isabelle.in.tum.de/doc/tutorial.pdf))
- Pugh (1991) — *The Omega Test: A Fast and Practical Integer Programming Algorithm*
- Lean4 DiscrTree module — [source](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/DiscrTree.lean)
- Metatheory.jl — [Julia e-graph library](https://github.com/JuliaSymbolics/Metatheory.jl)
- Zucker (2023) — *Knuth Bendix Solver on Z3 AST* ([blog](https://www.philipzucker.com/knuth_bendix_knuck/))
- Nelson & Oppen (1979) — *Simplification by Cooperating Decision Procedures*
- Jaffar & Maher (1994) — *Constraint Logic Programming: A Survey*
- Triska — *The Finite Domain Constraint Solver of SWI-Prolog* ([paper](https://www.metalevel.at/swiclpfd.pdf))
- Mercury mode system — [reference](https://www.mercurylang.org/information/doc-latest/mercury_ref/Determinism.html)
- XSB Prolog — *Extending Prolog with Tabled Logic Programming* ([paper](https://arxiv.org/abs/1012.5123))
- Betz — *A Unified Analytical Foundation for CHR* (CHR ↔ linear logic connection)
