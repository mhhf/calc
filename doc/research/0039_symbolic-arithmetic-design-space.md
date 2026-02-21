---
title: "Symbolic Arithmetic: Design Space Comparison"
created: 2026-02-21
modified: 2026-02-21
summary: "Comparison of how five tools (hevm, halmos, K/KEVM, Rosette, Ciao) handle symbolic arithmetic: eager vs lazy simplification, own AST vs solver AST, fork vs merge."
tags: [symbolic-arithmetic, hevm, halmos, K-framework, Rosette, design-space, symbolic-execution]
category: "Symbolic Execution"
---

# Symbolic Arithmetic: Design Space Comparison

How five tools answer: "what happens when you encounter `plus(symbolic_X, 3)`?"

## Tool Summaries

### 1. hevm (Haskell, EVM)

**Representation:** GADT `Expr a` indexed by type (`EWord`, `Byte`, `Buf`, `Storage`). Arithmetic nodes: `Add`, `Sub`, `Mul`, `Div`, `SHL`, etc. Concrete values: `Lit (W256)`. Symbolic variables: `Var Text`. Path conditions: separate `Prop` type (`PEq`, `PLT`, `PAnd`, ...).

**When simplification happens:** Eagerly, at construction via *smart constructors*. `add`, `mul`, etc. use `op2` combinator that returns concrete result if all args are `Lit`, else builds symbolic node. Additional rewrites: `normArgs` canonicalizes commutative ops (smaller arg left); `Add` and `Mul` are associative-flattened. A separate `simplify :: Expr a -> Expr a` pass runs before SMT calls doing constant folding, equivalence propagation (`Var "a"` forced to `Lit 5` => replace everywhere), dead write elimination, Keccak concretization.

**Branching:** At `JUMPI` with symbolic condition, query SMT for both branches. Proceed along satisfiable branches. `--smttimeout` controls solver budget.

**Blowup prevention:** Static simplification is cheap, runs before SMT. Bounded model checking via `--max-iterations`. Memory modeled with concrete addresses only (avoids symbolic index explosion). Storage decomposition splits into logical sub-stores.

**Bottleneck:** SMT solver time dominates on complex contracts. Simple contracts: 0.1s. Complex (MakerDAO-like): 2+ minutes. Fastest of EVM tools by 10-30x due to Haskell + aggressive pre-solver simplification.

### 2. halmos (Python, EVM)

**Representation:** Z3 `BitVec(256)` objects directly. Originally wrapped *every* value as Z3 BitVec (stack, memory, everything). v0.1.0 shifted to lazy promotion: concrete buffers stay as Python `bytes`, promoted to Z3 only when mixed with symbolic values.

**When simplification happens:** Delegated to Z3. No custom expression simplifier. Z3 does internal canonicalization when terms are constructed. Optimizations are in *how* queries are encoded: explicit quantifier instantiation (quantifier-free queries), alternative const-array encoding, multi-phase queries for nonlinear arithmetic.

**Branching:** At conditional branch, query solver for feasibility of *both* branches. Only fork if both are satisfiable (lazy branching, since v0.1.0). Previously eagerly forked. Default solver timeout during exploration: 1ms (fast pruning). Bounded loop unrolling (default 2 iterations).

**Blowup prevention:** Bounded execution (loops, recursion depth). Lazy Z3 expression building. Parallel solving (`--solver-parallel`). Small per-query timeouts prune infeasible branches fast.

**Bottleneck:** Z3 solving time. Python interpreter overhead. The "every value is a Z3 object" design was a major perf issue (fixed in v0.1.0 with lazy promotion). Multi-phase queries help with nonlinear arithmetic.

### 3. KEVM / K Framework (Haskell backend)

**Representation:** K's internal term representation. Functions like `+Int` are *symbols* with rewrite rules. Concrete execution (LLVM backend): hooked builtins evaluate immediately. Symbolic execution (Haskell backend): terms stay as unevaluated function applications when arguments are symbolic.

**When simplification happens:** Rule-driven, with fine-grained control.
- `[function]` attribute: symbol evaluates eagerly wherever it appears. For concrete args, hooked builtin fires. For symbolic args, stays stuck unless a `[simplification]` rule matches.
- `[simplification]` attribute: rules that fire on symbolic terms via *matching* (not unification). Can have priority ordering. Backend applies at any time.
- `[concrete(X)]` / `[symbolic(B)]` attributes: restrict when a rule applies. E.g. `A +Int (B +Int Z) => B +Int (X +Int Z) [concrete(X,Z), symbolic(B)]` fires only when X,Z are concrete and B is symbolic.
- When no rule matches, term stays *stuck* (unevaluated). Users write *lemmas* to unstick terms.

**Branching:** Rewriting with unification produces a *disjunction of conjunctions* -- multiple possible next states. Haskell backend delegates feasibility to Z3.

**Blowup prevention:** Stuck terms don't explode -- they just don't reduce. Users manually add lemmas to control simplification depth. Priority system on simplification rules.

**Bottleneck:** Writing correct lemmas is the major usability bottleneck. Without appropriate lemmas, proofs get stuck on terms that are logically simplifiable but have no matching rule. The `bool2Word` example: without explicit `bool2Word(X) => 1 requires X [simplification]`, the prover cannot simplify compound boolean expressions.

### 4. Tamarin Prover (Haskell, security protocols)

**Representation:** Sorted term algebra. Terms are `f(m1,...,mn)` -- function symbols applied to messages. Sorts: `msg` (default), `fr` (fresh names/nonces), `pub` (public names). Built-in: pairing `<x,y>`, projection `fst`/`snd`. User-defined functions via `functions: f/arity`. Equational theories model cryptographic properties (e.g. `dec(enc(m,k),k) = m`).

**When simplification happens:** Terms are rewritten to *normal form* modulo equational theory E during constraint reduction. The finite variant property is exploited: reasoning modulo E reduces to reasoning modulo AC (associativity-commutativity) on precomputed variants. Simplification happens during constraint reduction steps, interleaved with case distinctions.

**Branching:** Constraint solving via *backward search*. Constraint system = current knowledge about trace. Two split strategies: `SplitNow` (immediate case split) and `SplitLater` (defer until equations solved). Case distinctions are one of the constraint reduction rules. Heuristics guide which reduction to apply.

**Blowup prevention:** Variant pruning (precomputation phase reduces variants). Subterm-convergent equations preferred (RHS is ground or proper subterm of LHS). Heuristics select reduction rules. `whileChanging` combinator iterates reductions to fixpoint. `ChangeIndicator` avoids redundant work.

**Bottleneck:** State space explosion from case distinctions. The constraint solving search can become intractable on complex protocols. Performance improvement is an active research area (variant restriction pruning, 2026). Maude used as external unification backend.

### 5. Rosette/Racket (Racket, general-purpose)

**Representation:** Racket structs with type metadata. Term cache (hash-consing) ensures no syntactically identical terms exist. Canonical form via term ordering (natural number based on introduction order). Commutative ops like `(+ x y)` and `(+ y x)` are identical after canonicalization. Types: `integer?`, `boolean?`, `bitvector?`, etc. mapped directly to SMT sorts.

**When simplification happens:** Eagerly at construction ("push up equivalence reasoning at Rosette level"). `(+ 1 2)` => `3`. `(+ 1 x 3)` => `(+ 4 x)`. Partial concrete evaluation is the primary strategy. Simplification happens *before* SMT encoding, not at solver time. `(if (= (+ x 4) (+ 4 x)) x 4)` reduces to `x` without solver.

**Branching:** *Symbolic unions* -- lists of `(guard, value)` pairs with mutually exclusive guards. All paths executed, results merged with auxiliary variables. Merging reduces path count but increases state complexity. Not classic forking -- more like bounded model checking with merged states.

**Blowup prevention:** Hash-consing (term cache). Eager concrete evaluation. Finitization: concrete bounds on recursion/data structure size. Canonical term ordering reduces redundant SMT encoding. `current-bitwidth` setting trades soundness for speed (bitvector theory faster than integer theory).

**Bottleneck:** Path explosion at symbolic conditionals (2^n paths for n unknowns). Union merging cost. Symbolic profiler identifies: union size, merge cases, term count, unused terms. Common fix: replace guarded recursion with unconditional recursion + conditional assignment. Expression blowup from `split-then-merge` patterns vs `iterate-and-update`.

## Comparison Matrix

| Dimension | hevm | halmos | K/KEVM | Tamarin | Rosette |
|---|---|---|---|---|---|
| **Simplification timing** | Eager (smart constructors) + pre-SMT pass | Delegated to Z3 | Rule-driven (function/simplification attrs) | During constraint reduction (fixpoint) | Eager at construction |
| **Expression repr** | Haskell GADT | Z3 BitVec AST | K term (rewrite system) | Sorted term algebra + equational theory | Racket structs + hash-consing |
| **Content-addressed?** | No (structural equality) | No (Z3 internal) | No (term structure) | No (modulo AC) | Yes (term cache) |
| **Branching strategy** | Fork + SMT feasibility | Fork + SMT feasibility (lazy since v0.1.0) | Disjunction of states via unification | Backward search + case distinction | Merge all paths (symbolic unions) |
| **Depth control** | --max-iterations | Bounded loops (default 2) | Manual lemmas | Heuristic-guided search | Finitization (concrete bounds) |
| **Where bottleneck** | SMT solver | SMT solver + Python overhead | Lemma engineering | State space from case splits | Path explosion + union merging |
| **Custom simplification** | Extensive (canonicalize, propagate, decompose) | Minimal (encoding optimizations) | User-written lemmas | Equational theory + variant computation | Partial concrete eval + canonicalization |

## Key Design Trade-offs

### Eager vs Lazy Simplification
- **Eager** (hevm, Rosette): cheaper per-step, keeps expressions small, but must be carefully designed to be confluent/terminating
- **Lazy/delegated** (halmos): simpler implementation, but solver sees larger expressions, pays at query time
- **Rule-driven** (K): most flexible (user controls what simplifies when), but requires expertise to write good lemmas

### Own AST vs Solver AST
- **Own AST** (hevm, K, Tamarin): full control over simplification, can implement domain-specific rewrites, but must maintain/traverse custom trees
- **Solver AST** (halmos): Z3 does canonicalization internally, fewer bugs in simplification, but opaque -- can't inspect/rewrite intermediate forms easily
- **Hybrid** (Rosette): own AST with hash-consing, then compile to SMT -- gets benefits of both but must maintain the translation

### Fork vs Merge at Branches
- **Fork** (hevm, halmos, K): each branch gets independent state, exponential in branch count, but each path is simple to reason about
- **Merge** (Rosette): polynomial bound on state count, but merged states are complex symbolic unions that stress the solver differently
- **Backward/constraint** (Tamarin): doesn't execute forward -- searches backward from goal, avoids some explosion but has its own combinatorial issues

### Expression Blowup Mitigation
- **Structural**: canonicalization + hash-consing (Rosette), smart constructors (hevm)
- **Semantic**: equivalence propagation (hevm), partial eval (Rosette), variant pruning (Tamarin)
- **Bounding**: loop bounds (halmos), max iterations (hevm), finitization (Rosette)
- **Manual**: user lemmas (K) -- most powerful but highest effort

## Relevance to CALC

CALC's situation: forward multiset rewriting with content-addressed terms. When `plus(X, 3)` appears and X is symbolic:

1. **Current CALC approach**: FFI proves `plus` via backward chaining. If X is symbolic, backward proving fails (no ground result). The rule with `plus` as persistent antecedent simply doesn't fire.

2. **What other tools do**: They would keep `plus(X, 3)` as a symbolic term and propagate it. The question is *when* and *how* to simplify.

3. **Closest analogy**: Tamarin (multiset rewriting + backward constraint solving) and K (rewrite rules with controlled simplification). Both let symbolic terms exist in state and reduce them when rules match.

4. **Design options for CALC**:
   - **Symbolic terms in state**: let `plus(X, 3)` exist as a fact, fire rules that pattern-match on it
   - **Smart constructors**: when creating `plus(Lit(2), Lit(3))`, immediately reduce to `Lit(5)`; when creating `plus(Var(X), Lit(3))`, keep symbolic
   - **Constraint accumulation**: accumulate `Y = plus(X, 3)` as a constraint, solve at branch points
   - **Content-addressed symbolic terms**: hash `plus(X, 3)` like any other term -- CALC already does this for ground terms

## Theory-Informed Approaches

Beyond EVM-specific tools, proof theory and term rewriting literature offer techniques that directly address expression simplification. See `doc/research/expression-simplification.md` for the full survey; key highlights:

### AC-Normalization (Maude philosophy)

**Highest-impact single technique.** Declare `plus`/`mul` as associative-commutative operators. At term construction time, flatten and sort children canonically:
- `plus(plus(a,b), c)` → flattened sorted `[a, b, c]` under `plus`
- Constant folding: `plus(3, x, 5)` → `plus(8, x)`
- Content-addressing then makes `plus(a,plus(b,c))` and `plus(c,plus(a,b))` hash-identical

This is "normalize at construction time" — zero per-step cost, benefits all downstream operations.

### E-Graphs / Equality Saturation (egg, egglog)

Represent **all equivalent forms** simultaneously via union-find + hashcons. Store is already half an e-graph (content-addressed dedup). Missing half: equivalence classes. Colored e-graphs (Singher & Shacham 2023) add context-sensitive equalities for branching — each JUMPI branch gets a "color."

Tension with linear logic: e-graphs are monotonic, ILL consumes facts. Need scoped/colored variant.

### CHR Compilation Techniques

CHR simpagation IS ILL forward rules. 25+ years of compilation research applies:
- **Join ordering**: match most selective antecedent first (not left-to-right)
- **Guard scheduling**: evaluate cheap FFI guards (neq, lt) before expensive pattern matches
- **Propagation history**: prevent redundant firings (already have `pathVisited`)

### Isabelle-style Simplifier

Bottom-up rewriting with simpset + simprocs + congruence rules. CALC's forward engine has the pieces (rules = simpset, FFI = simprocs). Missing: congruence rules for context propagation (if `A = 5`, simplify `plus(A, 3)` to `8`).

### CLP Attributed Variables

Variables carry attached constraints, checked on unification. Maps to the loli/eigenvariable approach: evars could carry domain constraints (interval bounds, modular arithmetic properties). Constraint propagation fires when evars become bound.

### Polynomial Normalization (Horner form)

Canonical representation for polynomial expressions: `f(x) = c + x * g(x)`. Two polynomials are equal iff their Horner forms are syntactically identical. Relevant for complex multi-variable arithmetic in k-dss (37 variables in `frob`).
