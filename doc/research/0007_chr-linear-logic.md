---
title: "CHR and Linear Logic: A Survey"
created: 2026-02-20
modified: 2026-02-20
summary: Comprehensive survey of Constraint Handling Rules (CHR), CHR∨, their linear logic semantics, compilation, analysis, and extensions. Focus on the Betz/Frühwirth soundness/completeness results connecting CHR to ILL.
tags: [chr, linear-logic, forward-chaining, multiset-rewriting, compilation, confluence, CHRv]
category: "Performance"
---

# CHR and Linear Logic: A Survey

## 1. CHR Fundamentals

### 1.1 Rule Types

CHR (Frühwirth, 1991) has three rule types over a constraint store (multiset):

```
Simplification:   r @ H₁,...,Hₙ  ⟺  G | B₁,...,Bₘ
Propagation:      r @ H₁,...,Hₙ  ⟹  G | B₁,...,Bₘ
Simpagation:      r @ H₁,...,Hₗ \ Hₗ₊₁,...,Hₙ  ⟺  G | B₁,...,Bₘ
```

- **Simplification**: match heads, check guard G, **remove** all matched heads, add body.
- **Propagation**: match heads, check guard, **keep** all heads, add body.
- **Simpagation**: match heads, check guard, **keep** H₁..Hₗ (before `\`), **remove** Hₗ₊₁..Hₙ (after `\`), add body.

Simpagation subsumes both: simplification has empty kept head, propagation has empty removed head.

Guards G are built-in constraints (equality, arithmetic) that must hold for the rule to fire. Body constraints can be user-defined (added to store) or built-in.

### 1.2 Abstract Operational Semantics (omega_t)

The theoretical semantics omega_t (Frühwirth, 1998) defines states as tuples `<G, S, B, T>_n`:

| Component | Meaning |
|---|---|
| G | Goal (multiset of constraints to process) |
| S | CHR constraint store (user-defined) |
| B | Built-in constraint store |
| T | Propagation history (set of fired propagation rule instances) |
| n | Next free constraint identifier |

**Transition rules:**

1. **Solve**: Move a built-in constraint from G to B. `<{c} ++ G, S, B, T>_n --> <G, S, c /\ B, T>_n`

2. **Introduce**: Move a user-defined constraint from G to S, assigning it identifier n. `<{c} ++ G, S, B, T>_n --> <G, {c#n} ++ S, B, T>_{n+1}`

3. **Apply**: For a rule `r @ H₁ \ H₂ ⟺ G | B` and matching constraints in S with substitution theta: if guard holds under B, and the rule instance is not in T (for propagation), fire the rule. Remove H₂theta from S, add body to G, record in T.

omega_t is highly nondeterministic: it does not fix rule order, constraint order, or matching order. Programs must be **confluent** for deterministic results under omega_t.

### 1.3 Refined Operational Semantics (omega_r)

Duck, Stuckey, Garcia de la Banda, Holzbaur (ICLP 2004) formalized omega_r, the semantics actually implemented in CHR systems.

**Key differences from omega_t:**

- **Execution stack**: G becomes an ordered stack A, not a multiset. Constraints processed left-to-right.
- **Active constraint**: The topmost user-defined constraint on A becomes "active" and tries rules in textual order.
- **Occurrence numbering**: Each head occurrence of a constraint in the program is numbered. The active constraint `c#i:j` tracks which occurrence j to try next.
- **Deterministic rule selection**: Rules tried in program-text order for each active constraint.

**Transition rules of omega_r:**

1. **Solve**: Built-in constraint on top of A: add to B, possibly wake suspended constraints.
2. **Activate**: User-defined constraint on top of A: assign ID, push as `c#n:1` (start at occurrence 1).
3. **Reactivate**: Woken constraint: push as `c#i:1` (restart from occurrence 1).
4. **Drop**: Active constraint `c#i:j` with no more occurrences: pop from A.
5. **Simplify**: Active constraint matches occurrence j of a simplification/simpagation rule (as removed head): fire rule, remove constraint, push body onto A.
6. **Propagate**: Active constraint matches occurrence j of a propagation rule (as kept head): fire rule (if not in history T), push body onto A, increment occurrence to j+1.
7. **Default**: Active constraint cannot match occurrence j: increment to j+1.

**Correctness**: omega_r implements omega_t -- every omega_r derivation corresponds to an omega_t derivation.

### 1.4 Propagation History

Propagation rules keep their heads -- without guarding against re-firing, they trivially loop. The propagation history T records `(rule_name, {id₁,...,idₙ})` tuples for each fired propagation instance. A propagation rule fires only if the specific combination of matched constraint IDs is not already in T.

This is the CHR analog of our engine's loli continuation mechanism: a loli `A ⊸ B` in the state is a one-shot rule (it self-deletes). CHR propagation rules are persistent but use the history to prevent refiring.

## 2. CHR <-> Linear Logic (Betz & Frühwirth)

### 2.1 The Translation (CP 2005)

Betz and Frühwirth, "A Linear-Logic Semantics for Constraint Handling Rules" (CP 2005, LNCS 3709, pp. 137-151).

**Core insight**: The difference between built-in and user-defined constraints in CHR mirrors the difference between banged (`!A`) and linear atoms in ILL. Simplification rule application resembles modus ponens in linear logic.

**Translation function** `(-)^L`:

- User-defined constraint `c(t)` --> `c(t)` (linear atom)
- Built-in constraint `b(t)` --> `!b(t)` (banged/persistent)
- Conjunction of constraints `C₁ /\ C₂` --> `C₁^L ⊗ C₂^L` (tensor)
- True --> `1` (unit of tensor)

**Rule translation** (Definition 4.4 in TOCL 2013 version):

For simpagation rule `r @ H₁ \ H₂ ⟺ G | B_b /\ B_u`:

```
H₁^L ⊗ H₂^L ⊗ G^L  ⊢  H₁^L ⊗ ∃ȳ.(B_b^L ⊗ B_u^L ⊗ G^L)
```

Equivalently as a linear implication (proper axiom):

```
∀x̄. (H₁^L ⊗ H₂^L ⊗ G^L ⊸ H₁^L ⊗ ∃ȳ.(B_b^L ⊗ B_u^L ⊗ G^L))
```

Where:
- H₁^L = kept head (appears on both sides -- preserved)
- H₂^L = removed head (consumed on left, absent on right)
- G^L = guard (banged, so present on both sides via contraction)
- B_u^L = user-defined body (produced)
- B_b^L = built-in body (banged)
- ∃ȳ = existential over local variables in the body

**Special cases:**
- **Simplification** (H₁ empty): `H₂^L ⊗ G^L ⊸ ∃ȳ.(B^L ⊗ G^L)` -- pure consumption
- **Propagation** (H₂ empty): `H₁^L ⊗ G^L ⊸ H₁^L ⊗ ∃ȳ.(B^L ⊗ G^L)` -- no consumption

**State translation**: A CHR state `<G, S, B, T>` translates to the linear logic context containing all constraints translated via `(-)^L`.

### 2.2 Soundness and Completeness (TOCL 2013)

Betz and Frühwirth, "Linear-Logic Based Analysis of Constraint Handling Rules with Disjunction" (ACM TOCL, 14(1), 2013).

**Theorem 4.8 (Soundness)**: Let P be a program, CT a constraint theory, Sigma = Sigma_P union Sigma_CT union Sigma_=. For arbitrary states S, T:

```
S |->* T  implies  S^L ⊢_Sigma T^L
```

Every operational derivation (sequence of state transitions) corresponds to a valid deduction in the linear logic theory.

**State entailment** (Definition 4.9): S entails S' (written `S ⊳ S'`) iff `S^L ⊢_Sigma S'^L`.

**Theorem 4.10 (Decidable state entailment)**: State entailment is decidable and characterized by:

```
[S] ⊳ [S'] iff CT |= forall(B -> exists l'((U = U') /\ B'))
```

where B, B' are the built-in stores and U, U' are the user-defined stores.

**Corollary 4.11 (State equivalence)**: `S ≡_e T` iff both `S ⊳ T` and `T ⊳ S`.

The completeness story is more nuanced than soundness. Full completeness (every linear logic derivation corresponds to an operational derivation) does not hold in general because:
1. Linear logic allows arbitrary resource shuffling that doesn't correspond to rule application
2. The propagation history restricts operational derivations beyond what logic captures

Completeness holds for specific program classes (e.g., range-restricted programs) and relative to specific equivalence notions.

### 2.3 Phase Semantics Verification

Betz, "Verification of Constraint Handling Rules using Linear Logic Phase Semantics" (Ulm University).

Uses Girard's phase semantics (a denotational semantics for linear logic based on commutative monoids) to verify CHR program properties. Phase semantics provides an alternative to proof-theoretic reasoning: a formula is valid iff it holds in all phase models. This enables model-theoretic verification of CHR programs through their linear logic translation.

### 2.4 Proof-Theoretical Semantics (Stéphan, ICLP 2018)

Stéphan, "A New Proof-Theoretical Linear Semantics for CHR" (ICLP 2018, OASIcs, pp. 4:1-4:17).

Instead of translating CHR states to ILL formulas and showing entailment (Betz), Stéphan defines two sequent calculus systems where CHR derivations **are** proof trees.

**Motivation — four hidden nondeterminism sources in CHR:**
1. Don't-care rule selection (committed choice) — inherent, by design
2. Don't-know disjunction (CHR∨) — deliberate
3. Constraint store ordering (unordered multiset → wake-up order unspecified)
4. Multi-headed matching (which constraints from multiset are chosen/kept)

None of the prior semantics (ω_t, ω_r, Betz's translation, axiomatic semantics) resolve sources 3+4. Stéphan's ω_l^⊗ system eliminates them.

**Two sequent calculus systems:**

**ω_l system** (store as multi-set):
- Two kinds of sequents:
  - Non-focused: `(Γ ▸ Ω_# ◁ S_↑ ⊢ S_↓)` — process goal Ω_# using program Γ, consuming from up-store S_↑, producing down-store S_↓
  - Focused: `(Γ ! Δ ▷ a ◁ S_↑ ⊢ S_↓)` — focused on identified constraint a, trying rules Δ
- Inference rules: true (axiom), ⊗_L (split goal), W (skip rule), F (focus on constraint), ↑ (inactivate/store), \⟺ (apply simpagation)
- **Theorem 7**: Sound AND complete w.r.t. ω_t

**ω_l^⊗ system** (store as sequence):
- Adds Exchange rule (X) for permuting identified constraints
- Completely deterministic — eliminates nondeterminism sources 3+4
- **Theorem 8**: Sound (but not complete) w.r.t. ω_t

**Hidden Cut insight:** The ⊗_L (left-elimination-of-conjunction) rule is actually a hidden use of the cut rule in linear logic. It splits resources between a "lemma" (left subproof — solve one constraint) and its "use" (right subproof — solve the rest). Both operational semantics eliminate cut instances to linearize derivations. The Apply rule also uses cut when kept-head resources (S^K) haven't been fully consumed.

**Translation to linear logic (Definition 10):**

Simpagation rule (K\D ⟺ B₁,...,B_p) translates to:
```
∀x̄∃ȳ(K₁(x₁)⊗...⊗K_m(x_m)⊗D₁(x_{m+1})⊗...⊗D_n(x_{m+n}) ⊸ K₁(x₁)⊗...⊗K_m(x_m)⊗B₁(y₁)⊗...⊗B_p(y_p))
```

**Crucial difference from Betz:** In Stéphan, the program comma "," between rules translates to **& (additive conjunction)**, not ⊗ or bang. Rule selection = &L₁ or &L₂ (committed choice between rules via additive elimination). In Betz, the program is a conjunction of banged implications `!(K⊗D ⊸ K⊗B)`.

This means:
- **Betz**: program = `!r₁ ⊗ !r₂ ⊗ ... ⊗ !rₙ` (all rules always available, via dereliction)
- **Stéphan**: program = `r₁ & r₂ & ... & rₙ` (choose one rule = additive left rule)

The & translation elegantly captures committed choice: picking a rule is an additive choice, and the unchosen rules remain available (via Weakening) for future steps. This is more proof-theoretically natural than Betz's bang-based encoding.

**Translation of sequents (Definition 12):** The goal becomes a tensor product (inducing sequence structure), the up-store becomes a set of tokens, and the down-store becomes a tensor of tokens. The full translation L(.) maps each ω_l inference rule to a derivable linear-logic proof fragment:
- true → 1L + !W
- ⊗_L → ⊗L + Cut
- W → &L₂
- F → !D + !C
- ↑ → !W (for inactivate axiom)
- \⟺ → ⊸L + ∃L + ∀L

**Theorems 14, 15**: The translation of any ω_l (resp. ω_l^⊗) proof is a valid linear proof. This establishes the soundness of the sequent calculus w.r.t. linear logic.

**Focusing connection (Section 4 Discussion):** Stéphan notes that the two phases of ω_l^⊗ (non-focused / focused) resemble Andreoli's focusing (asynchronous / synchronous), but they are NOT the same: ω_l^⊗ phases are about constraint activation order, while focusing is about connective polarity. Stéphan suggests translating ω_l proofs into focusing proofs as future work, which would "understand the semantics of CHR in terms of synchronous and asynchronous connectors."

### 2.5 Quantified CHR (Stéphan & Barichard, TOCL 2025)

Barichard and Stéphan, "Quantified Constraint Handling Rules" (ACM TOCL 26(3), 2025, pp. 1-46).

Extends CHR with quantified rules, building on the ω_l sequent calculus from ICLP 2018.

**New rule types:**
- Existential simpagation: body succeeds if ∃ value in [low,up] makes it succeed
- Universal simpagation: body succeeds if ∀ values in [low,up] make it succeed
- Subsumes existential/universal simplification and propagation

**Key innovation — dynamic binder:** Quantifiers generated during execution, not declared statically (unlike QCSP/QCSP+ which require a fixed alternation of quantifiers). This allows modeling games where the number of moves is unknown a priori.

**Proof-theoretical semantics ω_l^{∃∀}:** Extends ω_l with four new inference rules and one axiom:
- ∃-Apply / ∀-Apply: apply quantified simpagation to focused constraint
- ∃-elimination: finds at least one value in interval making goal succeed
- ∀-elimination: proves goal succeeds for all values in interval
- ∀-true: terminal axiom for universal quantifier

**Theorem 5.1**: Operational semantics ω_r^{∃∀} is sound and complete w.r.t. ω_l^{∃∀}.

**Game-tree semantics:**
- ∃ = player A (can choose strategy) → like ⊕ (internal choice)
- ∀ = player B (adversary, tries all moves) → like & (external choice) or exhaustive exploration
- Execution tree = game tree with ∃/∀ branching at quantified rule applications
- Tabling/memoization: store previously explored states, avoid re-computation

**Performance:** QCHR++ (C++ implementation) outperforms QuaCode (QCSP solver) by 30-100x on game benchmarks (Nim, Connect-Four, Checkers). Tabling gives additional 100x on games with repeated states.

**Relevance to CALC:** See Section 10.3 below.

### 2.6 Betz PhD Thesis (2014)

Betz, "A Unified Analytical Foundation for Constraint Handling Rules" (PhD thesis, Ulm University, 2014).

Unifies the various linear logic semantics for CHR into a single framework. Grounds CHR on intuitionistic linear logic, showing ILL is substantially better-suited than classical logic to express CHR's operational behavior. Covers:
- The CP 2005 translation
- The TOCL 2013 extension to CHR-v
- Phase semantics verification
- Transaction logic semantics (Betz & Frühwirth, 2007)

## 3. CHR-v (CHR with Disjunction)

### 3.1 Definition

Abdennadher and Schütz (1998) introduced CHR-v, extending CHR rule bodies with disjunction:

```
r @ H₁ \ H₂ ⟺ G | (B₁ ; B₂ ; ... ; Bₖ)
```

The semicolon `;` is disjunction in the body: the rule nondeterministically produces one of the B_i alternatives. This adds **don't-know nondeterminism** (backtracking search) to CHR's inherent **don't-care nondeterminism** (committed choice in rule selection).

### 3.2 Operational Semantics (omega_e)

CHR-v uses the equivalence-based semantics omega_e, extended with a disjunction transition:

**Disjunction**: `<(B₁ ; B₂) ++ G, S, B, T>_n --> <B_i ++ G, S, B, T>_n` for i in {1,2}

The disjunction creates a **choice point**: execution can proceed with either branch. For exhaustive analysis, both branches must be explored (search tree).

### 3.3 Linear Logic Translation of Disjunction

The key result from Betz & Frühwirth (TOCL 2013): disjunctive bodies map to **additive disjunction** (oplus) in ILL:

```
(B₁ ; B₂)^L = B₁^L ⊕ B₂^L
```

For a CHR-v rule `r @ H₁ \ H₂ ⟺ G | (B₁ ; B₂)`:

```
∀x̄. (H₁^L ⊗ H₂^L ⊗ G^L ⊸ H₁^L ⊗ (∃ȳ₁.B₁^L ⊕ ∃ȳ₂.B₂^L) ⊗ G^L)
```

The oplus (internal choice) is the correct connective because the *system* decides which branch to take (based on guards, constraint values, etc.), not the consumer. This matches our engine's use of oplus for EVM comparison branching (eq, iszero, jumpi).

**Soundness extends to CHR-v**: operational derivations in CHR-v correspond to linear logic proofs with oplus.

### 3.4 Connection to CALC's Forward Engine

Our engine already implements the CHR-v pattern:
- Forward rules with `⊕` in consequents = CHR-v disjunctive bodies
- `expandItem` treats `plus` by forking = CHR-v disjunction transition
- Execution tree exploration = CHR-v search tree over choice points
- Committed choice for rule selection + don't-know for disjunction = CHR-v semantics

## 4. CHR Compilation

### 4.1 Basic Compilation Scheme

Holzbaur and Frühwirth, "Compiling Constraint Handling Rules into Prolog with Attributed Variables" (PPDP 1999).

CHR rules compile to host-language (Prolog) code via:

1. **Per-constraint procedure**: Each user-defined constraint `c/n` gets a procedure. When `c(...)` is added, its procedure is called.
2. **Occurrence iteration**: The procedure iterates over all occurrences of `c` in rule heads (in program order).
3. **Partner search**: For each occurrence, search the constraint store for matching partner constraints (the other heads).
4. **Guard check**: If partners found, check the guard.
5. **Rule firing**: Remove constraints (simplification/simpagation), add body constraints.

### 4.2 Occurrence Indexing

Sneyers, Schrijvers, Demoen, "Guard and Continuation Optimization for Occurrence Representations of CHR" (ICLP 2005).

Each head in each rule is an **occurrence**. A constraint `c` appearing in 5 rule heads has 5 occurrences. The compiled code for `c` tries each occurrence in order. If one succeeds (rule fires), the constraint may be consumed (simplification) or continue to the next occurrence (propagation).

**Continuation optimization**: If a constraint is in the removed head of a rule that fires, no further occurrences need be tried. If it's in the kept head, jump to the next occurrence.

### 4.3 Join Ordering

Duck, Stuckey, Garcia de la Banda, "Optimizing Compilation of Constraint Handling Rules in HAL" (TPLP 2004).

Multi-headed rules require **joining** multiple constraints. The order in which partner constraints are searched matters for performance:

- **Functional dependencies**: If constraint `c(X,Y)` has FD `X -> Y`, index by X first.
- **Guard scheduling**: Interleave guard tests with partner search -- test guards early to prune.
- **Cost model**: Estimate join cost based on constraint store sizes and selectivity.

### 4.4 Constraint Indexing

Schrijvers (2005) introduced hash-table indexing for the constraint store. Sneyers, Schrijvers et al. (2006) added array-based indexes for correct complexity guarantees. The index structure depends on:

- Which argument positions are bound (mode analysis)
- Which arguments appear in guards (guard analysis)
- Functional dependencies between arguments

### 4.5 Key Implementations

| System | Host | Authors | Notes |
|---|---|---|---|
| SWI-Prolog CHR | Prolog | Holzbaur, Schrijvers | K.U.Leuven system, attributed variables |
| JCHR | Java | Van Weert, Schrijvers | Imperative compilation |
| CCHR | C | Wuille, Schrijvers | Low-level, efficient |
| HaskellCHR | Haskell | Stuckey, Sulzmann | Type-level CHR |
| CHR.js | JavaScript | -- | Browser-based |

## 5. CHR and Forward Chaining

### 5.1 Relationship to Rete/TREAT

CHR's execution model is a forward-chaining production system. Connections:

- **Rete** (Forgy, 1982): Shares partial matches across rules via a network of alpha/beta nodes. CHR does NOT use Rete -- it uses per-constraint occurrence iteration instead.
- **TREAT** (Miranker, 1987): No persistent beta-memories; recomputes joins. Closer to CHR's approach.
- **LEAPS** (Miranker et al., 1990): Lazy evaluation of joins. CHR's refined semantics (active constraint tries rules lazily) is similar.

CHR's key difference: **multi-headed rules** with **constraint removal**. Rete/TREAT were designed for assertion-only systems. CHR's simpagation (partial removal) has no direct Rete analog.

### 5.2 Non-Monotonicity of Constraint Removal

Classical forward chaining (Datalog) is monotonic: the database only grows. CHR's simplification rules remove constraints, making it non-monotonic. This means:
- Standard semi-naive evaluation does not directly apply
- No fixpoint guarantee (the store can shrink)
- Termination must be proved separately

### 5.3 Logical Algorithms (Ganzinger & McAllester)

Ganzinger and McAllester (2002) defined a forward-chaining language with a cost semantics for complexity analysis. Key result: LA programs can be compiled into CHR with rule priorities (CHRrp).

Sneyers, Schrijvers, Demoen, "The Correspondence Between the Logical Algorithms Language and CHR" (ICLP 2007): establishes a formal translation from LA to CHR, enabling McAllester's prefix firing cost semantics to apply to CHR.

Simmons and Pfenning, "Linear Logical Algorithms" (ICALP 2008): extends Ganzinger-McAllester to **linear logic**, enabling cost analysis for algorithms with resource consumption. Directly relevant to our engine: forward-chaining algorithms expressed in ILL with formal complexity bounds.

## 6. CHRiSM (Probabilistic CHR)

Sneyers, "CHR(PRISM)-based Probabilistic Logic Learning" (TPLP, 2010).

**CHRiSM** = Chance Rules induce Statistical Models. Combines CHR with PRISM (probabilistic Prolog):

```
r @ H₁ \ H₂ ⟺ G | B₁ ?? p₁ ; B₂ ?? p₂ ; ... ; Bₖ ?? pₖ
```

Each alternative body B_i has probability p_i. Probabilities can be expressions over head variables (dynamic). The actual firing probability is p_i normalized over all fireable rule instances.

**Operational semantics**: Like CHR-v but with weighted disjunction. Choice points carry probability distributions.

**Ambiguity**: A CHRiSM program is **unambiguous** if the probability of reaching any final state is independent of the order of rule application. Unambiguous programs have well-defined distribution semantics.

**Relation to our engine**: If we ever need probabilistic symbolic execution (e.g., modeling transaction probabilities), CHRiSM provides the theory for weighted branching in forward-chaining multiset rewriting.

## 7. Adaptive CHR and Rule Priorities

### 7.1 CHRrp (Rule Priorities)

De Koninck, Schrijvers, Demoen, "User-Definable Rule Priorities for CHR" (PPDP 2007).

Extends CHR with a priority annotation per rule:

```
r @ priority :: H₁ \ H₂ ⟺ G | B
```

Priority can be a number or an arithmetic expression over head variables (dynamic). Rules fire in priority order: higher-priority rules always fire before lower-priority ones.

**Refined priority semantics** omega_rp: combines omega_r (occurrence ordering) with priority ordering. Proved to be an instance of omega_t.

**Meta-complexity**: Sneyers, Schrijvers, Demoen (2009) showed that the meta-complexity theorem of Ganzinger-McAllester applies to CHRrp via the LA-to-CHRrp translation. This means: if the derivation DAG has size D, the CHRrp program runs in O(D) time.

### 7.2 Adaptive Constraint Handling

Wolf, "Intelligent Search Strategies Based on Adaptive Constraint Handling Rules" (TPLP, 2005).

Combines CHR with intelligent search strategies for CSP solving:
- Conflict-directed backjumping
- Dynamic backtracking
- Adaptive variable/value ordering

The CHR constraint store provides a natural interface for search strategy adaptation: strategies are themselves constraints that can be added, removed, and propagated.

### 7.3 Adaptive CHR meets CHR-v

Wolf et al. (2008) combine adaptive search with CHR-v disjunction, enabling runtime adaptation of search strategy within disjunctive CHR programs. Backtracking over disjunctive choices uses adaptive heuristics to select which branch to explore first.

## 8. CHR Analysis Techniques

### 8.1 Confluence

A CHR program is **confluent** if for every state, all derivations lead to equivalent final states (result is independent of rule application order).

**Abdennadher, Frühwirth, Meuss** (CP 1996): For terminating programs, confluence is decidable via **critical pair analysis**. Two rules overlap if they share a head constraint. The **critical pair** is the pair of states reachable by applying either rule. If all critical pairs are joinable (reach the same final state), the program is confluent.

**Observable confluence** (Duck, Stuckey, Sulzmann, 2007): Weaker notion where only observable outputs need to agree, not internal store structure. Many practical programs are observably confluent but not confluent under the strict definition.

**Confluence modulo equivalence** (Christiansen, Hanne, 2019): Only requires final states to be equivalent under a program-specific equivalence relation.

### 8.2 Termination

Two main approaches:

1. **Frühwirth (2000)**: Ranking function on states. Proves termination for programs **without propagation**. Defines a norm on terms and level mapping on constraints. If every rule application decreases the ranking, the program terminates.

2. **Voets, Pilozzi, De Schreye**: Handles programs **with propagation**. Introduces the **propagation store** concept: the set of constraints that could be added by only propagating on the current state. Lexicographic ordering over (propagation store, constraint store, token store) provides the termination measure.

**Pilozzi, Schrijvers (2008)**: Transformational approach -- translate CHR to Prolog, then use Prolog termination analysis tools.

### 8.3 Operational Equivalence

Abdennadher and Frühwirth: Two terminating, confluent CHR programs are operationally equivalent iff for every input, they produce the same final store. Decidable for terminating, confluent programs via critical pair analysis.

### 8.4 Analysis Tools

- **Confluence checker** (Langbein, Raiser, Frühwirth, 2010): Automated tool for testing CHR confluence, based on critical pair enumeration and joinability testing.
- **State equivalence checker** (same authors): First tool for testing equivalence of CHR states, based on the linear logic state entailment characterization.
- **Termination analyzer** (Voets et al.): Prototype analyzer using the propagation store measure.

## 9. Key Theorems Summary

| Theorem | Paper | Statement |
|---|---|---|
| omega_r correctness | Duck et al. 2004 | omega_r implements omega_t (every omega_r derivation is an omega_t derivation) |
| Soundness | Betz & Frühwirth 2005/2013 | S \|->* T implies S^L ⊢_Sigma T^L |
| State entailment decidability | Betz & Frühwirth 2013 | [S] ⊳ [S'] is decidable via constraint theory |
| State equivalence | Betz & Frühwirth 2013 | S ≡_e T iff S ⊳ T and T ⊳ S |
| Confluence decidability | Abdennadher et al. 1996 | Confluence of terminating CHR programs is decidable via critical pairs |
| LA-CHRrp translation | Sneyers et al. 2007/2009 | LA programs translate to CHRrp preserving complexity |
| CHRiSM distribution | Sneyers 2010 | Unambiguous CHRiSM programs have well-defined distribution semantics |

## 10. Relevance to CALC's Forward Engine

### 10.1 What CALC Already Has (as CHR)

| CALC Concept | CHR Equivalent |
|---|---|
| Linear facts | User-defined constraints (removed heads) |
| Persistent facts (!A) | Built-in constraints / kept heads |
| Forward rules | Simpagation rules |
| Backward proving / FFI | Guard evaluation |
| oplus (⊕) in consequents | CHR-v disjunctive bodies |
| Execution tree exploration | CHR-v search tree |
| Strategy stack (opcode index) | Constraint indexing |
| Disc-tree | Specialized join index |

### 10.2 CALC ↔ Stéphan's ω_l System

Stéphan's proof-theoretical approach is arguably more natural for CALC than Betz's translation:

| Stéphan's ω_l concept | CALC equivalent |
|---|---|
| Non-focused sequent (process goal) | `findAllMatches` / `run` loop |
| Focused sequent (try rules on a constraint) | Strategy stack evaluation for one fact |
| ⊗_L (split goal into head + tail) | `expandItem` decomposing tensor/plus |
| W (Weakening — skip a rule) | Rule doesn't match, try next |
| F (Focusing — select constraint) | `matchFirstLoli` / `findMatch` picks a fact |
| ↑ (Inactivate — store unchanged) | Fact stays in state (no rule fires on it) |
| \⟺ (Apply — fire rule) | `applyMatch` / `mutateState` |
| & between rules (committed choice) | `findMatch` returns first successful rule |
| ω_l^⊗ (sequence store) | CALC's linear array ordering in `state.linear` |
| Hidden Cut in ⊗_L | `expandItem` splitting resources between subgoals |

**Program as & (not ⊗ or !):** Stéphan's translation of the program as additive conjunction directly models CALC's committed-choice rule selection in `run()`. The strategy stack's first-match-wins behavior is exactly &L₁ vs &L₂: try rule 1, if it doesn't apply, try rule 2.

**ω_l^⊗ = deterministic CALC:** The ω_l^⊗ system (store as sequence, Exchange rule for reordering) corresponds to CALC's `run()` in committed-choice mode. The sequence ordering eliminates the multiset nondeterminism — exactly what CALC's array-indexed state provides.

### 10.3 CALC ↔ QCHR

| QCHR concept | CALC equivalent |
|---|---|
| Existential branching (∃ — one value suffices) | ⊕ in consequent (some branch will be taken) |
| Universal branching (∀ — all values must work) | Symexec exhaustive exploration (all branches explored) |
| Dynamic binder (quantifiers generated at runtime) | Loli continuations (rules produced at runtime) |
| Game tree (∃/∀ alternation) | Execution tree (branch/fork nodes) |
| Tabling/memoization | `pathVisited` cycle detection + state hashing |
| QCHR++ solver | `symexec.js` explore() |

**Key insight:** CALC's symexec is conceptually a QCHR solver where all branching is universal (∀ — explore everything). When CALC adds constraint simplification (TODO_0002), some branches may become provably infeasible, turning universal branching into existential (only feasible branches survive). This is exactly QCHR's model: ∃ for "system decides" choices, ∀ for "must handle all cases" choices.

**Quantifiers for CALC's Q1:** QCHR's ∃/∀ rules provide the machinery CALC needs for explicit existential quantification in the monad (Q1 in `exhaustive-forward-chaining.md`). Fresh symbolic values = existentially quantified constraints. The ω_l^{∃∀} system gives a ready-made proof framework.

### 10.4 What CALC Could Gain from CHR Theory

1. **Formal soundness**: The Betz/Frühwirth translation provides a ready-made proof that our forward engine is sound w.r.t. ILL. The translation is nearly identical to what we already do.

2. **Confluence analysis**: For programs where rule application order shouldn't matter (many EVM opcodes are independent), CHR confluence analysis could verify this formally.

3. **Compilation techniques**: Occurrence indexing and join ordering could improve rule matching. Our disc-tree already handles predicate indexing; CHR's guard scheduling could optimize the backward-proving integration.

4. **Priority scheduling**: CHRrp's dynamic priorities could replace our current fixed strategy stack ordering, enabling e.g., gas-aware opcode scheduling in EVM execution.

5. **Propagation history**: CHR's propagation history mechanism is more general than our loli continuation model. For rules that should fire persistently but not re-fire on the same inputs, the history mechanism provides the correct semantics.

## References

### Core CHR
- Frühwirth, T. (1998). "Theory and Practice of Constraint Handling Rules." *J. Logic Programming*, 37(1-3):95-138.
- Frühwirth, T. (2009). *Constraint Handling Rules*. Cambridge University Press.
- Duck, G.J., Stuckey, P.J., Garcia de la Banda, M., Holzbaur, C. (2004). "The Refined Operational Semantics of Constraint Handling Rules." *ICLP 2004*, LNCS 3132.
- Sneyers, J., Van Weert, P., Schrijvers, T., De Koninck, L. (2010). "As Time Goes By: Constraint Handling Rules -- A Survey of CHR Research 1998-2007." *TPLP*, 10(1):1-47.

### Linear Logic Semantics
- Betz, H. and Frühwirth, T. (2005). "A Linear-Logic Semantics for Constraint Handling Rules." *CP 2005*, LNCS 3709, pp. 137-151.
- Betz, H. and Frühwirth, T. (2013). "Linear-Logic Based Analysis of Constraint Handling Rules with Disjunction." *ACM TOCL*, 14(1).
- Betz, H. (2014). *A Unified Analytical Foundation for Constraint Handling Rules*. PhD thesis, Ulm University.
- Betz, H. "Verification of CHR Using Linear Logic Phase Semantics." Ulm University.
- Stéphan, I. (2018). "A New Proof-Theoretical Linear Semantics for CHR." *ICLP 2018*, OASIcs, pp. 4:1-4:17.
- Barichard, V. and Stéphan, I. (2025). "Quantified Constraint Handling Rules." *ACM TOCL*, 26(3), pp. 1-46.

### Compilation
- Holzbaur, C. and Frühwirth, T. (1999). "Compiling CHR into Prolog with Attributed Variables." *PPDP 1999*.
- Duck, G.J. et al. (2004). "Optimizing Compilation of CHR in HAL." *TPLP*, 4(5-6).
- Sneyers, J. et al. (2005). "Guard and Continuation Optimization for Occurrence Representations of CHR." *ICLP 2005*.

### Extensions
- Abdennadher, S. and Schütz, H. (1998). "CHR-v: A Flexible Query Language." *FQAS 1998*.
- De Koninck, L., Schrijvers, T., Demoen, B. (2007). "User-Definable Rule Priorities for CHR." *PPDP 2007*.
- Sneyers, J. (2010). "CHR(PRISM)-based Probabilistic Logic Learning." *TPLP*, 10(4-5).
- Wolf, A. (2005). "Intelligent Search Strategies Based on Adaptive CHR." *TPLP*, 5(4-5).

### Analysis
- Abdennadher, S., Frühwirth, T., Meuss, H. (1996). "On Confluence of CHR." *CP 1996*.
- Duck, G.J., Stuckey, P.J., Sulzmann, M. (2007). "Observable Confluence for CHR." *ICLP 2007*.
- Voets, D. et al. (2008). "Termination Analysis of CHR Revisited." *ICLP 2008*.
- Langbein, M., Raiser, F., Frühwirth, T. (2010). "A State Equivalence and Confluence Checker for CHR." *CHR Workshop 2010*.

### Forward Chaining / Complexity
- Ganzinger, H. and McAllester, D. (2002). "Logical Algorithms." *ICLP 2002*.
- Sneyers, J. et al. (2007). "The Correspondence Between LA and CHR." *ICLP 2007*.
- Simmons, R.J. and Pfenning, F. (2008). "Linear Logical Algorithms." *ICALP 2008*.
