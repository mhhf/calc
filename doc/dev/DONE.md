# DONE

Completed tasks and research for the CALC project.

---

## v1→v2 Migration ✅
**Date:** 2026-02-03

The v2 rewrite is now the primary codebase.

**UI (100% migrated):**
- All pages use v2 API via `calcV2.ts` and `proofLogicV2.ts`
- Bundle size reduced ~25% by removing v1 dependencies

**CLI (v2 is default):**
- `calc parse` → uses v2 (focused parser)
- `calc proof` → uses v2 (focused prover)
- v1 tools renamed to `calc parse-v1` and `calc proof-v1` for benchmarking

---

## MDE/Celf Implementation ✅
**Date:** 2026-02-05

Full MDE (Celf-compatible) implementation with forward/backward chaining and FFI.

### Tree-sitter Parser
- `lib/tree-sitter-mde/` — Full Celf grammar, WASM build for browser
- Handles 1000+ nesting levels (GLR algorithm)
- Deep nesting test: 0.002s

### MDE Module (`lib/mde/`)
- `convert.js` — Tree-sitter AST → content-addressed hashes
- `prove.js` — Backward chaining with indexing and FFI
- `index.js` — Unified API: load, parseExpr, prove, exec
- `hex.js` — N_XX hex notation expansion

### Forward Chaining Engine (`lib/v2/prover/forward.js`)
- Multiset rewriting with committed choice
- Quiescence detection (runs until no rules fire)
- Predicate indexing for O(1) rule matching
- Backward proving integration for side conditions

### FFI (`lib/mde/ffi/`)
- `convert.js` — bin ↔ BigInt conversion
- `mode.js` — Mode checking (+ = ground, - = output)
- `arithmetic.js` — plus, inc, mul, sub, div, mod, lt, le, eq
- ~15-20x speedup for arithmetic operations

**Remaining:**
- [ ] `@ffi` and `@mode` annotation parsing in MDE source files
- [ ] `@literal` and `@desugar` for syntax sugar
- [ ] Generate ll.json from .calc for backwards compatibility

**See:** dev/FFI-IMPLEMENTATION-PLAN.md, dev/research/clf-celf-ceptre.md

---

## Research Insights ✅

**See:** dev/research/insights.md

Key discoveries from the CALC research program:

1. **Three-Level Structure** — CALC's distinctive contribution
   - Structural (adjoint modes): Linear vs Cartesian
   - Epistemic (principal index): [Alice], [Bob]
   - Quantitative (grades): Pacioli T-accounts
   - These combine multiplicatively

2. **Pacioli Group as Grading Ring** — T-accounts native to type system

3. **Ownership as Fibration** — Correct categorical model (`[P] A` in fiber over P)

4. **Debt as Session/Channel** — Unifies debt with session types

5. **Options map to additive &** — Financial choice = logical choice

6. **Terms as Audit Trails** — Proofs carry provenance

7. **Closed Questions** — What NOT to pursue:
   - Threshold modalities: no compact form
   - Ownership as adjunction: no, it's reindexing
   - Principals as modes: no, keep as orthogonal index

---

## HIGH Priority Research — Complete

### Fibrations: Study Plan for Ownership Semantics ✅

Understanding fibrations is essential for the correct categorical model of ownership.

**See:** dev/research/fibrations-study-plan.md

**Key Findings:**
- [x] Created complete study plan (prerequisites → definition → application)
- [x] ~2 week reading path: Capriotti → Vistoli → Jacobs
- [x] Ownership as fibration: `[Alice] A` = "A in fiber over Alice"
- [x] Transfer as reindexing along principal morphisms
- [x] Connection to dependent types (Lawvere correspondence)

---

### Resource Semantics: What Are Terms? ✅

If `A` is a resource type, what is the semantics of `a : A`?

**See:** dev/research/resource-term-semantics.md

**Key Findings:**
- [x] Terms can be 'receipts' or 'audit trails' showing provenance
- [x] Calculus of Audited Units (CAU): expressions with computation history trails
- [x] Proof-relevant vs proof-irrelevant: we want proof-relevant (proofs carry info)
- [x] Realizability: realizer = computational evidence (tx hash, merkle path, signature chain)
- [x] Proposed term structure with trail annotations for CALC

---

### Financial Primitives in CALC ✅

Research how basic financial derivatives map to linear logic / CALC machinery.

**See:** dev/research/financial-primitives.md

**Key Findings:**
- [x] **Options map to additive & (choice)**: `(cash ⊸ underlying) & 1` = exercise or expire
- [x] **Swaps are iterated atomic swaps**: already have primitive
- [x] **Futures need temporal modality**: `A ⊸_{at_time} B`
- [x] **Leverage involves debt + oracles**: position ⊗ debt(...)
- [x] **Order books as offer collections**: bid/ask with &
- [x] **Peyton-Jones combinators**: many map to CALC, some need extensions
- [x] Extensions needed: temporal modalities, oracles, commitment schemes

---

### Study Linear Negation as Debt Semantics ✅

**See:** dev/research/linear-negation-debt.md

Linear negation `A⊥` naturally interprets as "obligation" or "debt."

**Key Findings:**

1. **Yes, `[Alice] coin(BTC, 0.5)⊥` = "Alice owes 0.5 BTC"**
   - Use `[Alice] (A⊥)` for "Alice's debt" (ownership doesn't commute with negation)

2. **Modality/negation interaction:**
   - `[Alice] (A⊥)` ≠ `([Alice] A)⊥`
   - First = "Alice controls an obligation"
   - Second = "Negation of Alice controlling A"

3. **Game-semantic interpretation:**
   - A = Proponent has winning strategy
   - A⊥ = Opponent has winning strategy (role reversal)
   - Debt = being in Opponent role for that resource

4. **Settlement rule:**
   - `A ⊗ A⊥ ⊢ 1` (having + owing = nothing)
   - Follows from CLL axiom ⊢ A, A⊥

**Key Interpretations:**
- Girard: "male/female plug" (complementarity)
- Action/reaction, supply/demand, input/output
- Session types: dual channel endpoints

**CALC Implications:**
- CLL fragment needed for full debt support (currently ILL)
- Or use explicit `debt(C, q)` predicate
- Connect to authorization logic for creditor specification

**Answered Questions:**
- [x] Multi-party debt: who is the creditor? → **Use explicit predicate: `debt(debtor, creditor, commodity, quantity)`**
- [x] CLL extension worth the complexity? → **Stay ILL short-term, add negation only if needed**

---

### Can Ownership Modalities Be Expressed as Session Types? ✅

**See:** dev/research/ownership-as-session-types.md

**Answer: Partially.** Core features overlap but session types lack principal identity.

**What overlaps:**
- [x] Linear resources (ownership via linearity)
- [x] Ownership transfer (delegation = channel passing)
- [x] One-time vs reusable (linear vs `!A`)
- [x] Acquire-release = temporary ownership

**What's missing in session types:**
- Principal identity (WHO owns, not just THAT it's owned)
- Multi-sig / consensus modalities (`[A ∧ B]`)
- Authorization reasoning (`says`, `controls`)

**Three possible unifications:**
1. Principals as processes (simple but limited)
2. Principals as modes (adjoint logic extension)
3. Endpoint assignment (`Alice owns c+`)

**Recommendation:** Don't reduce ownership to session types. Keep as complementary:
- Session types → protocol/communication
- Ownership modalities → principals/authorization
- Adjoint logic → potential unifying framework

**Answered Questions:**
- [x] Adjoint logic with principal-indexed modes? → **Agent-indexed adjoint pairs exist (Sadrzadeh-Dyckhoff). Keep principals as orthogonal index, not modes.**
- [x] Channel passing = `speaks for`? → **Related but not identical. Channel delegation is linear ownership transfer; speaks-for is general authority.**

---

### How Do Consensus Modalities Fit with Multiparty Sessions? ✅

**See:** dev/research/consensus-modalities-mpst.md

`[Alice ∧ Bob] A` requires both parties. Multiparty session types (MPST) model multi-party protocols.

**Key Findings:**

1. **MPST has roles but not consent primitives**
   - Roles/participants exist, projection works
   - No native "both must agree" construct
   - Consensus is implicit in protocol structure

2. **Composite principals from authorization logic**
   - `(A ∧ B) says S` = `(A says S) ∧ (B says S)`
   - `A speaks for B` = delegation
   - Clean semantics, but not native to session types

3. **Approaches to consensus in session types:**
   - Synchronized branching: `sync(Alice, Bob) : choice`
   - Choreographic programming with `sync` construct
   - Explicit consent channels
   - Encode as protocol pattern (verbose but works)

4. **Threshold (k-of-n) is problematic:**
   - Linear logic encodes it exponentially (C(n,k) cases)
   - No compact representation in additive connectives
   - Cryptographic threshold schemes exist but separate concern

5. **Ludics orthogonality may help:**
   - D ⊥ E = "designs interact successfully"
   - Could model "parties agree" = "strategies are orthogonal"

**Recommendation for CALC:**
- Short-term: Encode consensus as protocol patterns
- Medium-term: Add `[A ∧ B]` as primitive composite principal
- Long-term: Explore adjoint logic and Ludics

**Answered Questions:**
- [x] Modal logic of composite principals? → **Composite principals have established semantics: (A ∧ B) says φ ≡ (A says φ) ∧ (B says φ)**
- [x] Threshold modalities compact representation? → **NO compact form exists — use predicate `threshold(k, principals, φ)`**
- [x] Ludics multi-party orthogonality? → **MCP's coherence is best answer, not native Ludics**
- [x] Global types as authorization policies? → **Strong parallel: global types ≈ authorization policies, projection ≈ local permissions**

---

### Should Adjoint Logic Be the Unifying Framework? ✅

**See:** dev/research/adjoint-logic-unifying-framework.md

**Answer: Yes, as structural foundation. But not complete solution.**

**What adjoint logic IS:**
- Logic parametrized by a **preorder of modes**
- Each mode has structural properties: σ(m) ⊆ {W, C}
- **Adjoint modalities** ↑ᵏₘ and ↓ᵐₖ bridge between modes
- Generic cut elimination from framework

**What it unifies:**
- [x] LNL decomposition (! = ↓ᵁₗ ↑ₗᵁ) — CALC already does this!
- [x] Subexponentials (modes as indices)
- [x] Modal S4 and lax logic
- [x] Session types (Nomos: shared/linear modes)
- [x] Graded types (via Eades-Orchard extension)

**What it doesn't handle directly:**
- Principal identity (WHO owns) — modes don't identify principals
- Composite principals (A ∧ B) — no mode products
- Authorization (says, speaks for) — different concern
- Threshold (k-of-n) — not expressible

**Key insight: CALC's persistent_ctx/linear_ctx IS adjoint logic!**
- Two modes: U (Cartesian), L (Linear)
- Bang_L = F modality (↓ᵁₗ)
- Implicit dereliction = G modality (↑ₗᵁ)

**Recommendation: Layered approach**
- Layer 1: Adjoint logic (structural) — already have
- Layer 2: Principal modes (extension) — research direction
- Layer 3: Authorization logic (orthogonal) — separate judgment
- Layer 4: Consensus (built on top) — protocol encoding

**Answered Questions:**
- [x] Principal-indexed modes: M_Alice, M_Bob → **Agent-indexed adjoints exist. Recommend two-layer architecture: structural modes + principal index**
- [x] Mode products for composite principals → **Hard: modes form preorder, not monoidal category. Keep composites at formula level**
- [x] Graded principal modes: □ʳ_Alice A → **Promising: grade on comonad, principal on formula — they compose naturally**

---

### Research Algebraic Accounting Systems ✅

Study the theoretical foundations of accounting from an algebraic perspective.

**See:** dev/research/algebraic-accounting.md

**Key Findings:**
- [x] **Pacioli Group**: T-accounts [x // y] form a group via "group of differences"
- [x] **Grothendieck Group**: Generalization to any commutative monoid → abelian group
- [x] **Graph Theory**: Accounts = nodes, transactions = edges, zero-sum property
- [x] **Linear Algebra**: Incidence matrices, null space = conservation
- [x] **Category Theory**: Limits verify constraints, colimits aggregate

**Deep Connection to Linear Logic:**
- Conservation = resource-sensitivity (no weakening/contraction)
- T-accounts [x // y] ↔ formulas with negation (x ⊗ y⊥?)
- Transactions ↔ linear implications
- Liabilities ↔ linear negation

**Answered Questions:**
- [x] How does Pacioli group relate to linear logic additives (⊕, &)? → **NOT additives! It's multiplicative: [x // y] ≈ x ⊗ y⊥**
- [x] Is [x // y] related to A ⊕ A⊥ or par (⅋)? → **No, it's tensor with negation**
- [x] Is the Grothendieck group construction = linear negation? → **Conceptually similar but structurally different**
- [x] **Key insight:** Pacioli group should be a GRADING RING for graded linear logic

**Key Insight:** Linear logic IS the logic of accounting!

---

### Research Plain Text Accounting Systems ✅

Study practical plain-text accounting tools and their inner workings.

**See:** dev/research/plain-text-accounting.md

**Key Findings:**
- [x] **Data model**: Transactions → Postings → Accounts (hierarchical) → Commodities
- [x] **Conservation enforced by**: transaction must sum to zero (fundamental invariant)
- [x] **Balance assertions**: periodic checks that account balance = expected value
- [x] **Multi-commodity**: inventory/lot tracking with cost basis, FIFO/LIFO booking
- [x] **Algebraic structure**: Pacioli Group (Ellerman) — ordered pairs [debit // credit]

**Deep Connection to Linear Logic:**
- Conservation law = no weakening + no contraction
- T-accounts = group of differences (signed from unsigned)
- Liabilities = linear negation (debt as A⊥)
- Transaction = linear implication (transfer)

**What PTA does that CALC could adopt:**
- Hierarchical accounts: `[Alice]:wallet:cold:btc`
- Balance assertions as periodic consistency checks
- Lot matching for capital gains

**What CALC adds:**
- Ownership modalities as first-class (`[Alice]` vs `[Bob]`)
- Authorization logic (`A says transfer(...)`)
- Atomic swaps via proof search
- Formal semantics, not just software

---

### Research Girard's Recent Work (Ludics, Transcendental Syntax) ✅

**See:** dev/research/girard-recent-work.md, dev/research/ludics-orthogonality-consensus.md

Brief research into Girard's post-linear-logic program, with deep dive into Ludics.

**Key Concepts:**
- [x] **Geometry of Interaction**: Proofs as operators, cut = composition
- [x] **Ludics**: Proofs as interactive strategies, meaning from orthogonality
- [x] **Transcendental Syntax**: Logic derived from computation

**Ludics Deep Dive:**
- [x] **Designs**: Abstractions of proofs, positive/negative actions, daimon (†)
- [x] **Orthogonality**: D ⊥ E iff [[D, E]] = † (interaction converges)
- [x] **Behaviours**: B = B⊥⊥ (bi-orthogonal closed = types)
- [x] **Internal completeness**: (A ⊗ B)⊥⊥ = A ⊗ B (no closure needed!)
- [x] **L-nets (Faggian-Maurel)**: Concurrent extension with parallel composition

**Orthogonality as Consensus:**
- [x] D ⊥ E = "D and E agree/interact successfully" — YES, this works!
- [x] Convergence = parties reach agreement (daimon)
- [x] Divergence = deadlock/disagreement
- [x] Atomic swap: Alice's strategy ⊥ Bob's strategy iff swap succeeds

**Gap: Binary vs N-ary Orthogonality:**
- Standard Ludics is binary (D ⊥ E)
- Consensus needs n-ary: D₁ ⊥ D₂ ⊥ ... ⊥ Dₙ
- Solution from MCP: **Coherence generalizes duality**
- Carbone et al.: n-ary compatibility via MCut rule

**Recommendation:**
- Short-term: Use orthogonality as intuition (guides design)
- Medium-term: Study coherence from MCP
- Long-term: Formal Ludics model for CALC

**Answered Questions:**
- [x] n-ary orthogonality: symmetric, conservative, associative-like? → **MCP's coherence is best answer. NOT symmetric in general, conservative for n=2, NOT associative**
- [x] Principal-aware designs? → **No existing work found. Would need external annotation. Research direction.**
- [x] Behaviours as authorization policies? → **Conceptually promising. Policy = bi-orthogonal closed set of authorized strategies. No formalization yet.**

---

### Study Adjunctions Deeply ✅

**See:** dev/research/adjunctions-deep-study.md

Comprehensive treatment of adjunctions from categorical and proof-theoretic perspectives.

**Categorical Adjunctions (F ⊣ G):**
- [x] **Definition**: Hom-isomorphism or unit η + counit ε + triangle identities
- [x] **Key examples**:
  - Free ⊣ Forgetful (paradigmatic: "to define homomorphism from free, say where generators go")
  - Product ⊣ Diagonal ⊣ Coproduct (+ ⊣ Δ ⊣ ×)
  - Curry ⊣ Eval ((−) × A ⊣ (−)^A) — exponential adjunction, gives currying
  - Limits/Colimits ⊣ Diagonal (colim ⊣ Δ ⊣ lim)
- [x] **Properties**:
  - RAPL: Right adjoints preserve limits
  - LAPC: Left adjoints preserve colimits
  - Adjoint functor theorem: preserves limits + solution set → has left adjoint

**Adjunctions Generate Monads/Comonads:**
- [x] Every F ⊣ G induces monad T = G∘F and comonad D = F∘G
- [x] Kleisli category: initial among adjunctions inducing T
- [x] Eilenberg-Moore category: terminal among adjunctions inducing T
- [x] The ! modality IS the comonad from LNL adjunction

**Adjunctions vs Galois Connections vs Residuation:**
- [x] All the same structure at different generality levels!
- [x] Galois connection = adjunction for posets
- [x] Residuation = a · b ≤ c ↔ a ≤ c/b ↔ b ≤ a\c
- [x] Deduction theorem IS residuation: Γ, A ⊢ B ↔ Γ ⊢ A → B

**Proof-Theoretic Adjunctions:**
- [x] Residuation in sequent calculus: (−) ⊗ A ⊣ A ⊸ (−)
- [x] Display postulates encode adjunctions: X ; Y ⊢ Z ↔ X ⊢ Y > Z
- [x] LNL: F ⊣ G between Cart and Lin, ! = F∘G
- [x] Adjoint logic generalizes to mode preorders

**Curry-Howard-Lambek:**
- [x] Every fundamental datatype arises from an adjunction
- [x] Exponential adjunction gives currying
- [x] State monad from (−) × S ⊣ (−)^S

**String Diagrams:**
- [x] Zig-zag identities: "pull string straight through bend"
- [x] Monad laws follow from zig-zag identities!

**CALC Relevance:**
- persistent_ctx/linear_ctx IS the LNL adjunction
- New modalities should be designed as adjunctions
- Checklist: residuation? unit/counit meaning? triangle identities?

---

### Study Garg et al. — Linear Logic of Authorization ✅

**Key paper** for combining linear logic with authorization modalities. Directly relevant to our ownership/consensus goals.

- [x] **Core concepts** (See: dev/research/authorization-logic.md)
  - [x] `A says φ` modality (principal affirmation) — subjective belief, like `□_A φ`
  - [x] Linear vs exponential affirmations — consumable (use once) vs reusable (!)
  - [x] Knowledge modalities — `K knows φ` for information flow
  - [x] `speaks for` — delegation: if A says φ then B says φ
  - [x] `controls` — trust: `(A says φ) → φ`
- [x] **BL Family of Logics** (Garg thesis)
  - [x] BL0: core sorted first-order intuitionistic + `k says s`
  - [x] BL1: adds state predicates
  - [x] BL: adds explicit time `s @ [u1,u2]`
  - [x] BLL: linear extension (most relevant for CALC)
- [x] **Proof theory**
  - [x] Natural deduction + sequent calculus presentations
  - [x] Kripke semantics with views
  - [x] Cut elimination proven
- [x] **Related work analyzed**
  - [x] Delegation Logic (Li): k-of-n thresholds
  - [x] NAL: dynamic principals, groups
  - [x] Nomos: linear types for smart contracts
  - [x] Modal deconstruction: translation to S4

**Key Finding:** No existing work handles weighted/graded authorization or consensus-as-modality (PoW/PoS). This is CALC's opportunity!

**Mapping to CALC:**
- `A says φ` → `[Alice] A` (ownership modality)
- Linear affirmation → `linear_ctx` (already implemented!)
- Exponential affirmation → `persistent_ctx` (already implemented!)
- `speaks for` → mode hierarchy in adjoint logic
- Composite principals → multi-type DC with principal types

---

### Research: Multi-Type Display Calculus in CALC ✅

Our `persistent_ctx` + `linear_ctx` IS multi-type display calculus (Benton's LNL).
Research confirmed this and analyzed generalization options.

- [x] **Confirm LNL Structure** (See: dev/research/multi-type-display-calculus.md)
  - [x] Verified: persistent_ctx = Cartesian type (set, contraction/weakening OK)
  - [x] Verified: linear_ctx = Linear type (multiset, exact resource tracking)
  - [x] Verified: Bang_L is the F functor (prover.js:308-316)
  - [x] Verified: G functor is implicit (persistent_ctx propagated to all premises)

- [x] **Can Special Rules Be Generalized?**
  - [x] Researched calculus-toolbox-2: uses DSL with explicit type parameters
  - [x] Researched Greco & Palmigiano: properness + multi-type methodology
  - [x] Researched Pfenning's adjoint logic: generalizes to preorder of modes
  - [x] **Conclusion: Three options identified** (see research doc)

- [x] ~~**Recommendation: Keep It Simple (YAGNI)**~~ → **REVISED: Generalize for multimodalities**

**Key Finding:** CALC already implements multi-type DC correctly! Use as case study for generalization.

---

## Implementation — Complete

### Content-Addressed Formulas & Proof Infrastructure ✅

Implemented content-addressed hashing for O(1) equality and structural sharing.

**Core Infrastructure:**
- [x] `lib/hash.js` — FNV-1a 64-bit hashing (fast, non-cryptographic)
- [x] `lib/intern.js` — Global interning store for hash-consing
- [x] `lib/store.js` — Singleton store pattern (like `Calc.db`)
- [x] `lib/profiler.js` — Operation counting and timing infrastructure

**Integration:**
- [x] `mgu.js` — O(1) term equality via `internNode(t).hash` comparison
- [x] `substitute.js` — O(1) node matching via content-addressed hashes
- [x] `sequent.js` — Content-addressed context entries, sequent hashing

**Benchmarking:**
- [x] `benchmarks/` directory with micro-benchmarks
- [x] `CALC_PROFILE=1` environment flag for profiling
- [x] `npm run bench` and `npm run bench:save` scripts

**Cleanup:**
- [x] Removed `lib/compare.js` (obsolete O(n) comparison)
- [x] Removed SHA3/keccak dependencies (replaced with FNV-1a)

**Deferred Optimizations:** See `dev/optimization_strategies.md`

---

### Multi-Type Display Calculus Research ✅
- [x] Confirmed CALC implements Benton's LNL (persistent_ctx + linear_ctx)
- [x] Bang_L is the F functor (Lin → Cart bridge)
- [x] G functor implicit via persistent_ctx propagation
- [x] Researched Greco & Palmigiano, calculus-toolbox-2, Pfenning's adjoint logic
- [x] Recommendation: Keep current implementation (YAGNI)
- [x] Created: dev/research/multi-type-display-calculus.md

### Display Calculus Verification ✅
- [x] Implement C1-C8 checker in JavaScript (via /health UI)
- [x] Document the hybrid architecture (display rules + focused search)
- [x] Document which conditions pass/fail for ll.json
- [x] Decide: stay with ILL fragment (no ⅋, +, ?)

### UI Revival ✅
- [x] Get basic rendering working (SolidJS + Vite)
- [x] Add interactive rule application
- [x] Classical proof tree view
- [x] Structured (Lamport-style) proof view
- [x] ASCII proof tree view
- [x] JSON export view
- [x] Clickable rule labels with detail dialog
- [x] Show abstract rule, substitution (MGU), instantiated premises

### Interactive Proof Enhancements ✅
- [x] Show rule premises when selecting a rule
- [x] Display abstract rule pattern
- [x] Show sigma (substitution) applied by rule
- [x] Context split dialog for Tensor_R etc.

### Calculus Health Check UI ✅
- [x] Create /health route with educational C1-C8 explanation
- [x] Show overall cut elimination status
- [x] Expandable condition cards with full explanations
- [x] Architecture section explaining hybrid (display + focused)

### Clean Up & Polish ✅
- [x] Clean up ll.json - mark what's used vs unused clearly

---

## Research Documentation ✅

- [x] Logics overview: which logics can be displayed (dev/research/logics-overview.md)
- [x] Proof calculi foundations (dev/research/proof-calculi-foundations.md)
- [x] Display calculus deep research (dev/research/display-calculus.md)
- [x] Q&A on proof theory (dev/research/QnA.md)
- [x] Logic engineering guide (dev/research/logic_engineering.md)
- [x] Residuation knowledge base (dev/research/residuation.md)
- [x] Exponential display problem (dev/research/exponential-display-problem.md)
- [x] QTT overview (dev/research/QTT.md)
- [x] DSL approaches comparison (dev/research/DSL-approaches.md)
- [x] Interactive proving & prover orchestration (dev/research/interactive_proving.md)

---

## Interactive Proving Research ✅

- [x] LCF architecture (trusted kernel + untrusted tactics)
- [x] de Bruijn criterion vs LCF architecture comparison
- [x] Isabelle tacticals (THEN, ORELSE, REPEAT, etc.)
- [x] Isabelle Sledgehammer (parallel provers, relevance filtering, proof reconstruction)
- [x] Lean4 TacticM monad hierarchy (CoreM → MetaM → TermElabM → TacticM)
- [x] Coq Ltac2 (Hindley-Milner types, effects model, backtracking)
- [x] CoqHammer (ATP integration, proof reconstruction)
- [x] Twelf logic programming (mode checking, totality checking, coverage)
- [x] Prover orchestration patterns (parallel race, tacticals, translation+reconstruction)
- [x] Relation to CALC: FocusedProver ≈ untrusted tactics, mgu.js ≈ MetaM, Sequent ≈ LNL

---

## Key Papers Studied ✅

- [x] Pfenning's 15-836 Substructural Logics course notes
- [x] Wadler's "Propositions as Types" (Curry-Howard)
- [x] Granule ICFP 2019 (Graded Modal Types)
- [x] Benton's LNL (Linear/Non-Linear) Logic
- [x] Greco & Palmigiano's "Linear Logic Properly Displayed"

---

## Foundational Understanding ✅

- [x] **Study Curry-Howard correspondence in depth**
  - [x] Read Wadler's "Propositions as Types" paper
  - [x] Understand the three levels: syntax, structure, dynamics
  - [x] Work through Curry-Howard-Lambek (category theory connection)
  - [x] Understand why classical logic → continuations/control operators
  - See: proof-calculi-foundations.md, ANKI.md
- [x] **Understand proof calculi hierarchy**
  - [x] Natural deduction vs sequent calculus trade-offs
  - [x] Why sequent calculus is good for proof search
  - [x] Display calculus requirements (residuation, 8 conditions)
  - [x] When logics lack sequent calculi (fixpoints, context-sensitivity)
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Study cut elimination deeply**
  - [x] Why cut elimination = consistency
  - [x] Why subformula property enables proof search
  - [x] Proof size explosion (Boolos's example)
  - See: QnA.md

---

## Logic Engineering ✅

- [x] **Syntax vs Semantics: Which comes first?**
  - [x] Study proof-theoretic semantics (meaning from rules)
  - [x] Study model-theoretic semantics (meaning from truth)
  - [x] Understand the iteration between syntax and semantics
  - See: logic_engineering.md
- [x] **Checklist for a "good" sequent calculus**
  - [x] Cut elimination (must have)
  - [x] Subformula property (should have)
  - [x] No global side conditions (nice to have)
  - [x] Modularity (adding connectives doesn't break things)
  - See: logic_engineering.md, QnA.md

---

## Residuation & Exponentials ✅

- [x] **Study residuation in depth**
  - [x] Work through examples in residuated lattices
  - [x] Understand Galois connections as requirement for residuation
  - [x] Why ! is a comonad, not residuated
  - [x] Examples of non-residuated connectives and why
  - See: residuation.md, exponential-display-problem.md
- [x] **Study adjoint decomposition for exponentials**
  - [x] Read Benton's LNL (Linear/Non-Linear) paper
  - [x] Understand multi-type display calculus approach
  - [x] How ! = F ∘ G (composition of adjoints)
  - [x] Study Greco & Palmigiano's "Linear Logic Properly Displayed"
  - See: exponential-display-problem.md, ANKI.md
- [x] **Study left/right decomposition patterns**
  - [x] What makes a "good" sequent rule?
  - [x] When do you need hypersequents/labels?
  - [x] Understand "local" vs "global" conditions in rules
  - [x] Which connectives fail decomposition (modalities, fixpoints)
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Study non-determinism and confluence**
  - [x] Why classical cut-elimination is non-deterministic
  - [x] How polarization/focusing restores determinism
  - See: QnA.md

---

## Categorical & Algebraic Foundations ✅

- [x] **Comonads** (in the sense of "! is a comonad")
  - [x] Definition: counit and comultiplication
  - [x] Why comonads are different from residuated operations
  - See: exponential-display-problem.md, QnA.md
- [x] **Adjoint decomposition** (! = F ∘ G)
  - [x] Adjunctions vs residuations
  - [x] How adjoints between TYPES give well-behaved rules
  - [x] Benton's LNL logic as canonical example
  - See: ANKI.md, exponential-display-problem.md
- [x] **Multi-type display calculus**
  - [x] Multiple types of formulas/structures
  - [x] Bridge connectives between types
  - [x] How this solves the exponential problem
  - See: exponential-display-problem.md, logics-overview.md
- [x] **Galois connections**
  - [x] Formal definition (f ⊣ g)
  - [x] Relationship to residuation
  - [x] Why they're required for display postulates
  - See: residuation.md, QnA.md
- [x] **Labelled sequents**
  - [x] How labels solve context-sensitivity
  - [x] Labels as explicit worlds (Kripke-style)
  - [x] Relationship to display calculus
  - See: QnA.md, proof-calculi-foundations.md
- [x] **Hypersequents**
  - [x] Definition: multiset of sequents
  - [x] How they solve S5 modal logic
  - [x] Comparison with display calculus
  - See: QnA.md, ANKI.md
- [x] **Global side conditions**
  - [x] What they're used for (modal logic, exponentials, eigenvariables)
  - [x] Why they're problematic for cut elimination
  - [x] Alternative formulations that avoid them
  - See: QnA.md

---

## General Research ✅

- [x] Read Pfenning's 15-836 notes - DONE (see ANKI.md)
- [x] Study Granule ICFP 2019 paper - DONE (see QTT.md)
- [x] Research Nomos language (blockchain + linear types) - DONE (see nomos.md)
- [x] Research FFI for logics (mode-checked trusted computation) - DONE (see ffi-logics.md)

---

*Last updated: 2026-02-01*
