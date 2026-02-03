# ANKI.md

Flashcard-style definitions for key concepts. Format: **Term** → Definition

---

## Proof Theory Terminology

**Proof calculus / Proof system**
→ Synonymous. A formal system for constructing proofs (axioms + inference rules). Examples: sequent calculus, natural deduction, Hilbert systems.

**Proof formalism**
→ The "shape" or "syntax" of judgments that the proof system manipulates. Defines what objects you write down and manipulate during proof construction.
- Sequents: `Γ ⊢ Δ`
- Hypersequents: `Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ...`
- Nested sequents: `Γ ⊢ Δ, [Γ' ⊢ Δ']`
- Display structures: `X ; Y ⊢ Z` with structural connectives
- Labelled sequents: `w:A, wRv, v:B ⊢ w:C` with explicit worlds/labels

**Proof search strategy**
→ How you search for proofs. Orthogonal to the formalism - you can apply different strategies to the same formalism.
- Focusing: alternating invertible/non-invertible phases
- Tableaux: tree-based refutation
- Resolution: clause-based contradiction finding

**Proof representation**
→ How you represent completed proofs. May differ from how you search.
- Trees: standard derivation trees
- Proof nets: graphs that quotient away "bureaucracy"
- Lambda terms: via Curry-Howard

**Canonical proof**
→ A unique representative for each equivalence class of "essentially same" proofs. Two proofs are "essentially same" if they differ only in irrelevant details (rule order, associativity, etc.).

---

## Linear Logic Connectives

**Tensor (⊗)**
→ Multiplicative conjunction. "I have both A AND B simultaneously, as separate resources."

**Par (⅋)**
→ Multiplicative disjunction. De Morgan dual of tensor: `A ⅋ B = (A⊥ ⊗ B⊥)⊥`. Hard to interpret as resources; better understood via game semantics or as "entangled disjunction."

**With (&)**
→ Additive conjunction. "I can choose to use A OR to use B, but not both."

**Plus (⊕)**
→ Additive disjunction. "Either A or B is available, but I don't control which."

**Lollipop (⊸)**
→ Linear implication. "Consuming A produces B." Defined as `A ⊸ B = A⊥ ⅋ B`.

**Bang (!)**
→ Exponential "of course". Allows unlimited use (contraction/weakening). "As many copies of A as needed."

**Why Not (?)**
→ Exponential dual of bang. `?A = (!A⊥)⊥`. Allows structural rules on the left.

---

## Polarity

**Positive connectives**
→ ⊗, ⊕, !, 1, 0, atoms. Rules are invertible on the LEFT, non-invertible on the RIGHT.

**Negative connectives**
→ ⅋, &, ?, ⊥, ⊤, ⊸. Rules are invertible on the RIGHT, non-invertible on the LEFT.

**Focusing**
→ Proof search strategy based on polarity. Alternate between:
1. **Async phase**: eagerly apply invertible rules (no backtracking needed)
2. **Sync phase**: choose a formula, apply non-invertible rules until done

---

## Display Calculus

**Display calculus**
→ Proof formalism introduced by Belnap (1982). Uses structural connectives that mirror logical connectives, plus display postulates to shuffle structures around.

**Display property**
→ Any formula occurrence can be "displayed" (made the sole occupant of one side of the turnstile) using only display postulates.

**Display postulate**
→ A rule that rearranges structures without changing provability. Example: `X ; Y ⊢ Z ↔ X ⊢ Y > Z` (residuation).

**Structural connective**
→ A connective at the structure level (not formula level) that mirrors a logical connective. E.g., `;` mirrors ⊗, `>` mirrors ⊸.

**Belnap's conditions (C1-C8)**
→ Eight syntactic conditions. If a display calculus satisfies them, cut elimination is guaranteed.

---

## Residuation

**Residuation**
→ An adjunction/Galois connection between connectives. For tensor: `A ⊗ B ⊢ C` iff `A ⊢ B ⊸ C` iff `B ⊢ A −○ C`.

**Left residual**
→ Given `A ⊗ B ⊢ C`, the left residual `B ⊸ C` is what A must imply.

**Right residual**
→ Given `A ⊗ B ⊢ C`, the right residual `A −○ C` is what B must imply.

---

## Other Proof Formalisms

**Hypersequent**
→ A multiset of sequents: `Γ₁ ⊢ Δ₁ | Γ₂ ⊢ Δ₂ | ...`. Read as "at least one component is provable."

**Nested sequent**
→ Sequents containing sequents recursively (tree structure). More expressive than hypersequents.

**Labelled sequent**
→ Sequents with explicit labels (worlds) and accessibility relations. Most expressive, but "external" (encodes semantics).

**Deep inference**
→ Rules can apply anywhere inside a structure, not just at the root. Eliminates need for display postulates.

**Proof net**
→ Graphical proof representation. Quotients away "bureaucratic" differences between sequent proofs. Cut elimination is local graph rewriting.

---

## Hierarchy of Expressiveness

**Less expressive → More expressive:**
Standard sequent < Hypersequent < Nested sequent < Display calculus ≈ Labelled sequent

**Trade-off:** More expressive = can handle more logics, but harder to prove meta-properties and may lose subformula property or internality.

---

---

## Curry-Howard Correspondence

**Curry-Howard correspondence**
→ Isomorphism between proof systems and type systems: propositions ↔ types, proofs ↔ programs, proof normalization ↔ computation.

**The three levels of Curry-Howard**
→ 1. Syntax: propositions = types, proofs = terms
→ 2. Structure: proof rules = typing rules, assumptions = free variables
→ 3. Dynamics: cut elimination = β-reduction, normal proofs = values

**Curry-Howard-Lambek**
→ Three-way isomorphism: Logic ↔ Type Theory ↔ Category Theory. Objects = types = propositions, morphisms = terms = proofs.

**Why Curry-Howard needs constructive logic**
→ Classical logic has excluded middle (A ∨ ¬A). Computationally, this corresponds to control operators (call/cc, continuations) - programs that can "escape" normal evaluation.

**Logic vs Type Theory**
→ Same mathematical content, different presentations. Logic focuses on provability and proof structure; type theory focuses on typing programs and computation.

---

## Why Sequent Calculus is Good

**Why sequent calculus for proof search?**
→ 1. Uniform bottom-up reading (every rule breaks goal into subgoals)
→ 2. All rules are "introduction" rules (no elimination rules to reverse)
→ 3. Structural rules explicit (can control for substructural logics)
→ 4. Subformula property bounds search space

**Subformula property**
→ In a cut-free proof, every formula is a subformula of the goal. This bounds the search space for proof search.

**Cut rule**
→ "If I can prove A, and use A to prove C, I can prove C directly." `Γ ⊢ A` and `A, Δ ⊢ C` implies `Γ, Δ ⊢ C`.

**Cut elimination (Hauptsatz)**
→ Any proof using cut can be transformed into a cut-free proof. Implies consistency (can't prove ⊥) and subformula property.

**Sequent calculus vs natural deduction**
→ Natural deduction: bi-directional info flow (intro up, elim down), closer to human reasoning.
→ Sequent calculus: uniform bottom-up, explicit contexts, better for proof search.

---

## Why Display Calculus is Hard

**Display property requirement**
→ Any formula can be "displayed" as the entire antecedent or succedent using only structural rules.

**Structural connective requirement**
→ Every logical connective needs a structural counterpart (⊗ → comma, ⊸ → >, etc.)

**Residuation requirement**
→ Connectives must form Galois connections: `A ⊗ B ⊢ C` iff `A ⊢ B ⊸ C`. Not all connectives have residuals!

**Exponential problem in display calculus**
→ The exponentials (!,?) are not residuated, so structural counterparts would break the display property. Requires special treatment.

**Belnap's 8 conditions payoff**
→ If satisfied, cut elimination is GENERIC - one proof works for all proper display calculi. Worth the setup cost for modularity.

---

## Benton's LNL (Linear/Non-Linear) Logic

**LNL model**
→ A symmetric monoidal adjunction between a cartesian closed category C and a symmetric monoidal closed category M. C models intuitionistic logic; M models linear logic.

**Bang decomposition (! = F ∘ G)**
→ The of-course modality ! decomposes into two adjoint functors: F (Lin): C → M (embeds intuitionistic into linear) and G (Mny): M → C (extracts reusable part). Then !A = F(G(A)).

**Why LNL decomposition works**
→ F and G are adjoints (F ⊣ G), so F(X) ⊢ Y iff X ⊢ G(Y). This adjunction induces a comonad on M (the ! modality), avoiding the residuation problem.

**F is strong monoidal**
→ Lin preserves products: Lin(⊤) = I and Lin(X × Y) = Lin(X) ⊗ Lin(Y). This means the adjunction "lifts" to monoidal structure automatically.

---

## Graded Modal Types (Granule)

**Graded modality (□_r)**
→ A modality indexed by elements of a semiring. □_r A means "r copies of A available." Generalizes linear (r=1) and unrestricted (r=ω) to any semiring.

**Semiring for resource tracking**
→ (S, +, ·, 0, 1) where + combines uses, · scales uses. Examples: {0,1,ω} for basic linearity; ℕ for exact counting; ℝ≥0 for quantities.

**Graded comonad**
→ A comonad indexed by a semiring, generalizing the ! modality. □_r is a graded comonad; graded monads capture effects.

**QTT vs Granule**
→ QTT: grades on binders (x :_r A). Granule: grades on types (□_r A). Same expressivity, different presentation. QTT better for dependent types; Granule better for grade polymorphism.

---

## Multi-Type Display Calculus

**Multi-type display calculus**
→ Display calculus with multiple sorts/types of formulas. Different types have different structural rules. Connectives can bridge types.

**Why multi-type solves exponentials**
→ Instead of trying to residuate ! (impossible), separate Linear and Cartesian types. ! becomes a bridge between types via the F ⊣ G adjunction.

**Properness (Greco & Palmigiano)**
→ Rules are closed under uniform substitution of ALL parametric parts. Enables smoothest cut elimination proof and modular extensions.

---

## Curry-Howard Deep Correspondences

**Curry-Howard-Lambek**
→ Three-way isomorphism: Logic ↔ Type Theory ↔ Category Theory. Propositions = Types = Objects. Proofs = Terms = Morphisms.

**Classical logic ↔ Control operators**
→ Classical logic (with excluded middle) corresponds to type systems with call/cc and continuations. Proofs can "escape" normal evaluation.

**Linear logic ↔ Session types**
→ Linear types track resource usage; session types track communication protocols. Both ensure resources/channels used exactly as specified.

**Wadler's mystery**
→ Why did Gentzen's natural deduction (1935) and Church's lambda calculus (1936) turn out to be the same thing, discovered 30 years later?

---

## Pfenning's Substructural Logics

**Substructural hypotheses**
→ Different kinds of assumptions: ordered (position matters), linear (use once), affine (use at most once), relevant (use at least once), persistent (use any times).

**Concurrent computation as cut reduction**
→ Cut elimination corresponds to communication in concurrent processes. Proof normalization = message passing. Session types make this explicit.

**Resource semantics**
→ Interpret formulas as resources: A ⊗ B = both together, A ⊸ B = consuming A produces B, !A = unlimited supply of A.

---

## Nomos (Blockchain + Linear Types)

**Nomos**
→ A programming language for smart contracts based on resource-aware session types, developed at CMU by Ankush Das, Pfenning et al. Combines linear types, session types, and automatic resource analysis.

**Session types**
→ Types that prescribe bidirectional communication protocols. In Curry-Howard correspondence with linear logic propositions. ⊗ = send, ⊸ = receive, & = external choice, ⊕ = internal choice.

**Session types and linear logic**
→ Linear logic propositions correspond to session types: A ⊗ B = "send A then behave as B", A ⊸ B = "receive A then behave as B". Cut elimination = communication.

**Resource-aware session types**
→ Session types annotated with potential (gas costs). Type system statically bounds resource consumption, ruling out out-of-gas vulnerabilities.

**AARA (Automatic Amortized Resource Analysis)**
→ Type-based technique for inferring resource bounds. Each process gets initial potential; operations consume it; type system ensures non-negative potential.

**Shared vs linear channels in Nomos**
→ Linear channels ($c) used exactly once. Shared channels (#c) reusable (like !A). Mode shifts (↑↓) convert between them.

---

## FFI for Logics

**Mode declaration in logic programming**
→ Specifies information flow for predicates: `+` = input (must be ground), `-` = output (will be ground), `*` = unrestricted. Example: `%mode plus +A +B -C`.

**Prolog's `is/2` predicate**
→ Built-in that escapes unification for arithmetic. `X is 3+4` computes 7 and unifies with X. Right-hand side must be ground. Essentially an FFI to native arithmetic.

**CLP (Constraint Logic Programming)**
→ Logic programming extended with constraint solvers. Constraints collected and solved by external solver, not via backtracking proof search. Examples: CLP(FD), CLP(R), CLP(Q).

**CLP solver as trusted oracle**
→ The constraint solver in CLP is external to the logic - it's trusted to correctly solve constraints and return results for proof search to use.

**Oracle predicate**
→ A predicate whose truth is determined by external computation rather than proof search. The oracle is trusted to give correct answers.

**Certified computation**
→ Safer oracle approach: oracle gives answer, then we verify it's correct. For arithmetic: verify A + B = C is cheap even if computing it was external.

**FFI trust boundary**
→ Proof search is verified; FFI functions are trusted. The boundary between them must be carefully managed (type checking, mode checking, optional verification).

**Agda postulates and FFI**
→ Agda uses postulates to declare FFI functions. At type-checking time, treated as axioms; at runtime, external code executes. No verification that they match - potential inconsistency.

**Twelf's purity**
→ Twelf has no built-in arithmetic or FFI - everything must be derived from axioms. Pure but slow for computation. Safe but impractical for real arithmetic.

**Forward vs backward chaining**
→ Backward chaining: start from goal, work back to axioms (proof search). Forward chaining: start from facts, derive consequences (state transitions). Can be combined (Celf, LolliMon).

---

## Interactive Proving & Prover Orchestration

**LCF architecture**
→ Milner's approach: theorems are an abstract data type. Only the trusted kernel can construct `thm` values. ML type system enforces soundness. Tactics are untrusted code that can only produce theorems via kernel primitives.

**de Bruijn criterion**
→ Alternative to LCF: proof assistant generates proof certificates that can be checked by an independent program. Sceptics can write their own checker. Trade-off: requires storing full proof objects.

**LCF vs de Bruijn trade-off**
→ LCF: low memory (no proof storage), trust the kernel. de Bruijn: high memory (proof objects), independent verification possible. Modern systems often use both.

**HOL Light trusted kernel**
→ Extreme LCF minimalism: ~400 lines of OCaml, 3 axioms, 10 inference rules. Everything else built on top. Verified implementation (Candle) compiled to machine code.

**Sledgehammer architecture**
→ Isabelle's ATP integration: (1) relevance filter selects lemmas, (2) translate to TPTP, (3) run provers in parallel, (4) first success wins, (5) reconstruct proof in Metis.

**Sledgehammer relevance filters**
→ MePo (Meng-Paulson): symbol-based iterative selection. MaSh: machine learning (naive Bayes, k-NN). MeSh: hybrid. Key insight: unusual constants discriminate better.

**Sledgehammer proof reconstruction**
→ Don't translate ATP proofs directly. Use ATP as "lemma finder": extract which facts were used, re-prove locally with Metis using those facts. ~5% reconstruction failure rate.

**Sledgehammer parallel provers**
→ "Running E, SPASS, and Vampire in parallel for five seconds solves as many problems as running a single theorem prover for two minutes." First success wins, others terminated.

**Isabelle tacticals**
→ Tactic combinators: THEN (sequence), ORELSE (choice), TRY (try or skip), REPEAT (iterate), EVERY (sequence list), FIRST (first success). ALLGOALS, SOMEGOAL, FIRSTGOAL address specific goals.

**Lean4 monad hierarchy**
→ CoreM (environment) → MetaM (metavariables) → TermElabM (elaboration) → TacticM (goals). Each extends the ones below via transformer stacking. Monads support backtracking via saveState/restoreState.

**Lean4 TacticM**
→ Monad for tactic implementation. Key operations: getMainGoal, getGoals, setGoals, closeMainGoal, replaceMainGoal. Access hypotheses via withMainContext + getLCtx.

**Lean4 MetaM metavariables**
→ Metavariables are dual: holes in expressions AND proof goals. Three kinds: Natural (freely assignable), Synthetic (assignment-avoiding), Synthetic Opaque (never assignable).

**Coq Ltac2**
→ Redesign of Ltac1 following ML tradition. Static Hindley-Milner types, call-by-value evaluation, explicit quotations for meta/object distinction, first-class backtracking via plus/zero/case.

**Ltac2 effects model**
→ Three effect categories: (1) non-backtracking IO (mutation, printing), (2) fatal errors (throw), (3) backtracking (plus, zero). Operates in tactic monad, not standard IO.

**Ltac2 quotations**
→ Explicit meta/object separation: '[term] (open terms), constr:(expr) (closed terms), pat:(pattern) (patterns), @ident (identifiers).

**CoqHammer**
→ ATP integration for Coq: sauto tactic (CIC inhabitation), ATP translation, proof reconstruction. 39.1% success rate, 87-97% reconstruction. Limitations: no induction, poor on HOF/dependent types.

**Twelf totality checking**
→ Alternative to proof search: encode proofs as logic programs, verify totality via program analysis. Three components: input coverage (exhaustiveness), output coverage (generality), termination (structurally smaller).

**Twelf mode checking**
→ Mode declarations specify information flow: + (input, must be ground), - (output, will be ground), * (unrestricted). Ensures well-defined information flow in logic programs.

**Twelf coverage checking**
→ Verifies logic program handles all possible inputs. Input coverage: every ground input matches some case. Output coverage: outputs sufficiently general (no spurious pattern matching).

**Prover orchestration: parallel race**
→ Run multiple provers in parallel, first success wins. Promise.race semantics. Cancel others on success. Used by Sledgehammer, CoqHammer.

**Prover orchestration: slicing**
→ Run same prover with different heuristic configurations. Different configurations excel on different problems. Parallel slices improve coverage.

**Prover orchestration: translation + reconstruction**
→ Translate goal to external format (TPTP), call ATP, reconstruct proof natively. Key insight: use ATP as lemma finder, not proof generator.

---

## CALC's Multi-Type Implementation

**CALC's persistent_ctx**
→ The Cartesian/Intuitionistic type in CALC's LNL implementation. A **set** of formulas that can be used any number of times (contraction/weakening allowed). Corresponds to the C category in Benton's LNL model.

**CALC's linear_ctx**
→ The Linear type in CALC's LNL implementation. A **multiset** tracking exact resource counts. Corresponds to the M category in Benton's LNL model.

**CALC's Bang_L rule behavior**
→ The F functor implementation in CALC. Takes `!A` from linear_ctx, unwraps to `A`, places in persistent_ctx. This promotes a linear formula to the Cartesian world.

**CALC's implicit dereliction**
→ The G functor implementation in CALC. Everything in persistent_ctx is automatically available in all rule premises. Corresponds to the dereliction rule `!A ⊢ A`.

**Why CALC hardcodes Bang_L**
→ The "special case" for Bang_L in prover.js IS the F functor bridging Linear → Cartesian types. It's not a hack—it's the correct implementation of Benton's LNL adjunction.

**CALC already has multi-type DC**
→ The persistent_ctx + linear_ctx separation IS multi-type display calculus via Benton's LNL model. The "special rules" are the bridge functors F and G.

---

## Multi-Type Display Calculus Details

**Type-uniform sequent**
→ A sequent where antecedent and succedent have the same type. Required in multi-type display calculus. CALC handles this by operating primarily in Linear type with Cartesian as background.

**Multi-type display property**
→ Any formula can be displayed (isolated) on one side, potentially via crossing type boundaries. Bridge connectives (F, G) enable movement between types.

**Properness (Greco & Palmigiano)**
→ Closure under uniform substitution of ALL parametric parts in rules. Enables the smoothest proof of cut elimination and modular extensions.

**Adjoint logic (Pfenning)**
→ Generalization of LNL to arbitrary partial orders of modes with adjunctions between them. Each mode is a category; mode morphisms are adjunctions. Note: modes form a POSET (partial order), not preorder — incomparable modes (alice ⊥ bob) are natural.

---

## Advanced Proof Systems (Beyond Display/Labelled)

**Hierarchy extension**
→ Standard sequent < Hypersequent < Nested < Display ≈ Labelled < Deep Inference / Cyclic Proofs / Proof Nets. The top three solve different problems (structural flexibility, fixpoints, proof identity).

**Deep inference**
→ Proof formalism where rules apply anywhere inside structures, not just at the root. Provides symmetry (cut ↔ identity duality) and finer-grained analysis. Challenge: proof search harder to control.

**Cyclic proofs**
→ Non-wellfounded proofs as finite graphs (not trees). Essential for fixpoints (μ-calculus) and inductive definitions. Soundness via global trace condition. Berardi & Tatsuta: cyclic systems prove MORE than inductive systems.

**Global trace condition**
→ Soundness criterion for cyclic proofs. Requires that every infinite path through the proof graph passes through a "progress point" infinitely often, ensuring the proof isn't circular nonsense.

**Proof nets**
→ Geometric/graph representation of proofs eliminating "bureaucracy" — two sequent proofs differing only in rule order become the SAME proof net. Great for linear logic; BAD for multimodal logics.

**Why proof nets don't work for multimodal logic**
→ Correctness criteria become complex with modalities. No consensus on handling multiple modalities. For ownership/authorization, use Multi-Type DC or Labelled sequents instead.

**When to use cyclic proofs**
→ When modeling fixpoints, recursive definitions, inductive predicates. Relevant for: smart contracts with loops, transaction histories, "valid blockchain state" as least fixpoint. NOT needed for basic authorization modalities.

---

## Authorization Logic

**"A says φ" modality**
→ Principal A affirms/supports proposition φ. Core construct in authorization logics (ABLP, Garg et al.). "A says φ" means A believes φ is true or authorizes actions based on φ.

**Linear affirmation vs exponential affirmation**
→ Linear: consumable credential (use once, then gone). Exponential (!): reusable credential (can verify multiple times). Key innovation of Garg et al.'s linear authorization logic.

**Garg et al. (2006) — Linear Logic of Authorization**
→ Key paper combining linear logic with authorization modalities. Has: `A says φ`, consumable/reusable credentials, knowledge modalities, cut elimination. Model for CALC's ownership goals.

**Consensus modalities (generalization)**
→ Beyond simple ownership `[Alice] A`:
- Multi-sig: `[Alice ∧ Bob] A`
- k-of-n: `[2-of-{A,B,C}] A`
- Weighted: `[Alice:0.3, Bob:0.7] A`
- PoW: `[PoW(nonce, diff)] A`
- PoS: `[Stake(A, 100)] A`

**Mode partial order for authorization**
→ Modes form a POSET, not total order:
- shared ≥ alice, shared ≥ bob (consensus dominates)
- alice ⊥ bob (incomparable, neither controls other)
- staked ≥ linear (extra structure)

---

## Authorization Logic Deep Dive

**ABLP Logic (1993)**
→ Foundational authorization logic by Abadi, Burrows, Lampson, Plotkin. Introduced `A says φ` (principal affirmation) and `A speaks for B` (delegation). Used in Taos authentication system.

**"A says φ" — semantics**
→ Principal A affirms/supports proposition φ. It's subjective — different principals can disagree. Behaves like `□_A φ` (necessity indexed by A). Introduction: if φ is universally true, any A says it.

**"A speaks for B" — delegation**
→ If A says φ, then B says φ. Means A can act on B's behalf. Like power of attorney: anything A says counts as if B said it.

**"speaks for" examples**
→ (1) `ssh_key speaks for Alice` — key authentication counts as Alice authenticating. (2) `CEO speaks for Company` — CEO's signature = Company's signature. (3) `proxy_contract speaks for wallet` — proxy can act as the wallet. Transitive but NOT symmetric.

**"A controls φ"**
→ Abbreviation for `(A says φ) → φ`. Means A is authoritative/trusted about φ. If A controls φ and A says φ, then φ is objectively true.

**BL0 (core authorization logic)**
→ Sorted first-order intuitionistic logic + `k says s`. No state, no time. Judgment form: `K · ⊢ A` where K is the "view" (which principal's perspective).

**BL1 (with state)**
→ BL0 + interpreted predicates for system state (file permissions, time, ACLs). State can change non-deterministically between derivation steps.

**BL (full, with time)**
→ BL1 + temporal connective `s @ [u1, u2]` meaning s holds during interval. Enables credential expiration, time-limited permissions, audit trails.

**BLL (linear extension)**
→ BL + linear logic for consumable resources. Linear credentials (one-time use) vs exponential credentials (reusable). Most relevant variant for CALC.

**Kripke semantics for authorization logic**
→ Possible worlds W, accessibility R_k per principal k, views θ(w) = principals who see world w. Truth: `w ⊩ k says φ` iff `∀v. wR_k v → v ⊩ φ`.

**Composite principals**
→ Combining principals: `A ∧ B` (both), `A ∨ B` (either), `A │ B` (A quoting B), `A as R` (A in role R). Enables multi-sig and threshold.

**Threshold structure (k-of-n)**
→ Any k of n principals suffices: `threshold(k, {A,B,C})`. Without native support, requires exponential delegations: `2-of-{A,B,C} = (A∧B) ∨ (A∧C) ∨ (B∧C)` = C(n,k) cases.

**Modal deconstruction (Garg & Abadi 2008)**
→ Authorization logic translates to modal S4: `A says φ` → `□_A φ`. Sound and complete translation. Extends to composite principals and speaks-for. Proves decidability.

**Nomos language**
→ CMU language for smart contracts with session types + linear types. Assets as linear channels (can't duplicate). Acquire-release discipline prevents re-entrancy. Same research group as authorization logic.

---

## Session Types Deep Dive

**Propositions-as-Sessions (Caires & Pfenning 2010)**
→ Curry-Howard correspondence for concurrency: linear logic propositions = session types, proofs = processes, cut elimination = communication. Foundation for Nomos.

**Session type correspondence table**
→ A ⊗ B = send channel of type A, continue as B
→ A ⊸ B = receive channel of type A, continue as B
→ A & B = external choice (client picks)
→ A ⊕ B = internal choice (server picks)
→ 1 = close channel
→ !A = shared/replicable service

**Re-entrancy attack**
→ Smart contract vulnerability where malicious contract calls back into victim before state update. DAO hack 2016: $60M drained. Pattern: withdraw → send ETH → attacker calls withdraw again → balance not yet updated.

**Acquire-release discipline (Nomos)**
→ Prevents re-entrancy: client acquires shared process, gets private linear channel, must release back to shared state. Only one client has access at a time. Violations are compile errors, not runtime errors.

**Equi-synchronizing constraint**
→ In shared session types, must release at exactly the same type as acquired. Ensures state consistency. Relaxed to "subsynchronizing" in later work (Sano et al. 2021).

**Linear channel ($c) vs Shared channel (#c)**
→ Linear: must be used exactly once (like linear types). Shared: reusable, follows acquire-release. Mode shifts `/\` (up) and `\/` (down) convert between them.

**Automatic Amortized Resource Analysis (AARA)**
→ Type-based technique for statically bounding gas consumption. Each process has "potential" (budget). Operations consume potential. Type system ensures non-negative. Inference via LP solver.

**Potential annotations in Nomos**
→ `|{q}> A` = send q potential units along with channel. `<{q}| A` = receive q potential units. `*` = infer automatically. Enables gas bound inference.

**Process modes in Nomos**
→ asset: purely linear, for assets/private data. contract: shareable, in shared phase. transaction: issued by users. Mode determines structural rules available.

**Manifest deadlock-freedom (Balzer et al. 2019)**
→ Solves deadlock in shared session types using "worlds" (abstract locations) with partial order. Processes must acquire in ascending world order, preventing cycles.

---

## Adjoint Logic & Multi-Type Connections

**Nomos's /\ and \/ modalities**
→ `/\ A` = acquire (linear → shared), `\/ A` = release (shared → linear). These are the up-shift and down-shift from adjoint logic, same math as multi-type display calculus!

**Adjoint logic (Benton, Reed, Pfenning)**
→ Generalization of LNL to preorder of modes with adjunctions. Each mode is a category. Mode morphisms are adjunctions. !A decomposes as F(U(A)) where F ⊣ U.

**Shared session types from adjoint logic**
→ The shared/linear distinction in Nomos comes from adjoint logic's mode separation. `/\` and `\/` are the counit/unit of the adjunction. Same structure as CALC's persistent_ctx/linear_ctx!

**Rast (Das & Pfenning)**
→ Extends Nomos with arithmetic refinements. Ergometric types track work (sequential complexity). Temporal types track span (parallel complexity). Enables automatic complexity bounds.

---

## Session Types + Authorization

**Session types vs Authorization logic**
→ Session types: WHAT protocol must be followed (communication order). Authorization logic: WHO can make assertions (principals). Different concerns, same research group, potential unification.

**Potential unification of session types and authorization**
→ Principals as process identities. `A says φ` as "A offers channel of type φ". `speaks for` as channel delegation. Both have linear/exponential distinction. Open research direction!

**Move language vs Nomos**
→ Move: linear types only, no session types, no dynamic dispatch (prevents re-entrancy), manual gas, sequential. Nomos: session types + linear, acquire-release for re-entrancy, automatic gas, concurrent. Move simpler, Nomos more expressive.

**CALC's opportunity from Nomos**
→ (1) Proof channels: proof state as session type. (2) Authorization + protocols: principals + communication. (3) Adjoint logic unifies: authorization modalities, session modalities, display calculus rules. All instances of adjunctions!

---

**CALC's opportunity in authorization logic**
→ No existing work combines: (1) graded/weighted authorization, (2) consensus as modality (PoW/PoS), (3) multi-type DC for principals. This is our potential contribution!

---

## Plain Text Accounting

**Plain Text Accounting (PTA)**
→ Bookkeeping methodology using human-readable text files and CLI tools (Ledger, hledger, Beancount). Data is user-owned, tools are read-only, version-controllable.

**The fundamental accounting invariant**
→ The sum of all postings in a transaction must equal zero. Value cannot be created or destroyed, only transferred. This is the "conservation law" of accounting.

**Accounting equation**
→ Assets = Liabilities + Equity. Equivalently: A + L + E + I + X = 0 (with sign conventions). Every transaction maintains this equation.

**T-account**
→ Two-column accounting format: debits on left, credits on right. Mathematically: ordered pair [debit // credit]. The Pacioli group formalizes these as [x // y] with x, y ≥ 0.

**Pacioli Group (Ellerman)**
→ Algebraic structure underlying double-entry bookkeeping. T-accounts as ordered pairs [x // y] of non-negative numbers, with addition [a//b] + [c//d] = [a+c // b+d] and equality via cross-sums: [a//b] = [c//d] iff a+d = b+c. Isomorphic to ℤ (or ℝ).

**Why ordered pairs instead of signed numbers?**
→ (1) Historical: bookkeepers used unsigned numbers. (2) Provenance: separate debit/credit trails. (3) Auditing: verify debits and credits independently. (4) Error detection: cross-sum equality is a checksum.

**Group of differences**
→ Mathematical construction (Hamilton, 19th c.) that creates a group from a monoid by using ordered pairs. The Pacioli group IS the group of differences for non-negative numbers.

**Position (Beancount)**
→ Units of a commodity with optional acquisition info: amount, commodity, cost basis, acquisition date, label. Example: 25 AAPL {$150, 2024-01-15, "lot1"}.

**Inventory (Beancount)**
→ Collection of positions. Map from (Commodity × CostBasis) → Quantity. Augmentation creates new positions; reduction matches existing positions.

**Inventory booking methods**
→ STRICT (exact lot match required), FIFO (first-in-first-out), LIFO (last-in-first-out), NONE (no matching). Determines which lots are reduced when selling.

**Balance assertion**
→ A directive that asserts expected account balance at a specific date. Validation: if assertion fails, error. Used for reconciliation with external statements.

**Pad directive (Beancount)**
→ Automatically inserts balancing transaction to satisfy subsequent balance assertion. Typically pads from Equity:Opening. Useful for starting balances.

**Ledger vs hledger vs Beancount philosophy**
→ Ledger: optimistic, trusts user. hledger: Ledger-compatible, stricter. Beancount: pessimistic, maximum validation, assumes user makes mistakes.

**Beancount's five account types**
→ Assets, Liabilities, Equity, Income, Expenses. Enforced by Beancount for specialized reporting. Ledger/hledger allow arbitrary hierarchies.

**Virtual postings (Ledger/hledger)**
→ Postings in (parentheses) excluded from real balance; [brackets] ensure virtual subset balances. Not supported by Beancount (too lax).

**Conservation in PTA vs Linear Logic**
→ PTA: transaction sums to zero. LL: no weakening (can't discard) + no contraction (can't copy). Both enforce resource conservation.

**Liabilities as linear negation**
→ In PTA, liabilities are "negative assets" — what you owe. This maps to linear negation A⊥ = obligation to provide A. Settlement: A ⊗ A⊥ ⊢ 1.

**Transaction as linear implication**
→ Transfer $100 from A to B: `[A] coin($,100) ⊸ [B] coin($,100)`. The transaction is a proof of this implication.

**PTA's "500 years of applied linear logic"**
→ Double-entry bookkeeping (Pacioli, 1494) implements resource-sensitive accounting. Linear logic (Girard, 1987) formalizes the same ideas. Same math, discovered independently!

---

## Algebraic Accounting

**Grothendieck Group**
→ Universal construction that turns a commutative monoid into an abelian group. For monoid (M, +, 0), form pairs (a, b) representing "a - b", with equivalence (a,b) ~ (c,d) iff a+d = b+c. The integers ℤ are the Grothendieck group of natural numbers ℕ.

**Pacioli Group = Grothendieck Group of ℝ≥0**
→ The Pacioli group (T-accounts [x // y]) is exactly the Grothendieck group construction applied to non-negative reals. This is why accountants could "invent" negative numbers without using negative numbers!

**Accounting as graph theory (Kleppmann)**
→ Accounts = nodes, transactions = directed edges with amounts. Balance = Σ(incoming) - Σ(outgoing). Zero-sum property: total of all balances = 0, because every edge appears twice (once positive, once negative).

**Partition property**
→ For any partition of accounts into sets S₁ and S₂: Σ(balances in S₁) = -Σ(balances in S₂). This is why Assets = Liabilities + Equity works!

**Incidence matrix representation**
→ Rows = accounts, columns = transactions. Entry +1 = debit, -1 = credit. The vector [1,1,1,...] is in the left null space, meaning: for every transaction, debits = credits.

**Linear logic IS the logic of accounting**
→ Conservation = resource-sensitivity. T-accounts = formulas with negation. Transactions = linear implications. Liabilities = linear negation. The parallel is exact!

---

## Girard's Post-Linear-Logic Work

**Geometry of Interaction (GoI)**
→ Semantics for linear logic where proofs are endomorphisms (operators), not morphisms. Cut elimination = operator composition + trace. Setting: traced monoidal categories or C*-algebras.

**GoI and quantum operations**
→ GoI structures overlap with quantum channels (completely positive maps). Subcategories of Int(C) = superoperators on density matrices. Deep connection between proof theory and quantum information.

**Ludics (Girard 2001)**
→ Framework where proofs are interactive strategies in a game between Player (prover) and Opponent (challenger). Meaning arises from interaction, not pre-existing semantics. "From the rules of logic to the logic of rules."

**Designs (in Ludics)**
→ Generalized proofs as sequences of alternating positive/negative actions. Prefix-closed, coherent, terminate positively. Like "focalized proofs without formulas."

**Orthogonality (in Ludics)**
→ Two designs are orthogonal (D ⊥ E) if their interaction converges (reaches daimon †). Validity = having an orthogonal partner. Meaning = interaction patterns.

**Behaviours (in Ludics)**
→ Sets of designs closed under bi-orthogonality: B = B⊥⊥. These are the "formulas" of Ludics — they emerge from interaction patterns, not defined a priori.

**Transcendental Syntax (2011+)**
→ Girard's most radical program: derive logic from computation, not vice versa. "What are the conditions of possibility for logic?" Uses constellations (multisets of clauses) interacting via resolution.

**Four levels of semantics (Girard)**
→ Alethic (truth/models), Functional (functions/categories), Interactive (games), Deontic (normativity/formatting). Each descends deeper into meaning.

**Ludics inverts the usual order**
→ Traditional: Formulas → Proofs → Semantics. Ludics: Interaction → Designs → Behaviours (=formulas). Meaning from use (Wittgenstein).

**Orthogonality as consensus?**
→ Potential CALC insight: D ⊥ E could model "D and E agree" or "parties D and E can interact successfully." Relates to our atomic swap requirement.

---

## Linear Negation as Debt

**Linear negation (A⊥)**
→ In classical linear logic, every formula A has a dual A⊥. Unlike classical ¬A, linear negation is involutive: (A⊥)⊥ = A. Interpreted as: A = having resource, A⊥ = owing resource (debt/obligation).

**Involution of linear negation**
→ (A⊥)⊥ = A. Interpretation: "owing a debt = having an asset." If I owe you an obligation to give you something, that's equivalent (after settlement) to you having it. Matches financial intuition!

**Girard's male/female plug analogy**
→ Negation = complementarity between male and female plugs. A = male plug (provides), A⊥ = female plug (receives). A proof is "equipment" connecting compatible interfaces. Axiom ⊢ A, A⊥ is like an extension cord.

**Linear negation as action/reaction**
→ Girard: "action of type A = reaction of type A⊥". Other dualities: output/input, answer/question, supply/demand, production/consumption.

**De Morgan duality in linear logic**
→ Negation distributes: (A⊗B)⊥ = A⊥⅋B⊥, (A&B)⊥ = A⊥⊕B⊥, (!A)⊥ = ?A⊥. Every connective has a dual. This is why CLL has "perfect" duality unlike intuitionistic logic.

**Linear implication via negation**
→ A ⊸ B = A⊥ ⅋ B. "Consuming A to produce B" is definable from negation and par. The contrapositive A ⊸ B = B⊥ ⊸ A⊥ also holds (transforming demand for B into demand for A).

**Settlement rule: A ⊗ A⊥ ⊢ 1**
→ Having A and owing A cancel out. In accounting: asset + liability = zero net. In linear logic: follows from the axiom/identity rule ⊢ A, A⊥. This IS debt settlement!

**Game-semantic interpretation of A⊥**
→ A = game where Proponent wins. A⊥ = same game with Player/Opponent roles swapped. Debt = being in Opponent role (the one who must respond/provide).

**Session types and linear negation**
→ If channel c has type A on one endpoint, it has type A⊥ on the other. Negation = switching from send to receive perspective. Dual endpoints have dual types.

**Ownership and negation don't commute**
→ [Alice] (A⊥) ≠ ([Alice] A)⊥. The first = "Alice controls an obligation." The second = "Negation of Alice controlling A." For debt, use [Alice] (coin(C,q)⊥) = "Alice's debt."

**Classical vs intuitionistic linear logic on negation**
→ CLL: negation primitive, involutive, full duality. ILL: negation defined as A ⊸ 0, not involutive. CLL better for debt semantics because (A⊥)⊥ = A makes sense for "debt of debt = asset."

**Borrowing as creating debt**
→ borrow(q,C) ⊢ coin(C,q) ⊗ coin(C,q)⊥. Creates both asset (borrowed coins) and liability (debt). Net value: zero. Exactly how accounting works!

---

## Ownership Modalities and Session Types

**Propositions-as-sessions (Caires-Pfenning)**
→ Linear logic corresponds to session-typed π-calculus. A ⊗ B = send then continue. A ⊸ B = receive then continue. A & B = offer choice. A ⊕ B = make choice. Cut elimination = communication.

**Session type correspondence table**
→ Linear Logic ↔ Session Type: (A ⊗ B) ↔ Output, (A ⊸ B) ↔ Input, (A & B) ↔ External choice, (A ⊕ B) ↔ Internal choice, 1 ↔ Close, !A ↔ Server/replicable service.

**Can [Alice] A be expressed as session types?**
→ Partially. Session types capture linearity (ownership exists) but not principal identity (WHO owns). No syntax for "channel owned by Alice". Session types track THAT something is owned, not BY WHOM.

**What overlaps between ownership and session types**
→ Linear resources, ownership transfer (delegation = channel passing), one-time vs reusable (linear vs !A), acquire-release discipline.

**What session types lack for ownership**
→ Principal identity (WHO owns), multi-sig / consensus modalities ([A ∧ B]), authorization reasoning (says, controls, speaks for).

**Delegation in session types**
→ Sending a channel transfers ownership: `send c d` gives d to the receiver. This is like [Alice] A ⊸ [Bob] A. But session types don't track that it was Alice → Bob.

**Acquire-release discipline (Nomos)**
→ Shared channels require acquire before use, release after. Client gets private linear channel during use. Prevents re-entrancy. Like temporary ownership.

**Adjoint logic and modes**
→ Pfenning's adjoint logic has modes (linear, affine, shared) with adjunctions between them. Potential extension: principals as modes. [Alice] A = A at mode M_Alice.

**Multiparty session types (MPST)**
→ Global type specifies full protocol. Projection gives each participant (role) a local type. Roles are like principals but determined by protocol, not ownership modalities.

**Recommendation: keep ownership and session types complementary**
→ Don't reduce one to the other. Session types for protocol/communication. Ownership modalities for principals/authorization. Adjoint logic as potential unifying framework.

---

## Consensus Modalities and Multiparty Session Types

**Composite principals (A ∧ B)**
→ Both principals must agree. `(A ∧ B) says S` = `(A says S) ∧ (B says S)`. Used for multi-sig: both Alice and Bob must consent.

**Composite principal disjunction (A ∨ B)**
→ Either principal suffices. `(A ∨ B) says S` = `(A says S) ∨ (B says S)`. Any-of consent.

**Multiparty Session Types (MPST)**
→ Session types with multiple participants. Global type describes full protocol; projection gives each role a local type. Roles are named but no native "consent" construct.

**MPST global type**
→ Bird's-eye view of protocol: `G = Alice → Bob : transfer { ok: Bob → Alice : ack.end, fail: end }`. Specifies all messages, choices, termination.

**MPST projection**
→ Extracting a participant's local type from global type. G↾Alice gives what Alice sends/receives. Enables type-safe distributed implementation.

**Knowledge of choice problem**
→ In MPST branching, all relevant participants must know which branch was taken. If Alice chooses, Bob learns via message, but Carol may not. Challenge for consensus.

**Choreographic programming**
→ Write protocols as global programs, compile to distributed implementations. Explicit `sync` constructs for coordination. Endpoint projection ensures correctness.

**Consensus as protocol pattern**
→ Encode `[Alice ∧ Bob]` as: Alice proposes → Bob confirms → then proceed. Not a primitive, but expressible. Verbose but works.

**Threshold (k-of-n) in linear logic**
→ `2-of-{A,B,C}` requires exponential encoding: (A∧B) ∨ (A∧C) ∨ (B∧C). Additive connectives don't compactly express "any k of n."

**Ludics orthogonality for consensus**
→ D ⊥ E means designs interact successfully. Potential model: parties agree iff their strategies are orthogonal. Multi-party: D₁ ⊥ D₂ ⊥ ... ⊥ Dₙ.

**MPST lacks authorization reasoning**
→ MPST has roles (WHO participates) but not "says", "speaks for", "controls". Session types describe WHAT protocol, not WHO is authorized.

**Composite principal as primitive**
→ Add `[A ∧ B]` as first-class modality. Rules: `[A] φ ⊗ [B] φ ⊢ [A ∧ B] φ` (introduction), `[A ∧ B] φ ⊢ [A] φ` (elimination).

**Implicit consensus in atomic swap**
→ `[Alice] BTC ⊗ [Bob] ETH ⊸ [Bob] BTC ⊗ [Alice] ETH`. Both must provide their assets. Consensus implicit in tensor structure, not explicit.

**Making consensus explicit**
→ `(Alice says swap) ⊗ (Bob says swap) ⊗ [Alice] BTC ⊗ [Bob] ETH ⊸ ...`. Or: `(Alice ∧ Bob) says swap ⊗ ...`.

**Adjoint logic with principal modes**
→ Extend mode hierarchy: M_Alice, M_Bob, M_AliceAndBob. Mode morphisms as adjunctions. `M_Alice ⊗ M_Bob → M_AliceAndBob`.

**Deadlock freedom = consensus achievability?**
→ MPST's deadlock freedom: well-typed processes progress. Hypothesis: for consensus modalities, this means protocol design guarantees agreement is reachable.

**Additive choice with multiple principals: who chooses?**
→ In `[P] (A & B)`, owner P has internal choice (P decides). In `[P] (A ⊕ B)`, owner P has external choice (counterparty decides). The & and ⊕ are duals: if Alice has &, her counterparty has ⊕. For explicit attribution, use session-type polarity or MPST global types that specify chooser at each branch.

**Options as additive choice**
→ A call option is `[Alice] ((cash ⊸ underlying) & 1)` — Alice owns it, Alice chooses (exercise or let expire). The & gives holder the choice, matching financial semantics.

**Explicit consent via says**
→ For multi-party choice, use explicit authorization: `Alice says offer(A ⊕ B)` (Alice offers, external choice) combined with `Bob says choose(X)` (Bob selects). Or `(Alice says X) ⊗ (Bob says X)` for joint consent.

---

## Adjoint Logic

**Adjoint logic**
→ A formal logic parametrized by a preorder (or 2-category) of modes, where adjoint modalities bridge between modes with different structural properties. Provides generic cut elimination for many substructural and modal logics.

**Mode in adjoint logic**
→ A "kind of truth" with specific structural properties. Each mode m has σ(m) ⊆ {W, C} specifying which structural rules apply. Examples: linear ({}), affine ({W}), relevant ({C}), cartesian ({W,C}).

**Mode preorder**
→ A partial order m ≥ k on modes meaning "a proof at mode k may depend on assumptions at mode m." Must satisfy monotonicity: if m ≥ k then σ(m) ⊇ σ(k).

**Upshift modality (↑ᵏₘ A)**
→ "Lift" A from mode k to mode m (where m ≥ k). The U (right adjoint) in the F ⊣ U adjunction between modes.

**Downshift modality (↓ᵐₖ A)**
→ "Project" A from mode m to mode k (where m ≥ k). The F (left adjoint) in the F ⊣ U adjunction between modes.

**LNL as adjoint logic**
→ Two modes {U, L} with U > L. F = ↓ᵁₗ (Lin), G = ↑ₗᵁ (Mny). The ! modality decomposes as !A = F(G(A)) = ↓ᵁₗ ↑ₗᵁ A. CALC's persistent_ctx/linear_ctx IS this!

**Comonad from adjunction**
→ ↓ᵐₖ ↑ᵏₘ A forms a comonad (like □ or !). Apply downshift then upshift to get back to original mode with comonadic structure.

**Monad from adjunction**
→ ↑ᵏₘ ↓ᵐₖ A forms a monad (like ○ or Moggi's computational monad). Apply upshift then downshift.

**S4 in adjoint logic**
→ Two modes {V, U} with V > U (V = valid, U = true). □A = ↓ᵁᵥ ↑ᵁᵥ Aᵤ. Models Pfenning-Davies judgmental S4.

**Lax logic in adjoint logic**
→ Two modes {U, X} with U > X. ○A = ↑ˣᵤ ↓ˣᵤ Aᵤ. The monad captures computational effects.

**Subexponentials as modes**
→ Subexponentials !ₐA are modes in a preorder. a ≤ b means !ᵦA ⊢ !ₐA. Different modes can have different structural rules.

**Nomos mode shifts**
→ /\\ A = ↑ˢₗ A (acquire: shared → linear), \\/ A = ↓ˢₗ A (release: linear → shared). The acquire-release discipline IS adjoint logic!

**Fibrational framework (Licata-Shulman-Riley)**
→ General framework abstracting substructural/modal logics. Context descriptors as terms from mode theory. Cut admissibility proven once for entire framework.

**What fibrational framework covers**
→ Non-associative, ordered, linear, affine, relevant, cartesian products/implications; bunched logic; n-linear variables; □ and ! and subexponentials; monadic ♦ and ○; adjoint F and G.

**Graded adjoint logic (Eades-Orchard)**
→ Combines adjoint logic with graded modalities □ᵣA where r is from a semiring. Enables tracking quantities, sensitivity, security levels.

**Structural rules per mode**
→ Each mode m has σ(m) ⊆ {W, C}. Weakening (W): assumption need not be used. Contraction (C): assumption can be used multiple times. Linear mode has neither.

**CALC's Bang_L is the F modality**
→ The "special case" for !A in prover.js IS the ↓ᵁₗ modality crossing from Linear to Cartesian. It's the correct adjoint logic implementation!

**Cut elimination in adjoint logic**
→ Follows by induction on (Aₘ, D, E) where D, E are premise proofs. The mode structure ensures structural compatibility. Generic for all modes.

**Principal modes (speculative)**
→ Could principals be modes? M_Alice, M_Bob with shared ≥ alice, shared ≥ bob, alice ⊥ bob. Mode morphisms = delegation. Research direction.

**What adjoint logic doesn't handle**
→ Principal identity (WHO owns), composite principals (A ∧ B — no mode products), authorization (says, speaks for — different judgment), threshold (k-of-n).

**Layered approach for CALC**
→ Layer 1: Adjoint logic (structural) — already have. Layer 2: Principal modes (extension). Layer 3: Authorization logic (orthogonal). Layer 4: Consensus (protocol encoding).

---

## Adjunctions (Categorical and Proof-Theoretic)

**Adjunction (categorical)**
→ A pair of functors F : C → D (left adjoint) and G : D → C (right adjoint) with natural bijection Hom_D(F(X), Y) ≅ Hom_C(X, G(Y)). Written F ⊣ G.

**Unit of an adjunction (η)**
→ Natural transformation η : Id_C → G ∘ F. Embeds X into G(F(X)). "Canonical map from X into the image of the round-trip."

**Counit of an adjunction (ε)**
→ Natural transformation ε : F ∘ G → Id_D. Projects F(G(Y)) back to Y. "Canonical map collapsing the round-trip."

**Triangle identities (zig-zag)**
→ (ε_F) ∘ (F η) = Id_F and (G ε) ∘ (η_G) = Id_G. In string diagrams: "pull the zig-zag straight."

**Free ⊣ Forgetful adjunction**
→ Paradigmatic example. Free(X) is left adjoint to Forgetful(M). "To define homomorphism from free object, just say where generators go."

**Product ⊣ Diagonal ⊣ Coproduct**
→ + ⊣ Δ ⊣ ×. Coproduct is left adjoint to diagonal; product is right adjoint. Limits are right adjoints; colimits are left adjoints.

**Exponential adjunction (currying)**
→ (−) × A ⊣ (−)^A. "Morphisms X × A → B correspond to morphisms X → B^A." Counit is evaluation; gives curry/uncurry isomorphism.

**RAPL (Right Adjoints Preserve Limits)**
→ If G is a right adjoint, G preserves all limits. Dually: left adjoints preserve colimits (LAPC). "Right adjoints are continuous."

**Adjoint functor theorem**
→ Converse of RAPL: a functor preserving limits that satisfies solution set condition has a left adjoint. Crucial for constructing adjoints.

**Every adjunction induces monad and comonad**
→ Given F ⊣ G: monad T = G∘F with unit η, multiplication Gε F. Comonad D = F∘G with counit ε, comultiplication Fη G.

**Kleisli category**
→ For monad T: objects same as C, morphisms X → T(Y). The "free T-algebra" adjunction. Initial among all adjunctions inducing T.

**Eilenberg-Moore category**
→ For monad T: objects are T-algebras (X, α : T(X) → X), morphisms are algebra homomorphisms. Terminal among all adjunctions inducing T.

**Galois connection**
→ Adjunction for posets. Monotone f : P → Q and g : Q → P with f(x) ≤ y iff x ≤ g(y). Same math as adjunction, simpler setting.

**Residuation**
→ In algebra: a · b ≤ c iff a ≤ c/b iff b ≤ a\\c. Right and left residuals are adjoints to multiplication. Foundation of substructural logics.

**Deduction theorem as adjunction**
→ Γ, A ⊢ B iff Γ ⊢ A → B. This IS the adjunction (−) ⊗ A ⊣ A → (−). Implication is right adjoint to conjunction/tensor.

**Display postulates as adjunctions**
→ X ; Y ⊢ Z iff X ⊢ Y > Z. Structural connectives ; and > are adjoint. Belnap's display calculus encodes residuation.

**! = F ∘ G (LNL decomposition)**
→ F : Cart → Lin embeds cartesian into linear. G : Lin → Cart extracts cartesian. Comonad F∘G IS the ! modality.

**Curry-Howard-Lambek**
→ Three-way correspondence: Logic ↔ Type Theory ↔ Category Theory. Every fundamental datatype (products, sums, functions) arises from an adjunction.

**State monad from adjunction**
→ State S A = S → (A, S). Arises from (−) × S ⊣ (−)^S. Product with S and exponential with S are adjoint.

**String diagrams for adjunctions**
→ Draw L going up, R going down. Unit η is a cup (∪), counit ε is a cap (∩). Triangle identities = straightening zig-zags.

**Adjunction checklist for CALC modalities**
→ When designing new modality: Is there residuation? What are unit/counit semantically? Do triangle identities hold? What monad/comonad does it induce?

---

## Ludics and Orthogonality

**Ludics (Girard 2001)**
→ Framework where logic emerges from interaction. Objects (designs) interact via normalization; types (behaviours) emerge from orthogonality. "From the rules of logic to the logic of rules."

**Design (in Ludics)**
→ Abstraction of a proof retaining only interaction-relevant info. Alternating tree of positive/negative actions at addresses (loci), possibly ending in daimon (†). Like a strategy in a game.

**Positive action (in Ludics)**
→ Player makes a move: chooses a locus ξ and ramification I (set of subaddresses). Active, non-deterministic phase. E.g., making a choice or sending a message.

**Negative action (in Ludics)**
→ Player awaits Opponent's move: passive, deterministic. Records what was received and plans response.

**Daimon (†)**
→ Terminal signal in Ludics indicating successful interaction/acceptance. Like "I accept" or "I give up." Convergence = reaching daimon.

**Polarity in Ludics**
→ Designs strictly alternate positive/negative phases (focalization). Positive = active (⊗, ⊕, ∃), negative = passive (⅋, &, ∀). Determines turn order.

**Orthogonality in Ludics**
→ D ⊥ E iff [[D, E]] = † (interaction converges to daimon). Means D and E "fit together" — compatible strategies. Foundational relation.

**[[D, E]] = interaction result**
→ Normalization (cut elimination) between designs D and E. Alternates moves until: daimon (success), or no matching move (divergence/deadlock).

**Orthogonal set A⊥**
→ A⊥ = { E | ∀D ∈ A. D ⊥ E }. All designs that successfully interact with every element of A. The "set of tests" for A.

**Behaviour (in Ludics)**
→ A set of designs G that is bi-orthogonally closed: G = G⊥⊥. These ARE the types/formulas of Ludics — they emerge from interaction patterns.

**Internal completeness (Ludics)**
→ For well-behaved constructions: (A ⊗ B)⊥⊥ = A ⊗ B. No need for bi-orthogonal closure — the construction is already complete. Key property of Ludics.

**Convergence vs divergence**
→ Convergence: interaction reaches †, parties "agree." Divergence: interaction fails (no matching move), parties "disagree" or deadlock.

**Designs as dialogue**
→ D and E are dialogue strategies. D ⊥ E means they can complete a dialogue (one eventually accepts via †). Lecomte-Quatrini: "speakers go together towards agreement."

**L-nets (Faggian-Maurel)**
→ Extension of Ludics for concurrent interaction. Designs become graphs (not trees), interactions produce partial orders allowing parallelism. Model for MALL.

**Ludics and π-calculus (Faggian-Piccolo)**
→ Ludics is a model for finitary linear π-calculus. Addresses ≈ channels. Ludics discipline on names ≈ internal π-calculus. Full completeness and full abstraction.

**Orthogonality as consensus**
→ Hypothesis: [A ∧ B] φ can be modeled as D_Alice ⊥ D_φ ∧ D_Bob ⊥ D_φ. Both parties have compatible strategies for φ. Consensus = mutual orthogonality.

**Atomic swap as orthogonality**
→ Alice: "give BTC if receive ETH". Bob: "give ETH if receive BTC". These strategies are ORTHOGONAL — they fit together. D_Alice ⊥ D_Bob iff swap succeeds.

**Gap: n-ary orthogonality**
→ Standard Ludics orthogonality is binary (D ⊥ E). Consensus needs n-party: D₁ ⊥ D₂ ⊥ ... ⊥ Dₙ. Not naturally defined — pairwise ≠ global.

**Coherence generalizes duality (Carbone et al.)**
→ MCP introduces n-ary compatibility: coherent(T₁,...,Tₙ) means types can jointly participate. Generalizes binary duality from CLL. MCut rule for composition.

**MCut rule**
→ Generalized cut for multiparty: compose n processes with coherent types. `Γ₁ ⊢ T₁ ... Γₙ ⊢ Tₙ coherent(T₁,...,Tₙ) / Γ₁,...,Γₙ ⊢ ·`. Ensures deadlock freedom.

**Krivine realizability**
→ Related orthogonality framework. t ⊥ π iff t ⋆ π ∈ ⊥⊥ (pole). Truth value |A| = {t | ∀π ∈ ‖A‖. t ⊥ π}. Pole is parameter controlling "success."

**Pole (in realizability)**
→ Parameter ⊥⊥ of realizability model — set of "good" processes closed under anti-evaluation. Different poles = different notions of success/agreement.

**Behaviours as authorization policies**
→ Open question: Can authorization policies be behaviours? policy_P = {D | D realizes P's authorization}. If policy_P = policy_P⊥⊥, it's "closed under tests."

**Transcendental Syntax**
→ Girard's later program: derive logic from computation. Uses "stellar resolution" (logic-free). Constellations = multisets of clauses. Too foundational for immediate CALC use.

---

## Principal-Indexed Modes and Authorization

**Agent-indexed adjoint pairs (Sadrzadeh-Dyckhoff)**
→ Algebraic semantics using lattices with agent-indexed families of adjoint pairs. Left adjoints express agents' uncertainties, right adjoints express beliefs. Applied to multi-agent epistemic reasoning.

**IIK (Indexed Intuitionistic K)**
→ Intuitionistic propositional logic + "K says ·" modality for each principal K. Foundation for authorization logics. Satisfies necessitation and K axiom.

**DTL₀ authorization logic**
→ Relativizes reasoning to principal beliefs. Includes "conceited" axiom: principals believe they believe. Translates to modal S4: `A says φ` → `□_A φ`. Sound and complete for Kripke semantics.

**Composite principal (conjunction): (A ∧ B) says φ**
→ Equivalent to (A says φ) ∧ (B says φ). Both must affirm. Intersection semantics: belief in group's worldview iff in intersection of all members' worldviews.

**Composite principal (disjunction): (A ∨ B) says φ**
→ Equivalent to (A says φ) ∨ (B says φ). Either suffices. BUT: "or-groups are not sound with respect to IMP-E" — requires special proof rules.

**Local reasoning property in authorization logic**
→ From "A says false" can derive "A says G" for any G, BUT cannot derive "B says G" for different B. Inconsistency is contained within principal's worldview.

**Two parallel structures: Adjoint Logic vs Authorization Logic**
→ Modes vs Principals, Mode preorder vs Principal hierarchy (speaks for), Structural properties vs Epistemic properties, Adjoint modalities (↑/↓) vs Says modality (□_A). These are orthogonal — they combine multiplicatively.

**Why mode products are hard**
→ Adjoint logic modes form a preorder, not monoidal category. Tensor product m ⊗ n would need: morphisms from m and n, associativity, compatibility with existing morphisms. Major extension required.

**Two-layer architecture for CALC**
→ Layer 1: Adjoint logic (structural: modes U/L/S with ↑/↓). Layer 2: Principal index (epistemic: [Alice], [Bob], says). Combine: [Alice] (↓ᵁₗ A) = Alice controls linear resource lifted from cartesian.

**Formula-level vs mode-level composite principals**
→ Formula-level: [Alice ∧ Bob] A (supported). Mode-level: A at mode (Alice ⊗ Bob) (not supported in current theory). Workaround: keep composites at formula level.

---

## Pacioli Group and Linear Logic

**Pacioli group is NOT related to linear logic additives**
→ Additives (⊕, &) are about CHOICE between alternatives. Pacioli group [x // y] tracks BOTH debit AND credit simultaneously — this is MULTIPLICATIVE structure: [x // y] ≈ x ⊗ y⊥.

**Pacioli group corresponds to tensor with negation**
→ [x // y] ≈ x ⊗ y⊥ where x = asset/debit (positive resource), y⊥ = liability/credit (obligation). The inverse -[x // y] = [y // x] ≈ y ⊗ x⊥ flips which side is the obligation.

**Grothendieck group vs linear negation**
→ Conceptually similar (both "add inverses") but structurally different. Grothendieck: element-level, monoid → group (left adjoint construction). Linear negation: formula-level, A → A⊥ (built-in involution in star-autonomous categories).

**Pacioli group as grading ring**
→ Key insight: Pacioli group should be a GRADING structure for graded linear logic, not formula structure. □_{[x//y]} A = "have x of A, owe y of A". Connects Ellerman's accounting to Granule-style graded types.

**Why T-accounts aren't additive connectives**
→ [x // y] + [a // b] = [x+a // y+b] — both sides accumulate in parallel. A ⊕ B means "choose x OR y" (external choice). A & B means "offer choice" (internal choice). T-accounts track both simultaneously, not either/or.

---

## Multi-Party Debt and CLL Extension

**Multi-party debt: creditor specification problem**
→ `[Alice] coin(BTC, q)⊥` = "Alice owes q BTC" but doesn't specify TO WHOM. Solutions: (A) explicit predicate `debt(Alice, Bob, BTC, q)`, (B) directed ownership `[Alice → Bob]`, (C) channel endpoints from session types, (D) composite principal `[Alice ⊸ Bob]`.

**Session types dual endpoints for debt**
→ In session types, channel c has type A on one endpoint, A⊥ on the other. The channel itself specifies the bilateral relationship between parties. Duality ensures endpoints have matching actions.

**Recommended CALC debt syntax**
→ Use explicit predicate: `debt(debtor, creditor, commodity, quantity)`. Simple, clear, requires no new logic. Settlement: `[Alice] coin(BTC, q) ⊗ debt(Alice, Bob, BTC, q) ⊸ [Bob] coin(BTC, q)`.

**CLL vs ILL for CALC: tradeoffs**
→ CLL: clean debt semantics via involutive negation, full De Morgan duality, richer protocols. BUT: harder proof search, non-deterministic cut-elimination, more complex. Recommendation: stay ILL short-term, add negation only if needed.

**Channel passing in session types**
→ Session types support delegation by sending channels: `send c d` transfers ownership of d. This is like ownership transfer `[Alice] A ⊸ [Bob] A`. Connection to "speaks for": passing a channel grants the recipient authority to act on that channel.

**Channel delegation vs speaks-for**
→ Channel delegation: transfers ownership of specific communication endpoint (linear, dynamic). Speaks-for: transfers general authority as principal (can be persistent). Related but not identical — channel passing is "speaks for" in a specific, linear context.

**Threshold modalities: no compact representation**
→ [k-of-{A,B,C,...}] φ expands combinatorially: [2-of-{A,B,C}] = ([A∧B] ∨ [A∧C] ∨ [B∧C]). C(n,k) terms — exponential. No compact modal representation found. Use predicate: `threshold(k, principals, φ)`.

**Global types as authorization policies**
→ MPST global types specify "who sends what to whom" = authorization policy. Projection → local types = local permissions. Deadlock freedom = consensus achievable. Strong parallel but different focus: MPST = protocol correctness, Auth = access control.

**Ownership transfer is NOT an adjunction**
→ Transfer `[Alice] A ⊸ [Bob] A` is a linear implication (morphism), not an adjunction-derived operation. Ownership `[P]` is an index over principals, not a mode. Better model: fibration over principals, with transfer as reindexing.

**Fibration model for ownership**
→ Base category: Principals. Fiber over P: Resources owned by P. Transfer: Reindexing along principal morphisms. This is indexed category / fibration structure, not adjoint logic modes.

---

## Fibrations

**Grothendieck fibration**
→ Functor p: E → B where fibers E_b depend pseudofunctorially on b ∈ B. Key property: cartesian morphisms exist — these are "universal lifts" that capture how fibers change along base morphisms.

**Cartesian morphism**
→ A morphism in E that is the "best" lift of a base morphism f: a → b. Universal property: any other lift factors through it uniquely. Captures reindexing/pullback structure.

**Fibration ↔ Indexed Category equivalence**
→ Fib(B) ≃ [B^op, Cat]. Fibrations over B correspond to contravariant pseudofunctors B → Cat. The Grothendieck construction converts between views.

**Why fibrations for ownership**
→ `[Alice] A` is not "A at mode Alice" but "A in fiber over Alice." Transfer `[Alice] A ⊸ [Bob] A` = reindexing along authority morphism. Fibrations give proper categorical semantics.

**Fibrations ≈ Dependent Types (Lawvere)**
→ Base category ≈ context of type variables. Fiber over b ≈ types depending on b. Cartesian morphisms ≈ substitution. This is the Lawvere correspondence.

---

## Resource Term Semantics

**Proof-relevant vs proof-irrelevant types**
→ Proof-irrelevant: only care THAT something is provable. Proof-relevant: distinct proofs are tracked and meaningful. For accounting, we want proof-relevant — proofs carry provenance.

**Terms as audit trails**
→ Term t : [Alice] coin(BTC, 0.5) could encode: how Alice got this coin, from whom, when, what authorizations. The Calculus of Audited Units (CAU) formalizes this: "expressions carrying a trail of past computation history."

**Realizability semantics**
→ "The meaning of a proposition is given by what counts as evidence for it." A realizer of A is computational evidence that A holds. For ownership: realizer = transaction hash, merkle path, or signature chain.

**Phase semantics vs proof semantics in linear logic**
→ Phase semantics: formula ↦ set of contexts that prove it. Proof semantics: meaning given to proofs directly. For CALC we want proof semantics — the proof itself carries information.

---

## Financial Primitives in Linear Logic

**Options map to additive conjunction (&)**
→ call_option : (cash(strike) ⊸ underlying) & 1. The & means holder CHOOSES: exercise or let expire. Additive connectives model choice.

**Futures need temporal modality**
→ Future is OBLIGATION at specific time: A ⊸_{at_expiry} B. CALC needs temporal extension: □_{until}, ◇_{after}, ⊸_{at}.

**Swaps are iterated atomic swaps**
→ Already have atomic swap. Multi-period swap = sequence of atomic swaps linked by schedule. Fits naturally.

**Leverage involves debt**
→ position ⊗ debt(borrower, lender, amount). Liquidation when collateral insufficient. Needs debt type + external price oracle.

**Order book as collection of offers**
→ Bids: cash ⊸ asset. Asks: asset ⊸ cash. Matching finds compatible offers. Order book = (bid₁ & bid₂ & ...) ⊗ (ask₁ & ask₂ & ...).

**Peyton-Jones contract combinators**
→ ~10 combinators: zero, one(k), give, and, or, cond, scale, when, anytime, until. Many map to CALC: and = ⊗, or = & or ⊕. But scale, when, cond need oracles/temporal.

---

## Logical Frameworks and Typed DSLs

**LF (Edinburgh Logical Framework)**
→ Dependently typed lambda calculus for representing deductive systems. Key methodology: judgments as types, derivations as terms. `of : tm -> tp -> type` declares typing as a type family.

**CLF (Concurrent Linear Framework)**
→ Extension of LF with linear types and monadic encapsulation `{A}`. Supports both backward chaining (Prolog-style) and forward chaining (multiset rewriting). Celf is the implementation.

**Celf syntax elements**
→ `A -> B` (persistent function), `A -o B` (linear implication), `A * B` (tensor), `{A}` (monadic suspension), `!A` (persistent), `<-` (backward premise). Rules: `name : head <- premise1 <- premise2.`

**Adequacy in LF**
→ Correctness criterion: LF representation is adequate iff bijection between object-language entities and LF terms of corresponding type. Ensures encoding is faithful.

**Higher-Order Abstract Syntax (HOAS)**
→ Represent object-language binding using LF function types: `lam : tp -> (tm -> tm) -> tm`. Substitution is inherited from LF—no explicit substitution needed.

**Twelf metatheory checker**
→ Twelf can verify metatheorems about encodings: type preservation, progress, etc. Uses coverage checking and termination analysis.

**Ohm parser**
→ PEG-based JS parser with separate grammar/semantics. Key features: left recursion support, online visualizer, excellent error messages. Syntax: `Rule = "pattern"` in `.ohm` file.

**tree-sitter**
→ Incremental parsing library with grammar → C parser. Official Zig bindings exist. Used by editors (VSCode, Neovim). Best for production + editor integration.

**Chevrotain**
→ Fast JS parser combinator DSL. No code generation—grammar in JS classes. Best performance but verbose. Maintained by SAP.

**Shallow vs deep embedding**
→ Shallow: DSL constructs map directly to host language (TypeScript types). Deep: DSL has its own AST, type checker, interpreter. Deep = more control, more work.

**Lean4 syntax categories**
→ `declare_syntax_cat name` creates new category. `syntax pattern : category` adds rules. Precedence via numbers. Macros process syntax via pattern matching.

---

## Content-Addressing and Hash Consing

**Hash consing**
→ Technique ensuring structurally identical terms share memory. Each unique (constructor, child_ids...) tuple gets a unique integer ID. Equality becomes O(1) integer comparison. Used in: BDDs, SAT/SMT solvers, functional compilers. Key paper: Filliâtre & Conchon 2006.

**Unique table (BDD)**
→ Hash table mapping (variable, low_child_id, high_child_id) to unique node ID. Ensures canonical representation: two BDD nodes with same structure are the same node. Makes equivalence check O(1).

**Computed table (BDD)**
→ Cache mapping (operation, arg_ids...) to result_id. Avoids redundant computation of operations on previously-seen arguments. Memoization for BDD operations.

**Content-addressed storage**
→ Data identified by hash of content, not by location/name. Same content → same address. Used by: Git (commits), IPFS (files), Unison (code definitions). Enables deduplication and immutable references.

**De Bruijn indices**
→ Variable representation using depth to binder, not names. `λx.λy.x` → `λ.λ.1` (index 1 = skip 1 binder). Eliminates alpha-equivalence problem: α-equivalent terms become syntactically identical.

**Shift operation (de Bruijn)**
→ Increment indices above a threshold when going under a binder. Required for substitution: when substituting into a lambda body, shift free variables in the substituted term.

**Locally nameless representation**
→ Hybrid: bound variables as de Bruijn indices, free variables as names. `λx. x y` → `λ. 0 y`. Combines α-equivalence benefits (indices) with readability (named free vars).

**Opening (locally nameless)**
→ Operation replacing outermost bound variable (index 0) with a name or term. "Open" a binder to work with its body.

**E-graph (equality graph)**
→ Data structure representing equivalence classes of terms. E-class = set of equivalent e-nodes. E-node = operator with e-class children. Union-find tracks equivalences. Used in equality saturation (egg).

**Equality saturation**
→ Optimization technique: apply ALL rewrites to an e-graph until fixpoint, then extract best equivalent term. Avoids phase-ordering problem. Framework: egg.

**Structural sharing**
→ Immutable data structures share unchanged subtrees. Update creates new path to root but reuses siblings. O(log n) update with O(1) unchanged subtrees. Used by: Immutable.js, Clojure.

**O(1) equality via interning**
→ Assign unique integer ID to each unique structure. Two structures equal iff same ID. ID assignment via hash table lookup on construction. No need to compare structures recursively.

**Weak reference for hash consing**
→ WeakRef allows GC of unreferenced interned nodes. Without weak refs, interned nodes live forever. In JS: WeakRef + FinalizationRegistry. Caveat: GC timing is non-deterministic.

**Content hash vs identity hash**
→ Content hash: cryptographic hash of structure (SHA3, etc). Identity hash: cheap integer ID via interning. Use identity for runtime equality (O(1)), content hash for serialization/dedup (O(n) but cacheable).

**CALC current bottleneck: toString() equality**
→ `mgu.js:23`: `t0.toString() === t1.toString()` is O(n). Called frequently during proof search. Fix: use interned node IDs for O(1) equality.

**CALC current bottleneck: sha3 for context**
→ `sequent.js:255`: `sha3(ast.toString())` called on every context insertion. O(n) per formula. Fix: use interned node ID as context key directly.

**Arena allocator**
→ Memory allocator that frees all allocations at once. Fast allocation (bump pointer), no individual frees, batch deallocation. Ideal for proof search: allocate during search, free entire arena when done. Zig: `std.heap.ArenaAllocator`.

---

## Benchmarking and Performance

**Micro-benchmarking**
→ Measuring performance of small, isolated code units (single functions, operations). Requires careful methodology: warmup for JIT, statistical sampling, isolation from system noise. Pitfall: results may not reflect real-world performance in context.

**Macro-benchmarking**
→ Measuring performance of larger system components or complete operations. More realistic but harder to isolate bottlenecks. For CALC: full proof search benchmarks are macro, individual operation benchmarks are micro.

**Benchmark.js**
→ Popular JavaScript benchmarking library. Provides statistical analysis (ops/sec, margin of error), handles warmup automatically, supports async operations. Usage: `suite.add('name', fn).run()`.

**Node.js perf_hooks**
→ Native performance measurement API. `performance.now()` for high-resolution timestamps (μs). `performance.mark()/measure()` for timing spans. Monotonic clock, unaffected by system time changes.

**process.hrtime (Node.js)**
→ Nanosecond-precision timing. Returns [seconds, nanoseconds] tuple. Use `hrtime.bigint()` for simpler BigInt nanoseconds. Best for micro-benchmarks requiring maximum precision.

**JIT warmup**
→ Run code 10-100 times before measurement to allow V8 to optimize (Ignition → Sparkplug → Maglev → TurboFan). Cold code runs slower due to interpretation and compilation overhead.

**V8 optimization tiers**
→ Ignition (interpreter) → Sparkplug (fast baseline) → Maglev (mid-tier JIT) → TurboFan (optimizing JIT). Each tier is faster but takes longer to compile. Hot paths get promoted through tiers.

**Monomorphic vs polymorphic call sites**
→ Monomorphic: always same object shape, fastest (inline caching works). Polymorphic: few shapes, slower (megamorphic IC). Megamorphic: many shapes, slowest (generic lookup). Keep benchmarked code monomorphic.

**Hidden classes (V8)**
→ V8's internal structure describing object shape (property names, order, types). Objects with same hidden class share optimized code. Adding properties in different order creates different hidden classes → deoptimization.

**Dead code elimination**
→ Compiler removes code whose results are unused. In benchmarks, must ensure results are used (return, store to variable) or computation may be eliminated, making benchmark meaningless.

**GC interference in benchmarks**
→ Garbage collection pauses can skew timing. Mitigation: run with `--expose-gc`, call `global.gc()` between runs, use many samples, report median not just mean.

**Statistical significance in benchmarking**
→ Single timing meaningless due to variance. Need: multiple samples, mean/median/stddev, confidence intervals, p95/p99 percentiles. Benchmark.js provides ops/sec ±error%.

**Amortized complexity**
→ Average cost per operation over many operations. Relevant when some operations are expensive but rare (e.g., array resize). For hash tables: O(1) amortized despite occasional O(n) rehash.

**CALC proof search complexity**
→ O(b^d · n²) where b = branching factor, d = proof depth, n = formula size. The n² comes from unification. With interning: O(b^d · n).

**Hot path**
→ Code executed frequently during normal operation. Optimize hot paths first — Amdahl's law. For CALC: mgu(), substitute(), context operations are hot paths.

**Profiling vs benchmarking**
→ Profiling: find WHERE time is spent (flame graphs, CPU sampling). Benchmarking: measure HOW FAST specific code runs. Profile first to find hotspots, then benchmark alternatives.

**Flame graph**
→ Visualization of profiling data. X-axis = time or samples, Y-axis = call stack depth. Wide bars = hot functions. Node.js: `0x` tool, `--prof` flag, or Chrome DevTools.

---

---

## CLF/Celf/Ceptre

**CLF (Concurrent Logical Framework)**
→ Dependent type theory extending LLF with synchronous connectives (⊗, 1, !, ∃) inside a lax monad {A}. Supports both backward and forward chaining. Type theory notation: λΠ⊸&⊤{∃⊗1!}.

**Lax monad {A} in CLF**
→ Monadic type separating computation modes. Outside: backward chaining (Prolog-style). Inside: forward chaining (multiset rewriting). The monad contains synchronous connectives and runs until quiescence.

**Quiescence**
→ Termination criterion for forward chaining: no more rules can fire. Dual concept: saturation (no NEW facts can be derived, avoids infinite loops with persistent facts).

**Synchronous connectives**
→ ⊗, 1, !, ∃. Require let-style elimination (commuting conversions). Positive polarity. Confined inside the lax monad in CLF. Forward chaining uses committed choice (no backtracking).

**Asynchronous connectives**
→ ⊸, &, ⊤. Direct elimination forms. Negative polarity. Outside the monad, use backward chaining with backtracking (Prolog-style).

**Celf**
→ Reference implementation of CLF in Standard ML. Proof search: backward chaining outside monad, forward chaining inside. Directives: #query (backward), #exec/#trace (forward).

**Celf #exec directive**
→ `#exec * {initial_state}` runs forward chaining until quiescence. `#exec 100 {state}` runs max 100 steps. #trace also shows intermediate states.

**LolliMon**
→ Lolli + Monad. Extends Lolli (asynchronous fragment) with CLF's monadic encapsulation. Shows how to combine forward and backward chaining cleanly.

**Ceptre**
→ Simplified CLF for game mechanics and interactive narratives. Forward chaining only. Adds stages for structured quiescence. No dependent types. Created by Chris Martens (CMU).

**Ceptre stages**
→ Named program components with local rules. Each stage runs until quiescence, then stage transitions fire. Enables multi-phase computation: `stage combat = { ... }`, `stage exploration = { ... }`.

**Ceptre syntax**
→ `a * b * c -o d * e` = if a, b, c present, replace with d, e. Capital letters are variables. `#trace _ stage {initial_state}` executes.

**#interactive mode (Ceptre)**
→ Human chooses among applicable rules instead of random selection. Enables turn-based games and debugging.

**Focusing in CLF**
→ Same Andreoli focusing as ILL, but spans both backward and forward phases. Inversion phase applies invertible rules eagerly. Focus phase makes non-deterministic choices.

**Committed choice (forward chaining)**
→ No backtracking on rule application inside the monad. Once a rule fires, its effects are permanent. Contrasts with backward chaining which backtracks on failure.

**Multiset rewriting**
→ Operational model for forward chaining. State is a multiset of facts. Rules consume and produce facts atomically. Multiple rules may be applicable; one is chosen non-deterministically.

**CLF hierarchy**
→ LF (dependent types) → LLF (+ linear ⊸, &, ⊤) → CLF (+ monad {⊗, 1, !, ∃}) → Celf (implementation) → Ceptre (simplified + stages).

**deriv_lax judgment**
→ Hypothetical judgment for forward-chaining mode in CLF. `monad_r` rule switches from `deriv` to `deriv_lax`. The lax judgment enables synchronous connective decomposition.

---

*Last updated: 2026-02-02*
