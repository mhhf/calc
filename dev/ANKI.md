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

*Last updated: 2026-01-28*
