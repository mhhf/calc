# ANKI Flashcards

## What is the Betz/Frühwirth translation (-)^L for CHR user-defined constraints?

User-defined constraint `c(t̄)` → linear atom `c(t̄)` (no bang). Built-in constraint `b(t̄)` → `!b(t̄)` (banged/persistent). Conjunction → tensor (⊗). True → 1.

## What is the CHR simpagation rule translation to ILL?

`r @ H₁ \ H₂ ⟺ G | B` translates to: `H₁^L ⊗ H₂^L ⊗ G^L ⊢ H₁^L ⊗ ∃ȳ.(B^L ⊗ G^L)`. H₁ = kept head (both sides), H₂ = removed head (consumed), G = guard (banged, both sides).

## What does Theorem 4.8 (Betz & Frühwirth 2013) state?

**Soundness:** `S ↦* T ⟹ S^L ⊢_Σ T^L`. Every operational CHR derivation corresponds to a valid ILL deduction. Operational reachability implies logical entailment.

## How does CHR∨ disjunction map to linear logic?

`(B₁ ; B₂)^L = B₁^L ⊕ B₂^L`. Disjunctive rule bodies map to additive disjunction (⊕ / internal choice). The system decides which branch to take.

## Why does CALC use ⊕ (not &) for EVM comparison branching?

⊕ = internal choice = "producer decided" — the system (comparison result) decides which branch. & = external choice = "consumer decided". For `eq(X,Y)`, the comparison is system-determined, so ⊕ is correct.

## What are the three CHR rule types?

**Simplification:** `H ⟺ G | B` (consume all heads). **Propagation:** `H ⟹ G | B` (keep all heads). **Simpagation:** `H₁ \ H₂ ⟺ G | B` (keep H₁, consume H₂). Simpagation subsumes both.

## How does CALC's forward engine map to CHR?

Linear facts = user-defined constraints (removed heads). Persistent facts (!A) = built-in/kept heads. Forward rules = simpagation rules. FFI/backward proving = guard evaluation. ⊕ in consequents = CHR∨ disjunctive bodies.

## What is CHR confluence and when does it hold for CALC?

Confluence = all derivations from a state lead to equivalent final states. CALC's EVM rules are confluent for ground execution (deterministic opcode dispatch). Non-confluent for symbolic execution (⊕ creates choice points, by design).

## What is the CHR propagation history and why doesn't CALC need it?

CHR propagation rules keep their heads — without history, they loop. The propagation history records `(rule, {constraint IDs})` to prevent re-firing. CALC doesn't need this because linear facts are consumed when matched, preventing re-fire.

## What CHR compilation technique is CALC still missing?

**Delta-driven activation** (active constraint / TREAT dirty tracking). CHR activates rules from newly added constraints. CALC re-scans all candidates per step. Adding dirty tracking would skip ~80% of rule evaluations at scale.

## What is state entailment in the Betz/Frühwirth framework?

`S ⊳ S'` iff `S^L ⊢_Σ S'^L`. State equivalence: `S ≡_e T` iff `S ⊳ T` and `T ⊳ S`. State entailment is decidable (Theorem 4.10).

## Why is completeness harder than soundness for CHR ↔ ILL?

Full completeness (every ILL derivation = operational derivation) fails because: (1) ILL allows arbitrary resource shuffling not corresponding to rule application, (2) propagation history restricts operational derivations beyond what logic captures. Completeness holds for specific program classes.

## What is a "prefix firing" in Simmons/Pfenning's cost semantics?

A triple `⟨r, σ, [l₀,...,lₖ₋₁]⟩` — rule r, substitution σ, consumed linear facts. The abstract running time = total prefix firings to quiescence. There exists an interpreter achieving O(1) amortized per firing with appropriate indexing. (Simmons & Pfenning, ICALP 2008)

## What are omega_t and omega_r in CHR?

**omega_t** (theoretical): abstract operational semantics — highly nondeterministic, doesn't fix rule/constraint/matching order. **omega_r** (refined): the implemented semantics — deterministic rule order (textual), active-constraint driven. omega_r is correct w.r.t. omega_t (every omega_r derivation is an omega_t derivation). (Duck et al., ICLP 2004)

## How does Stéphan (ICLP 2018) differ from Betz/Frühwirth?

Betz shows operational derivations *imply* linear logic entailment (translation-based). Stéphan constructs a sequent calculus (ω_l) where CHR derivations *are* proof trees. Each CHR step = an inference rule application. Betz: program = `!r₁ ⊗ !r₂` (banged rules). Stéphan: program = `r₁ & r₂` (additive conjunction = committed choice).

## What are the two sequent forms in Stéphan's ω_l system?

**Non-focused:** `(Γ ▸ Ω_# ◁ S_↑ ⊢ S_↓)` — process goal Ω_# using program Γ, consuming from up-store S_↑, producing down-store S_↓. **Focused:** `(Γ ! Δ ▷ a ◁ S_↑ ⊢ S_↓)` — focused on identified constraint a, trying rules Δ.

## What are the key inference rules in ω_l?

**true** (axiom: goal solved), **⊗_L** (split goal, allocate resources — hidden Cut!), **W** (Weakening: skip rule), **F** (Focusing: select constraint), **↑** (Inactivate: store constraint unchanged), **\⟺** (Apply: fire simpagation rule on focused constraint).

## Why does Stéphan translate program comma as & (not ⊗)?

& (additive conjunction) captures committed choice: rule selection = &L₁ or &L₂. Unchosen rules remain available via Weakening. Betz uses `!r₁ ⊗ !r₂` (bang + tensor) which requires dereliction to access rules. Stéphan's & is more proof-theoretically natural for modeling "pick one rule to apply."

## What are the four hidden nondeterminism sources in CHR?

(1) Don't-care rule selection (committed choice — by design). (2) Don't-know disjunction (CHR∨ — deliberate). (3) Constraint store ordering (multiset → wake-up order unspecified). (4) Multi-headed matching (which constraints chosen from multiset). Stéphan's ω_l^⊗ (sequence store) eliminates sources 3+4.

## What is the Hidden Cut insight in Stéphan's ⊗_L rule?

The Left-elimination-of-conjunction (⊗_L) rule is a hidden use of Cut in linear logic. It splits resources between a "lemma" (left subproof — solve one constraint) and its "use" (right subproof — solve the rest). Both ω_l and ω_l^⊗ eliminate cut instances to linearize derivations.

## What is QCHR and how does it extend CHR?

QCHR (Barichard & Stéphan, TOCL 2025) adds quantified rules: **existential simpagation** (∃ value making body succeed) and **universal simpagation** (∀ values must succeed). Dynamic binder: quantifiers generated at runtime (not statically like QCSP). Enables modeling games with unknown number of moves.

## How does QCHR relate to CALC's symexec?

CALC's symexec = QCHR solving where all branching is universal (∀ — explore everything). ⊕ = existential (system decides). Loli continuations = dynamic binder (rules produced at runtime = quantifiers generated at runtime). `pathVisited` = QCHR tabling/memoization. ω_l^{∃∀} provides the proof framework for execution trees.

## What does Theorem 7 (Stéphan ICLP 2018) state?

The ω_l sequent calculus system is **sound AND complete** w.r.t. the ω_t operational semantics. A CHR goal is solved by program Γ iff there exists an ω_l proof of the corresponding sequent. (Contrast: ω_l^⊗ is only sound, not complete — it's deterministic.)
