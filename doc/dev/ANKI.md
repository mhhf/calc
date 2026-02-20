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
