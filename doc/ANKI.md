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

## How does separation logic's separating conjunction map to linear logic?

Separating conjunction `P * Q` = tensor `P ⊗ Q`. Magic wand `P -* Q` = lollipop `P ⊸ Q`. Empty heap `emp` = unit `1`. The key property: `P * Q` means P and Q hold on **disjoint** heap fragments — exactly tensor's "no implicit sharing."

## What is the frame rule in separation logic and what is its ILL equivalent?

Frame rule: if `{P} C {Q}` then `{P * R} C {Q * R}` (untouched resources R are preserved). In ILL: if a forward rule consumes P and produces Q, other linear facts are structurally preserved. This is automatic in CALC's forward engine — facts not mentioned in a rule's antecedent pass through unchanged.

## What are McCarthy's select/store axioms for memory arrays?

(1) `select(store(a, i, v), i) = v` — read what you wrote. (2) `i ≠ j ⟹ select(store(a, i, v), j) = select(a, j)` — reads at other indices unaffected. (3) `(∀i. select(a,i) = select(b,i)) ⟹ a = b` — extensionality. Foundation of SMT array theory (Z3 QF_ABV).

## How does hevm represent EVM memory symbolically?

Algebraic write-chain: `WriteWord offset value (WriteWord offset2 value2 (ConcreteBuf ""))`. MSTORE prepends a node. MLOAD traverses newest→oldest, checks overlap. Concrete offset exact match = O(1). Symbolic offset = abstract `ReadWord(sym, buf)` term deferred to SMT.

## Why is encoding SMT arrays via store chains 50x slower than via assertions?

EPFL study: `a = store(store(..., i1, v1), i2, v2)` creates deeply nested terms. Z3 must instantiate axioms per nesting level. Instead use `(assert (= (select a i1) v1))` etc. — flat, independent assertions. Also: QF_ABV theory config gives 100x speedup over default.

## What is CALC's structural advantage over hevm/halmos for memory aliasing?

Linear logic's no-contraction means each `mem M` fact exists exactly once — no aliasing by construction. hevm/halmos need SMT reasoning to determine if symbolic address A refers to the same cell as B. CALC's write-log is totally ordered: the question is "which write covers this byte?" — a local traversal, not a global constraint.

## What is the write-log memory model for CALC's EVM executor?

Single linear fact `mem M` where M is a content-addressed write-chain term: `write(offset, value, prev_mem)`. MSTORE wraps a `write` constructor (O(1)). MLOAD triggers a recursive forward-rule traversal (like `concatMemory`) gated by a loli continuation. Three rules encode McCarthy's axioms: `mem_read/hit` (exact match), `mem_read/miss` (`!neq` guard, skip), `mem_read/zero` (empty → 0). No FFI for reads — the rules ARE the semantics.

## Why do per-cell linear memory facts cause spurious branching in symexec?

Two rules needed: `mstore_init` (no existing cell) + `mstore_update` (overwrite). Symexec's `findAllMatches` returns both as applicable. For N MSTOREs: up to 2^N branches. The write-log model avoids this — single `evm/mstore` rule fires unconditionally, wrapping the write into the log term.

## How does MLOAD's loli continuation gate opcode dispatch during memory traversal?

The `evm/mload` rule consumes `pc` but does NOT produce `pc PC'` — it captures it in a loli: `(mem_read_done V -o { pc PC' * ... })`. During the traversal, no opcode rule can fire (they all need `pc`). Only `mem_read/*` rules match. When traversal produces `mem_read_done V`, the loli fires, restoring `pc`, stack, and the original `mem`.

## What happens when MLOAD encounters a symbolic offset in the write-log?

With concrete write `write(0x40, V, M)` and symbolic read offset `calldataload(4)`: `mem_read/hit` fails (structural unification mismatch — different tags). `mem_read/miss` fails (`!neq calldataload(4) 0x40` gets non-ground input → FFI fails). Neither fires → stuck leaf. This is the sound approximation: the logic can't determine the result without knowing the offset. If the offset is a free metavar instead, unification BINDS it to the write offset — naturally forking on possible values.

## Why do McCarthy's word-level axioms fail for EVM's byte-addressable memory?

McCarthy axioms model word-addressable arrays: `select(store(a, i, v), i) = v`. EVM MSTORE writes a 32-byte *window* at `[offset, offset+32)`. Two writes at offsets 0 and 16 produce a 16-byte overlap at `[16, 32)`. The word-level `hit` rule returns the full earlier value at offset 0, ignoring the later write's partial coverage. Need overlap-aware rules: `!no_overlap` to skip disjoint writes, `!overlaps` to detect partial coverage, `splice` to reconstruct bytes from multiple overlapping writes.

## What are the six approaches for byte-addressable symbolic memory in CALC?

(1) **Per-byte decomposition** — MSTORE→32 `write8` nodes. Correct but 32× chain blowup. (2) **Overlap detection rules** — word-level `write` + overlap guards + byte reconstruction. Medium complexity. (3) **Non-overlapping interval tree** — writes split existing intervals. O(log n) reads but order-dependent tree shape. (4) **Hybrid write-log + compaction** — periodic flatten to lookup table. O(1) amortized reads. (5) **Region splitting** (Certora) — static analysis separates memory regions. 120× speedup but needs bytecode analysis. (6) **Lazy splice** — collect overlapping writes as patches during traversal, assemble via `splice` term. Recommended: backward-compatible with Stage 1, minimal FFI, content-addressed sharing preserved.

## What is the `splice` operation in CALC's deferred overlap model?

`splice(Base, ReadOff, WriteOff, WriteVal)` = "take Base as the default 32-byte value, overlay bytes from WriteVal at WriteOff for the portion that intersects `[ReadOff, ReadOff+32)`." For concrete values: byte extraction + concatenation (FFI). For symbolic values: remains as an opaque term capturing the overlap relationship. Applied newest-first during patch assembly.

## How does MCOPY (EIP-5656) work in the write-log model?

An `mcopy(Dest, Src, Size, Prev)` term node in the write-log. Reading through it: if the read range `[R,R+32)` falls within `[Dest, Dest+Size)`, redirect to `[Src+(R-Dest), ...)` in the prior state (`Prev`). This is a pointer redirection within the log — pure ILL rule, no FFI. The source data is resolved by continuing traversal at the redirected offset.
