---
title: "Array Representation Independence: One Relation, Three Presentations, and the FFI Principle as a Theorem"
created: 2026-09-09
modified: 2026-09-09
summary: "arr_get/arr_set are one denotation-determined relation realized by three interchangeable presentations of an array — flat arrlit (FFI O(1) / clause arr_idx O(N)), bit-indexed trie (FFI trieNav / clause trie_get O(log N)), and acons list — plus the FFI as a fourth resolver. Derivability depends only on the array's denotation ⟦·⟧ : ℕ⇀bin, never its presentation, and the trie built from an arrlit denotes it EXACTLY (the zero-fill at intermediate nodes is never navigated to; out-of-bounds fails in every presentation). This makes the FFI principle a theorem for the array case: FFI and clause resolution are admissible implementations of one relation, and the exec/explore representation asymmetry (arrlit vs bytecodeToTrie) is provably benign — a pure O(N)-vs-O(log N) cost choice that cannot change a result. A corollary delimits the design space of TODO_0312: because backchain resolves subgoals against the immutable clause database and not runtime state, any navigable trie must BE the array term (an external index fact is unreachable), so the representation choice is necessarily in-term."
tags: [linear-logic, ffi, engine-metatheory, soundness, optimization, symbolic-execution, adequacy, representation-independence]
category: "Engine metatheory"
paper: "Open disposition. Candidate home: the toolbox paper's boundary-theorem family (alongside THY_0016 grade-0 PE and THY_0039 forced elimination) as 'the array fast path is a certified implementation of one relation'. Self-contained enough to also serve as a short note on verified representation choice in a substructural logical framework (McCarthy arrays × data refinement × content-addressing). The novel angle for a venue is linearity-agnostic representation independence certified by an executable differential over a real symbolic-execution corpus (EVM), not just an on-paper refinement."
unique_contribution: "Three results not stated in prior CALC docs or the literature in this combination: (1) a denotational representation-independence theorem for arr_get/arr_set over a substructural logical framework — derivability is a function of ⟦A⟧ : ℕ⇀bin alone, so the three ground presentations (arrlit, trie, acons) and the FFI resolver are mutually interchangeable, the FFI principle made a theorem for arrays rather than a discipline (extends THY_0039's 'tiered resolver = stack of implementations of one rule' from ∃-forcing to array access); (2) a faithful-construction lemma with the exact reason the bit-trie introduces NO out-of-domain entries — every index's terminal bit-path ends in 1, so the zero values placed at intermediate (0-terminated or later-overwritten) nodes during arrToTrie are never navigated to as a value, giving ⟦arrToTrie(ℓ)⟧ = ⟦ℓ⟧ with equal in-bounds values and coincident out-of-bounds failure, machine-checked by an 11k-lookup differential incl. OOB; (3) the engineering corollary that the exec/explore bytecode asymmetry is provably benign (not a latent soundness gap) and that TODO_0312's external-index refactor is INFEASIBLE — backchain resolves against the clause database, not runtime state, so a navigable trie must be the in-term array, forcing the representation choice to be in-place; the residual content of 0312 is cost-uniformity only."
references:
  - "McCarthy (1962). Towards a mathematical science of computation. IFIP — the read-over-write array axioms; arr_get/arr_set are their substructural realization, and Theorem 2's 'same presentation kind, updated denotation' is select/store adequacy."
  - "Hoare, He & Sanders (1987). Data refinement refined. ESOP — abstraction function α : concrete⇀abstract; ⟦·⟧ here is α, and representation independence is the refinement square for the read/write interface. The linear/persistent split (arrays are used linearly via $-preservation) is outside classical (persistent) data refinement — see doc/big_next.md §4."
  - "Watkins, Cervesato, Pfenning & Walker (2002/2004). A Concurrent Logical Framework (CLF). CMU-CS-02-101 + LFM 2004 — the rules-as-hypotheses adequacy method used for the (⇐)/(⇒) proof shape."
  - "Okasaki (1999). Purely Functional Data Structures — the bit-indexed (Braun/patricia-style) trie whose LSB-first navigation §2 formalizes."
  - "THY_0016 (partial evaluation as cut elimination — grade-0 specialization resolves !_0 arr_get bc PC OP; representation independence is why either resolver is a sound cut)."
  - "THY_0039 (parametric forward chaining — 'the tiered resolver is a stack of implementations of (force), each obligated to the same side condition'; this doc is the arr_get/arr_set instance, side condition = denotational equality)."
  - "THY_0001 (exhaustive forward chaining — the execution-tree judgment whose leaves this theorem shows are presentation-invariant)."
  - "THY_0023 (till metatheory — the sound+complete adequacy template, (⇐) execution→derivation and (⇒) the CLF permutation argument)."
  - "DEF_0046 (representation vs value equality — arrlit, trie, acons are hash-distinct, ⟦·⟧-equal; this theorem lifts value equality from scalars to arrays)."
---

# Array Representation Independence: One Relation, Three Presentations, and the FFI Principle as a Theorem

**Scope.** CALC's FFI principle — *FFI is optimization, clause resolution is semantics* (CLAUDE.md; `doc/documentation/ffi-audit.md`) — is stated as a discipline: every FFI predicate must have backward clauses, and turning FFI off must preserve results. This note discharges the discipline *as a theorem* for the array interface `arr_get`/`arr_set`, the hottest FFI path in the EVM model. An array has three ground **presentations** and, for each, up to two **resolvers** (clause SLD and FFI). We show that derivability of `arr_get`/`arr_set` is a function of the array's *denotation* alone, so all presentations and resolvers are interchangeable; that the bit-trie built from a flat array denotes it *exactly* (no spurious out-of-bounds entries); and, as a corollary, that the exec/explore representation asymmetry recorded against TODO_0312 is provably benign and that its tempting "external trie index" refactor is infeasible for a structural reason. Everything below is pinned by `tests/engine/array-repind-0312.test.js`, the noFFI arm, and `tools/fuzz-ffi.js`.

## 1. Presentations and denotation

Indices and values are binary numerals `bin` (`e`, `o·`, `i·`; `binlit n` the canonical form, DEF_0046). Write ⌊·⌋ : bin → ℕ for the numeric value: ⌊e⌋ = 0, ⌊o K⌋ = 2⌊K⌋, ⌊i K⌋ = 2⌊K⌋+1 (LSB-first). A **presentation** is a ground `arr` term of one of two kinds (`calculus/ill/prelude/arr.ill`):

- **List** — `ae` (empty), `acons(v,t)` written `[v|t]`. The packed **arrlit** is the store normal form of a list; `Store.put` normalizes `acons(h, arrlit) ↔ arrlit` (content-addressed store, DEF_0046), so arrlit and its acons unfolding are one presentation kind with one denotation.
- **Trie** — `tn_nil` (empty), `tn(L,v,R)` (`L,R` tries, `v : bin`).

The **denotation** ⟦A⟧ : ℕ ⇀ bin is the finite partial map:

```
⟦ae⟧ = ⟦tn_nil⟧ = ∅
⟦[v|t]⟧      = {0 ↦ v} ∪ { k+1 ↦ u | (k ↦ u) ∈ ⟦t⟧ }
⟦tn(L,v,R)⟧  : 0 ↦ v;   2m ↦ ⟦L⟧(m) (m ≥ 1);   2m+1 ↦ ⟦R⟧(m) (m ≥ 0)
```

The trie clause `o K → left` / `i K → right` / `e → value` (arr.ill:15–17, 28–30) is exactly this map: even indices route left (halved), odd route right, zero reads the node value. A **dense** array of length N denotes the total map on {0,…,N−1}.

The **resolvers** for the relation `arr_get(A, n̄, v̄)` — where n̄, v̄ are the `bin` encodings of n, v — are: the trie clause branch (`arr_get/trie_*` + `trie_get`, arr.ill:28–30,14–17), the list branch (`arr_get/go → arr_idx`, arr.ill:31–35, applying to arrlit via the store's acons↔arrlit bridge in `matchIdx`), and the **FFI** (`arr_get` in `calculus/ill/lib/ffi/array.js`, handling arrlit O(1) and trie O(log N)). Let ⊢ mean SLD-derivability from the array clauses under *any* resolver.

## 2. Representation independence of reads

**Theorem 1 (arr_get is denotation-determined).** For every ground presentation A, index n ∈ ℕ, and value v ∈ bin:

> ⊢ arr_get(A, n̄, v̄)   ⟺   n ∈ dom⟦A⟧ and ⟦A⟧(n) = v.

Consequently if ⟦A⟧ = ⟦B⟧ then `arr_get(A, n̄, ·)` and `arr_get(B, n̄, ·)` derive the same value or both fail: **presentation is unobservable through arr_get.**

*Proof (sketch).* By presentation kind; the encoding ⌊·⌋ is a bijection bin ↔ ℕ so we induct on n.

*Trie.* Base n = 0: only `arr_get/trie_hit : arr_get (tn L V R) e V` applies, deriving v iff A = tn(_,v,_), i.e. ⟦A⟧(0) = v; if A = tn_nil no clause matches and ⟦tn_nil⟧(0) is undefined. Step n = 2m (m ≥ 1): only `arr_get/trie_left` applies, reducing to `trie_get L m̄ v̄`; `trie_get` has the identical three-clause shape, so the same induction gives derivable iff ⟦L⟧(m) = v = ⟦tn(L,_,R)⟧(2m). Odd n = 2m+1 symmetric via `arr_get/trie_right`/R. One induction covers `arr_get`'s trie branch and `trie_get` because they are the same three clauses.

*List/arrlit.* Only `arr_get/go : arr_get A n̄ v̄ ← arr_idx A e n̄ v̄` applies. `arr_idx A c t v` derives iff the (⌊t⌋−⌊c⌋)-th tail element exists and equals v: `arr_idx/hit : arr_idx [V|W] K K V` fires when current = target (element present), `arr_idx/skip` increments the counter and recurses down the tail. Induction on the list length gives `arr_idx A e n̄ v̄` derivable iff n < len(A) and A[n] = v, i.e. n ∈ dom⟦A⟧ ∧ ⟦A⟧(n) = v. The store's acons↔arrlit bridge (matchIdx PM_COMPOUND decomposition) makes `arr_idx` match the packed arrlit identically to its acons unfolding, which have equal ⟦·⟧ by construction. ∎(sketch)

**Corollary 1.1 (FFI adequacy — the FFI principle for arrays).** The FFI `arr_get` (array.js:107) returns, for ground in-mode arguments, the value at index n of the arrlit (O(1), bounds-checked, line 119) or of the trie (trieNav, O(log N), line 126), and *fails* otherwise. By Theorem 1 this is exactly the clause relation; hence FFI is a sound and complete accelerator and switching it off preserves every result. Machine-checked cross-resolver agreement: `tools/fuzz-ffi.js` and the noFFI adversarial arm (`npm run test:noffi`).

## 3. Faithful construction: the trie denotes the arrlit exactly

`arrToTrie` (array.js:54) builds a trie from a length-N arrlit by inserting indices 0…N−1; `_trieInsert` (array.js:69) writes a placeholder **zero** at any freshly-created *intermediate* node (line 85). A naive worry: does the trie then *define* out-of-domain indices (return 0 where the arrlit is out of bounds), breaking Theorem 1's "both fail" for i ≥ N? It does not.

**Lemma 1 (no spurious entries).** For ℓ = [a₀,…,a_{N−1}] and τ = arrToTrie(ℓ): dom⟦τ⟧ = {0,…,N−1} and ⟦τ⟧(i) = aᵢ. Equivalently ⟦τ⟧ = ⟦ℓ⟧ — equal on [0,N), both failing on [N,∞).

*Proof.* Navigation returns a value only at a **terminal**: the node reached after consuming *all* bits of the index (trieNav returns at `bits === 0n`, array.js:41; clause `trie_get … e V`). The LSB-first bit-path of any n > 0 ends in its most-significant bit, which is 1; so **every index's terminal path ends in 1** (n = 0 terminates at the root). Now consider a node still holding the placeholder zero after all insertions. It was created as a proper prefix p of some inserted index i's path (line 85). Two cases: (a) p ends in 1 — then p = bits(j) for the index j with those bits, and j < i ≤ N−1, so j was also inserted and its insertion overwrote the placeholder with a_j (the `index === 0` branch replaces the value, preserving children, lines 71–78); this node is not zero. (b) p ends in 0 — then p is no index's terminal path, so navigation never reads its value. Hence no surviving zero placeholder is ever returned. For i < N the terminal was written with aᵢ (⟦τ⟧(i) = aᵢ). For i ≥ N: i's terminal path ends in 1 and would have to coincide with, or be a prefix of, some inserted j < N's path for the node to exist; either forces i ≤ j < N, contradiction — so navigation reaches `tn_nil` and fails. ∎

**Pin.** `tests/engine/array-repind-0312.test.js` (Lemma 1) checks trieNav vs flat indexing over 400 random arrays at every index in [0, N+8) — 11 327 lookups, in- and out-of-bounds, **zero mismatches**.

## 4. Writes

**Theorem 2 (arr_set is denotation-determined, in-domain, kind-preserving).** For ground A:

> ⊢ arr_set(A, n̄, v̄, A′)   ⟺   n ∈ dom⟦A⟧,  ⟦A′⟧ = ⟦A⟧[n ↦ v],  and A′ has the same presentation kind as A.

*Proof (sketch).* Same case split. Trie: `arr_set/trie_hit` replaces the node value at n = 0; `arr_set/trie_left`/`right` recurse via `trie_set`, rebuilding the spine and preserving the untouched subtree — so ⟦A′⟧ = ⟦A⟧[n↦v] and A′ is a trie. List: `arr_set/hit` replaces the head at index 0; `arr_set/skip` (with `arr_dec` producing canonical zeros, arr.ill:46–51) rebuilds the prefix and recurses — ⟦A′⟧ = ⟦A⟧[n↦v], A′ a list. Both branches are **in-domain**: no clause extends the array (`arr_set/skip` needs a non-empty tail; `arr_set/trie_*` needs an existing `tn` node), matching n ∈ dom⟦A⟧. FFI arr_set (array.js:138) is the O(1)/O(log N) accelerator of the same relation (bounds-checked at line 150). ∎(sketch)

Read-over-write (McCarthy) follows from Theorems 1–2: `arr_get(A′, n̄, v̄)` with A′ from `arr_set(A,n̄,v̄,_)` derives v; and for m ≠ n the value is unchanged — presentation-independently.

## 5. The engineering corollaries (TODO_0312)

Under FFI the EVM model presents the read-only, `$`-preserved bytecode as an **arrlit** (`bytecode([0x60,…])`); `explore` under FFI-off calls `bytecodeToTrie` to present it as a **trie** so clause resolution is O(log N) instead of `arr_idx`'s O(N); `exec` does neither and stays on the arrlit. This is the asymmetry recorded against TODO_0312.

**Corollary 5.1 (benign asymmetry).** Since the bytecode is used only through `arr_get` (`!arr_get BC PC OP`, evm.ill:521) and is never `arr_set` (immutable code), Theorem 1 gives: exec-on-arrlit, exec-on-arrlit-via-FFI, and explore-on-trie compute identical `arr_get` results, hence identical symbolic-execution leaves. The representation choice is a pure O(N)-vs-O(log N) *cost* decision and **cannot change a result**. Pinned end-to-end by `array-repind-0312.test.js` (all four exec/explore × FFI-on/off runs agree on every fact except the syntactic form of the one `bytecode` fact, whose two forms are ⟦·⟧-equal by Lemma 1) and, corpus-wide, by `tests/engine/ffi-differential.test.js`. The asymmetry is therefore not a latent soundness gap; it is cosmetic + asymptotic.

**Corollary 5.2 (the external-index refactor is infeasible).** The appealing "keep the bytecode an arrlit everywhere and consult a separate trie *index fact*" design cannot work. Under FFI-off, `arr_get(BC, PC, OP)` is proved by backward chaining, and backward chaining resolves subgoals against the **immutable clause database**, not the runtime persistent state (`lib/engine/backchain.js`). A `trie_index(arrlit, T)` living in the state is thus unreachable from an `arr_get` subgoal. For clause navigation to reach a trie, the trie must **be the array term** passed to `arr_get` — i.e. it must sit inside the `bytecode` fact. Representation choice for clause-navigable arrays is therefore necessarily *in-term*; the only conforming options are (a) swap the fact's payload (the current `bytecodeToTrie`), or (b) present the trie from the start. The residual, non-soundness content of TODO_0312 is cost-uniformity between exec and explore (lift the gated swap to a shared boundary), not a representation redesign.

**Remark (why the grade-0 gate is principled, not a hack).** `bytecodeToTrie` is skipped when the bytecode is grade-0 specialized (`!opts.extraGrade0Facts`, TODO_0307 Track 2). Under specialization `arr_get(bytecode, PC)` is resolved at compile time (THY_0016), so *no runtime clause navigates the bytecode* and the trie buys nothing; moreover the specialized rules preserve `bytecode(arrlit)`, so swapping to a trie would make that preserved pattern unmatchable. The gate is exactly the predicate "will a runtime `arr_get` navigate this array?" — a semantic condition, and Corollary 5.1 is why skipping the swap is result-preserving.

## 6. Positioning

The result is the array instance of THY_0039's thesis that the tiered resolver is "a stack of implementations of one rule, each obligated to the same side condition." There the rule was ∃-forcing and the side condition was uniqueness (groundness × functionality); here the rule is `arr_get`/`arr_set` and the side condition is denotational equality ⟦A⟧ = ⟦B⟧ — discharged unconditionally by Theorems 1–2, so array access needs no per-use certificate, unlike forced elimination. Read through Hoare–He–Sanders, ⟦·⟧ is the abstraction function and Theorems 1–2 are the read/write refinement squares; the novelty for a substructural framework is that arrays are consumed *linearly* (via `$`-preservation) yet the refinement is presentation-total, so classical persistent data refinement transfers without a linearity obligation on the *read-only* bytecode (mutable memory, also linear, is the case where the linear/persistent refinement question of `doc/big_next.md` §4 bites, and is future work). Against verified symbolic execution (KEVM, hevm), the contribution is that the fast path is not trusted but *certified equal to the logical semantics*, with the equality machine-checked by a differential over a real EVM corpus rather than assumed.

**Status.** Theorems 1–2 and Lemma 1 are proof-sketch level in the CLF rules-as-hypotheses style (THY_0023); Lemma 1's navigation argument is complete. Executable witnesses: `tests/engine/array-repind-0312.test.js` (Lemma 1 fuzz; §5 four-way end-to-end), `tests/engine/ffi-differential.test.js` (corpus FFI≡clause), `tools/fuzz-ffi.js` + `npm run test:noffi` (cross-resolver agreement). No claim here is machine-verified as a proof; each is machine-*tested* on a substantial corpus.
