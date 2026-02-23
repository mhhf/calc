---
title: "Lax Monad {A} — Backward/Forward Integration"
created: 2026-02-18
modified: 2026-02-23
summary: "Integrate forward and backward chaining via CLF lax monad"
tags: [architecture, clf, lax-monad, forward-backward, focusing, polarity, adjoint-logic]
type: research
cluster: CLF
status: researching
priority: 8
depends_on: []
required_by: [TODO_0010, TODO_0011]
starred: false
---

# Lax Monad {A} — Backward/Forward Integration

CLF/Celf/LolliMon integrate forward and backward chaining via the lax monad `{A}`: entering the monad switches from backward (goal-directed, backtracking) to forward (data-driven, committed choice), exiting at quiescence.

**Core question for CALC:** The forward engine already works. Do we need to make the monad explicit? What does it buy us?

---

## 1. What the Lax Monad Is

### 1.1 The Type `{S}`

The monadic type `{S}` is CLF's (Watkins et al. 2004) central innovation. It partitions types into two worlds:

```
Asynchronous types:  A ::= P | A -o B | A & B | T | {S}
Synchronous types:   S ::= P | S1 * S2 | 1 | !A | exists x.S
```

- **Asynchronous** (outside monad): loli, with, top — their right-rules are invertible. Correspond to backward chaining: decompose goals eagerly.
- **Synchronous** (inside monad): tensor, one, bang, exists — their right-rules require a choice. Correspond to forward chaining: produce data constructively.

The monad `{S}` is the **only bridge** from synchronous to asynchronous. It is a polarity shift.

### 1.2 Proof-Theoretic Foundation

The lax monad has clean proof theory (Fairtlough & Mendler 1997, Pfenning & Davies 2001):

**Introduction** — if we can prove `S` in forward mode, we can conclude `{S}`:
```
   Delta |-_fwd S
  ─────────────── {}I
   Delta |- {S}
```

**Elimination** — if we have `{S}`, we can bind the result and continue in lax mode:
```
   Gamma |- {S}    [S |- C lax]
  ─────────────────────────────── {}E  (let)
              C lax
```

The elimination is "sticky": once you enter lax/forward mode, you stay there. `C lax` means "C is achievable through computation," not "C is true."

### 1.3 Curry-Howard: Moggi's Computational Monad

Via Curry-Howard, `{S}` corresponds to Moggi's computational monad (1991):

| Logic | Type Theory | CALC |
|---|---|---|
| `A -> {A}` (unit) | `return : A -> T A` | Produce a fact in forward mode |
| `{{A}} -> {A}` (join) | `join : T(T A) -> T A` | Flatten nested forward blocks |
| `{A} -o (A -o {B}) -o {B}` | `bind` | Sequence forward computations |

### 1.4 Operational Semantics (LolliMon)

LolliMon (Lopez et al. 2005) gives the cleanest operational account:

1. Backward search encounters goal `{S}`
2. **Mode switch:** take current linear context as initial state
3. Forward engine applies rules by committed choice (no backtracking)
4. Forward rules can invoke backward chaining for persistent goals
5. **Quiescence:** forward engine halts when no rules fire
6. Return resulting state as proof of `{S}`

Step 4 is critical: forward rules call backward chaining for guards. This is exactly CALC's `provePersistentGoals` in `match.js`.

### 1.5 The Polarity Connection (Chaudhuri-Pfenning 2006)

The deepest insight: the monad is not an operational trick but a **polarity shift** in focusing:

- **Negative (asynchronous) atoms** → backward chaining (SLD resolution)
- **Positive (synchronous) atoms** → forward chaining (hyperresolution)
- The monad `{S}` = shift from negative to positive polarity

This is structural, not operational. CALC's strategy stack (fingerprint → disc-tree → predicate) is a compiled implementation of the synchronous focus phase.

---

## 2. CALC's Current Implicit Monad

### 2.1 The Code IS the Monad

CALC already has a lax monad — it's just implicit in the code structure rather than explicit in the type system:

| CLF concept | CALC code | File |
|---|---|---|
| Outside monad (backward) | L2/L3 focused prover | `lib/prover/focused.js` |
| Inside monad (forward) | Forward engine main loop | `lib/engine/forward.js:run()` |
| `{S}` introduction | `run()` returns `{ state, quiescent }` | `forward.js:107` |
| `{S}` elimination (let) | Sequencing in symexec | `symexec.js:explore()` |
| Mode switch (enter monad) | `mde.load()` → `symexec.explore()` | Entry point |
| Persistent goal proving | `provePersistentGoals` | `match.js` |
| Quiescence detection | `!m` check in `while` loop | `forward.js:97-100` |

The forward engine's `run()` function IS the monadic computation:
```javascript
while (steps < maxSteps) {
  let m = strategy.findMatch(state, indexedRules, calc, matchOpts);
  if (!m) {
    m = match.matchFirstLoli(state, calc);
    if (!m) return { state, quiescent: true, steps, trace };  // quiescence = monad exit
  }
  state = applyMatch(state, m);  // committed choice = monadic step
  steps++;
}
```

### 2.2 What the Implicit Monad Already Gives

- **Forward-backward integration:** `provePersistentGoals` calls backward proving (FFI + clause resolution) inside forward rules. This IS the LolliMon pattern.
- **Committed choice:** `applyMatch` mutates state without backtracking.
- **Quiescence:** The loop terminates when no rules fire.
- **Separation of concerns:** Forward rules (`lib/engine/`) are distinct from backward prover (`lib/prover/`).

### 2.3 What the Implicit Monad Lacks

1. **No backward→forward mode switch.** Currently, forward execution is the *only* mode. There is no backward-chaining outer layer that *enters* the monad. Users invoke `symexec.explore()` directly.

2. **No backward-chaining goals that trigger forward computation.** In CLF/LolliMon, a backward-chaining proof encountering `{S}` switches to forward mode. CALC's L2/L3 prover has no concept of `{S}`.

3. **No mixed-mode programs.** You can't write a .ill program that does backward chaining for part of the proof and forward chaining for another part.

4. **No type-level distinction.** Forward rules and backward rules are in separate files (`.ill` vs `.rules`), not distinguished by the type system.

---

## 3. Why Make the Monad Explicit?

### 3.1 What We'd Gain

**A. Mixed-mode programs.** A single program could do backward chaining (prove a theorem, compute a value) and then enter forward mode (execute a state machine). Example:

```ill
% Backward: compute optimal gas price
optimal_gas(G) :- current_base(B), priority_fee(F), !plus(B, F, G).

% Forward: execute transaction with computed gas
execute : optimal_gas(G) -o { submit_tx(G) * await_receipt }.
```

**B. Principled sequencing of forward phases.** Instead of Ceptre-style stages (extra-logical, see TODO_0010), use the monad to sequence forward computations via backward chaining:

```ill
phase1 : init -o { ... phase1 rules ... }.
phase2 : phase1_result(X) -o { ... phase2 rules ... }.
```

The backward chainer sequences `phase1` then `phase2` by proving goals of type `{S}`.

**C. Backward chaining for auxiliary computation.** Simmons & Pfenning (ICALP 2008) showed algorithms like Dijkstra need backward chaining for auxiliary computation (comparing distances). Currently CALC uses FFI for this. With the monad, arithmetic and comparisons could be backward-chaining goals.

**D. Clean theory.** The monad provides the formal bridge between THY_0001 (forward chaining theory) and the backward prover (L1-L3). Currently these are separate worlds with no formal connection.

### 3.2 What We'd Pay

- **Complexity.** The prover lasagne gains a new mode-switching mechanism.
- **Parser changes.** The grammar needs `{ ... }` as a formula constructor.
- **Rule format changes.** Rules need to declare whether they're forward or backward.
- **Bundle changes.** `out/ill.json` needs monad support.

---

## 4. Implementation Options

### 4.1 Option A: Minimal — Annotate Existing Separation

Keep the current architecture but add explicit annotations marking which rules are forward and which are backward.

**Changes:**
- Add `@mode forward` / `@mode backward` annotations to `.rules` parser
- Add `monad` connective to `ill.calc` (display only, no new proof rules)
- The prover lasagne doesn't change — forward and backward remain separate subsystems
- Entry point (`mde.load()`) chooses mode based on annotation

**Pros:** Minimal code change (~100 LOC). Documents the implicit monad without new machinery.
**Cons:** No mixed-mode programs. No backward→forward switching. Just documentation, not real integration.

**Estimated effort:** ~100 LOC

### 4.2 Option B: Mode Switch — Connect L3 to Forward Engine

Add a mode-switch rule to the backward prover that invokes the forward engine when encountering `{S}`.

**Changes:**
- Add `monad` connective to `ill.calc` and `ill.rules`
- Add `monad_r` rule to L3 focused prover: when the succedent is `{S}`, switch to forward mode
- Forward engine returns a proof tree node that L1 kernel can verify
- New judgment form: `deriv_fwd` for forward-chaining derivations
- Bridge in `lib/prover/strategy/forward.js` connects L3 to `lib/engine/forward.js`

**Architecture:**
```
L3 focused.js (backward chaining)
  encounters goal {S}
    → monad_r rule fires
    → calls forward engine run()
    → forward engine runs to quiescence
    → returns proof tree
    → L3 continues with result
```

**Pros:** Principled mixed-mode programs. Backward chaining can invoke forward computation. Subsumes TODO_0010 staging.
**Cons:** Significant complexity (~500 LOC). Need to bridge two proof term formats. Need to handle linear context transfer between modes.

**Key technical challenge:** The backward prover works with sequents (`{ contexts, succedent }`). The forward engine works with multiset state (`{ linear, persistent }`). The mode switch must convert between these representations.

**Estimated effort:** ~500 LOC + tests

### 4.3 Option C: Adjoint Logic — Generalize Beyond CLF

Replace the monadic boundary with adjoint logic shift operators (Pruiksma et al. 2018). Two modes:
- Mode `U` (unrestricted, backward chaining)
- Mode `X` (synchronous, forward chaining)

With an adjunction `F ⊣ U` between them:
- `↓ A` (downshift, F): enter forward mode
- `↑ S` (upshift, U): exit to backward mode
- Lax monad: `○ A = ↑(↓ A)` (enter forward, then exit)

**Pros:** Most general. Subsumes bang (`! = ↓↑` on linear→cartesian), lax monad, stages, and potentially graded modalities. Future-proofs the design for multimodal extensions (TODO_0012).
**Cons:** Most complex (~1500+ LOC). Requires mode theory infrastructure. Over-engineered for current use cases.

**Estimated effort:** ~1500 LOC + significant design work

### 4.4 Comparison

| | Option A | Option B | Option C |
|---|---|---|---|
| Mixed-mode programs | No | Yes | Yes |
| Backward→forward switch | No | Yes | Yes |
| Stages (TODO_0010) | No | Subsumes | Subsumes |
| Multimodal (TODO_0012) | No | No | Yes |
| Implementation cost | ~100 LOC | ~500 LOC | ~1500 LOC |
| Theory backing | Implicit | CLF/LolliMon | Adjoint logic |
| Practical value now | Low | Medium | Low (overengineered) |

### 4.5 Recommendation

**Start with Option A, plan for Option B.**

Option A is immediate — just annotate what's already there. This unblocks documentation and testing without new machinery.

Option B is the right medium-term goal. It gives mixed-mode programs, principled staging (subsumes TODO_0010), and connects the two halves of the system. The key implementation step is the bridge between sequent representation (prover) and multiset state (engine).

Option C should wait for TODO_0012 (proper MTDC). If CALC eventually needs multiple modes beyond forward/backward (ownership, location, grades), adjoint logic is the right framework. But it's premature now.

---

## 5. Step-by-Step Minimal Example

### 5.1 Current CALC (Implicit Monad)

```ill
% Forward rules (in .ill file, run by engine)
evm/add: pc(N) * stack(SH, X) * stack(SH2, Y) * !inc(N, N1) * !plus(X, Y, Z)
  -o { pc(N1) * stack(SH2, Z) }.
```

This rule is purely forward. The `!inc` and `!plus` guards are proved backward via FFI. The `{ ... }` in the consequent is already monadic notation, but it's parsed as syntactic sugar for tensor decomposition, not as a type constructor.

### 5.2 With Explicit Monad (Option B)

```ill
% Backward rule: prove optimal gas
optimal_gas : !current_base(B) -o !priority_fee(F) -o !plus(B, F, G)
  -o optimal_gas(G).

% Forward rule: execute with computed gas
execute : optimal_gas(G) -o { submit_tx(G) * await_receipt }.

% Mixed-mode query: "compute gas, then execute"
main : init -o { optimal_gas(G) * execute(G) }.
```

The backward prover proves `optimal_gas(G)` by goal decomposition. When it encounters `{ submit_tx(G) * await_receipt }`, it switches to forward mode with `G` bound.

### 5.3 The Mode Switch in Detail

```
1. L3 focused.js: goal = {submit_tx(G) * await_receipt}
2. monad_r fires: extract S = submit_tx(G) * await_receipt
3. Transfer linear context Delta to forward engine state
4. forward.run(state, rules) until quiescence
5. Return: state_final as proof of {S}
6. L3 continues backward chaining with the result
```

---

## 6. Relationship to CALC's Extensions (THY_0001)

CALC extends CLF in three ways (see THY_0001). The monad interacts with each:

### 6.1 Lolis Inside the Monad

CLF forbids `-o` inside `{S}`. CALC allows it for conditional production:
```ill
evm/iszero: ... -o { ... * (!eq V 0 -o { stack SH 1 }) }.
```

With an explicit monad, this becomes a **nested monadic computation**: the outer `{ }` enters forward mode, the inner `{ }` is a continuation triggered by `!eq V 0`. The loli `!eq V 0 -o { stack SH 1 }` is a linear fact in the forward state that fires via loli-left.

**Theoretical cost:** CLF's definitional equality (commuting independent let-bindings) breaks with loli-in-monad because dormant lolis create ordering dependencies. CALC doesn't need definitional equality (no concurrent computation model), so this is acceptable.

### 6.2 Additives (oplus) Inside the Monad

CLF excludes additives. CALC uses `oplus` for symbolic branching. With an explicit monad:
```ill
evm/eq: ... -o { (stack SH 0 * !neq X Y) + (stack SH 1 * !eq X Y) }.
```

`oplus`-left is invertible — the engine case-splits eagerly. Soundness transfers from CHR-with-disjunction (Betz & Fruhwirth 2013, see TODO_0043).

### 6.3 Exhaustive Exploration

CLF uses committed choice (don't-care nondeterminism). CALC's symexec explores all paths (don't-know nondeterminism). With an explicit monad, the execution tree is a proof in the universal fragment: "for all rule choices, the computation reaches quiescence."

The monad makes this cleanly expressible: a single `run()` produces one monadic value (committed choice), while `symexec.explore()` produces a tree of monadic values (exhaustive).

---

## 7. Relationship to Other TODOs

- **TODO_0010 (Stages):** The monad subsumes simple staging. Backward chaining sequences forward phases via `phase1 -o {phase1_rules}. phase2 -o {phase2_rules}.` But cyclic stages (game turns) still need extra mechanism. See TODO_0010 for full analysis.

- **TODO_0011 (Dependent Types):** The monad is orthogonal to dependent types. CLF has both but they're independent features. CALC can implement the monad without Pi types. See TODO_0011 for full analysis.

- **TODO_0012 (Proper MTDC):** The monad is one instance of adjoint logic's shift operators. TODO_0012's proper multi-type display calculus could generalize the monad to arbitrary mode shifts. Option C above is the bridge.

- **TODO_0041 (Unified Rule Matching):** The monad doesn't affect rule matching directly. But making the monad explicit clarifies the status of loli-in-state: a loli continuation IS a monadic let-binding that hasn't been evaluated yet.

- **TODO_0045 (Execution Tree Judgment):** The monad provides the type-theoretic home for the execution tree judgment `Sigma; Delta |-_fwd T : A`. The tree `T` is a proof of the monadic type `{S}`.

---

## 8. Key References

### CLF / Celf / LolliMon
- Watkins et al. (2004). [CLF: A Dependent Logical Framework](https://www.cs.cmu.edu/~fp/papers/clf04.pdf)
- Watkins et al. (2004). [Propositional Fragment](https://www.cs.cmu.edu/~iliano/papers/types03.pdf). TYPES 2003
- Lopez et al. (2005). [LolliMon (PPDP)](https://www.cs.cmu.edu/~fp/public/papers/mcllp05.pdf)
- Schack-Nielsen & Schurmann (2008). [Celf](https://link.springer.com/chapter/10.1007/978-3-540-71070-7_28). IJCAR

### Lax Logic and Monads
- Fairtlough & Mendler (1997). [Propositional Lax Logic](https://www.uni-bamberg.de/fileadmin/uni/fakultaeten/wiai_professuren/grundlagen_informatik/papersMM/pll.pdf). I&C 137(1)
- Pfenning & Davies (2001). [Judgmental Reconstruction of Modal Logic](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/judgmental-reconstruction-of-modal-logic/975027BB7F07B59619913EAD4CEE52F4). MSCS 11(4)
- Moggi (1991). [Notions of Computation and Monads](https://www.cs.cmu.edu/~crary/819-f09/Moggi91.pdf). I&C 93(1)
- Kavvos et al. (2026). [Lax Modal Lambda Calculi](https://arxiv.org/abs/2512.10779). CSL

### Focusing and Polarity
- Chaudhuri, Pfenning, Price (2006). [Forward and Backward Chaining via Focusing](https://www.cs.cmu.edu/~fp/papers/ijcar06.pdf). IJCAR
- Andreoli (1992). Focusing Proofs in Linear Logic. JLC 2(3)

### SLS and Forward Chaining
- Simmons & Pfenning (2008). [Linear Logical Algorithms](https://www.cs.cmu.edu/~fp/papers/icalp08.pdf). ICALP
- Simmons (2012). [Substructural Logical Specifications](https://www.cs.cmu.edu/~rwh/students/simmons.pdf). PhD thesis, CMU

### Adjoint Logic
- Pruiksma et al. (2018). [Adjoint Logic](https://ncatlab.org/nlab/files/PCPR18-AdjointLogic.pdf)
- Licata, Shulman, Riley (2017). [A Fibrational Framework](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.25). FSCD

### CALC Internal
- THY_0001 — Exhaustive Forward Chaining theory (`doc/theory/0001_exhaustive-forward-chaining.md`)
- RES_0008 — CLF/Celf/Ceptre research (`doc/research/0008_clf-celf-ceptre.md`)
- RES_0052 — CLF Lax Monad deep study (`doc/research/0052_clf-lax-monad-deep-study.md`)
- TODO_0010 — Ceptre Stages analysis
- TODO_0011 — CLF Dependent Types analysis
- TODO_0045 — Execution Tree Judgment

## Tasks

- [x] Study CLF, Celf, LolliMon lax monad semantics in depth — see [RES_0052](../research/0052_clf-lax-monad-deep-study.md)
- [x] Understand relationship to Ceptre stages — see [TODO_0010](0010_ceptre-stages.md)
- [ ] Design how `{A}` integrates with the prover lasagne layers (Option B)
- [ ] Prototype the sequent ↔ multiset state conversion (mode switch bridge)
- [ ] Add `monad` connective to `ill.calc` with `@mode_switch forward`
- [ ] Add `monad_r` rule to L3 focused prover
- [ ] Implement forward→backward callback for persistent goals within monadic block
- [ ] Write integration tests: backward goal triggers forward execution to quiescence
