---
title: Prover Lasagne — Layered Prover Architecture
created: 2026-02-12
modified: 2026-02-12
summary: Deliberation on a clean, layered prover architecture for CALC
tags: [architecture, prover, refactor, design]
status: active
---

# Prover Lasagne

Layered prover architecture for CALC. Each layer uses only the API of the layer below. No layer reimplements functionality from a lower layer.

## 1. The Problem

Current state (`lib/v2/prover/`):

```
manual.js         — interactive prover (getApplicableActions, applyAction, renderSequent)
rule-interpreter.js — generic spec builder from .rules ASTs (NEW — replaces hand-coded buildRuleSpecs)
focused/
  prover.js       — focused ILL prover (prove, buildRuleSpecs→delegates to rule-interpreter)
  state.js        — FocusedProofState class
  context.js      — multiset context operations
forward.js        — forward chaining engine (multiset rewriting)
explore.js        — execution tree exploration
pt.js             — ProofTree class
index.js          — thin wrapper (create, prove)
```

**What's wrong:**

1. **manual.js imports focused/prover.js internals.** It calls `createProver()` and `buildRuleSpecs()` from the focused prover, then builds its own parallel action system on top. It reimplements context splitting, premise computation, and resource tracking — duplicating what `prove()` already does internally.

2. **No verification layer.** The focused prover's `prove()` produces a proof tree, but nothing checks it. Bugs in focusing, context splitting, or resource threading produce wrong proofs silently.

3. **Rule specs hardcoded in the prover.** `buildRuleSpecs()` in `focused/prover.js` manually defines `makePremises` functions for each ILL rule (~170 lines of hand-coded JS). Meanwhile, the *same rules* are already declared in `calculus/ill.rules` and parsed by tree-sitter into rich ASTs. The `.rules` file is the source of truth — but the prover ignores it and reimplements the rules from scratch. See [section 3.1](#31-the-rules-pipeline-what-already-exists) for the full analysis of what's generated vs what's hardcoded.

4. **proofLogicV2.ts duplicates state threading.** The UI wrapper manages its own `ProofTreeNode` with `delta_in`/`delta_out`, focus tracking via `delta_in.focusPosition`, and context entries — parallel to `manual.js`'s `createProofState`. Two independent state representations of the same proof.

5. **Forward chaining is disconnected.** `forward.js` has its own state model (`{ linear: {hash: count}, persistent: {hash: true} }`), indexing, and matching — completely separate from the backward prover's `Context` and `Seq`. This may be partly justified by performance needs (see [section 3.6](#36-forward-chaining-state-and-performance)).

## 2. Design Principles

**Unix/suckless:**
- Each layer does one thing
- Layers communicate through minimal, well-defined interfaces
- Data flows in one direction (down for commands, up for results)
- No layer "knows about" the layer above it

**LCF trust model (de Bruijn approach):**
- The bottom layer is the trusted kernel — small enough to read in one sitting
- Upper layers produce proof trees; the kernel verifies them independently
- Trust boundary is explicit: above the line is untrusted
- We chose **de Bruijn** (certificate-based verification) over LCF (abstract types) because JS lacks ML's type system — a proof tree + independent checker is clearer and more debuggable

**Stacking:**
- Each layer extends the one below by adding *strategy*, not *mechanism*
- Layer N calls Layer N-1's API, never reaches into its internals
- You can test any layer by mocking the one below it

**Generate, don't hardcode:**
- Polarity, invertibility, context mode are already generated from `.rules` files
- Rule application should be too — the `.rules` AST contains enough structure
- Logic-specific code belongs in `.calc`/`.rules` data files, not in prover JS

## 3. The Five Layers

```
┌─────────────────────────────────────────────────────────┐
│  L5  INTERACTIVE / UI                                   │
│      ManualProof.tsx, proofLogicV2.ts                   │
│      Provides: UI state, view model, user interaction   │
│      Uses: L4 API                                       │
├─────────────────────────────────────────────────────────┤
│  L4  STRATEGY (Manual / Auto / Forward / SymExec)       │
│      manual.js, auto.js, forward.js, symexec.js         │
│      Provides: which rules to try, in what order        │
│      Uses: L3 API (or L2 directly for unfocused)        │
├─────────────────────────────────────────────────────────┤
│  L3  FOCUSED DISCIPLINE                                 │
│      focused.js                                         │
│      Provides: inversion/focus phases, polarity, blur   │
│      Uses: L2 API                                       │
├─────────────────────────────────────────────────────────┤
│  L2  GENERIC PROVER (exhaustive backward search)        │
│      generic.js                                         │
│      Provides: enumerate applicable rules, apply, prove │
│      Uses: L1 API + calculus object                     │
├─────────────────────────────────────────────────────────┤
│  L1  KERNEL (proof checker)                             │
│      kernel.js                                          │
│      Provides: verify proof step, verify proof tree     │
│      Uses: calculus object (from .calc/.rules)          │
└─────────────────────────────────────────────────────────┘
       ↑
┌──────┴──────────────────────────────────────────────────┐
│  L0  CALCULUS OBJECT (generated from .calc/.rules)      │
│      calculus/index.js, meta/focusing.js                │
│      Provides: parser, renderer, rules, polarity,       │
│                invertibility, context modes              │
│      Source of truth: .calc + .rules files              │
└─────────────────────────────────────────────────────────┘
```

### 3.1 The Rules Pipeline: What Already Exists

Before describing each layer, we must understand what the calculus loading already generates. This is critical because it answers the question: **do we need a separate `rules/ill.js` file?**

**Answer: No.** The `.rules` file is the source of truth. Here's the pipeline:

```
ill.calc + ill.rules
       │ (tree-sitter parse)
       ▼
calculus/index.js:loadRules()
       │ (extract declarations)
       ▼
calculus object = {
  rules:       { tensor_r: { head, premises, invertible, ... }, ... }
  polarity:    { tensor: 'positive', loli: 'negative', ... }
  invertible:  { tensor_r: false, tensor_l: true, loli_r: true, ... }
  AST:         { tensor: (a,b) => hash, ... }
  parse:       "A * B" → hash
  render:      hash → "A * B" | "A \otimes B"
  isPositive:  tag → boolean
  isNegative:  tag → boolean
}
```

**What's already generated from `.rules`:**

| Property | Generated by | How |
|---|---|---|
| `polarity` | `meta/focusing.js:inferPolarityFromRules` | Analyzes rule head structure: empty linear → positive, context-copy → negative, context-split → positive |
| `invertible` | `meta/focusing.js:inferInvertibilityFromRule` | Positive+L = invertible, Negative+R = invertible. Explicit `@invertible` overrides |
| `contextMode` | `meta/focusing.js:analyzeContextFlow` | Returns `'split'`, `'copy'`, `'preserved'`, `'empty'` per rule |
| `rules[name].head` | `calculus/index.js:loadRules` | Parsed AST of the rule's conclusion pattern |
| `rules[name].premises` | `calculus/index.js:loadRules` | Parsed ASTs of premise patterns |
| `rules[name].numPremises` | `calculus/index.js:loadRules` | Count |
| `parser`, `renderer` | `calculus/index.js:buildParser/Renderer` | From `@ascii`/`@latex`/`@prec` annotations |

**What's NOT generated — the gap:**

| What | Where it's hardcoded | Why |
|---|---|---|
| `makePremises(formula, seq, idx) → sequents[]` | ~~`focused/prover.js:buildRuleSpecs`~~ **RESOLVED** — now generated by `rule-interpreter.js` | Converts a rule application into concrete premise sequents. Was hand-coded per rule (~170 lines), now generated from rule ASTs (~250 lines generic interpreter) |
| Identity axiom logic | `focused/prover.js:tryIdentity` | Unification-based matching |
| Context threading | `focused/prover.js:prove` | Hodas-Miller lazy delta passing |

**Closing the gap — `makePremises` is now generated.**

The generic structural interpreter (`lib/v2/prover/rule-interpreter.js`) reads rule ASTs from `calculus.rules` and produces identical spec objects to what was hand-coded. It works by:

1. **Parsing** the rule head to find the principal connective and its formula variable bindings (A, B)
2. **Analyzing** each premise to find what formulas are added to linear/cartesian context
3. **Building** a `makePremises` function that uses `Store.child` to extract concrete subformulas at runtime

Key functions: `analyzeHead` (find principal), `analyzePremise` (diff premise vs head), `buildMakePremises` (runtime premise constructor). Special cases: structural rules (no principal connective), axiom rules (0 premises), name collisions (dereliction/absorption both match `bang_l`).

The interpreter produces: `{ specs, alternatives }` where `alternatives` maps colliding keys to their alternative rule names (e.g., `{ bang_l: ['absorption'] }`).

**Verified** with 41 tests across 4 categories: metadata, makePremises output, extraLinear, and integration proof search. All 13 ILL rules produce identical output to the former hand-coded version.

### 3.2 L1 — Kernel (Proof Checker)

**Responsibility:** Given a proof tree, answer "is this valid?"

**What it does:**
- Verify that a single rule application is correct (conclusion + premises match the rule, resources consumed correctly)
- Verify an entire proof tree bottom-up
- Nothing else. No search, no strategy, no heuristics.

**Interface:**

```javascript
createKernel(calculus) → {
  // Verify one step: does applying `rule` to `conclusion` produce `premises`?
  verifyStep(conclusion, rule, premises) → { valid, error? }

  // Verify entire proof tree
  verifyTree(tree) → { valid, errors[] }

  // List available rules (from calculus.rules)
  getRules() → string[]
}
```

**Where rules come from:** The `calculus` object, loaded from `.calc`/`.rules` files. No separate rules file. L1 reads `calculus.rules` to know what rules exist and how to verify them.

**Trust:** This is the only trusted code. Target: ~200-300 lines. Verifiable by inspection.

### 3.3 L2 — Generic Prover (Exhaustive Search)

**Responsibility:** Given a sequent, find a proof by trying all applicable rules.

**What it does:**
- For a sequent, enumerate every rule from the calculus that could apply
- For each applicable rule, compute the premises
- Context threading uses Hodas-Miller (lazy splitting)
- Recurse on premises; backtrack on failure
- Loop detection via sequent canonicalization + visited set
- Depth bounding

**Interface:**

```javascript
createGenericProver(calculus, kernel) → {
  // Find all rules that apply to this sequent
  applicableRules(seq) → [{ rule, match, premises, contextMode }]

  // Apply a specific rule with specific context assignment
  applyRule(seq, rule, match, contextSplit?) → premises[]

  // Exhaustive backward search
  prove(seq, opts?) → { success, proofTree? }

  // Verify proof using L1 kernel
  verify(proofTree) → { valid, errors[] }
}
```

**Key:** `applicableRules` is purely structural — no polarity, no invertibility, no focusing. "Does the sequent's shape match any rule in the calculus?" This is what the manual prover's unfocused mode wants.

**Trust:** Semi-trusted. Bugs here → failed or slow proofs, never wrong proofs (L1 verifies).

### 3.4 L3 — Focused Discipline

**Responsibility:** Restrict L2's rule enumeration using Andreoli's focusing.

**What it does:**
- Wraps L2's `applicableRules` with polarity/invertibility filtering
- Inversion phase: only return invertible rules
- Focus phase: choose a formula, only return its decomposition rule
- Blur: transition back to inversion when hitting invertible formula during focus

**Interface:**

```javascript
createFocusedProver(genericProver, calculus) → {
  // Like L2.applicableRules, but filtered by focusing discipline
  applicableActions(seq, phase) → actions[]

  // Focused proof search
  prove(seq, opts?) → { success, proofTree? }

  // What can we focus on?
  focusTargets(seq) → [{ position, formula }]

  // Is this rule invertible?
  isInvertible(ruleName) → boolean
}
```

**Key:** L3 never computes premises or manipulates contexts. It *filters* L2's results. Polarity and invertibility come from the `calculus` object (already generated from `.rules` by `meta/focusing.js`). L3 contains zero logic-specific code.

**How generic is L3?** Fully generic for any polarized logic. The focusing discipline is parametric: it only needs a polarity assignment per connective and an invertibility assignment per rule. Both are generated from `.rules`. Adding `next: positive` to a `.calc` file automatically integrates `next` into focusing — no L3 code changes.

**The L3 question: is focusing always the right strategy?** For ILL, yes. For other logics (modal, temporal), focusing also works if you assign polarities correctly. For logics without a clean polarity story, L4 strategies can bypass L3 and use L2 directly. The layer is optional, not mandatory.

### 3.5 L4 — Strategy Layer

**Responsibility:** Provide different *interfaces* and *policies* for driving proof search.

Multiple strategies coexist, all built on L3/L2:

**L4a — Manual (Interactive):**

```javascript
createManualProver(focusedProver, genericProver) → {
  // What can the user do at this proof state?
  getActions(proofState, opts) → actions[]
  //   opts.mode = 'focused' → delegates to L3.applicableActions
  //   opts.mode = 'unfocused' → delegates to L2.applicableRules

  // User applies an action
  applyAction(proofState, action, userInput?) → newProofState

  // Render sequent with focus highlighting
  renderSequent(seq, format, focus?) → string
}
```

**L4b — Automated (focused backward search):**

```javascript
createAutoProver(focusedProver) → {
  prove(seq, opts?) → { success, proofTree? }
}
```

**L4c — Forward (multiset rewriting):**

```javascript
createForwardEngine(calculus) → {
  step(state) → state'
  run(state, opts?) → finalState
}
```

**L4d — Symbolic Execution (execution tree builder):**

```javascript
createSymExecEngine(forwardEngine) → {
  // Explore all execution paths, branching at nondeterminism
  explore(state, opts?) → executionTree
  // Tree utilities
  getAllLeaves(tree) → state[]
  countBranches(tree) → number
}
```

This is today's `explore.js`. It wraps L4c's forward engine by branching at nondeterministic choice points (multiple rules can fire) instead of committing to one. It produces a tree of all reachable states — the foundation for metaproofs, model checking, and test generation.

**Context split in L4/L5:**

For interactive context splits, two modes:

1. **Manual split** (current): L2 detects the split need, L4 surfaces distributable formulas, L5 shows the split dialog, user assigns formulas to premises.

2. **Lazy split** (Hodas-Miller, new option): All distributable formulas go into premise 1. Whatever premise 1 doesn't consume flows to premise 2 automatically. No dialog needed. User can switch between modes in L5.

### 3.6 Forward Chaining State and Performance

Forward chaining (`forward.js`) currently maintains its own state representation:
```javascript
{ linear: { [hash]: count }, persistent: { [hash]: true }, index: { ... } }
```

This is *intentionally* different from the backward prover's `Seq` + `Context`. Forward chaining does thousands of match-apply cycles per second. Its state needs:
- O(1) predicate-head lookup (indexed by head symbol)
- O(1) add/remove from multiset
- No sequent structure (no succedent, no cartesian/linear distinction at this level)

Celf and Lollimon also maintain separate state representations for forward vs backward modes. The monad acts as the mode switch; internal representations differ for performance.

**What to share vs what to duplicate:**

| Shared | Why |
|---|---|
| Rule definitions (calculus object) | Same rules, different execution strategy |
| Context multiset operations (`context.js`) | Same O(1) add/remove/merge |
| Store (content-addressed formulas) | Same formula representation everywhere |

| Separate | Why |
|---|---|
| State representation | Forward: flat multiset. Backward: sequent with contexts |
| Indexing | Forward: predicate-head index for O(1) match. Backward: none needed |
| Matching | Forward: pattern match against state. Backward: unify against sequent |

**Decision:** Share what's cheap to share (rule defs, multiset ops, Store). Don't force forward chaining into backward's state model. Benchmark before optimizing further — if the current forward.js is fast enough with its own state, there's no reason to change it.
> You said "if the current forward.js is fast enough with its own state, there's no reason to change it" - I rather argue for the different - if its fast enough with relying on the lower layers to store state we don't need to dublicate the state and accessors (indexing matching) in the forward chaining layer. But for that we need tests and benchmarks, so we would need to implement both - this can be a separate task once we've implemented everything else since this would be considered an optimization.

### 3.7 L5 — UI Layer

**Responsibility:** Pure view. Translates between L4's proof state and DOM/components.

```
proofLogicV2.ts  — type adapter (L4 types ↔ TS types)
ManualProof.tsx  — SolidJS components (tree view, rule selector, split dialog)
```

**The key rule:** L5 never does proof logic. If L5 needs information, L4 provides it.

**What changes:** `proofLogicV2.ts` currently maintains its own `ProofTreeNode` with `delta_in`/`delta_out` and reimplements focus propagation. After refactor: thin type adapter only, proof state lives entirely in L4.

## 4. Data Flow

### Proof State

One proof state representation, used by all layers:

```javascript
ProofState = {
  // Universal (all logics, all layers read these):
  conclusion: Sequent,     // what we're proving
  rule: string | null,     // applied rule (null = open goal)
  premises: ProofState[],  // child states
  proven: boolean,         // is this subtree complete?

  // Strategy-specific metadata (layers read/write their own keys):
  meta: {
    // L2 writes, L1 verifies:
    delta: Multiset,         // remaining linear resources to distribute
    // L3 writes, L4 reads:
    focus: { position, index, formula } | null,
    // Future extensions go here without changing the core shape:
    // mode: 'linear' | 'cartesian' | ...,
    // temporalStep: number,
    // grading: { ... },
  },
}
```

The `meta` bag keeps calculus/strategy-specific annotations separate from the universal proof tree structure. L1 only reads `conclusion`, `rule`, `premises` for verification — it ignores `meta`. L2 manages `meta.delta`. L3 manages `meta.focus`. Future logics can add their own keys (e.g., `meta.temporalStep`, `meta.grading`) without changing the core ProofState shape.

### Rule Application Pipeline

When the user clicks a rule in the UI:

```
L5: user clicks "loli_l" on formula at index 2
 │
 ▼
L4.manual: applyAction(state, { rule: 'loli_l', position: 'L', index: 2 })
 │  needs context split → asks L5 for user input (or uses lazy split)
 │
 ▼
L3.focused: (if focused mode) verifies rule is valid in current phase
 │
 ▼
L2.generic: applyRule(seq, 'loli_l', match, split)
 │  computes premises, threads delta
 │
 ▼
L1.kernel: verifyStep(conclusion, 'loli_l', premises)
 │  checks rule schema matches, resources consumed correctly
 │
 ▲ returns { valid: true }
```

### Automated Proof Pipeline

```
L4.auto: prove(seq)
 │
 ▼
L3.focused: inversion phase
 │  finds invertible rule (with_r) via L2.applicableRules + polarity filter
 │
 ▼
L2.generic: applyRule(seq, 'with_r', match)
 │  computes premises, copies delta (additive)
 │  recurses on each premise → L3 → L2 → ...
 │
 ▼
L1.kernel: verifyTree(proofTree)
 │  post-hoc verification of entire tree
```

## 5. How Generic Can We Go?

This is the central question: as we go up the layer stack, how much is logic-independent vs ILL-specific?

### Analysis per layer

 | Layer             | Logic-independent                                                 | Logic-specific                                                                   |
 | ---               | ---                                                               | ---                                                                              |
 | **L1 kernel**     | Tree verification structure                                       | Rule matching (now generated by `rule-interpreter.js` from `.rules` ASTs) |
 | **L2 generic**    | Backtracking, depth limit, loop detection, Hodas-Miller threading | Which rules exist (from calculus object)                                         |
 | **L3 focused**    | Phase alternation, blur condition, focus/inversion protocol       | Polarity assignments (from calculus object)                                      |
 | **L4 strategies** | Manual UI protocol, auto search loop, forward step/run            | None (pure strategy, no logic)                                                   |
 | **L5 UI**         | Components, rendering, interaction                                | None (pure view)                                                                 |

**The picture:** L3, L4, L5 are already logic-independent by design. L2 is logic-independent except for its dependency on rule specs. L1 is the place where logic-specificity concentrates — and the structural interpreter (`rule-interpreter.js`) now makes it largely generic.

**What the interpreter handles:**

1. **Structural connective interpretation.** Bridges between `.rules` notation (`comma`, `empty`, `hyp`) and flat arrays. Currently handles LNL family (cartesian+linear). Parameterized by family would generalize to display calculi.

2. **Special context modes.** `bang_r` requires empty linear context → detected via `headInfo.emptyLinear`. `absorption` moves formula to cartesian → detected via `extraCartesianFormulas`. Both derived from rule AST structure, no annotations needed.

3. **Non-standard rule shapes.** `with_l1`/`with_l2` (alternative left rules) → handled by `specKey` suffix logic. `copy` (structural, no principal) → handled via `rule.structural` flag. Name collisions (dereliction/absorption) → `alternatives` map.

**Conclusion:** The structural interpreter is built (251 lines). It generates all 13 ILL rule specs from `.rules` ASTs. Adding new rules to `.rules` requires zero prover code changes. Generalizing to other families (display calculi, adjoint logics) would need parameterizing the family-specific parts of the interpreter.

## 6. Concrete Refactor Plan

### What moves where

| Current file | Current responsibility | After refactor |
|---|---|---|
| `focused/prover.js:buildRuleSpecs` | Hand-coded rule functions | **DONE** — replaced by `rule-interpreter.js`. `buildRuleSpecs` now delegates to `buildRuleSpecsFromAST(calculus)` |
| `focused/prover.js:prove` | Focused search + resource threading | → L3 (focusing) + L2 (search) |
| `focused/prover.js:tryIdentity` | Identity axiom | → L2 (it's a rule like any other) |
| `focused/prover.js:chooseFocus` | Focus target selection | → L3 |
| `focused/prover.js:ruleIsInvertible` | Polarity check | → L3 (reads `calculus.invertible`) |
| `focused/prover.js:applyRule` | Single rule application | → L2.applyRule |
| `focused/prover.js:addDeltaToSequent` | Resource threading | → L2 (internal) |
| `focused/context.js` | Multiset operations | → stays (shared utility) |
| `focused/state.js` | FocusedProofState | → L3 (internal) |
| `manual.js:getApplicableActions` | Action enumeration | → L4.manual (delegates to L3/L2) |
| `manual.js:buildRuleAction` | Action + premise computation | → L2.applicableRules + L4 formatting |
| `manual.js:applyAction` | State transition | → L4.manual (delegates down) |
| `manual.js:renderSequent` | Focus-aware rendering | → shared renderer (uses `calculus.render`) |
| `manual.js:getAbstractRule` | Rule schemas for display | → `calculus.rules[name].pretty` (already there) |
| `pt.js` | ProofTree class | → L2 (proof tree is L2's data structure) |
| `proofLogicV2.ts` | UI state + focus threading + type adapter | → L5 (thin adapter only) |
| `forward.js` | Forward chaining engine | → L4c (keeps own state for performance) |
| `explore.js` | Execution tree exploration | → L4d (wraps L4c) |

### New file structure

```
lib/v2/prover/
├── rule-interpreter.js # L0→L2: generic spec builder from .rules ASTs (EXISTS, 251 lines)
├── kernel.js          # L1: verifyStep, verifyTree (~200 lines)
├── generic.js         # L2: applicableRules, applyRule, prove (~300 lines)
├── focused.js         # L3: focusing discipline, phase management (~200 lines)
├── strategy/
│   ├── manual.js      # L4a: interactive prover
│   ├── auto.js        # L4b: automated search (wraps L3.prove)
│   ├── forward.js     # L4c: forward chaining engine
│   └── symexec.js     # L4d: symbolic execution / execution trees
├── context.js         # multiset operations (shared utility)
└── pt.js              # proof tree data structure
```

No `rules/ill.js` file. Rules come from `calculus/ill.rules` → `calculus/index.js` → calculus object. All layers receive the calculus object as a constructor argument.

### What gets deleted

- `focused/prover.js` — split into `generic.js` + `focused.js` (rule specs now generated by `rule-interpreter.js`)
- `focused/state.js` — absorbed into `focused.js`
- `index.js` — replaced by direct imports

## 7. Migration Strategy

**Test-and-benchmark driven.** No incremental migration needed — but comprehensive test coverage and benchmarks first.

### Phase 1: Prepare (before touching prover code)

1. **Expand test suite.** Ensure every current behavior is tested:
   - `tests/manual-prover-logic.test.js` (38 tests) — expand to cover all edge cases
   - `tests/manual-proof-flow.test.js` (15 tests) — add more complete proof walkthroughs
   - Add focused prover tests: prove N standard sequents, save proof trees
   - Add forward chaining tests: step counts, final states
2. **Benchmark.** Save timings for:
   - Focused prover: N standard sequents, measure time per proof
   - Forward chaining: step throughput (steps/second)
   - Manual prover: action enumeration latency

### Phase 2: Build new layers (parallel to existing code)

1. **L1 kernel.js** — pure addition, no existing code touched
2. **L2 generic.js** — extract from `focused/prover.js`, share `buildRuleSpecs`
3. **L3 focused.js** — extract focusing logic
4. **L4 strategy/** — rewire manual.js, auto, forward, symexec

### Phase 3: Cut over

1. Rewire all imports to new layers
2. Run full test suite — must be green
3. Run benchmarks — must be within tolerance
4. Delete old files

### Phase 4: Generic interpreter ~~(separate effort)~~ **COMPLETE**

1. ~~Build structural interpreter for `.rules` ASTs~~ → `lib/v2/prover/rule-interpreter.js` (251 lines)
2. ~~Replace `buildRuleSpecs` hand-coded functions~~ → `buildRuleSpecs` now delegates to `buildRuleSpecsFromAST`
3. ~~Test: same proof results, same performance~~ → 41 interpreter tests + 53 regression tests pass

## 8. Extensibility: Adding Temporal Modalities

To add `○` (next) and `●` (previous) to CALC:

**Step 1: Add connectives** to `ill.calc` (or a new `ill-temporal.calc`):

```celf
next: formula -> formula
  @ascii "O _"
  @latex "\\bigcirc #1"
  @prec 80
  @category temporal.

prev: formula -> formula
  @ascii "@ _"
  @latex "\\bullet #1"
  @prec 80
  @category temporal.
```

**Step 2: Add rules** to `ill.rules` (or a new `ill-temporal.rules`):

```celf
next_r: deriv (seq G D (hyp any (next A)))
  <- deriv (seq G D (hyp any A))
  @pretty "○R".

next_l: deriv (seq G (comma D (hyp any (next A))) C)
  <- deriv (seq G (comma D (hyp any A)) C)
  @pretty "○L".
```

**That's it.** The calculus loader generates polarity (positive, from context-preserving right rule), invertibility (inferred from polarity), parser, renderer. All layers pick it up:
- L1 can verify proofs with `next_r`/`next_l`
- L2 can search for them
- L3 applies the focusing discipline (next is positive → invertible on L, focusable on R)
- L4 shows them in the UI
- No code changes in any layer

(The generic structural interpreter is built. Adding new rules to `.rules` automatically generates the corresponding `makePremises` — no prover code changes needed.)

## 9. Resolved Questions

1. **LCF vs de Bruijn?** → **de Bruijn.** Produce proof trees, verify independently. LCF is low-priority research for later — it adds compile-time safety via abstract types but requires ML-style type discipline that JS doesn't have.

2. **Context split interaction?** → **Two modes in L5.** Manual split (user assigns formulas to premises via dialog) and lazy split (Hodas-Miller: everything to premise 1, remainder to premise 2). User toggles between them. L2 supports both via `applyRule(seq, rule, match, explicitSplit?)`.

3. **Forward chaining state sharing?** → **Share rule defs and multiset ops; keep separate state models.** Benchmark-driven: if forward chaining is fast enough, don't change it. If a shared representation proves faster, refactor then. Celf and Lollimon also maintain separate representations per mode.

4. **Incremental migration?** → **No. Test+benchmark driven.** Full test coverage + benchmarks before migration. After migration, same tests + benchmarks must pass. No halfway state.

## 10. Open Research

| Question | Priority | Notes |
|---|---|---|
| ~~Generic structural interpreter for `.rules` ASTs~~ | ~~HIGH~~ **DONE** | `lib/v2/prover/rule-interpreter.js` (251 lines). Replaces `buildRuleSpecs`. Generates all 13 ILL specs from rule ASTs. 41 tests. |
| Forward/backward state unification | LOW | Benchmark first. Only pursue if perf allows or if sharing saves significant code. |
| LCF-style abstract types in JS | LOW | WeakMap + closures could simulate ML's abstract types. Adds compile-time safety. Not urgent. |
| Generic structural connective interpretation per family | MEDIUM | Different families (LNL, display, adjoint) have different structural connective sets. The interpreter needs to be parameterized by family. |

## 11. References

### Architecture patterns
- HOL Light kernel: ~400 lines, 10 rules, abstract `thm` type ([Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/hollight.pdf))
- Isabelle layering: kernel → tactics → Sledgehammer ([Paulson](https://arxiv.org/pdf/1907.02836))
- Lean 4 monad stack: CoreM → MetaM → TermElabM → TacticM
- Foundational Proof Certificates: focusing as proof format ([Miller](https://dl.acm.org/doi/10.1145/2503887.2503894))
- Calculus Toolbox: JSON spec → generic rule application ([docs](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculus-encoding.html))

### Linear logic provers
- Hodas-Miller lazy splitting: delta threading ([1994](https://www.sciencedirect.com/science/article/pii/S0890540184710364))
- Cervesato-Hodas-Pfenning efficient resource management ([1996](https://www.cs.cmu.edu/~fp/papers/elp96.pdf))
- Celf 5-mode operational semantics (inversion L/R, focusing L/R, monadic)
- Lollimon: monad separates backward/forward modes

### Proof refinement
- Sterling-Harper proof refinement logics ([2017](https://arxiv.org/abs/1703.05215))
- RedPRL: 5 atomic judgments, tactics propose, kernel validates

### Existing CALC docs
- [[prover-architecture]] — LCF, tactics, Sledgehammer research
- [[CORE_SPLIT]] — original core/calculus separation design
- [[manual-proof-architecture]] — suckless principle, single source of truth
- [[manual-prover-refactor]] — bug analysis and fix history
- [[dsl_refactor]] — .calc/.rules migration status
