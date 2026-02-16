---
title: Prover Architecture (Lasagne)
modified: 2026-02-15
summary: Five-layer prover architecture separating verification, search, focusing, and strategy.
tags: [architecture, prover, focusing, polarity, layers]
---

# Prover Architecture

CALC's prover is structured as five layers. Each layer uses only the API of the layer below. No layer reimplements functionality from a lower layer.

```
┌─────────────────────────────────────────────────────────┐
│  L5  INTERACTIVE / UI                                   │
│      ManualProof.tsx, proofLogic.ts                     │
│      Provides: UI state, view model, user interaction   │
│      Uses: L4 API                                       │
├─────────────────────────────────────────────────────────┤
│  L4  STRATEGY (Manual / Auto / Forward / SymExec)       │
│      strategy/manual.js, auto.js, forward.js, symexec.js│
│      Provides: which rules to try, in what order        │
│      Uses: L3 API (or L2 directly for unfocused)        │
├─────────────────────────────────────────────────────────┤
│  L3  FOCUSED DISCIPLINE                                 │
│      focused.js                                         │
│      Provides: inversion/focus phases, polarity, blur   │
│      Uses: L2 API                                       │
├─────────────────────────────────────────────────────────┤
│  L2  GENERIC PROVER (search primitives)                 │
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

## File Structure

```
lib/prover/                      # Backward proof search
├── kernel.js                    # L1: verifyStep, verifyTree
├── generic.js                   # L2: connective, tryIdentity, applyRule, applicableRules
├── focused.js                   # L3: findInvertible, chooseFocus, prove (Andreoli)
├── strategy/
│   ├── manual.js                # L4a: interactive proof (getApplicableActions, applyAction)
│   └── auto.js                  # L4b: automated backward search (wraps L3.prove)
├── context.js                   # shared: multiset operations { [hash]: count }
├── state.js                     # shared: FocusedProofState class
├── pt.js                        # shared: ProofTree class
├── rule-interpreter.js          # shared: builds rule specs from .rules descriptors
└── index.js                     # convenience re-exports

lib/engine/                      # Forward execution engine (L4c/L4d)
├── forward.js                   # matching + state transformation
├── symexec.js                   # execution tree exploration (DFS + mutation/undo)
├── compile.js                   # rule compilation (de Bruijn slots, metavar analysis)
├── rule-analysis.js             # pattern roles, compiled substitution recipes
├── disc-tree.js                 # discrimination tree indexing
├── prove.js                     # backward chaining for persistent antecedents
├── ffi/                         # foreign function interface (arithmetic, etc.)
├── convert.js                   # .ill → content-addressed hashes
├── hex.js                       # hex/binary utilities
└── index.js                     # loader + API

lib/kernel/                      # Content-addressed AST substrate
├── store.js                     # SoA TypedArray arena (tags, arities, children)
├── unify.js                     # pattern matching (matchIndexed) + unification
├── substitute.js                # substitution (applyIndexed, subCompiled)
├── ast.js                       # AST construction helpers
├── ast-hash.js                  # stable hashing for AST equality
└── sequent.js                   # sequent structure
```

## Design Principles

**De Bruijn trust model.** L1 is the trusted kernel — small enough to read in one sitting. Upper layers produce proof trees; the kernel verifies them independently. Bugs in L2–L4 produce failed or slow proofs, never wrong proofs.

**Generate, don't hardcode.** Polarity, invertibility, and rule application are all generated from `.rules` files via `rule-interpreter.js`. Adding a new connective to `.rules` requires zero prover code changes.

**Stacking.** Each layer extends the one below by adding *strategy*, not *mechanism*. Layer N calls Layer N-1's API, never reaches into its internals.

## L0 — Calculus Object

Generated from `ill.calc` + `ill.rules` at load time. The calculus object is the single source of truth for all layers:

```javascript
calculus = {
  rules:       { tensor_r: { descriptor, invertible, pretty, ... }, ... }
  polarity:    { tensor: 'positive', loli: 'negative', ... }
  invertible:  { tensor_r: false, tensor_l: true, loli_r: true, ... }
  AST:         { tensor: (a,b) => hash, ... }
  parse:       "A * B" → hash
  render:      hash → "A * B" | "A \\otimes B"
  isPositive:  tag → boolean
  isNegative:  tag → boolean
}
```

Properties generated from `.rules`:

| Property | Generated by |
|---|---|
| `polarity` | `meta/focusing.js:inferPolarityFromRules` |
| `invertible` | `meta/focusing.js:inferInvertibilityFromRule` |
| `rules[name].descriptor` | `rules2-parser.js:parseRules2` |
| `parser`, `renderer` | `calculus/index.js` from `@ascii`/`@latex`/`@prec` annotations |

## L1 — Kernel (Proof Checker)

Given a proof tree, answers "is this valid?" No search, no strategy, no heuristics.

```javascript
createKernel(calculus) → {
  verifyStep(conclusion, rule, premises) → { valid, error? }
  verifyTree(tree) → { valid, errors[] }
}
```

Rule verification uses `rule-interpreter.js` to compute expected premises from the rule descriptor, then compares against the actual premises.

## L2 — Generic Prover (Search Primitives)

Provides logic-independent search primitives. All functions are unfocused — no polarity filtering.

```javascript
createGenericProver(calculus) → {
  // Helpers
  connective(h)                    // formula hash → tag (null for atoms)
  isPositive(tag), isNegative(tag) // polarity checks
  ruleName(h, side)                // formula + side → rule name
  ruleIsInvertible(tag, side)      // invertibility check

  // Core
  tryIdentity(seq, focusPos, focusIdx) // identity axiom via unification
  applyRule(seq, position, index, spec) // single rule application → premises
  computeChildDelta(premise, delta)     // merge premise linear into delta
  addDeltaToSequent(seq, delta, copy)   // inject delta into sequent

  // Search
  applicableRules(seq, specs, alts)     // enumerate ALL applicable rules
  tryRuleAndRecurse(...)                // apply rule + recurse into premises
}
```

Context threading uses Hodas-Miller lazy splitting: resources flow into the first premise, whatever remains flows to the next.

## L3 — Focused Discipline

Restricts L2's rule enumeration using Andreoli's focusing. Contains only focusing-specific logic.

```javascript
createProver(calculus) → {
  findInvertible(seq)   // find formula with invertible rule
  chooseFocus(seq)      // choose focus targets
  prove(seq, opts)      // focused proof search with phases:
                        //   0: identity, 0.5: copy, 1: inversion,
                        //   2: focus choice, 3: focused decomposition
  // + re-exports L2 helpers
}
```

**Phase structure:**
- **Inversion:** eagerly apply invertible rules (negative R, positive L)
- **Focus:** choose a formula to focus on (positive R, negative L)
- **Decomposition:** apply focused rules until blur or identity
- **Blur:** transition back to inversion when hitting an invertible formula during focus

Polarity assignments come from the calculus object. L3 contains zero logic-specific code.

## L4 — Strategy Layer

Multiple strategies coexist, all built on L3/L2:

**L4a — Manual (interactive):** `strategy/manual.js`
- `getApplicableActions(state, { mode })` — `'focused'` delegates to L3, `'unfocused'` to L2
- `applyAction(state, action, userInput?)` — state transition with optional context split
- Focus actions: `Focus_L` / `Focus_R`

**L4b — Auto (automated backward search):** `strategy/auto.js`
- Wraps L3's `prove()` with goal normalization

**L4c/L4d — Forward Engine:** `lib/engine/`

The forward engine has its own internal layered architecture, separate from the backward proof search (L1–L3). It implements committed-choice forward chaining (multiset rewriting) with a compilation pipeline:

```
┌──────────────────────────────────────────────────────────────┐
│  EXPLORATION       symexec.js                                │
│  DFS over execution tree, mutation+undo, branching           │
├──────────────────────────────────────────────────────────────┤
│  EXECUTION         forward.js: applyMatch, run               │
│  State transformation: consume facts, produce new facts      │
├──────────────────────────────────────────────────────────────┤
│  MATCHING          forward.js: tryMatch, findAllMatches      │
│  Worklist-based pattern matching with de Bruijn theta        │
├──────────────────────────────────────────────────────────────┤
│  INDEXING          symexec.js: strategy stack                │
│  fingerprintLayer → discTreeLayer → predicateLayer           │
├──────────────────────────────────────────────────────────────┤
│  COMPILATION       compile.js, rule-analysis.js              │
│  De Bruijn slots, pattern roles, compiled substitution       │
├──────────────────────────────────────────────────────────────┤
│  STORE             lib/kernel/store.js, unify.js             │
│  Content-addressed SoA arena, matchIndexed, applyIndexed     │
└──────────────────────────────────────────────────────────────┘
```

**Program-aware indexing (auto-detected).** The strategy stack includes a fingerprint layer that detects dominant discriminating predicates from rule structure. For EVM, `code(PC, OPCODE)` is the discriminator — 40 of 44 rules have a ground opcode child. The fingerprint layer resolves these in O(1). This is auto-detected by `detectFingerprintConfig()` from rule patterns; no program-specific code exists. The disc-tree layer (general-purpose trie) handles all remaining rules. See `doc/documentation/strategy-layers.md`.

**Backward proving for guards.** Persistent antecedents (`!C` in `A * B * !C -o { D }`) are proved via backward chaining or FFI. `prove.js` handles clause resolution; `ffi/` handles arithmetic (inc, plus, neq, mul). `tryFFIDirect()` in forward.js bypasses the full prove machinery for O(1) FFI evaluation.

**Mutation+undo.** During DFS exploration, `state`, `stateIndex`, and `pathVisited` are mutated in-place and restored after each child subtree returns. Snapshots are taken only at terminal nodes. See `doc/documentation/symexec-optimizations.md`.

## L5 — UI Layer

Pure view. `proofLogic.ts` is a thin type adapter; `ManualProof.tsx` renders the proof tree and delegates all logic to L4a.

## Genericity

| Layer | Logic-independent | Logic-specific |
|---|---|---|
| **L1 kernel** | Tree verification structure | Rule matching (generated by `rule-interpreter.js`) |
| **L2 generic** | Backtracking, depth limit, Hodas-Miller threading | Which rules exist (from calculus object) |
| **L3 focused** | Phase alternation, blur condition, focus protocol | Polarity assignments (from calculus object) |
| **L4 backward** | Manual UI protocol, auto search | None |
| **L4 forward** | Strategy stack, matching, mutation+undo | None (indexing auto-detected from rules) |
| **L5 UI** | Components, rendering, interaction | None |

Adding a new connective (e.g., temporal `○`/`●`) requires only `.calc` + `.rules` changes. All backward layers pick it up automatically.

Adding new forward rules requires only `.ill` changes. The strategy stack auto-detects whether fingerprint indexing is available from rule structure — no code changes needed for program-specific optimizations.

## Proof State

```javascript
ProofState = {
  conclusion: Sequent,      // what we're proving
  rule: string | null,      // applied rule (null = open goal)
  premises: ProofState[],   // child states
  proven: boolean,          // is this subtree complete?
  focus: { position, index, hash } | null,  // L3 focus state
  delta: Multiset,          // remaining linear resources
}
```

## Backward vs Forward

| | Backward (L1–L3) | Forward (L4c/L4d) |
|---|---|---|
| **State** | Sequent `{ contexts, succedent }` | Flat multiset `{ linear: {h: count}, persistent: {h: true} }` |
| **Matching** | Unification (bidirectional) | Pattern matching (one-way, matchIndexed) |
| **Execution** | Proof tree construction | Multiset rewriting (consume/produce facts) |
| **Indexing** | Rule enumeration from sequent | Strategy stack (fingerprint → disc-tree → predicate) |
| **Shared** | Store, unify.js, substitute.js | Store, unify.js, substitute.js |

See `doc/dev/forward-optimization-roadmap.md` for profiling history (181ms → ~1ms).

## Open Research

| Question | Notes |
|---|---|
| Lax monad `{A}` as backward/forward mode switch | CLF/Celf/LolliMon integrate via monad. May restructure L2/L4c boundary |
| Metaproofs over execution trees | Property verification: conservation, safety, reachability, deadlock-freedom |
| Generic structural interpreter per family | Different families (LNL, display, adjoint) need parameterized interpreter |
| Ceptre stages | Named rule subsets running to quiescence with inter-stage transitions |

## References

- HOL Light kernel: ~400 lines, abstract `thm` type ([Harrison](https://www.cl.cam.ac.uk/~jrh13/papers/hollight.pdf))
- Isabelle layering: kernel → tactics → Sledgehammer ([Paulson](https://arxiv.org/pdf/1907.02836))
- Foundational Proof Certificates: focusing as proof format ([Miller](https://dl.acm.org/doi/10.1145/2503887.2503894))
- Hodas-Miller lazy splitting ([1994](https://www.sciencedirect.com/science/article/pii/S0890540184710364))
- Sterling-Harper proof refinement logics ([2017](https://arxiv.org/abs/1703.05215))
