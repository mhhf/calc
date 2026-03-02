---
title: "Forward Chaining Engine — Architecture & Implementation"
created: 2026-02-18
modified: 2026-02-23
summary: How the CALC forward chaining engine works — modules, data flow, matching, strategy, optimizations.
tags: [implementation, forward-chaining, engine, architecture, CHR]
---

# Forward Chaining Engine

The forward engine executes ILL programs by multiset rewriting. A state (multiset of linear + persistent facts) is transformed by rules until quiescence. Conceptually a CHR-like runtime with exhaustive exploration (CHR-v).

## Module Architecture

```mermaid
graph TB
    subgraph Compilation["Compile Time"]
        COMPILE["<b>compile.js</b> (315 lines)<br/>Rule compilation:<br/>flatten, de Bruijn slots,<br/>discriminator detection"]
        ANALYSIS["<b>rule-analysis.js</b> (285 lines)<br/>Pattern classification:<br/>preserved, delta, consumed,<br/>compiled substitution"]
    end

    subgraph Runtime["Runtime"]
        MATCH["<b>match.js</b> (730 lines)<br/>Pattern matching primitives:<br/>tryMatch, provePersistentGoals,<br/>matchLoli, state indexing"]
        STRATEGY["<b>strategy.js</b> (237 lines)<br/>Rule selection:<br/>fingerprint, disc-tree, predicate<br/>findMatch, findAllMatches"]
        FORWARD["<b>forward.js</b> (145 lines)<br/>Execution + main loop:<br/>applyMatch, run, createState"]
        SYMEXEC["<b>symexec.js</b> (590 lines)<br/>Exhaustive exploration:<br/>explore, mutateState/undo,<br/>ExploreContext, tree utils"]
    end

    subgraph Support["Support"]
        DTREE["<b>disc-tree.js</b> (242 lines)<br/>Discrimination tree indexing"]
        PROVE["<b>prove.js</b> (350 lines)<br/>Backward chaining"]
        FFI["<b>ffi/</b><br/>Foreign function interface"]
        CONVERT["<b>convert.js</b> (403 lines)<br/>.ill → content-addressed hashes"]
    end

    subgraph Kernel["lib/kernel/"]
        STORE["store.js — content-addressed arena"]
        UNIFY["unify.js — matchIndexed, undo stack"]
        SUBST["substitute.js — applyIndexed, subCompiled"]
    end

    COMPILE --> ANALYSIS
    MATCH --> UNIFY
    MATCH --> SUBST
    MATCH --> PROVE
    MATCH --> FFI
    STRATEGY --> MATCH
    STRATEGY --> DTREE
    FORWARD --> STRATEGY
    FORWARD --> MATCH
    FORWARD --> COMPILE
    SYMEXEC --> STRATEGY
    SYMEXEC --> MATCH
    SYMEXEC --> SUBST
    PROVE --> FFI
    PROVE --> UNIFY

    style MATCH fill:#cce5ff,stroke:#004085
    style STRATEGY fill:#e2d5f1,stroke:#5a3d8a
    style FORWARD fill:#d4edda,stroke:#155724
    style SYMEXEC fill:#fff3cd,stroke:#856404
    style COMPILE fill:#e8e8e8,stroke:#666
    style ANALYSIS fill:#e8e8e8,stroke:#666
```

## Data Flow: .ill to Execution

```mermaid
flowchart LR
    ILL[".ill file"] --> CONV["convert.load()"]
    CONV --> TYPES["types"]
    CONV --> CLAUSES["clauses<br/>(backward)"]
    CONV --> FWRULES["forwardRules<br/>(raw)"]

    FWRULES --> COMP["compileRule()"]
    COMP --> COMPILED["compiled rules<br/>slots, triggers,<br/>pattern roles,<br/>compiled sub"]

    CLAUSES --> IDX["prove.buildIndex()"]
    IDX --> CIDX["clause index"]

    COMPILED --> RUN["forward.run()"]
    COMPILED --> EXPLORE["symexec.explore()"]
    CIDX --> RUN
    CIDX --> EXPLORE
```

## Matching Pipeline

`tryMatch(rule, state, calc)` — "can this rule fire against this state?"

```mermaid
flowchart TB
    START["tryMatch(rule, state)"] --> SETUP["Create theta[], consumed{}, reserved{}"]
    SETUP --> WORKLIST

    subgraph WORKLIST["matchAllLinear — worklist with persistent interleaving"]
        direction TB
        LP["Phase 1: Match next linear pattern"]
        PP["Phase 2: Prove persistent patterns"]
        LP --> |"all linear matched"| PP
        PP --> |"new bindings unlock deferred patterns"| LP
        LP --> |"pattern fails"| FAIL1["FAIL"]
        PP --> |"can't prove"| FAIL2["FAIL"]
    end

    subgraph LINEAR["Linear Pattern Strategies"]
        direction TB
        A["<b>Delta bypass</b><br/>Direct Store.child extraction<br/>O(arity) for flat deltas"]
        B["<b>Secondary index</b><br/>O(1) fingerprint lookup<br/>for discriminator predicate"]
        C["<b>General matching</b><br/>matchIndexed against<br/>indexed candidates"]
        A --> |"not delta"| B
        B --> |"not fingerprint"| C
    end

    LP --> LINEAR

    WORKLIST --> EXIST["resolveExistentials()<br/>bind forall vars via state/FFI/backward"]
    EXIST --> RESULT["return { rule, theta, consumed }"]

    style FAIL1 fill:#f8d7da,stroke:#721c24
    style FAIL2 fill:#f8d7da,stroke:#721c24
    style RESULT fill:#d4edda,stroke:#155724
```

## Persistent Proving

Persistent antecedents (e.g. `!inc PC PC'`, `!neq X Y`) must be proved, not consumed. Two conceptual levels:

```mermaid
flowchart TB
    GOAL["Persistent goal<br/>e.g. inc(PC, PC')"] --> LOOKUP

    subgraph LEVEL1["Level 1: State Lookup"]
        LOOKUP["Pattern-match against<br/>state.persistent facts"]
    end

    LOOKUP --> |"found"| SUCCESS["Proved<br/>update theta"]
    LOOKUP --> |"not in state"| BACKWARD

    subgraph LEVEL2["Level 2: Backward Prove"]
        BACKWARD["prove(goal)"]
        FFI_CHECK{"FFI available<br/>for predicate?"}
        FFI["<b>2a. FFI</b><br/>O(1) arithmetic<br/>(inc, plus, neq, ...)"]
        CLAUSES["<b>2b. Clause resolution</b><br/>Backward chaining<br/>via prove.js"]

        BACKWARD --> FFI_CHECK
        FFI_CHECK --> |"yes"| FFI
        FFI_CHECK --> |"no"| CLAUSES
        FFI --> |"mode mismatch"| CLAUSES
    end

    FFI --> |"success"| SUCCESS
    FFI --> |"definitive fail<br/>(e.g. neq 5 5)"| FAIL["FAIL<br/>rule cannot fire"]
    CLAUSES --> |"success"| SUCCESS
    CLAUSES --> |"fail"| FAIL

    style SUCCESS fill:#d4edda,stroke:#155724
    style FAIL fill:#f8d7da,stroke:#721c24
    style FFI fill:#fff3cd,stroke:#856404
```

FFI is an optimization of backward proving — arithmetic predicates like `inc`, `plus`, `neq` have O(1) native implementations that bypass the full clause resolution pipeline.

## Strategy Stack

Rule selection uses a layered strategy stack. Each layer claims rules it can index efficiently; unclaimed rules fall through.

```mermaid
flowchart TB
    STATE["State + Rules"] --> DETECT["detectStrategy(rules)<br/>auto-select layers"]

    DETECT --> FP{"Fingerprint<br/>structure<br/>detected?"}
    FP --> |"yes"| FPLAYER["<b>Fingerprint Layer</b><br/>O(1) by ground discriminator<br/>e.g. code(PC, <b>OPCODE</b>)<br/>Claims 40/44 EVM rules"]
    FP --> |"no"| DTLAYER

    FPLAYER --> |"unclaimed rules"| DTLAYER["<b>Disc-Tree Layer</b><br/>O(depth) trie lookup<br/>Catches remaining rules"]

    DTLAYER --> |"unclaimed rules"| PREDLAYER["<b>Predicate Layer</b><br/>O(R) safety net<br/>Filter by trigger preds"]

    subgraph Selection["Selection Modes"]
        COMMITTED["<b>findMatch</b><br/>First match (committed choice)<br/>Used by forward.run()"]
        EXHAUSTIVE["<b>findAllMatches</b><br/>All matches + loli scan<br/>Used by symexec.explore()"]
    end

    FPLAYER --> Selection
    DTLAYER --> Selection
    PREDLAYER --> Selection
```

The fingerprint layer is **program-agnostic** — it auto-detects any dominant discriminating predicate from rule structure. For EVM, `code(PC, OPCODE)` is the discriminator (40/44 rules have a ground opcode child). For other programs, a different predicate may be detected, or the fingerprint layer is skipped entirely.

## Execution Modes

### Single-Path: `forward.run()`

Committed choice — fires first matching rule, one execution path:

```
while steps < maxSteps:
  m = findMatch(state, rules, calc)      // strategy stack
  if !m: m = matchFirstLoli(state, calc) // loli fallback
  if !m: return QUIESCENT
  state = applyMatch(state, m)           // immutable: new state
```

### Exhaustive: `symexec.explore()`

DFS over all execution paths with mutation + undo:

```mermaid
flowchart TB
    START["explore(state, rules)"] --> INIT["Create mutable state copy<br/>Build ExploreContext (index + hash)"]
    INIT --> DFS

    subgraph DFS["go(depth, ctx)"]
        CYCLE{"cycle?<br/>hash in<br/>pathVisited"} --> |"yes"| CYCLENODE["CYCLE node"]
        CYCLE --> |"no"| DEPTH{"depth<br/>limit?"}
        DEPTH --> |"yes"| BOUNDNODE["BOUND node"]
        DEPTH --> |"no"| FIND["findAllMatches()"]
        FIND --> |"none"| LEAF["LEAF node<br/>(snapshot state)"]
        FIND --> |"matches found"| FOREACH

        subgraph FOREACH["For each match"]
            MUTATE["mutateState()<br/>in-place + undo log"]
            CHILD_CTX["makeChildCtx()<br/>incremental index + hash"]
            RECURSE["go(depth+1, childCtx)"]
            UNDO_IDX["undoIndexChanges()"]
            UNDO_STATE["undoMutate()"]

            MUTATE --> CHILD_CTX --> RECURSE --> UNDO_IDX --> UNDO_STATE
        end
    end

    DFS --> TREE["Execution tree<br/>leaf / branch / bound / cycle"]
```

**Core invariant:** When `go()` returns, state, stateIndex, and pathVisited are in their original state.

## Rule Compilation Pipeline

`compileRule(rule)` transforms a raw rule into an optimized compiled form:

```mermaid
flowchart LR
    RAW["Raw rule<br/>{name, hash,<br/>antecedent,<br/>consequent}"]

    RAW --> F1["flattenTensor<br/>→ linear[] + persistent[]"]
    F1 --> F2["Extract triggers<br/>+ discriminator"]
    F2 --> F3["Collect persistent<br/>output vars"]
    F3 --> F4["De Bruijn slot<br/>assignment"]
    F4 --> F5["analyzeDeltas<br/>preserved/consumed/delta"]
    F5 --> F6["computePatternRoles<br/>per-position metadata"]
    F6 --> F7["compileSubstitution<br/>O(1) recipes"]
    F7 --> F8["expandConsequentChoices<br/>pre-expand with/oplus"]

    F8 --> COMPILED["Compiled rule"]
```

## Loli Continuations

Guarded loli continuations (e.g. `!eq V 0 -o { stack SH 1 }`) become linear facts in state. `matchLoli` uses the same persistent proving pipeline as `tryMatch`:

1. Extract trigger → `flattenTensor` → linear + persistent components
2. Match linear triggers against state (via matchIndexed)
3. Prove persistent triggers (state lookup → backward prove [FFI | clauses])
4. Guard succeeds → loli fires, body produced. Guard fails → null (stuck leaf).

## Optimization Summary

| Stage | What | Speedup | Technique |
|-------|------|---------|-----------|
| Strategy stack | Rule selection | 12.7x | O(1) fingerprint + disc-tree vs O(R) scan |
| Incremental context | State hashing + indexing | 1.7x | O(delta) XOR hash + incremental index |
| Mutation + undo | State management | 1.8x | In-place mutation, undo log, snapshot only at terminals |
| Index + Set undo | Index management | 1.25x | Mutable index + undo, mutable pathVisited |
| Direct FFI bypass | Persistent proving | 1.2x | O(1) FFI call inside backward prove |
| De Bruijn theta | Substitution lookup | 2.1x | Compile-time slot assignment, O(1) access |
| Delta bypass | Linear matching | ~8% | Direct Store.child extraction for flat patterns |
| Compiled substitution | Consequent production | ~8% | Store.put recipe vs generic applyIndexed |
| Disc-tree | Catch-all rule selection | ~0% at 44 rules | Trie over preorder traversals |
| Flat undo log | State undo | ~13% | Flat array vs object allocation |
| Numeric tagId | Tag comparison | ~2% | Numeric comparison vs string |
| Unified loli matching | Soundness fix | 62x | Dead branches → stuck leaves |

Total: **181ms → ~1ms** median for the 210-node multisig execution tree (43 rules).

## CHR Correspondence

The forward engine implements a fragment of CHR (Constraint Handling Rules):

| CHR | CALC Forward Engine |
|-----|---------------------|
| Simpagation `H1 \ H2 <=> G \| B` | Forward rule: preserved + consumed → produced |
| Removed heads (H2) | Linear facts in `state.linear` |
| Kept heads (H1) | Persistent facts in `state.persistent` |
| Guard evaluation | Persistent proving (state lookup → backward) |
| CHR-v disjunctive body | oplus in consequent (`expandChoiceItem` forking) |
| Propagation history | N/A (lolis are self-deleting linear facts) |
| omega_r occurrence iteration | Strategy stack (fingerprint → disc-tree → predicate) |
| Committed choice | `forward.run()` |
| CHR-v backtracking search | `symexec.explore()` with mutation + undo |

Soundness: Betz & Fruhwirth (2013) — every CHR derivation corresponds to a valid ILL proof.

## Design Decisions

**TREAT-like, not Rete.** No cached partial matches. Full re-evaluation per step. Correct for linear logic's non-monotonicity.

**Strategy stack over Rete network.** Layered indexing auto-detected from rule structure. Each layer claims rules; unclaimed fall through.

**Mutation + undo over immutable state.** DFS mutates one shared state in-place, restoring after each child. Only terminals snapshot.

**De Bruijn indexed theta.** Metavars get compile-time slot indices. Theta is a flat array.

**State lookup before backward proving.** Check if a persistent fact is already known before attempting to prove it via FFI or clause resolution.

**FFI as backward prove optimization.** FFI (arithmetic) is conceptually a fast path within backward proving, not a separate proving mechanism.
