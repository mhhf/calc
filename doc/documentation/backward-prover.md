---
title: "Backward Prover Architecture"
created: 2026-02-23
modified: 2026-02-23
summary: Clean layered architecture of the backward proof search engine (L1-L4a).
tags: [architecture, prover, backward, focusing, layers]
---

# Backward Prover Architecture

The backward prover searches for proofs of ILL sequents. It is structured as five layers with strict upward-only dependency and shared utilities.

```mermaid
graph TB
    subgraph Layers["Prover Layers"]
        direction TB
        L5["<b>L5 UI</b><br/>ManualProof.tsx, proofLogic.ts<br/><i>Pure view — renders proof tree</i>"]
        L4["<b>L4 Strategy</b><br/>manual.js, auto.js<br/><i>Which rules to try, in what order</i>"]
        L3["<b>L3 Focused Discipline</b><br/>focused.js (291 lines)<br/><i>Inversion / focus / blur phases</i>"]
        L2["<b>L2 Generic Prover</b><br/>generic.js (234 lines)<br/><i>Search primitives — apply rule, enumerate</i>"]
        L1["<b>L1 Kernel</b><br/>kernel.js (193 lines)<br/><i>Proof verification — trusted core</i>"]
        L0["<b>L0 Calculus Object</b><br/>.calc + .rules files<br/><i>Single source of truth</i>"]
    end

    L5 --> L4
    L4 --> L3
    L4 -.->|unfocused mode| L2
    L3 --> L2
    L2 --> L1
    L1 --> L0

    subgraph Shared["Shared Utilities"]
        CTX["context.js<br/>Multiset operations"]
        ST["state.js<br/>FocusedProofState"]
        PT["pt.js<br/>ProofTree"]
        RI["rule-interpreter.js<br/>Descriptor → specs"]
    end

    L2 --> CTX
    L2 --> RI
    L3 --> ST
    L3 --> PT
    L1 --> RI

    style L1 fill:#d4edda,stroke:#155724
    style L2 fill:#cce5ff,stroke:#004085
    style L3 fill:#e2d5f1,stroke:#5a3d8a
    style L4 fill:#fff3cd,stroke:#856404
    style L5 fill:#f8d7da,stroke:#721c24
    style L0 fill:#e8e8e8,stroke:#666
```

## Layer Responsibilities

### L0 — Calculus Object

Generated from `.calc` + `.rules` files at load time. Single source of truth for all layers.

```javascript
calculus = {
  rules:      { tensor_r: { descriptor, invertible, ... }, ... },
  polarity:   { tensor: 'positive', loli: 'negative', ... },
  isPositive: tag => boolean,
  isNegative: tag => boolean,
  parse:      "A * B" => hash,
  render:     hash => "A \\otimes B",
}
```

### L1 — Kernel (Proof Checker)

The trusted core. Answers "is this proof tree valid?" — never searches.

```javascript
createKernel(calculus) => {
  verifyStep(conclusion, ruleName, premises) => { valid, error? }
  verifyTree(tree) => { valid, errors[] }
}
```

193 lines. Can be read in one sitting. Bugs here are security bugs; bugs in L2-L4 are completeness/performance bugs.

### L2 — Generic Prover (Search Primitives)

Logic-independent search utilities. No polarity awareness.

```javascript
createGenericProver(calculus) => {
  connective(h)                     // hash => tag (null for atoms)
  isPositive(tag), isNegative(tag)  // polarity (delegates to calculus)
  ruleName(h, side)                 // formula + side => rule name
  tryIdentity(seq, pos, idx)        // identity axiom
  applyRule(seq, pos, idx, spec)    // single rule application => premises
  applicableRules(seq, specs, alts) // enumerate ALL applicable rules
}
```

Context threading uses Hodas-Miller lazy splitting: resources flow into the first premise, whatever remains flows to the next.

### L3 — Focused Discipline

Restricts L2's search using Andreoli's focusing. Three phases:

```mermaid
stateDiagram-v2
    [*] --> Identity: try axiom
    Identity --> Inversion: not identity
    Inversion --> Inversion: invertible rule found
    Inversion --> Focus: no invertible rules
    Focus --> Decomposition: choose focus target
    Decomposition --> Decomposition: focused rule
    Decomposition --> Blur: hit invertible formula
    Blur --> Inversion: restart inversion
    Decomposition --> [*]: identity / complete
    Inversion --> [*]: identity / complete
```

- **Inversion**: eagerly apply all invertible rules (negative right, positive left)
- **Focus**: choose a formula to focus on (positive right, negative left)
- **Decomposition**: apply focused rules until blur or identity
- **Blur**: transition back to inversion when hitting an invertible formula during focus

### L4 — Strategy

**L4a Manual** (`manual.js`): Interactive proof. `getApplicableActions(state, {mode})` delegates to L3 (focused) or L2 (unfocused). Focus actions: `Focus_L` / `Focus_R`.

**L4b Auto** (`auto.js`): Wraps L3's `prove()` with goal normalization.

## Data Flow

```mermaid
flowchart LR
    subgraph Input
        CALC[".calc + .rules"]
        SEQ["Sequent<br/>{contexts, succedent}"]
    end

    subgraph Compilation
        RI["rule-interpreter.js<br/>computeRuleSpecMeta()"]
        SPECS["specs: {<br/>  makePremises,<br/>  copyContext,<br/>  contextSplit<br/>}"]
    end

    subgraph Search["Proof Search"]
        L3P["L3 prove()"]
        L2A["L2 applyRule()"]
        L2I["L2 tryIdentity()"]
    end

    subgraph Output
        PT["ProofTree<br/>{conclusion, rule,<br/> premises, proven}"]
    end

    CALC --> RI --> SPECS
    SEQ --> L3P
    SPECS --> L2A
    L3P --> L2A
    L3P --> L2I
    L2A --> L3P
    L3P --> PT
```

## Design Patterns

**Vertical stratification.** Each layer has one job. L3 never reimplements L2 logic — it calls `applyRule()`.

**Cascading delegation.** Upper layers compose lower layers' APIs. No layer reaches into another's internals.

**Data over code.** Polarity, invertibility, rules — all tables in the calculus object, queried by L2/L3. Zero logic-specific code in the prover.

**Two-phase compilation.** `computeRuleSpecMeta()` runs at build time, producing JSON-serializable data. `buildRuleSpecsFromMeta()` creates closures at runtime. Browser loads precomputed metadata from `ill.json`.

**Immutable state objects.** `FocusedProofState` transitions create new instances. Multisets are externally immutable. ProofTree is immutable once created.

**Factored recursion.** `tryRuleAndRecurse()` extracts the "apply rule + recurse into premises" pattern to avoid duplication across phases.
