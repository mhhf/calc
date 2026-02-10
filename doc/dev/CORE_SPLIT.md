---
title: Core/Calculus Separation
created: 2026-02-10
modified: 2026-02-10
summary: Design for separating generic sequent calculus machinery from ILL-specific focused proof search optimization
tags: [architecture, separation, prover, core, calculus]
---

# Core/Calculus Separation Architecture

Design document for separating generic "Gentzen machinery" from logic-specific optimized provers.

---

## Table of Contents

1. [Vision](#vision)
2. [Two Separate Provers](#two-separate-provers)
3. [File Structure with Types](#file-structure-with-types)
4. [Current State Analysis](#current-state-analysis)
5. [Multi-Type Display Calculus](#multi-type-display-calculus)
6. [Open Questions](#open-questions)
7. [Future: Prover Interoperability](#future-prover-interoperability)

---

## Vision

### The Problem

The current codebase mixes two concerns:
1. **What ILL is** (syntax + rules) - the calculus definition
2. **How to prove things efficiently in ILL** (focusing, polarity, lazy splitting) - prover optimization

### The Solution: Two Separate Provers

```
┌─────────────────────────────────────────────────────────────────┐
│                    ILL Prover (Specialized)                      │
│         Focused proof search, lazy resource management           │
│                                                                  │
│    - Fast (polynomial)                                           │
│    - Uses focusing, polarity, lazy splitting                     │
│    - ILL-specific (not portable)                                 │
│    - Produces: ProofTree                                         │
└─────────────────────────────────────────────────────────────────┘

┌─────────────────────────────────────────────────────────────────┐
│                    Generic Prover (Core)                         │
│              "I just try all rules, including structural"        │
│                                                                  │
│    - Correct by construction                                     │
│    - Works for ANY calculus (ordered, linear, classical...)      │
│    - Slow (no optimizations)                                     │
│    - Can verify proof trees from specialized provers             │
└─────────────────────────────────────────────────────────────────┘
```

**Key insight**: These are TWO SEPARATE implementations. No oracle/FFI interaction for now.
The only interaction is: ILLProver produces a ProofTree, GenericProver can verify it.

### Why Separate?

1. **YAGNI**: Don't abstract until we have a second specialized prover
2. **Correctness**: GenericProver is simple enough to trust
3. **Experimentation**: ILLProver can use any optimizations
4. **Verification**: GenericProver.verify(proofTree) catches bugs in specialized provers

---

## Two Separate Provers

### GenericProver

A "dumb" prover that works for ANY sequent calculus. Key principles:

1. **No explicit enumeration of context splits**
   - Splitting is implicit through structural rules (P_L, P_R, A_L, A_R, I_L, I_R)
   - This allows supporting ordered logic (no exchange), linear logic, etc.
   - Enumeration is already an optimization - we avoid it here

2. **Just try all rules**
   - For each goal, try matching against each rule's conclusion
   - If match succeeds, recursively prove premises
   - Backtrack on failure

3. **Loop detection required**
   - Structural rules can loop: A, B => B, A => A, B => ...
   - Need visited state tracking or depth limiting

```typescript
// lib/core/prover.ts

type ProofTree = {
  type: string;                    // Rule name
  conclusion: Sequent;
  premises: ProofTree[];
  substitution: Substitution;
}

type ProofResult =
  | { success: true; proof: ProofTree }
  | { success: false }

class GenericProver {
  calculus: Calculus;
  visited: Set<string>;  // For loop detection
  maxDepth: number;

  constructor(calculus: Calculus, options?: { maxDepth?: number });

  // Main entry point
  prove(goal: Sequent): ProofResult;

  // Verify a proof tree (from specialized prover)
  verify(proof: ProofTree): boolean;

  // Internal: try all rules
  private tryAllRules(goal: Sequent, depth: number): ProofResult;

  // Internal: match rule conclusion against goal
  private matchRule(rule: Rule, goal: Sequent): Substitution | null;
}
```

**Important**: The GenericProver includes structural rules in its search. This means:
- It tries display postulates (P_L, P_R, etc.) as regular rules
- Context splitting happens implicitly through these rules
- This is slower but more general (works for ordered logic too)

### ILLProver

The current focused prover, kept as-is. It's specialized for ILL:

```typescript
// lib/provers/ill/prover.ts

class ILLProver {
  polarity: Map<string, 'positive' | 'negative'>;
  contextModes: Map<string, 'split' | 'copy'>;

  constructor(calculus: Calculus);

  // Prove using focused proof search with lazy resource management
  prove(goal: Sequent): ProofResult;

  // The key optimization: lazy resource management
  // See dev/research/proof-search-oracles.md for details
  private provePremises(pt: ProofTree): ProofResult;
}
```

The ILLProver uses:
- **Focusing discipline** (Andreoli): inversion → focus choice → focused decomposition
- **Lazy resource management** (Hodas-Miller): delta_in → prove → delta_out
- **Polarity** (inferred from rules): determines which phase a formula belongs to

See `dev/research/proof-search-oracles.md` for detailed documentation.

---

## File Structure with Types

### Proposed Structure

```
ll.json                     # CALCULUS DEFINITION
                            # - Syntax (calc_structure)
                            # - Rules (rules)
                            # - Display formats (ascii, latex, isabelle)
                            # - NO prover hints

lib/
├── core/                   # GENERIC MACHINERY
│   │
│   ├── types.ts            # Core type definitions
│   │   │
│   │   │  type Node = {
│   │   │    id: number;
│   │   │    ruleName: string;
│   │   │    ruleConstructor: string;
│   │   │    vals: (Node | string)[];
│   │   │  }
│   │   │
│   │   │  type Sequent = {
│   │   │    antecedent: Context;
│   │   │    succedent: Node;
│   │   │  }
│   │   │
│   │   │  type ProofTree = {
│   │   │    type: string;
│   │   │    conclusion: Sequent;
│   │   │    premises: ProofTree[];
│   │   │    substitution: Substitution;
│   │   │    delta_in?: Multiset;   // For resource tracking
│   │   │    delta_out?: Multiset;  // For resource tracking
│   │   │  }
│   │   │
│   │   │  type Rule = {
│   │   │    name: string;
│   │   │    conclusion: string;    // Pattern
│   │   │    premises: string[];    // Patterns
│   │   │  }
│   │   │
│   │   │  type Calculus = {
│   │   │    name: string;
│   │   │    structure: Record<string, Record<string, StructureRule>>;
│   │   │    rules: Record<string, Record<string, Rule>>;
│   │   │  }
│   │
│   ├── prover.ts           # Generic structural prover
│   │   │
│   │   │  class GenericProver {
│   │   │    prove(goal: Sequent): ProofResult
│   │   │    verify(proof: ProofTree): boolean
│   │   │  }
│   │
│   ├── node.ts             # AST representation
│   │   │
│   │   │  class Node {
│   │   │    copy(): Node
│   │   │    toString(options?: FormatOptions): string
│   │   │    toLatex(): string
│   │   │    toIsabelle(): string
│   │   │  }
│   │
│   ├── sequent.ts          # Sequent operations
│   │   │
│   │   │  class Sequent {
│   │   │    substitute(theta: Substitution): Sequent
│   │   │    toString(options?: FormatOptions): string
│   │   │  }
│   │   │
│   │   │  // Static helpers
│   │   │  Sequent.fromAntecedent(structure: Node): Sequent
│   │   │  Sequent.copy(seq: Sequent): Sequent
│   │
│   ├── mgu.ts              # Most general unifier
│   │   │
│   │   │  function mgu(n1: Node, n2: Node): Substitution | false
│   │
│   ├── substitute.ts       # Substitution application
│   │   │
│   │   │  function substitute(node: Node, key: Node, val: Node): Node
│   │
│   ├── parser.ts           # Parser generator (from calculus)
│   │   │
│   │   │  function generateParser(calculus: Calculus): Parser
│   │   │  function parse(input: string): Node
│   │
│   ├── calc.ts             # Calculus database
│   │   │
│   │   │  const Calc = {
│   │   │    db: Calculus,
│   │   │    init(calc: Calculus): void,
│   │   │    getRule(id: number): Rule,
│   │   │  }
│   │
│   └── pt.ts               # Proof tree utilities
│       │
│       │  class PT {
│       │    static fresh(rule: Rule): ProofTree
│       │    static toString(pt: ProofTree): string
│       │    static toLatex(pt: ProofTree): string
│       │  }
│
├── provers/                # SPECIALIZED PROVERS
│   │
│   └── ill/
│       │
│       ├── prover.ts       # ILL focused prover
│       │   │
│       │   │  class ILLProver {
│       │   │    prove(goal: Sequent): ProofResult
│       │   │  }
│       │
│       ├── polarity.ts     # Polarity inference
│       │   │
│       │   │  function inferAllPolarities(rules): Map<string, Polarity>
│       │
│       └── config.ts       # ILL-specific configuration
│           │
│           │  const contextModes = {
│           │    'Tensor_R': 'split',
│           │    'Loli_L': 'split',
│           │    'With_R': 'copy',
│           │  }
│           │
│           │  const specialRules = {
│           │    'Bang_L': { action: 'promote_to_persistent' }
│           │  }
│
└── index.ts                # Main entry
    │
    │  export { GenericProver } from './core/prover'
    │  export { ILLProver } from './provers/ill/prover'
    │  export { Calc } from './core/calc'
```

> why do we need a config.ts to begin with? can't we put it all into ill/prover.ts ?

### Where Do Interpretations Go?

**Interpretations (ascii, latex, isabelle) stay in ll.json.**

They are part of the calculus definition - how to display formulas. Example:

```json
{
  "Formula_Tensor": {
    "type": ["Formula", "Formula"],
    "ascii": "_ * _",
    "latex": "_ \\otimes _",
    "isabelle": "_ \\<otimes> _"
  }
}
```

This is correct - ll.json defines both:
- **Syntax**: what constructs exist, their types
- **Presentation**: how to display them in various formats

---

## Current State Analysis

### What's Already Generic

| File            | Status     | Notes                          |
| ------          | --------   | -------                        |
| `mgu.js`        | ✅ Generic | No changes needed              |
| `pt.js`         | ✅ Generic | No changes needed              |
| `helper.js`     | ✅ Generic | No changes needed              |
| `parser.js`     | ✅ Generic | Already fully parametric       |

### What Needs Investigation

| File            | Issue                     | Investigation Needed                |
| ------          | -------                   | ----------                          |
| `substitute.js` | `Formula_Forall` check    | Is this for bound variables? Can generalize to any binder? |
| `calc.js`       | `Structure_Term_Formula`  | Marks "term type" - can infer from types? |
| `compare.js`    | Commented code            | Check git history - why added/removed? |
| `sequent.js`    | `persistent_ctx`, `linear_ctx` | This IS multi-type DC! See below |
| `node.js`       | `isLax()`, `isMonad()`    | ILL-specific, move to prover |

### Code Details

**substitute.js:10 - Formula_Forall check**
```javascript
if (type.ruleName === "Formula_Forall" && node.vals[0].vals[0] == key.vals[0]) {
  return node;  // Don't substitute bound variable
}
```
This avoids substituting bound variables in ∀x.P. It's a standard requirement for substitution with binders.
- Could generalize: any rule that "binds" a variable in its first child
- Or: mark binder rules in ll.json with `"binds": 0`
- Or: YAGNI - keep hardcoded, only one binder currently

**calc.js:214 - Structure_Term_Formula check**
```javascript
if (ruleName === "Structure_Term_Formula" || ruleName === "Structure_Focused_Term_Formula") {
  o.isTermType = true;
}
```
Marks nodes as "term type" for rendering. Could infer from types (rules with Formula child).
Or: YAGNI - only used for display.

---

## Multi-Type Display Calculus

### Our Sequent Structure IS Multi-Type

Looking at `sequent.js`:

```javascript
class Sequent {
  constructor(params) {
    this.persistent_ctx = params?.persistent_ctx || {};  // Set (Cartesian/unrestricted)
    this.linear_ctx = params?.linear_ctx || {};          // Multiset (Linear)
    this.succedent = params?.succedent || {};
  }
}
```

This is **Benton's LNL (Linear/Non-Linear) logic**:
- `linear_ctx` = Linear type (resources, used exactly once)
- `persistent_ctx` = Cartesian type (assumptions, can be reused)

The **Bang_L rule** is the bridge:
```
!A (linear) → A (persistent)
```

This is `F: Lin → Cart` in Benton's terminology.

### Can We Generalize?

The "special rule" handling for Bang_L in `proofstate.js`:
```javascript
if (pt.type === "Bang_L") {
  // Extract inner formula and add to persistent context
  let inner = pt.conclusion.succedent.vals[1].vals[0];
  pt.conclusion.persistent_ctx[id] = inner;
}
```

**Question**: Can this be specified declaratively rather than hardcoded?

Possibilities:
1. **Multi-type rules in ll.json**: Mark rules as "bridge rules" with source/target types
2. **Superstructural layer**: Rules that operate on the context structure itself
3. **Keep it simple**: Bang_L is the only bridge rule in ILL, hardcode is fine

---

## Open Questions

### 1. Loop Detection in GenericProver

Structural rules can loop infinitely:
```
A, B ⊢ C
⟹ (by exchange) B, A ⊢ C
⟹ (by exchange) A, B ⊢ C
⟹ ...
```

Options:
- **Visited set**: Hash sequents, don't revisit
- **Depth limit**: Stop after N steps
- **Canonical forms**: Normalize sequents before comparison
- **Ordered search**: Prioritize logical rules over structural

### 2. Verification Granularity

When GenericProver.verify(proofTree):
- Check rule names are valid?
- Check substitutions are correct?
- Check resource flow (delta_in ⊇ delta_out)?
- Re-prove from scratch?

Start simple: just check each rule application is valid.

### 3. Where Does Polarity Live?

Currently inferred at load time by `lib/polarity.js`. Options:
- Keep as-is (inferred from rules)
- Move to `lib/provers/ill/polarity.js` (prover-specific)
- Both: core infers, prover can override

---

## Future: Prover Interoperability

**NOT implementing now** - YAGNI. But documenting for future reference.

### LCF Architecture

The classic approach (used by Isabelle, Coq, Lean):
- **Trusted kernel**: Small, verified, produces proofs
- **Untrusted tactics**: Large, optimized, suggest proof steps
- **Verification**: Kernel checks tactic output

### For CALC

```
ILLProver.prove(goal)  →  ProofTree
                              │
                              ▼
GenericProver.verify(proofTree)  →  true/false
```

The ILLProver is an "untrusted tactic" that produces proof trees.
The GenericProver is the "trusted kernel" that verifies them.

### Sledgehammer-Style Orchestration

Multiple provers in parallel, first to succeed wins:
```javascript
async function prove(goal) {
  return Promise.race([
    illProver.prove(goal),
    genericProver.prove(goal),
    // future: otherProver.prove(goal)
  ]);
}
```

**Requires research**: See `dev/research/interactive_proving.md` (TODO).

---

*Created: 2026-01-27*
*Updated: 2026-01-28*
