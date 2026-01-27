# Core/Calculus Separation Architecture

Design document for separating generic "Gentzen machinery" from logic-specific optimized provers.

---

## Table of Contents

1. [Vision](#vision)
2. [Two-Tier Prover Architecture](#two-tier-prover-architecture)
3. [Oracle/FFI Protocol](#oracleffi-protocol)
4. [File Separation Philosophy](#file-separation-philosophy)
5. [Current State Analysis](#current-state-analysis)
6. [Implementation Details](#implementation-details)
7. [Migration Strategy](#migration-strategy)

---

## Vision

### The Problem

The current codebase mixes two concerns:
1. **What ILL is** (syntax + rules) - the calculus definition
2. **How to prove things efficiently in ILL** (focusing, polarity, context splitting) - prover optimization

### The Solution: Two Tiers

```
┌─────────────────────────────────────────────────────────────────┐
│                    Optimized Prover (ILL)                        │
│         "I know focusing, polarity, efficient splitting"         │
│                                                                  │
│    Provides: rule + substitution + metadata                      │
│    Says: "trust me bro, apply this"                              │
└───────────────────────────┬─────────────────────────────────────┘
                            │ Oracle/FFI
                            ▼
┌─────────────────────────────────────────────────────────────────┐
│                    Generic Prover (Core)                         │
│              "I just pattern-match and apply rules"              │
│                                                                  │
│    - Correct by construction                                     │
│    - Works for ANY calculus                                      │
│    - Slow (enumerates all possibilities)                         │
│    - Can be advised by oracle                                    │
└─────────────────────────────────────────────────────────────────┘
```

### Why?

1. **Correctness**: The generic prover is simple enough to trust. It's the "ground truth".

2. **Experimentation**: Specialized provers can try wild optimizations. If they're wrong, the generic prover catches it (in verified mode).

3. **Extensibility**: New logics get a working prover for free (generic). Then optimize later.

4. **Clean separation**: ll.json defines what ILL IS. Prover code defines how to prove things FAST.

---

## Two-Tier Prover Architecture

### Tier 1: Generic Structural Prover

A "dumb" prover that works for ANY sequent calculus:

```javascript
class GenericProver {
  constructor(calculus) {
    this.rules = calculus.rules;  // From calculus.json
  }

  prove(goal) {
    // 1. Check if goal is an axiom
    if (this.isAxiom(goal)) return { success: true, type: 'Axiom' };

    // 2. Try each rule
    for (const [ruleName, rule] of Object.entries(this.rules)) {
      // 3. Try to match rule conclusion against goal
      const matches = this.matchConclusion(rule.conclusion, goal);

      for (const substitution of matches) {
        // 4. Generate premises by applying substitution
        const premises = rule.premises.map(p =>
          this.applySubstitution(p, substitution)
        );

        // 5. Recursively prove all premises
        const premiseProofs = premises.map(p => this.prove(p));

        if (premiseProofs.every(p => p.success)) {
          return {
            success: true,
            type: ruleName,
            substitution,
            premises: premiseProofs
          };
        }
      }
    }

    return { success: false };
  }

  // The expensive part: enumerate ALL ways to match
  *matchConclusion(pattern, goal) {
    // For rules like "?X, ?Y |- ..." this enumerates ALL splits!
    // Exponential in context size - this is why we need oracles
    yield* this.enumerateSubstitutions(pattern, goal);
  }
}
```

**Properties:**
- ✅ Correct (just follows the rules)
- ✅ Works for any calculus
- ❌ Slow (exponential in worst case)
- ❌ No intelligence (no focusing, no polarity)

### Tier 2: Specialized Oracle Provers

Logic-specific provers that "know" how to prove things efficiently.

**Key insight**: The oracle doesn't advise individual steps - it **takes over entire proof branches** and returns complete proof trees with resource tracking.

```javascript
// lib/provers/ill/oracle.js
class ILLOracle {
  constructor(calculus) {
    this.polarity = inferPolarities(calculus.rules);
    this.contextModes = config.contextModes;
  }

  // Takes over proof of a goal, returns complete result with delta_out
  prove(pt, options = {}) {
    // Phase 1: INVERSION - eagerly apply all invertible rules
    while (this.hasInvertibleRule(pt)) {
      const invertible = this.findInvertibleFormula(pt);
      this.applyRule(pt, invertible.ruleName);
    }

    // Phase 2: FOCUS CHOICE - pick what to focus on (backtrack point!)
    const focusChoices = this.getFocusCandidates(pt);

    for (const focus of focusChoices) {
      // Phase 3: FOCUSED DECOMPOSITION - follow the focus until atomic
      const result = this.focusedProve(pt, focus);

      if (result.success) {
        return result;  // Includes delta_out!
      }
    }

    return { success: false };
  }

  // The key: lazy resource management through premises
  proveMultiplePremises(pt) {
    let delta = Proofstate.copyMS(pt.delta_in);
    const propagate = this.contextModes[pt.type] === 'copy';

    for (const premise of pt.premisses) {
      // For additive rules (With_R), COPY context to each premise
      if (propagate) delta = Proofstate.copyMS(pt.delta_in);

      // Give current delta to premise
      Sequent.add_to_antecedent_bulk(premise.conclusion, delta);

      // Recursively prove - this discovers what's actually consumed
      const result = this.prove(premise, options);

      if (!result.success) return { success: false };

      // CRITICAL: leftover becomes input for next premise
      delta = result.delta_out;
    }

    return { success: true, delta_out: delta };
  }
}
```

**Properties:**
- ✅ Fast (polynomial - no 2^n context splitting enumeration)
- ✅ Uses focusing, polarity, lazy resource management
- ❌ Logic-specific (only works for ILL)
- ❌ Must be trusted or verified by generic prover

---

## Oracle/FFI Protocol

**Important**: See `dev/research/proof-search-oracles.md` for detailed research.

### Key Insight: Lazy Resource Management

The ILL prover does NOT precompute context splits. It uses **lazy resource management** (Hodas & Miller, 1994):

> "The nondeterminism that results from the need to split contexts can be handled by viewing proof search as a **process that takes a context, consumes part of it, and returns the rest**."

This is exactly what `delta_in` and `delta_out` implement in our prover.

### How It Actually Works

```
NAIVE (exponential):
  Goal: A, B, C |- D * E
  Try: {} | {A,B,C}     → prove |- D and A,B,C |- E
  Try: {A} | {B,C}      → prove A |- D and B,C |- E
  ... 2^n possibilities

LAZY (linear - what ILL prover does):
  Goal: A, B, C |- D * E
  delta_in = {A, B, C}   # Available resources

  Step 1: Prove first premise with ALL resources
    A, B, C |- D         # Give everything
    ... proof search ...
    delta_out = {B, C}   # A was consumed, B,C left over

  Step 2: Prove second premise with LEFTOVER
    B, C |- E            # delta_out becomes delta_in
    ... proof search ...
    delta_out = {}       # All consumed

  SUCCESS! Split was DISCOVERED: {A} | {B, C}
```

### The Interface: Proof Trees, Not Hints

The oracle doesn't advise individual steps - it **takes over entire proof branches** and returns:

```typescript
interface ProofResult {
  success: boolean;

  // The complete proof tree (if successful)
  proofTree?: PT;

  // Resources NOT consumed (for lazy splitting)
  delta_out: Record<string, { num: number, val: Node }>;

  // Substitutions discovered during proof
  theta: [Node, Node][];
}

interface Oracle {
  // Prove a goal, return complete result
  prove(pt: PT, options: ProverOptions): ProofResult;
}
```

This is more like **LCF-style tactics** than simple oracles:
- The oracle (ILL prover) is like an untrusted tactic
- The generic prover is like the trusted kernel
- Tactics produce proof trees; kernel verifies them

### Trust Levels

```javascript
class GenericProver {
  constructor(calculus, options = {}) {
    this.oracle = options.oracle;
    this.trustLevel = options.trustLevel || 'verify';
  }

  prove(pt, options) {
    // Let oracle prove it
    if (this.oracle && this.trustLevel !== 'none') {
      const result = this.oracle.prove(pt, options);

      if (result.success) {
        switch (this.trustLevel) {
          case 'full':
            // "Trust me bro" - fastest
            return result;

          case 'verify':
            // Check every rule application
            if (this.verifyProofTree(result.proofTree, options)) {
              return result;
            }
            console.warn('Oracle produced invalid proof!');
            break;

          case 'paranoid':
            // Verify AND re-prove with generic
            if (!this.verifyProofTree(result.proofTree, options)) {
              throw new Error('Oracle produced invalid proof!');
            }
            return result;
        }
      }
    }

    // Fallback: enumerate (exponential but correct)
    return this.enumerativeProve(pt, options);
  }

  verifyProofTree(pt, options) {
    // For each node in tree:
    // 1. Check rule name is valid
    // 2. Check conclusion matches rule schema
    // 3. Check substitution is correct
    // 4. Check resources flow correctly (delta_in ⊇ delta_out)
    // 5. Recursively verify premises
  }
}
```

### Context Modes (Split vs Copy)

Different connectives have different resource modes:

| Connective | Mode | Behavior |
|------------|------|----------|
| `Tensor_R` | split | First premise gets all, leftover to second |
| `Loli_L` | split | Same - multiplicative |
| `With_R` | copy | Both premises get full context (additive) |

This is the `propagate` flag in our prover:
```javascript
let propagate = pt.type === "With_R";  // With copies context
```

---

## File Separation Philosophy

### Unix Philosophy

> "Do one thing and do it well"

Each file should have ONE clear purpose:

### Proposed File Structure

```
ll.json                     # CALCULUS: syntax + rules (NOTHING ELSE)
                            # - What ILL IS
                            # - No prover hints
                            # - No polarity annotations
                            # - No metadata
                            # - Just: calc_structure + rules

lib/
├── core/                   # GENERIC MACHINERY
│   ├── prover.js           # Generic structural prover
│   │                       # - Pattern matching
│   │                       # - Rule application
│   │                       # - Substitution enumeration
│   │                       # - Oracle interface
│   │
│   ├── sequent.js          # Sequent representation
│   │                       # - NO hardcoded rule names
│   │                       # - Receives structure hints from calculus
│   │
│   ├── node.js             # AST nodes
│   │                       # - NO isLax(), isMonad() methods
│   │                       # - Pure tree structure
│   │
│   ├── parser.js           # Parser generator (already generic)
│   ├── mgu.js              # Unification (already generic)
│   ├── substitute.js       # Substitution (already generic)
│   ├── pt.js               # Proof trees (already generic)
│   └── helper.js           # Utilities (already generic)
│
├── provers/                # LOGIC-SPECIFIC PROVERS
│   └── ill/
│       ├── oracle.js       # ILL Oracle (the optimized prover)
│       │                   # - Focusing discipline
│       │                   # - Polarity-driven search
│       │                   # - Efficient context handling
│       │
│       ├── polarity.js     # Polarity inference
│       │                   # - Computes from rules (already implemented!)
│       │                   # - NO hardcoded map
│       │
│       └── config.js       # ILL-specific configuration
│                           # - Context modes (split vs copy)
│                           # - Special rule behaviors (Bang_L promotion)
│                           # - Semantically positive formulas
│
└── index.js                # Main entry: assembles prover from parts
```

### What Goes Where

| Concern | File | Rationale |
|---------|------|-----------|
| ILL syntax | ll.json | Defines the language |
| ILL inference rules | ll.json | Defines the logic |
| Generic proof search | core/prover.js | Works for any logic |
| AST structure | core/node.js | Generic tree |
| Sequent manipulation | core/sequent.js | Generic multiset ops |
| Polarity inference | provers/ill/polarity.js | Computed from rules |
| Context modes | provers/ill/config.js | ILL-specific behavior |
| Focusing discipline | provers/ill/oracle.js | ILL-specific optimization |
| Bang_L special case | provers/ill/config.js | ILL-specific behavior |

### Clean ll.json

Current ll.json has some cruft. After cleanup:

```json
{
  "calc_name": "ILL",

  "calc_structure": {
    "Atprop": { ... },
    "Formula": { ... },
    "Structure": { ... },
    "Sequent": { ... }
  },

  "calc_structure_rules": {
    "RuleZer": { "Id": { "ascii": "Id", "latex": "Id" } },
    "RuleU": { ... },
    "RuleBin": { ... }
  },

  "rules": {
    "RuleZer": { "Id": ["-- : A?A |- -- : A?A", ""] },
    "RuleU": { ... },
    "RuleBin": { ... }
  }
}
```

**Removed:**
- `_documentation` → move to README or separate doc
- `_architecture` → move to this document
- `_status` annotations → not needed
- Any polarity hints → computed by provers/ill/polarity.js

---

## Current State Analysis

### What's Already Generic

| File | Status | Notes |
|------|--------|-------|
| `mgu.js` | ✅ Generic | No changes needed |
| `substitute.js` | ⚠️ Almost | One `Formula_Forall` check |
| `pt.js` | ✅ Generic | No changes needed |
| `helper.js` | ✅ Generic | No changes needed |
| `parser.js` | ✅ Generic | Already fully parametric |
| `calc.js` | ⚠️ Almost | `Structure_Term_Formula` check |
| `compare.js` | ⚠️ Almost | Commented references |
| `ressource.js` | ⚠️ Almost | `Structure_Freevar` check |

### What Needs Refactoring

| File | Issue | Solution |
|------|-------|----------|
| `node.js` | `isLax()`, `isMonad()` | Remove; oracle tracks this |
| `sequent.js` | Hardcoded structure names | Pass as config |
| `proofstate.js` | Mix of generic + ILL | Split into core/prover + ill/oracle |
| `prover.js` | Same | Same |
| `polarity.js` | Hardcoded connective map | Already infers! Just clean up |

### Coupling Points

Only 6 places need changes:

1. **`node.js:67-74`** - `isLax()`, `isMonad()`
   ```javascript
   // REMOVE these methods entirely
   // Oracle tracks formula type externally
   ```

2. **`sequent.js:237-238,316-320`** - Hardcoded structure names
   ```javascript
   // BEFORE:
   if (type.ruleName !== "Structure_Freevar" ...
   if (type.ruleName === "Structure_Comma") ...

   // AFTER: receive from calculus config
   if (type.ruleName !== this.config.structuralVar) ...
   if (type.ruleName === this.config.structuralComma) ...
   ```

3. **`substitute.js:10`** - Formula_Forall check
   ```javascript
   // BEFORE:
   type.ruleName === "Formula_Forall"

   // AFTER: pass as config or remove if not needed
   ```

4. **`proofstate.js:259,405-412`** - With_R and Bang_L special cases
   ```javascript
   // MOVE to provers/ill/config.js:
   export const contextModes = {
     'With_R': 'copy',
     'Tensor_R': 'split',
     'Loli_L': 'split'
   };

   export const specialRules = {
     'Bang_L': {
       action: 'promote_to_persistent',
       extractFormula: node => node.vals[1].vals[0]  // Inner of !A
     }
   };
   ```

5. **`polarity.js:153-159`** - Hardcoded connective→rule map
   ```javascript
   // Already infers from rules! Just remove the hardcoded fallback.
   // The map is computed, not declared.
   ```

6. **`sequent.js:25`** - Direct ll.json import
   ```javascript
   // REMOVE: const calc = require('../ll.json');
   // Access via Calc.db instead
   ```

---

## Implementation Details

### Generic Prover Interface

```javascript
// lib/core/prover.js

class GenericProver {
  constructor(calculus, options = {}) {
    this.calculus = calculus;
    this.oracle = options.oracle || null;
    this.trustLevel = options.trustLevel || 'verify';

    // Structural hints from calculus (no hardcoded names!)
    this.hints = calculus._structure_hints || this.inferHints(calculus);
  }

  inferHints(calculus) {
    // Infer structural element names from calc_structure
    // E.g., find the rule that has type: ["Structure", "Structure"]
    // That's probably the comma/conjunction structure
    return {
      atomicFormulas: this.findAtomicFormulas(calculus),
      structuralComma: this.findStructuralComma(calculus),
      structuralNeutral: this.findStructuralNeutral(calculus),
      structuralVar: this.findStructuralVar(calculus),
      termFormula: this.findTermFormula(calculus)
    };
  }

  prove(pt, options = {}) {
    // Let oracle try first (it proves entire branches)
    if (this.oracle && this.trustLevel !== 'none') {
      const result = this.oracle.prove(pt, options);

      if (result.success) {
        if (this.trustLevel === 'full') {
          // "Trust me bro" - fastest
          return result;
        }

        if (this.trustLevel === 'verify') {
          // Check the proof tree is valid
          if (this.verifyProofTree(result.proofTree)) {
            return result;
          }
          console.warn('Oracle produced invalid proof!');
        }
      }
    }

    // Fall back to enumeration (exponential but correct)
    return this.enumerativeProve(pt, options);
  }

  // Verify oracle's proof tree is actually valid
  verifyProofTree(pt) {
    // 1. Check rule is valid for this calculus
    // 2. Check conclusion matches rule schema
    // 3. Check each premise was proven correctly
    // 4. Check resources flow correctly (delta_in ⊇ delta_out)
    return true; // Details omitted
  }
}
```

### ILL Oracle (Current Prover Refactored)

The ILL oracle wraps the current focused prover logic. The key insight is that it implements **lazy resource management** - it doesn't precompute splits, it discovers them.

```javascript
// lib/provers/ill/oracle.js

const config = require('./config.js');
const { inferAllPolarities } = require('./polarity.js');

class ILLOracle {
  constructor(calculus) {
    this.calculus = calculus;
    this.polarity = inferAllPolarities(calculus.rules);
    this.contextModes = config.contextModes;
    this.specialRules = config.specialRules;
  }

  // Main entry: prove goal, return complete result with delta_out
  prove(pt, options = {}) {
    // INVERSION PHASE: eagerly apply all invertible rules
    pt = this.inversionPhase(pt);

    // FOCUS CHOICE: pick what to focus on (this is the backtrack point)
    const candidates = this.getFocusCandidates(pt);

    for (const focus of candidates) {
      const result = this.focusedPhase(pt, focus);
      if (result.success) {
        return result;  // Includes delta_out for lazy splitting
      }
    }

    return { success: false };
  }

  inversionPhase(pt) {
    // Keep applying invertible rules until none left
    while (true) {
      const invertible = this.findInvertibleFormula(pt);
      if (!invertible) break;

      this.applyRule(pt, invertible);
      // Recursively prove premises (threaded resources)
      this.proveInversionPremises(pt);
    }
    return pt;
  }

  focusedPhase(pt, focus) {
    // Decompose the focused formula until atomic
    // Then try identity axiom
    // Returns { success, delta_out } with resources left over
  }

  // CRITICAL: This is where lazy resource management happens
  provePremises(pt) {
    let delta = Proofstate.copyMS(pt.delta_in);
    const mode = this.contextModes[pt.type] || 'split';

    for (const premise of pt.premisses) {
      // For 'copy' rules (With_R): give FULL context to each premise
      if (mode === 'copy') {
        delta = Proofstate.copyMS(pt.delta_in);
      }

      // Add available resources to premise
      Sequent.add_to_antecedent_bulk(premise.conclusion, delta);

      // Prove recursively - discovers what's consumed
      const result = this.prove(premise);
      if (!result.success) return { success: false };

      // LEFTOVER becomes input for next premise
      delta = result.delta_out;
    }

    return { success: true, delta_out: delta };
  }
}
```

This is essentially what `proofstate.js:255-288` already does - the refactoring makes it explicit and separates it from generic machinery.

### ILL Configuration

```javascript
// lib/provers/ill/config.js

// How context flows through binary rules
export const contextModes = {
  'Tensor_R': 'split',    // ?X, ?Y split across premises
  'Loli_L': 'split',      // ?X, ?Y split across premises
  'With_R': 'copy'        // ?X copied to both premises
};

// Rules with special behavior
export const specialRules = {
  'Bang_L': {
    // When Bang_L is applied, the !A formula's inner A
    // is promoted to persistent context
    action: 'promote_to_persistent',
    extractInner: (node) => {
      // node is "-- : !A", extract "A"
      return node.vals[1].vals[0];
    }
  }
};

// Formulas that are semantically positive despite context-preserving rules
export const semanticallyPositive = ['Formula_Lax', 'Formula_Monad'];
```

---

## Migration Strategy

### Phase 1: Add Structure Hints (Non-Breaking)

Add `_structure_hints` to ll.json (optional, can be inferred):

```json
{
  "_structure_hints": {
    "atomicFormulas": ["Formula_Atprop", "Formula_Freevar"],
    "structuralComma": "Structure_Comma",
    "structuralNeutral": "Structure_Neutral",
    "structuralVar": "Structure_Freevar",
    "termFormula": "Structure_Term_Formula"
  }
}
```

### Phase 2: Create Generic Prover

1. Create `lib/core/prover.js` with oracle interface
2. Add hint inference (so hints in JSON are optional)
3. Implement enumerative prove (correct but slow)
4. Add trust levels for oracle advice

### Phase 3: Extract ILL Oracle

1. Create `lib/provers/ill/` directory
2. Move polarity.js (already mostly standalone)
3. Create config.js with context modes, special rules
4. Create oracle.js wrapping current focused prover logic

### Phase 4: Refactor Core Files

1. Remove `isLax()`, `isMonad()` from node.js
2. Parametrize sequent.js structure name checks
3. Remove direct ll.json imports
4. Update substitute.js Forall check

### Phase 5: Validate

1. Run existing tests with generic prover (slow but correct)
2. Run existing tests with ILL oracle (fast)
3. Run in 'paranoid' mode: oracle advises, generic verifies
4. Compare proof trees from both approaches

### Phase 6: Document & Clean

1. Remove cruft from ll.json
2. Document oracle protocol
3. Update CLAUDE.md
4. Add example of new logic (LK) using just generic prover

---

## Summary

**The architecture:**
1. **ll.json**: Pure calculus definition (syntax + rules)
2. **lib/core/**: Generic prover that works for any calculus
3. **lib/provers/ill/**: Optimized ILL prover as oracle
4. **Oracle protocol**: Optimized prover takes over proof branches, returns complete results

**The key insight: Lazy Resource Management**

The ILL oracle does NOT precompute context splits (which would be 2^n). Instead:
- Give ALL resources to first premise
- Prove it - discover what's consumed
- Leftover goes to second premise
- The split is DISCOVERED, not computed

This is the `delta_in → prove → delta_out` pattern from Hodas & Miller (1994).

**Trust levels:**
- `full`: Oracle proves, generic trusts ("trust me bro")
- `verify`: Oracle proves, generic checks the proof tree
- `none`: Generic enumerates (exponential, but correct)

**Benefits:**
- Clean separation of concerns
- New logics work immediately (with generic prover)
- Can experiment with optimizations safely
- ll.json stays minimal and clean
- Safety: can verify oracle proofs against generic prover

---

*Created: 2026-01-27*
