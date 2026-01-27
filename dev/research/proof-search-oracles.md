# Proof Search Oracles: Strategy FFI for Theorem Provers

How optimized provers can "take over" from generic provers while maintaining trust.

---

## Table of Contents

1. [The Problem](#the-problem)
2. [Key Insight: Lazy Resource Management](#key-insight-lazy-resource-management)
3. [How the ILL Prover Actually Works](#how-the-ill-prover-actually-works)
4. [Approaches in the Literature](#approaches-in-the-literature)
5. [Architecture Options](#architecture-options)
6. [Proposed Design for CALC](#proposed-design-for-calc)
7. [Sources](#sources)

---

## The Problem

### Generic vs Optimized Provers

A **generic structural prover** is simple and correct:
- Pattern-match rules against goals
- Generate premises via substitution
- Backtrack on failure

But it's slow because it must enumerate all possibilities:
- For context-splitting rules like `Tensor_R: ?X, ?Y |- A * B`, it tries ALL 2^n ways to split the context
- No intelligence about which rules to try first

An **optimized prover** (like the ILL focused prover) is fast:
- Uses domain knowledge (polarity, focusing)
- Lazy resource management (no enumeration)
- But it's complex and could have bugs

### The Trust Question

How do we get the speed of optimized provers with the trust of generic provers?

**Bad answer**: "Oracle advises substitutions"
- This doesn't capture how the ILL prover actually works
- Context splitting isn't precomputed - it's discovered lazily

**Good answer**: "Optimized prover takes over, returns proof + resources"
- The optimized prover proves entire branches
- Returns what resources it consumed
- Generic prover can verify or trust the result

---

## Key Insight: Lazy Resource Management

### The Hodas-Miller Approach

From ["Logic Programming in a Fragment of Intuitionistic Linear Logic"](https://www.sciencedirect.com/science/article/pii/S0890540184710364) (Hodas & Miller, 1994):

> "The nondeterminism that results from the need to split contexts in order to prove a multiplicative conjunction can be handled by viewing proof search as a **process that takes a context, consumes part of it, and returns the rest** (to be consumed elsewhere)."

### Input/Output Contexts

Instead of guessing how to split upfront:

```
NAIVE (exponential):
  Goal: A, B, C |- D * E
  Try: {} | {A,B,C}     → prove |- D and A,B,C |- E
  Try: {A} | {B,C}      → prove A |- D and B,C |- E
  Try: {B} | {A,C}      → prove B |- D and A,C |- E
  ... 2^n possibilities

LAZY (linear):
  Goal: A, B, C |- D * E
  delta_in = {A, B, C}   # Available resources

  Step 1: Prove first premise with ALL resources
    A, B, C |- D         # Try to prove D
    ... proof search ...
    delta_out = {B, C}   # A was consumed, B,C left over

  Step 2: Prove second premise with LEFTOVER
    B, C |- E            # delta_out becomes delta_in
    ... proof search ...
    delta_out = {}       # All consumed
```

**Key**: The split is DISCOVERED during proof, not GUESSED upfront.

### Split vs Copy

Different connectives have different resource modes:

| Connective | Mode | Behavior |
|------------|------|----------|
| `Tensor_R` | split | First premise gets all, leftover to second |
| `Loli_L` | split | Same |
| `With_R` | copy | Both premises get full context (additive) |

This is exactly what CALC's `propagate` flag does:
```javascript
let propagate = pt.type === "With_R";  // With copies context
```

---

## How the ILL Prover Actually Works

### Data Structures

**ProofSearchState** tracks prover-specific state:
```javascript
class ProofSearchState {
  phase: 'inversion' | 'focus'   // Which phase of focusing
  focusPosition: 'L' | 'R'       // Where is focus
  focusId: string | null         // Which formula in context
}
```

**delta_in / delta_out** track resource flow:
```javascript
pt.delta_in   // Resources available for this subproof
pt.delta_out  // Resources NOT consumed (leftover)
```

### The Main Loop (proofstate.js:auto)

```javascript
Proofstate.auto = function(pt, o) {
  // Phase 1: INVERSION
  // Apply invertible rules eagerly (no backtracking needed)
  let invertableId = Proofstate.getInvertableRule(pt, o);
  if (invertableId) {
    Proofstate.apply(pt, rule_name, invertableId, rule);
    // continue to premises...
  }

  // Phase 2: FOCUS
  // If focused, decompose the focused formula
  else if (state.isFocused()) {
    if (isAtomic) {
      // Try identity rules (Id_+ or Id_-)
    } else {
      // Apply rule for the focused connective
    }
  }

  // Phase 3: CHOOSE FOCUS
  // Pick a formula to focus on (backtrack over choices)
  else {
    filter = getLeftNegatives().concat(getRightPositives());
    for (id in filter) {
      Proofstate.focus(pt, id);
      // try proof...
    }
  }
}
```

### Resource Threading (proofstate.js:255-306)

The critical code for lazy splitting:

```javascript
let delta = Proofstate.copyMS(pt.delta_in);
let propagate = pt.type === "With_R";

for (let j = 0; j < pt.premisses.length; j++) {
  // For additive rules, COPY context to each premise
  if (propagate)
    delta = Proofstate.copyMS(pt.delta_in);

  let ptp = pt.premisses[j];

  // Add resources to premise
  Sequent.add_to_antecedent_bulk(ptp.conclusion, delta);

  // Recursively prove
  let result = Proofstate.auto(ptp, o);

  // LEFTOVER becomes input for next premise
  delta = result.delta_out;
}

pt.delta_out = delta;  // Final leftover
```

### What the ILL Prover Returns

```javascript
{
  success: boolean,           // Did proof succeed?
  delta_out: Multiset,        // Resources NOT consumed
  theta: Substitution[],      // Discovered substitutions
  debug: { ... }              // Proof trace
}
```

The proof tree `pt` is also mutated:
- `pt.type` = rule name applied
- `pt.premisses` = child proof trees
- `pt.delta_in` / `pt.delta_out` = resource flow

---

## Approaches in the Literature

### 1. LCF-Style Tactics (HOL, Isabelle, Lean)

**Architecture**:
```
┌─────────────────────────────────────────────────────┐
│                UNTRUSTED TACTICS                     │
│  (Can be arbitrarily complex, potentially buggy)    │
│                                                      │
│  Returns: proof term / tactic proof                  │
└───────────────────────────┬─────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────┐
│                TRUSTED KERNEL                        │
│  (Small, verified, checks every inference step)     │
│                                                      │
│  Abstract type: only kernel can create theorems     │
└─────────────────────────────────────────────────────┘
```

**Key insight**: "The only mechanism automation has for constructing an authenticated theorem is by using [the kernel] API, with the inference rules of the logic exposed as a suite of smart constructors manipulating an abstract type of theorems."

**Relevance to CALC**: The ILL prover is like a tactic; the generic prover is like the kernel.

Source: [From LCF to Isabelle/HOL](https://arxiv.org/pdf/1907.02836)

### 2. Proof by Reflection (Coq, Agda)

**Architecture**:
- Write decision procedure IN the logic itself
- Procedure returns small proof witness
- Witness is checked by kernel

**Example** (from [Coq'Art Chapter 16](https://www-sop.inria.fr/members/Yves.Bertot/coqart-chapter16.pdf)):
```
Instead of:  Even_SS (Even_SS (Even_SS Even_O))  -- large proof term
Return:      IsEven(6) = true                    -- small witness
Kernel checks: IsEven computes correctly
```

**Key insight**: "Decision procedures can be written either in Type Theory—in a purely functional way that also ensures termination—or in an effectful programming language, where they are used as oracles for the certified checker."

**Relevance to CALC**: Could implement ILL prover in a verified way, or trust it as oracle.

### 3. Foundational Proof Certificates (FPC)

**Architecture**:
- Provers output proof certificates
- Certificates are checked by small kernel (LKF-based)
- Certificate format is flexible (more/less detail)

**Key insight**: "An important decision in designing a proof certificate format is the choice of how many details are to be placed within certificates. Formats with fewer details are smaller and easier for theorem provers to output but they require more sophistication from checkers."

**Relevance to CALC**: Could define proof certificate format that ILL prover produces.

Source: [Foundational Proof Certificates](https://dl.acm.org/doi/10.1145/2503887.2503894)

### 4. Certified Solvers (SAT, SMT)

**Architecture**:
- Solver finds solution
- Produces certificate (DRAT proof, etc.)
- Independent checker verifies certificate

**Example**: CakeLPR verified proof checker for SAT:
> "Our cake_lpr and cake_pb tools are used to audit solver outputs in the annual international SAT solving competitions."

**Relevance to CALC**: Similar trust model - optimized solver, verified checker.

Source: [Verified Proof Checking](https://cakeml.org/checkers.html)

### 5. Lolli Resource Management

**Architecture**:
- Lazy splitting (input/output contexts)
- Resources threaded through proof search
- Backtracking only when proof fails, not for splits

**Key paper**: ["Efficient Resource Management for Linear Logic Proof Search"](https://www.cs.cmu.edu/~fp/papers/elp96.pdf) (Cervesato, Hodas, Pfenning, 1996)

**This is exactly what CALC implements!** The delta_in/delta_out mechanism is the Hodas-Miller lazy splitting approach.

---

## Architecture Options

### Option A: LCF-Style (Proof Trees)

**ILL prover** produces complete proof tree.
**Generic prover** verifies each step.

```
┌─────────────────────────────────────────────────────┐
│              ILL PROVER (Tactic)                     │
│                                                      │
│  Input: Goal sequent                                 │
│  Output: {                                           │
│    success: true,                                    │
│    proofTree: PT { type, premisses, ... },          │
│    delta_out: { resources not consumed },           │
│    theta: [ substitutions ]                         │
│  }                                                   │
└───────────────────────────┬─────────────────────────┘
                            │
                            ▼
┌─────────────────────────────────────────────────────┐
│            GENERIC PROVER (Kernel)                   │
│                                                      │
│  verifyProofTree(pt):                               │
│    For each node:                                    │
│      1. Check rule name is valid                     │
│      2. Check conclusion matches rule schema         │
│      3. Check premises are correct for rule          │
│      4. Check resources flow correctly               │
│    Return: valid / invalid                           │
└─────────────────────────────────────────────────────┘
```

**Pros**:
- Clear separation of concerns
- Full proof is available for inspection
- Can switch between trust levels at runtime

**Cons**:
- Requires proof tree serialization
- Verification adds overhead

### Option B: Coroutine/Callback

**ILL prover** calls back to generic prover at key points.

```javascript
class ILLProver {
  prove(goal, kernel) {
    // Do ILL-specific work (focusing, inversion)
    ...

    // At rule application: ask kernel to validate
    kernel.validateRuleApplication(ruleName, substitution, goal);

    // At premise: kernel continues or ILL continues
    for (premise of premises) {
      result = this.prove(premise, kernel);  // ILL handles
      // OR
      result = kernel.prove(premise);        // Kernel handles
    }
  }
}
```

**Pros**:
- Fine-grained control
- Can mix strategies mid-proof

**Cons**:
- Complex control flow
- Harder to reason about

### Option C: Certificate Format

**ILL prover** produces proof certificate (compact format).
**Generic prover** elaborates and checks.

```
Certificate: [
  { rule: "Loli_R", focus: null },
  { rule: "Focus_L", focus: "id_0" },
  { rule: "Loli_L", split: [0.6, 0.4] },  // hint for split
  { rule: "Id_+", match: "id_0" }
]

Checker:
  1. Parse certificate
  2. For each step, verify rule is applicable
  3. Fill in details (compute actual substitution)
  4. Produce full proof tree
```

**Pros**:
- Small certificates
- Flexible detail level

**Cons**:
- Checker needs reconstruction logic
- Certificate format design is tricky

### Option D: Trust Levels (Recommended)

Combine approaches with configurable trust:

```javascript
class GenericProver {
  constructor(calculus, options) {
    this.trustLevel = options.trustLevel;  // 'full' | 'verify' | 'none'
    this.oracle = options.oracle;           // ILL prover
  }

  prove(goal) {
    if (this.oracle && this.trustLevel !== 'none') {
      // Let oracle prove it
      let result = this.oracle.prove(goal);

      if (this.trustLevel === 'full') {
        // Trust completely
        return result;
      } else {
        // Verify the proof tree
        if (this.verifyProofTree(result.proofTree)) {
          return result;
        } else {
          console.warn("Oracle produced invalid proof!");
          // Fall back to enumeration
        }
      }
    }

    // No oracle or verification failed: enumerate
    return this.enumerativeProve(goal);
  }
}
```

**Trust levels**:
- `'full'`: Trust oracle completely (fastest, for production)
- `'verify'`: Check every rule application (medium, for testing)
- `'none'`: Don't use oracle (slowest, for validation)

---

## Proposed Design for CALC

### Interface: ProofResult

```typescript
interface ProofResult {
  success: boolean;

  // The proof tree (if successful)
  proofTree?: PT;

  // Resources NOT consumed (for lazy splitting)
  delta_out: Record<string, { num: number, val: Node }>;

  // Substitutions discovered during proof
  theta: [Node, Node][];

  // Debug trace (optional)
  debug?: DebugInfo;
}
```

### Interface: Prover

```typescript
interface Prover {
  /**
   * Prove a goal sequent
   *
   * @param pt - Proof tree node with goal as conclusion
   * @param options - Rules, mode, etc.
   * @returns ProofResult
   */
  prove(pt: PT, options: ProverOptions): ProofResult;
}

interface ProverOptions {
  rules: Record<string, Sequent[]>;  // Available rules
  getRule: (name: string) => Sequent[];
  mode: 'proof' | 'interactive';
  affine: boolean;  // Allow leftover resources?
}
```

### Generic Prover

```javascript
class GenericProver implements Prover {
  constructor(calculus, options = {}) {
    this.calculus = calculus;
    this.oracle = options.oracle;
    this.trustLevel = options.trustLevel || 'verify';
  }

  prove(pt, options) {
    // Try oracle first
    if (this.oracle && this.trustLevel !== 'none') {
      const result = this.oracle.prove(pt, options);

      if (result.success) {
        if (this.trustLevel === 'full') {
          return result;
        }
        if (this.verifyProofTree(result.proofTree, options)) {
          return result;
        }
        // Verification failed - fall through
      }
    }

    // Enumerative fallback
    return this.enumerativeProve(pt, options);
  }

  verifyProofTree(pt, options) {
    // Check rule application is valid
    const rule = options.getRule(pt.type);
    if (!rule) return false;

    // Check substitution produces correct premises
    // ... (pattern match conclusion, verify premises)

    // Check resources flow correctly
    // ... (delta_in contains delta_out)

    // Recursively verify premises
    for (const premise of pt.premisses) {
      if (!this.verifyProofTree(premise, options)) {
        return false;
      }
    }

    return true;
  }

  enumerativeProve(pt, options) {
    // Naive backtracking search
    for (const [ruleName, rule] of Object.entries(options.rules)) {
      for (const subst of this.enumerateSubstitutions(rule, pt.conclusion)) {
        // ... try each possibility
      }
    }
  }
}
```

### ILL Oracle (Existing Prover)

The existing `FocusedProver` already implements the oracle interface:

```javascript
// lib/prover.js - already returns ProofResult!
auto(pt, options) {
  // ... focused proof search ...
  return {
    success,
    delta_out,
    theta,
    debug: { head: debug, children: debug_children }
  };
}
```

Just need to:
1. Wrap in Oracle interface
2. Ensure proof tree is properly constructed
3. Add verification hook

### File Structure

```
lib/
├── core/
│   ├── prover.js         # GenericProver with oracle support
│   ├── verifier.js       # Proof tree verification
│   └── ...               # Other generic machinery
│
├── provers/
│   └── ill/
│       ├── oracle.js     # ILL oracle (wraps FocusedProver)
│       ├── focused.js    # FocusedProver (current prover.js)
│       ├── polarity.js   # Polarity inference
│       └── config.js     # Context modes, special rules
│
└── index.js
```

---

## Sources

### Linear Logic Resource Management

- [Hodas & Miller: Logic Programming in a Fragment of Intuitionistic Linear Logic](https://www.sciencedirect.com/science/article/pii/S0890540184710364) (1994) — Foundational paper on lazy splitting
- [Cervesato, Hodas, Pfenning: Efficient Resource Management for Linear Logic Proof Search](https://www.cs.cmu.edu/~fp/papers/elp96.pdf) (1996) — Detailed resource management systems
- [Lolli Homepage](https://www.lix.polytechnique.fr/~dale/lolli/) — Reference implementation

### LCF-Style Theorem Proving

- [From LCF to Isabelle/HOL](https://arxiv.org/pdf/1907.02836) — History and architecture
- [Paulson: LCF and HOL Papers](https://www.cl.cam.ac.uk/~lp15/papers/hol.html) — Original LCF papers
- [Theorem Provers - From Zero to QED](https://sdiehl.github.io/zero-to-qed/03_theorem_provers.html) — Modern overview

### Proof by Reflection

- [Coq'Art Chapter 16: Proof by Reflection](https://www-sop.inria.fr/members/Yves.Bertot/coqart-chapter16.pdf)
- [CPDT: Proof by Reflection](https://alectryon-paper.github.io/bench/books/proof-by-reflection.html)
- [Engineering Proof by Reflection in Agda](https://www.researchgate.net/publication/281886057_Engineering_Proof_by_Reflection_in_Agda)

### Proof Certificates

- [Foundational Proof Certificates](https://dl.acm.org/doi/10.1145/2503887.2503894) (Miller et al.)
- [Verification of Certifying Computations](https://people.eng.unimelb.edu.au/rizkallahc/publications/VerificationCertComps.pdf)
- [Verified Proof Checking (CakeML)](https://cakeml.org/checkers.html)

### Tactics and Automation

- [Ltac — Coq Documentation](https://coq.inria.fr/refman/proof-engine/ltac.html)
- [CMU Blog: Connecting ATP and ITP](https://www.cs.cmu.edu/~csd-phd-blog/2025/atp-itp-connection/)

## Cross-References

See also in this knowledge base:
- [[ffi-logics]] — FFI for computational predicates (different problem)
- [[CORE_SPLIT]] — Architecture for core/calculus separation
- [[QnA]] — Proof theory background

---

*Created: 2026-01-27*
