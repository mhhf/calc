# Architecture

CALC uses a clean three-layer separation between Framework, Object Logic, and Prover.

```
┌─────────────────────────────────────────────────────────────┐
│  PROVER LAYER (lib/prover.js, lib/proofstate.js)            │
│  - ProofSearchState: { phase, focusPosition, focusId }      │
│  - FocusedProver: implements Andreoli's focusing discipline │
│  - Focus tracked on ProofTree, NOT in sequent syntax        │
│  - Uses polarity/context-mode inference (lib/polarity.js)   │
├─────────────────────────────────────────────────────────────┤
│  OBJECT LOGIC LAYER (ll.json)                               │
│  - Syntax definitions (NO focus types)                      │
│  - Inference rules (NO focus brackets)                      │
│  - Pure logical specification                               │
├─────────────────────────────────────────────────────────────┤
│  FRAMEWORK LAYER                                            │
│  - calc.js, parser.js, node.js, sequent.js, mgu.js, pt.js   │
│  - Generic: works for ANY calculus                          │
│  - NO knowledge of focusing or proof search strategy        │
└─────────────────────────────────────────────────────────────┘
```

## Framework Layer

Generic proof infrastructure, independent of any specific calculus or proof strategy.

| File | Purpose |
|------|---------|
| `lib/calc.js` | Calculus loader, initializes rules database |
| `lib/parser.js` | Dynamic Jison grammar generation from ll.json |
| `lib/node.js` | AST node representation, format-polymorphic rendering |
| `lib/sequent.js` | Sequent structure (persistent_ctx, linear_ctx, succedent) |
| `lib/mgu.js` | Most General Unifier - pattern matching |
| `lib/pt.js` | Proof Tree data structure |
| `lib/substitute.js` | Substitution application |

## Object Logic Layer

Pure logical specification in `ll.json`. Contains:

- **Syntax definitions**: Formula constructors, structure types, terms
- **Inference rules**: Left/right introduction rules for each connective
- **Display formats**: ASCII, LaTeX, Isabelle output specifications

Rules are written without prover-specific annotations:
```json
"Tensor_R": [
  "?X, ?Y |- -- : F?A * F?B",
  "?X |- -- : F?A",
  "?Y |- -- : F?B"
]
```

## Prover Layer

Implements focused proof search (Andreoli's discipline).

| File | Purpose |
|------|---------|
| `lib/prover.js` | ProofSearchState, FocusedProver classes |
| `lib/proofstate.js` | Main proof search API (Proofstate.auto) |
| `lib/polarity.js` | Polarity and context-mode inference |

### Key Insight: Focus = Position, Not Syntax

Focusing is just knowing WHICH formula to decompose. It doesn't require syntactic transformation.

- Prover tracks state externally: `{ phase: 'focus', focusPosition: 'R', focusId: null }`
- Rules have `F?A * F?B` (no brackets, pure logical rules)
- `applyRule()` extracts formula at position, matches against rule
- MGU matches `Formula_Tensor` ↔ `Formula_Tensor` (no wrappers)
- Sequent is NEVER modified for focus - focus is prover-internal state

### ProofSearchState

Tracks focusing state on ProofTree nodes:

```javascript
class ProofSearchState {
  constructor() {
    this.phase = 'inversion';  // 'inversion' | 'focus'
    this.focusPosition = null; // 'L' | 'R' | null
    this.focusId = null;       // for left formulas
  }
}
```

### Polarity Inference

Polarity is inferred from rule structure at load time (not specified in ll.json):

- **Positive connectives**: Context split across premises (Tensor, Bang)
- **Negative connectives**: Context preserved or copied (Loli, With, Forall)

See `lib/polarity.js` for the inference algorithm.
