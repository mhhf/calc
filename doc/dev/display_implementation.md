---
title: Display Calculus UI Implementation
created: 2026-02-10
modified: 2026-02-10
summary: Plan for implementing Calculus Overview and Meta Overview pages following academic presentation conventions
tags: [ui, display-calculus, documentation, presentation]
---

# Display Implementation Plan

This document describes how to implement the Calculus Overview and Meta Overview pages following academic conventions for presenting sequent calculi and display calculi.

## Research Summary

### Academic Presentation Conventions

**Sequent Calculi** in papers typically include:
1. **BNF Syntax** - Recursive grammar for formulas
2. **Sequent Notation** - Explanation of Γ ⊢ Δ format
3. **Inference Rules** - Fraction notation (premises/conclusion)
4. **Rule Categories** - Grouped by connective or type (structural, logical)

**Display Calculi** (Belnap 1982) add:
1. **Structural Connectives** - Meta-level operators (comma, star)
2. **Display Property** - Any formula can be isolated on one side
3. **Eight Conditions** - Guarantees for cut elimination

### Key Sources
- [Stanford Encyclopedia - Linear Logic](https://plato.stanford.edu/entries/logic-linear/)
- [nLab - Sequent Calculus](https://ncatlab.org/nlab/show/sequent+calculus)
- [nLab - Display Logic](https://ncatlab.org/nlab/show/display+logic)
- [Calculus Toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/)

---

## Calculus Overview (Object Logic)

**Purpose**: Present the full object logic defined in ll.json as academic papers do.

### Section 1: Syntax (BNF Grammar)

Display the formula grammar extracted from `calc_structure`:

```
Formulas    A, B ::= p | A ⊗ B | A ⊸ B | A & B | !A | ...
Structures  X, Y ::= A | X, Y | I | [A]
Sequents    S    ::= X ⊢ Y
```

**Implementation**:
- Parse `calc_structure.Formula` to extract constructors
- Render in both ASCII and LaTeX (toggle)
- Show type signatures: `Formula_Tensor : Formula × Formula → Formula`

### Section 2: Connectives Reference

Table showing all connectives with:
| Name | ASCII | Symbol | Arity | Polarity |
|------|-------|--------|-------|----------|
| Tensor | `*` | ⊗ | binary | positive |
| Lollipop | `-o` | ⊸ | binary | negative |

**Implementation**:
- Extract from `calc_structure.Formula_Bin_Op` and polarity metadata
- Move current MetaOverview connectives table here

### Section 3: Inference Rules

Display rules in standard fraction notation:

```
      Γ, A, B ⊢ C
    ─────────────── (⊗L)
      Γ, A ⊗ B ⊢ C
```

**Two display modes**:

1. **Simplified** (paper-style):
   - Use Γ, Δ for contexts
   - Use A, B for formulas
   - Clean mathematical presentation

2. **Full** (ll.json form):
   - Show exact metavariables: `?X, -- : F?A * F?B |- -- : F?C`
   - Useful for understanding the framework

**Implementation**:
- Parse `rules` section of ll.json
- Create `InferenceRule` component with KaTeX rendering
- Group by `calc_structure_rules_meta.Contexts` labels

### Section 4: Rule Categories

Organize rules by their role:
- **Identity & Cut** (RuleZer, RuleCut)
- **Structural Rules** (RuleStruct) - display postulates
- **Logical Rules** (RuleU, RuleBin) - connective introduction/elimination

Show which rules are used by proof search vs. display-only.

### Section 5: Focusing (if applicable)

If the calculus uses focusing:
- Explain positive/negative polarity
- Show focused sequent notation: `Γ ; Δ ↓ A` vs `Γ ; Δ ↑ A`
- List which connectives are synchronous/asynchronous

---

## Meta Overview (Display Calculus Framework)

**Purpose**: Explain how to read/write ll.json files and understand the display calculus framework.

### Section 1: What is a Display Calculus?

Brief introduction:
- Belnap's generalization of sequent calculus (1982)
- Structural connectives supplement logical connectives
- Display property: any subformula can be isolated
- Guarantees cut elimination via eight conditions

### Section 2: The ll.json Specification Format

#### 2.1 Top-Level Structure
```json
{
  "calc_name": "LLog",
  "calc_structure": { ... },      // Syntax (sorts & constructors)
  "calc_structure_rules_meta": { ... },  // Metadata
  "calc_structure_rules": { ... }, // Rule names/labels
  "rules": { ... }                // Actual inference rules
}
```

#### 2.2 Defining Sorts (calc_structure)

Each sort is a syntactic category:
```json
"Formula": {
  "Formula_Tensor": {
    "type": ["Formula", "Formula"],  // Two Formula children
    "ascii": "_ * _",                // Display format
    "latex": "_ \\otimes _",
    "precedence": [320, 320, 321]
  }
}
```

**Key fields**:
| Field | Purpose |
|-------|---------|
| `type` | Child sorts (or `"string"` for terminals) |
| `ascii` | ASCII rendering template |
| `latex` | LaTeX rendering template |
| `isabelle` | Isabelle/HOL export format |
| `precedence` | Operator binding (higher = tighter) |
| `shallow` | Whether to inline in parent |

#### 2.3 Metavariables

Convention for schematic variables in rules:
| Pattern | Meaning | Example |
|---------|---------|---------|
| `?X`, `?Y` | Structure metavariable | Context placeholder |
| `F?A`, `F?B` | Formula metavariable | Any formula |
| `A?A` | Atomic proposition variable | Prop variable |
| `--` | Neutral/any term | Wildcard |

#### 2.4 Defining Rules

Rules are lists: `[conclusion, premise1, premise2, ...]`
```json
"Tensor_R": [
  "?X, ?Y |- -- : [ F?A * F?B ]",   // Conclusion
  "?X |- -- : [ F?A ]",              // Premise 1
  "?Y |- -- : [ F?B ]"               // Premise 2
]
```

#### 2.5 Metadata

```json
"calc_structure_rules_meta": {
  "polarity": {
    "Formula_Tensor": "positive",
    "Formula_Loli": "negative"
  },
  "Contexts": {
    "RuleZer": { "label": "Axioms", "simp": true },
    "RuleStruct": { "label": "Structural rules" }
  }
}
```

### Section 3: Adding a New Connective

Step-by-step guide:

1. **Add the operator** to `Formula_Bin_Op` (or appropriate sort)
2. **Add the formula constructor** to `Formula`
3. **Set polarity** in metadata
4. **Define inference rules** in `rules`
5. **Add rule metadata** in `calc_structure_rules`

Example: Adding additive disjunction (⊕)
```json
// In Formula_Bin_Op:
"Formula_Plus": {
  "ascii": "+",
  "latex": "\\oplus"
}

// In rules:
"Plus_L": ["?X, -- : F?A + F?B |- ?Y", "?X, -- : F?A |- ?Y", "?X, -- : F?B |- ?Y"],
"Plus_R1": ["?X |- -- : F?A + F?B", "?X |- -- : F?A"],
"Plus_R2": ["?X |- -- : F?A + F?B", "?X |- -- : F?B"]
```

### Section 4: Structural vs Logical Rules

**Structural Rules** (display postulates):
- Manipulate structure without touching formulas
- Enable the display property
- Example: associativity, commutativity, unit laws

**Logical Rules** (introduction/elimination):
- Introduce/eliminate logical connectives
- Have principal formula in conclusion
- Categorized by arity (unary, binary)

### Section 5: The Parser Pipeline

```
ll.json → calc-genparser → Jison grammar → parser.js → AST
```

Explain how:
- `calc_structure` defines the grammar
- Precedence controls parsing ambiguity
- Multi-format output (`ascii`, `latex`, `isabelle`) enables different views

---

## UI Components Needed

### New Components

1. **BNFGrammar** - Renders syntax in BNF notation
2. **InferenceRuleDisplay** - Renders rule with fraction bar
3. **RuleGroup** - Groups rules by category with headers
4. **JSONSchemaView** - Interactive ll.json structure viewer
5. **CodeExample** - Syntax-highlighted JSON/code blocks

### Enhanced Components

- **KaTeX** - Add support for inference rule layout (`\cfrac`)
- **RuleCard** - Add simplified/full toggle

---

## Data Extraction

Functions to add to lib or UI:

```typescript
// Extract BNF from calc_structure
function extractBNF(calcStructure: object): BNFDefinition[]

// Extract connectives with metadata
function extractConnectives(calc: object): Connective[]

// Parse rule string into structured form
function parseRule(ruleStr: string): ParsedRule

// Convert rule to simplified form (Γ, A, B notation)
function simplifyRule(rule: ParsedRule): SimplifiedRule
```

---

## Implementation Order

1. **Move connectives table** from Meta → Calculus
2. **Add BNF section** to Calculus Overview
3. **Implement InferenceRuleDisplay** component
4. **Refactor Calculus Overview** with proper rule grouping
5. **Rewrite Meta Overview** as framework documentation
6. **Add interactive elements** (toggles, collapsibles)
7. **Add JSON schema visualization** to Meta

---

## References

- Belnap, N.D. (1982). "Display logic". Journal of Philosophical Logic.
- Girard, J.Y. (1987). "Linear logic". Theoretical Computer Science.
- Andreoli, J.M. (1992). "Logic programming with focusing proofs in linear logic".
- [Calculus Toolbox Documentation](https://goodlyrottenapple.github.io/calculus-toolbox/)
