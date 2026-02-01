# Typed DSL / Logical Framework for CALC

Research on designing a typed meta-language for specifying CALC's calculus, investigating parser frameworks, and exploring how ll.json can evolve into or interoperate with a typed specification language.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [Current CALC Architecture](#current-calc-architecture)
3. [Logical Frameworks: LF, CLF, Twelf, Celf](#logical-frameworks)
4. [The optimism-mde DSL](#the-optimism-mde-dsl)
5. [Lean4 Approach](#lean4-approach)
6. [Parser Framework Comparison](#parser-framework-comparison)
7. [Design Options for CALC](#design-options-for-calc)
8. [**Proposed Three-File Architecture**](#proposed-three-file-architecture) ← NEW
9. [Recommendations](#recommendations)
10. [References](#references)

---

## Executive Summary

**Goal:** Design a typed DSL where inference rules are well-typed terms, catching malformed rules at definition time.

**Key Decision: Three-File Architecture**

Inspired by calculus-toolbox-2 and optimism-mde, we propose separating concerns:

| File Type | Purpose | Style Inspiration |
|-----------|---------|-------------------|
| `.calc` | Types, connectives, metadata | Lean 4 / Twelf |
| `.rules` | Inference rules | calculus-toolbox-2 (horizontal lines) |
| `.lib` / `.prog` | Stdlib and programs | Celf / optimism-mde |

**Key Features:**

1. **Rich connective metadata** — polarity, duals, adjoints, interpretations
2. **Human-readable rules** — Natural deduction style with horizontal lines
3. **Terms as first-class** — Proof terms, resource annotations
4. **Stdlib pattern** — Reusable libraries (arithmetic, base types)
5. **Multiple outputs** — ASCII, LaTeX, Isabelle from single source

**Approach Comparison:**

| Approach | Type Safety | Complexity | Zig Portable | Recommended |
|----------|-------------|------------|--------------|-------------|
| Keep ll.json + new parser | LOW | LOW | YES | Immediate needs |
| **Three-file DSL (proposed)** | **MEDIUM-HIGH** | **MEDIUM** | **YES** | **Primary goal** |
| Deep embedding (LF-style) | HIGH | HIGH | YES | Long-term |
| External tool (Twelf/Celf) | HIGH | MEDIUM | NO | Verification |

**Parser Recommendation:** **Ohm** for prototyping (best DX, visualization), with path to **tree-sitter** for production (Zig bindings, editor integration).

---

## Current CALC Architecture

### ll.json Structure

The current calculus specification (`ll.json`) has three main parts:

```
ll.json
├── calc_structure          # Type/constructor definitions (grammar)
│   ├── Atprop              # Atomic propositions
│   ├── Formula             # Logical formulas (⊗, ⊸, &, !)
│   ├── Structure           # Sequent structures
│   └── Sequent             # Full sequents
├── calc_structure_rules    # Rule names and labels
│   ├── RuleZer             # Axioms (Id)
│   ├── RuleU               # Unary rules (Tensor_L, Loli_R, etc.)
│   └── RuleBin             # Binary rules (Tensor_R, Loli_L, etc.)
└── rules                   # Actual inference rule patterns
    └── { "Tensor_L": ["conclusion", "premise1", ...] }
```

### How Parser Generation Works

`lib/parser.js` dynamically generates a Jison grammar from `ll.json`:

```javascript
// For each constructor in calc_structure:
// Formula_Bang: { type: ["Formula"], ascii: "! _ " }
// Generates Jison rule:
// ["! Formula", "$$ = new yy.Node(id, [$2]);"]
```

**Problems with current approach:**
1. **No type checking** — Rules are strings, typos silently fail
2. **Jison is outdated** — Unmaintained, poor error messages
3. **Implicit structure** — Rule arity, types inferred at runtime
4. **Hard to extend** — Adding new connectives requires JSON surgery

### Node Representation

`lib/node.js` represents AST nodes:

```javascript
class Node {
  constructor(id, vals) {
    this.id = id;      // Integer ID from Calc.db
    this.vals = vals;  // Child nodes or strings
  }
}
```

**Key insight:** Nodes are identified by integer IDs, which is good for content-addressing and Zig portability.

---

## Logical Frameworks

### LF (Edinburgh Logical Framework)

LF is a dependently typed lambda calculus for representing deductive systems.

**Core idea:** Judgments as types, derivations as terms.

**Twelf syntax example (STLC encoding):**

```twelf
% Types
tp : type.
arrow : tp -> tp -> tp.
unit : tp.

% Terms
tm : type.
app : tm -> tm -> tm.
lam : tp -> (tm -> tm) -> tm.    % Higher-order abstract syntax

% Typing judgment
of : tm -> tp -> type.           % Judgment declaration

of-lam : of (lam T2 ([x] E x)) (arrow T2 T)
        <- ({x: tm} of x T2 -> of (E x) T).

of-app : of (app E1 E2) T
        <- of E1 (arrow T2 T)
        <- of E2 T2.
```

**Key features:**
- **Dependent types**: `of : tm -> tp -> type` — typing is a type family
- **HOAS**: `(tm -> tm)` represents binding without explicit substitution
- **Adequacy**: Bijection between LF terms and object-language derivations

**Relevance to CALC:**
- Our sequent rules could be typed: `Tensor_L : rule (Γ, A ⊗ B ⊢ C) [(Γ, A, B ⊢ C)]`
- Dependent types ensure conclusion/premise formulas match
- HOAS could represent formula schemas with free variables

### CLF (Concurrent Linear Framework)

CLF extends LF with:
1. **Linear types** — Resources used exactly once
2. **Monadic encapsulation** — `{A}` for concurrent/stateful computation

**Celf syntax:**

```celf
% Type declaration
state : type.

% Linear resources
counter : nat -> type.          % Linear by default

% Persistent facts
!rule : ...                     % ! makes it persistent

% Linear rewrite rule
inc : counter N * trigger -o { counter (s N) }.

% Backward chaining (non-linear)
plus : nat -> nat -> nat -> type.
plus/z : plus z N N.
plus/s : plus (s M) N (s R) <- plus M N R.
```

**Key syntax elements:**
- `A -> B` — Intuitionistic function (persistent)
- `A -o B` — Linear implication (resource-consuming)
- `A * B` — Simultaneous conjunction (tensor ⊗)
- `{A}` — Monadic suspension (forward-chaining)
- `!A` — Persistent/unrestricted resource
- `<-` — Backward-chaining premise

### The optimism-mde DSL

Our local `~/src/optimism-mde/` uses Celf-style syntax to model EVM:

```celf
% lib/bin.mde - Binary numbers
bin: type.
e: bin.                         % Zero
i: bin -> bin.                  % Bit 1
o: bin -> bin.                  % Bit 0

% Arithmetic relations
plus: bin -> bin -> bin -> type.
plus/z1: plus e e e.
plus/s1: plus (o M) (o N) (o R)
  <- plus M N R.

% lib/evm.mde - EVM instructions
pc: bin -> type.                % Program counter (linear)
stack: nat -> bin -> type.      % Stack slot (linear)
code: bin -> bin -> type.       % Code at address (persistent via context)

% EVM ADD instruction
evm/add:
  pc PC *
  code PC N_01 *
  !inc PC PC' *                 % Persistent increment relation
  sh (s (s SH)) *               % Stack height
  stack (s SH) A *              % Pop A
  stack SH B *                  % Pop B
  !plus A B C                   % Compute A + B
  -o {
    code PC N_01 *
    pc PC' *
    sh (s SH) *
    stack SH C                  % Push result
  }.
```

**Pattern analysis:**
1. **Type declarations** — Simple: `name: type.`
2. **Constructors** — `name: arg -> ... -> return_type.`
3. **Relations/Judgments** — `name: arg1 -> arg2 -> type.`
4. **Clauses** — `name/case: head <- premises.` (backward) or `antecedent -o { consequent }.` (forward)

---

## Lean4 Approach

Lean4 provides a different model: **extensible syntax with macros**.

### Syntax Categories

```lean
declare_syntax_cat formula           -- Create new category
syntax "(" formula ")" : formula     -- Parentheses
syntax formula " ⊗ " formula : formula
syntax formula " ⊸ " formula : formula
syntax "!" formula : formula

-- Embed in term language
syntax "[F|" formula "]" : term
```

### Macro-Based Semantics

```lean
macro_rules
  | `([F| $a:formula ⊗ $b:formula ]) => `(Formula.tensor [F| $a ] [F| $b ])
  | `([F| $a:formula ⊸ $b:formula ]) => `(Formula.loli [F| $a ] [F| $b ])
  | `([F| ! $a:formula ]) => `(Formula.bang [F| $a ])
```

**Key insights:**
- Syntax and semantics are **separate** (like Ohm)
- **Precedence** via numbers: `syntax:60` binds tighter than `syntax:50`
- **Typed syntax** (`TSyntax`) provides category tracking
- **Hygienic macros** handle variable capture correctly

**Relevance to CALC:**
- We could define formula/sequent syntax categories
- Macros generate AST constructors
- Type checking happens at macro expansion time

---

## Parser Framework Comparison

### Current: Jison

**Pros:** Works, familiar LALR(1)
**Cons:** Unmaintained since 2017, poor error messages, no TypeScript

### Option 1: Ohm

**Type:** PEG-based, separate grammar file

```ohm
Calc {
  Sequent = Structure "|-" Structure
  Structure = Structure "," Structure  -- comma
            | "(" Structure ")"        -- paren
            | Formula
  Formula = Formula "*" Formula        -- tensor
          | Formula "-o" Formula       -- loli
          | "!" Formula                -- bang
          | ident                      -- atom
}
```

```javascript
const semantics = grammar.createSemantics().addOperation('toAST', {
  Formula_tensor(a, _, b) { return new Node(IDS.TENSOR, [a.toAST(), b.toAST()]); },
  // ...
});
```

| Aspect | Rating | Notes |
|--------|--------|-------|
| DX | ⭐⭐⭐⭐⭐ | Online editor, visualizer, excellent errors |
| Performance | ⭐⭐⭐ | Good, not fastest |
| Left recursion | ⭐⭐⭐⭐⭐ | Full support |
| Zig portable | ⭐⭐ | Grammar is portable, semantics are JS |
| Maintenance | ⭐⭐⭐⭐ | Active, single maintainer |

### Option 2: Chevrotain

**Type:** Parser combinator DSL in JS

```javascript
class CalcParser extends CstParser {
  constructor() {
    super(tokenVocabulary);
    this.RULE("sequent", () => {
      this.SUBRULE(this.structure);
      this.CONSUME(Turnstile);
      this.SUBRULE2(this.structure);
    });
    // ...
  }
}
```

| Aspect | Rating | Notes |
|--------|--------|-------|
| DX | ⭐⭐⭐ | Good, but verbose |
| Performance | ⭐⭐⭐⭐⭐ | Fastest JS parser |
| Left recursion | ⭐⭐ | Manual handling required |
| Zig portable | ⭐ | Parser logic is JS classes |
| Maintenance | ⭐⭐⭐⭐⭐ | Very active, SAP-backed |

### Option 3: tree-sitter

**Type:** External grammar → C parser → bindings

```javascript
// grammar.js
module.exports = grammar({
  name: 'calc',
  rules: {
    sequent: $ => seq($.structure, '|-', $.structure),
    structure: $ => choice(
      seq($.structure, ',', $.structure),
      $.formula
    ),
    // ...
  }
});
```

| Aspect | Rating | Notes |
|--------|--------|-------|
| DX | ⭐⭐⭐ | Steeper learning curve |
| Performance | ⭐⭐⭐⭐⭐ | Industrial strength |
| Incremental | ⭐⭐⭐⭐⭐ | Core feature |
| Zig portable | ⭐⭐⭐⭐⭐ | Official Zig bindings |
| Editor support | ⭐⭐⭐⭐⭐ | VSCode, Neovim, etc. |

### Option 4: Peggy

**Type:** PEG grammar → JS parser (successor to PEG.js)

```peggy
Sequent = left:Structure "|-" right:Structure
          { return { type: 'sequent', left, right }; }

Structure = head:Formula tail:("," Structure)*
            { return tail.reduce((acc, [_, s]) => ({type: 'comma', left: acc, right: s}), head); }
```

| Aspect | Rating | Notes |
|--------|--------|-------|
| DX | ⭐⭐⭐⭐ | Simple, familiar |
| Performance | ⭐⭐⭐ | Good |
| Left recursion | ⭐ | Not supported |
| Zig portable | ⭐⭐ | Grammar portable |
| Maintenance | ⭐⭐⭐⭐ | Active fork of PEG.js |

### Option 5: Hand-written Recursive Descent

```javascript
function parseFormula(tokens) {
  let left = parseAtom(tokens);
  while (tokens.peek() === '*' || tokens.peek() === '-o') {
    const op = tokens.consume();
    const right = parseAtom(tokens);
    left = new Node(op === '*' ? IDS.TENSOR : IDS.LOLI, [left, right]);
  }
  return left;
}
```

| Aspect | Rating | Notes |
|--------|--------|-------|
| DX | ⭐⭐ | More code, full control |
| Performance | ⭐⭐⭐⭐⭐ | As fast as you make it |
| Flexibility | ⭐⭐⭐⭐⭐ | Total control |
| Zig portable | ⭐⭐⭐⭐⭐ | Same algorithm, different syntax |
| Error messages | ⭐⭐⭐⭐⭐ | Full control |

### Recommendation

**For prototyping:** Ohm — best visualization and iteration speed.

**For production (with Zig path):**
1. **Short-term:** Ohm with clean AST design (integer IDs, arena-friendly)
2. **Long-term:** tree-sitter for editor integration + Zig bindings

**Migration path:**
```
Jison (current) → Ohm (prototype) → tree-sitter (production)
                      ↓
               Zig hand-written RD (performance-critical)
```

---

## Design Options for CALC

### Option A: Enhanced ll.json + Ohm Parser

Keep ll.json as source of truth, but:
1. Replace Jison with Ohm
2. Add schema validation (JSON Schema or Zod)
3. Generate Ohm grammar from ll.json

**Pros:** Minimal disruption, immediate benefit
**Cons:** Still no deep type checking

```javascript
// schema.ts (with Zod)
const RuleSchema = z.object({
  ascii: z.string(),
  latex: z.string(),
  type: z.array(z.string()).optional(),
  precedence: z.array(z.number()).optional(),
});
```

### Option B: Shallow Embedding in TypeScript

Define calculus in TypeScript with type safety:

```typescript
// Types
type Formula =
  | { tag: 'atom'; name: string }
  | { tag: 'tensor'; left: Formula; right: Formula }
  | { tag: 'loli'; left: Formula; right: Formula }
  | { tag: 'bang'; inner: Formula };

// Rule schema
interface Rule<Conclusion, Premises extends any[]> {
  name: string;
  apply(conclusion: Conclusion): Premises | null;
}

// Example rule
const TensorL: Rule<Sequent, [Sequent]> = {
  name: 'Tensor_L',
  apply(seq) {
    // Pattern match: Γ, A ⊗ B ⊢ C → Γ, A, B ⊢ C
    const match = matchTensorLeft(seq);
    if (!match) return null;
    return [{ ...seq, left: [...match.gamma, match.a, match.b] }];
  }
};
```

**Pros:** Type safety, IDE support, gradual migration
**Cons:** Rules defined in code, not data; harder to export to other tools

### Option C: DSL with Custom Type Checker

Create a new `.calc` DSL inspired by Celf:

```calc
% Type declarations
formula : type.
structure : type.
sequent : type.

% Formula constructors
atom : string -> formula.
tensor : formula -> formula -> formula.
loli : formula -> formula -> formula.
bang : formula -> formula.

% Sequent constructor
seq : structure -> structure -> sequent.

% Inference rules
rule Tensor_L :
  seq (comma Gamma (formula (tensor A B))) C
  <- seq (comma (comma Gamma (formula A)) (formula B)) C.

rule Loli_R :
  seq Gamma (formula (loli A B))
  <- seq (comma Gamma (formula A)) (formula B).
```

Then:
1. Parse with Ohm
2. Type-check the declarations
3. Generate ll.json (or use directly)

**Pros:** Clean syntax, type-safe, exportable
**Cons:** New language to maintain, learning curve

### Option D: Deep Embedding (LF-style)

Full dependent types for maximum precision:

```
% Universe
Type : Kind.
Formula : Type.
Structure : Type.
Sequent : Type.

% Sequent formation
seq : Structure -> Structure -> Sequent.

% Rule type
Rule : Sequent -> List Sequent -> Type.

% Tensor_L with precise types
Tensor_L : (Γ : Structure) -> (A B C : Formula) ->
           Rule (seq (comma Γ (tensor A B)) C)
                [(seq (comma (comma Γ A) B) C)].
```

**Pros:** Maximum type safety, provable properties
**Cons:** Very complex, needs dependent type checker

### Option E: External Verification with Twelf/Celf

Keep ll.json for runtime, export to Twelf/Celf for verification:

```
ll.json ←→ Export/Import ←→ Twelf signature
              ↓
        Twelf type-checks
        Twelf proves metatheorems
```

**Pros:** Leverage existing tools, no new type checker
**Cons:** Two sources of truth, sync issues

---

## Proposed Three-File Architecture

Based on analysis of calculus-toolbox-2, optimism-mde, Twelf, Lean 4, and Isabelle, we propose a **separation of concerns** into three distinct file types:

```
project/
├── linear-logic.calc     # Calculus definition (types, connectives)
├── linear-logic.rules    # Inference rules (sequent calculus)
├── lib/                  # Standard library
│   ├── base.lib          # Core types (nat, bin, bool)
│   ├── arithmetic.lib    # Relations (plus, mul, etc.)
│   └── ...
└── programs/             # Domain-specific programs
    ├── evm.prog          # EVM semantics
    ├── accounting.prog   # Accounting rules
    └── ...
```

### Design Principles

1. **Separation of concerns** — Types/connectives, rules, and programs are distinct
2. **Rich metadata** — Connectives carry interpretations, polarities, duals
3. **Human-readable rules** — Natural deduction style with horizontal lines
4. **Terms as first-class** — Proof terms, resource annotations
5. **Stdlib pattern** — Reusable libraries like optimism-mde/lib

---

### File Type 1: `.calc` — Extended Celf Syntax

Since you prefer Celf syntax (and it's already proven in optimism-mde), we'll use **Celf as the base** and extend it with metadata annotations.

#### Core Celf Syntax (unchanged)

```celf
% Type declarations
formula : type.
structure : type.
sequent : type.
term : type.

% Constructors (standard Celf)
atom : string -> formula.
tensor : formula -> formula -> formula.
loli : formula -> formula -> formula.
bang : formula -> formula.

% Sequent constructor
seq : structure -> structure -> sequent.
```

#### Extended Celf Syntax (our additions)

We add **annotation blocks** after constructor declarations:

```celf
% ============================================================
% Linear Logic Calculus Definition (Extended Celf)
% ============================================================

% ------------------------------------------------------------
% Types
% ------------------------------------------------------------

formula : type.
structure : type.
sequent : type.
term : type.


% ------------------------------------------------------------
% Atoms
% ------------------------------------------------------------

atom : string -> formula
  @ascii "_"
  @latex "#1_{F}".


% ------------------------------------------------------------
% Multiplicative Connectives
% ------------------------------------------------------------

tensor : formula -> formula -> formula
  @ascii "_ * _"
  @latex "#1 \\otimes #2"
  @isabelle "#1 *\\<^sub>F #2"
  @prec 60 left
  @polarity positive
  @category multiplicative
  @dual par
  @unit one
  @interp "Simultaneous availability: both A and B"
  @resource "Combines resources, total = sum of parts".

loli : formula -> formula -> formula
  @ascii "_ -o _"
  @latex "#1 \\multimap #2"
  @prec 50 right
  @polarity negative
  @category multiplicative
  @adjoint tensor            % loli is right adjoint to tensor
  @interp "Linear function: consumes A to produce B".

par : formula -> formula -> formula
  @ascii "_ | _"
  @latex "#1 \\parr #2"
  @prec 60 left
  @polarity negative
  @category multiplicative
  @dual tensor
  @unit bottom
  @interp "Parallel composition (dual of tensor)".


% ------------------------------------------------------------
% Additive Connectives
% ------------------------------------------------------------

with : formula -> formula -> formula
  @ascii "_ & _"
  @latex "#1 \\& #2"
  @prec 60 left
  @polarity negative
  @category additive
  @dual oplus
  @unit top
  @interp "External choice: client picks A or B".

oplus : formula -> formula -> formula
  @ascii "_ + _"
  @latex "#1 \\oplus #2"
  @prec 60 left
  @polarity positive
  @category additive
  @dual with
  @unit zero
  @interp "Internal choice: provider picks A or B".


% ------------------------------------------------------------
% Exponentials
% ------------------------------------------------------------

bang : formula -> formula
  @ascii "! _"
  @latex "!#1"
  @prec 70
  @polarity positive
  @category exponential
  @dual whynot
  @interp "Unlimited availability (0, 1, or many uses)"
  @adjoint "(persistent ⊣ linear)".   % Benton's LNL

whynot : formula -> formula
  @ascii "? _"
  @latex "?#1"
  @prec 70
  @polarity negative
  @category exponential
  @dual bang.


% ------------------------------------------------------------
% Quantifiers
% ------------------------------------------------------------

forall : (formula -> formula) -> formula    % HOAS binding
  @ascii "forall _. _"
  @latex "\\forall #1. #2"
  @prec 30 right
  @polarity negative
  @category quantifier
  @dual exists.

exists : (formula -> formula) -> formula
  @ascii "exists _. _"
  @latex "\\exists #1. #2"
  @prec 30 right
  @polarity positive
  @category quantifier
  @dual forall.


% ------------------------------------------------------------
% Units
% ------------------------------------------------------------

one : formula                     % Unit for tensor
  @ascii "1"
  @latex "\\mathbf{1}"
  @polarity positive
  @category multiplicative.

bottom : formula                  % Unit for par
  @ascii "_|_"
  @latex "\\bot"
  @polarity negative
  @category multiplicative.

top : formula                     % Unit for with
  @ascii "T"
  @latex "\\top"
  @polarity negative
  @category additive.

zero : formula                    % Unit for oplus
  @ascii "0"
  @latex "\\mathbf{0}"
  @polarity positive
  @category additive.


% ------------------------------------------------------------
% Structures
% ------------------------------------------------------------

struct : formula -> structure
  @ascii "_"
  @shallow true.                  % Not user-facing

comma : structure -> structure -> structure
  @ascii "_, _"
  @latex "#1, #2"
  @prec 20 left.

neutral : structure
  @ascii "I"
  @latex "\\cdot".


% ------------------------------------------------------------
% Sequent
% ------------------------------------------------------------

seq : structure -> structure -> sequent
  @ascii "_ |- _"
  @latex "#1 \\vdash #2"
  @prec 10.


% ------------------------------------------------------------
% Terms (proof annotations)
% ------------------------------------------------------------

term_any : term
  @ascii "--"
  @latex "\\cdot".

term_var : string -> term
  @ascii "T?_".

term_pair : term -> term -> term
  @ascii "(_,_)"
  @latex "(#1, #2)".

term_lam : (term -> term) -> term   % HOAS
  @ascii "\\_._ "
  @latex "\\lambda #1. #2".

term_app : term -> term -> term
  @ascii "_ _"
  @prec 80 left.


% ------------------------------------------------------------
% Focused formulas (for proof search)
% ------------------------------------------------------------

focus : formula -> formula
  @ascii "[ _ ]"
  @latex "[#1]"
  @shallow true.

struct_term : term -> formula -> structure
  @ascii "_ : _"
  @prec 80.
```

#### Annotation Reference

| Annotation | Purpose | Example |
|------------|---------|---------|
| `@ascii "..."` | Parser syntax pattern | `"_ * _"` |
| `@latex "..."` | LaTeX output | `"#1 \\otimes #2"` |
| `@isabelle "..."` | Isabelle export | `"#1 *\\<^sub>F #2"` |
| `@prec N [assoc]` | Precedence + associativity | `60 left` |
| `@polarity P` | Positive or negative | `positive` |
| `@category C` | Logical category | `multiplicative` |
| `@dual NAME` | Dual connective | `par` |
| `@adjoint NAME` | Adjoint relationship | `tensor` |
| `@unit NAME` | Unit for this connective | `one` |
| `@interp "..."` | Human interpretation | `"Simultaneous..."` |
| `@resource "..."` | Resource interpretation | `"Combines..."` |
| `@shallow true` | Internal only | `true` |

#### Why Extended Celf?

1. **Familiar syntax** — Already know it from optimism-mde
2. **HOAS for binders** — `(formula -> formula)` handles binding elegantly
3. **Backward compatible** — Pure Celf works, annotations are optional
4. **Clean extension** — `@annotations` don't clash with Celf syntax
5. **Proven at scale** — EVM model works with this approach

---

### File Type 2: `.rules` — Inference Rules

Two options for rule syntax:

#### Option A: Calculus-Toolbox-2 Style (Horizontal Lines)

Human-readable natural deduction style:

```rules
% ============================================================
% Linear Logic Inference Rules
% ============================================================
%
% Convention:
%   - Uppercase Greek (Γ, Δ) = structure
%   - Uppercase Latin (A, B, C) = formula
%   - premises above the line, conclusion below
%   - rule name to the right
% ============================================================

% Identity and Cut
------------ Id
A |- A

G |- A    D, A |- C
-------------------- Cut
G, D |- C

% Multiplicatives
G, A, B |- C
------------- *L
G, A * B |- C

G |- A    D |- B
----------------- *R
G, D |- A * B

G, A |- B
---------- -oR
G |- A -o B

G |- A    D, B |- C
-------------------- -oL
G, D, A -o B |- C

% Additives
G, A |- C
---------- &L1
G, A & B |- C

G, B |- C
---------- &L2
G, A & B |- C

G |- A    G |- B
----------------- &R
G |- A & B

% Exponential
G, A |- C
---------- !D
G, !A |- C

|- A
----- !R
|- !A
```

#### Option B: Celf-Style Rules (Consistent with .calc)

Keep everything in Celf syntax for uniformity:

```celf
% ============================================================
% Linear Logic Inference Rules (Celf syntax)
% ============================================================

% Judgments
deriv : sequent -> type.

% Identity
id : deriv (seq (struct A) (struct A)).

% Cut
cut : deriv (seq (comma G D) C)
   <- deriv (seq G (struct A))
   <- deriv (seq (comma D (struct A)) C).

% Tensor Left
tensor_l : deriv (seq (comma G (struct (tensor A B))) C)
        <- deriv (seq (comma (comma G (struct A)) (struct B)) C).

% Tensor Right
tensor_r : deriv (seq (comma G D) (struct (tensor A B)))
        <- deriv (seq G (struct A))
        <- deriv (seq D (struct B)).

% Lollipop Right
loli_r : deriv (seq G (struct (loli A B)))
      <- deriv (seq (comma G (struct A)) (struct B)).

% Lollipop Left
loli_l : deriv (seq (comma (comma G D) (struct (loli A B))) C)
      <- deriv (seq G (struct A))
      <- deriv (seq (comma D (struct B)) C).

% With Left (choice 1)
with_l1 : deriv (seq (comma G (struct (with A B))) C)
       <- deriv (seq (comma G (struct A)) C).

% With Left (choice 2)
with_l2 : deriv (seq (comma G (struct (with A B))) C)
       <- deriv (seq (comma G (struct B)) C).

% With Right
with_r : deriv (seq G (struct (with A B)))
      <- deriv (seq G (struct A))
      <- deriv (seq G (struct B)).

% Bang - Dereliction
bang_d : deriv (seq (comma G (struct (bang A))) C)
      <- deriv (seq (comma G (struct A)) C).

% Bang - Promotion (empty linear context)
bang_r : deriv (seq neutral (struct (bang A)))
      <- deriv (seq neutral (struct A)).
```

#### Hybrid: Celf + Pretty Annotations

Best of both worlds — Celf semantics with readable presentation:

```celf
% ============================================================
% Linear Logic Inference Rules (Hybrid)
% ============================================================

deriv : sequent -> type.

% -------- Id
% A |- A
id : deriv (seq (struct A) (struct A))
  @pretty "A |- A".

% G |- A    D, A |- C
% -------------------- Cut
% G, D |- C
cut : deriv (seq (comma G D) C)
   <- deriv (seq G (struct A))
   <- deriv (seq (comma D (struct A)) C)
  @pretty "Cut".

% G, A, B |- C
% ------------- *L
% G, A * B |- C
tensor_l : deriv (seq (comma G (struct (tensor A B))) C)
        <- deriv (seq (comma (comma G (struct A)) (struct B)) C)
  @pretty "*L"
  @direction backward
  @invertible true.

% G |- A    D |- B
% ----------------- *R
% G, D |- A * B
tensor_r : deriv (seq (comma G D) (struct (tensor A B)))
        <- deriv (seq G (struct A))
        <- deriv (seq D (struct B))
  @pretty "*R"
  @direction forward
  @splits context.         % Key for proof search

% G, A |- B
% ---------- -oR
% G |- A -o B
loli_r : deriv (seq G (struct (loli A B)))
      <- deriv (seq (comma G (struct A)) (struct B))
  @pretty "-oR"
  @direction backward
  @invertible true.

% G |- A    D, B |- C
% -------------------- -oL
% G, D, A -o B |- C
loli_l : deriv (seq (comma (comma G D) (struct (loli A B))) C)
      <- deriv (seq G (struct A))
      <- deriv (seq (comma D (struct B)) C)
  @pretty "-oL"
  @direction forward
  @splits context.
```

#### Rule Annotations for Proof Search

| Annotation | Purpose | Values |
|------------|---------|--------|
| `@pretty "..."` | Display name | `"*L"` |
| `@direction D` | When to apply | `forward`, `backward` |
| `@invertible B` | Safe to apply eagerly | `true`, `false` |
| `@splits X` | What gets split | `context`, `formula` |
| `@phase P` | Focusing phase | `inversion`, `focus` |

#### Recommendation

**Use Celf-style with `@pretty` annotations**:
- Single syntax for everything (.calc, .rules, .lib, .prog)
- Machine-readable (easy to parse, type-check)
- Pretty-print horizontal lines from `@pretty` annotations
- Annotations guide proof search strategy

---

### File Type 3: `.lib` — Standard Library

Libraries are **pure Celf syntax** (no extensions needed — the annotations are only for connectives). This is exactly what optimism-mde/lib already does.

#### Example: `lib/base.mde`

```celf
% ============================================================
% Base Library: Fundamental Types
% ============================================================
% This is standard Celf - no extensions needed

% ------------------------------------------------------------
% Natural Numbers (Peano style)
% ------------------------------------------------------------

nat : type.
z : nat.
s : nat -> nat.

% Equality
nat_eq : nat -> nat -> type.
nat_eq/refl : nat_eq N N.

% Inequality
nat_neq : nat -> nat -> type.
nat_neq/zs : nat_neq z (s N).
nat_neq/sz : nat_neq (s N) z.
nat_neq/ss : nat_neq (s M) (s N)
  <- nat_neq M N.


% ------------------------------------------------------------
% Binary Numbers (more efficient for arithmetic)
% ------------------------------------------------------------

bin : type.
e : bin.                          % Zero / empty
i : bin -> bin.                   % Bit 1 (2n + 1)
o : bin -> bin.                   % Bit 0 (2n)

% Examples:
%   1 = i e           (binary: 1)
%   2 = o (i e)       (binary: 10)
%   3 = i (i e)       (binary: 11)
%   5 = i (o (i e))   (binary: 101)

% Equality
eq : bin -> bin -> type.
eq/refl : eq X X.

% Inequality
neq : bin -> bin -> type.
neq/z1 : neq e (o Y).
neq/z2 : neq e (i X).
neq/z3 : neq (o X) e.
neq/z4 : neq (i X) e.
neq/z5 : neq (o X) (i Y).
neq/z6 : neq (i X) (o Y).
neq/s1 : neq (o X) (o Y) <- neq X Y.
neq/s2 : neq (i X) (i Y) <- neq X Y.


% ------------------------------------------------------------
% Booleans
% ------------------------------------------------------------

bool : type.
true : bool.
false : bool.

not : bool -> bool -> type.
not/t : not true false.
not/f : not false true.

and : bool -> bool -> bool -> type.
and/tt : and true true true.
and/tf : and true false false.
and/ft : and false true false.
and/ff : and false false false.

or : bool -> bool -> bool -> type.
or/tt : or true true true.
or/tf : or true false true.
or/ft : or false true true.
or/ff : or false false false.
```

#### Example: `lib/arithmetic.mde`

```celf
% ============================================================
% Arithmetic Library
% ============================================================
% Exactly like optimism-mde/lib/bin.mde

% ------------------------------------------------------------
% Binary Increment
% ------------------------------------------------------------

inc : bin -> bin -> type.
inc/z1 : inc (o X) (i X).         % 2n -> 2n+1
inc/z2 : inc e (i e).             % 0 -> 1
inc/s  : inc (i X) (o Y)          % 2n+1 -> 2(n+1) via carry
  <- inc X Y.


% ------------------------------------------------------------
% Binary Addition
% ------------------------------------------------------------

plus : bin -> bin -> bin -> type.

% Base cases
plus/z1 : plus e e e.
plus/z2 : plus e (o N) (o N).
plus/z3 : plus e (i N) (i N).
plus/z4 : plus (o M) e (o M).
plus/z5 : plus (i M) e (i M).

% Recursive cases
plus/s1 : plus (o M) (o N) (o R) <- plus M N R.
plus/s2 : plus (o M) (i N) (i R) <- plus M N R.
plus/s3 : plus (i M) (o N) (i R) <- plus M N R.
plus/s4 : plus (i M) (i N) (o R)  % Carry case
  <- plus M N Q
  <- inc Q R.


% ------------------------------------------------------------
% Binary Multiplication
% ------------------------------------------------------------

mul : bin -> bin -> bin -> type.

mul/z1 : mul e Y e.               % 0 × Y = 0
mul/s1 : mul (o X) Y Z            % 2X × Y = 2(X × Y)
  <- mul X (o Y) Z.
mul/s2 : mul (i X) Y Z'           % (2X+1) × Y = 2(X × Y) + Y
  <- mul X (o Y) Z
  <- plus Y Z Z'.


% ------------------------------------------------------------
% Comparison (from optimism-mde)
% ------------------------------------------------------------

%   X      Y      ass.   res.
gt : bin -> bin -> bin -> bin -> type.

gt/ee : gt e e A A.               % Equal: return assumption
gt/ie : gt (i X) e A (i e).       % X has more bits: X > Y
gt/ei : gt e (i Y) A (o e).       % Y has more bits: X < Y

gt/ii : gt (i X) (i Y) A R <- gt X Y A R.
gt/io : gt (i X) (o Y) A R <- gt X Y (i e) R.
gt/oi : gt (o X) (i Y) A R <- gt X Y (o e) R.
gt/oo : gt (o X) (o Y) A R <- gt X Y A R.
gt/oe : gt (o X) e A R <- gt X e A R.
gt/eo : gt e (o Y) A R <- gt e Y A R.
```

#### Key Insight: Stdlib is Pure Celf

The stdlib files (`.mde`) are **unchanged from optimism-mde** — pure Celf syntax. We only add the `@annotations` for:
- Connective definitions in `.calc` (polarity, dual, latex, etc.)
- Rule metadata in `.rules` (invertibility, proof search hints)

This means:
1. Existing optimism-mde/lib works as-is
2. No new syntax to learn for domain libraries
3. Focus extensions on where they add value

---

### File Type 4: `.mde` — Programs/Specifications

Programs use **pure Celf syntax** — exactly like optimism-mde. No extensions needed.

#### Example: `programs/accounting.mde`

```celf
% ============================================================
% Double-Entry Accounting Specification
% ============================================================
% Pure Celf - identical syntax to optimism-mde

% ------------------------------------------------------------
% Domain Types
% ------------------------------------------------------------

account : type.
currency : type.
amount : type.

% Accounts
alice : account.
bob   : account.
bank  : account.

% Currencies
usd : currency.
eur : currency.

% Amount as (quantity, currency)
amt : bin -> currency -> amount.


% ------------------------------------------------------------
% Ownership Predicate (Linear Resource)
% ------------------------------------------------------------

% owns A X means account A owns amount X (linearly)
owns : account -> amount -> type.


% ------------------------------------------------------------
% Transfer Rule
% ------------------------------------------------------------

transfer:
  owns From (amt Q C) *           % From has Q units of C
  !neq From To                    % Not self-transfer
  -o {
    owns To (amt Q C)             % To receives Q units of C
  }.


% ------------------------------------------------------------
% Split Rule (for partial transfers)
% ------------------------------------------------------------

split:
  owns A (amt Total C) *
  !plus Part1 Part2 Total         % Total = Part1 + Part2
  -o {
    owns A (amt Part1 C) *
    owns A (amt Part2 C)
  }.


% ------------------------------------------------------------
% Merge Rule
% ------------------------------------------------------------

merge:
  owns A (amt Q1 C) *
  owns A (amt Q2 C) *
  !plus Q1 Q2 Total
  -o {
    owns A (amt Total C)
  }.


% ------------------------------------------------------------
% Example Scenario
% ------------------------------------------------------------

% Initial state: Alice has 100 USD
init : owns alice (amt N_100 usd).

% Goal: Transfer 30 to Bob, keep 70
% Proof trace:
%   1. split: owns alice (amt N_100 usd)
%             owns alice (amt N_30 usd) * owns alice (amt N_70 usd)
%   2. transfer: owns alice (amt N_30 usd)
%                owns bob (amt N_30 usd)
%   3. Result: owns alice (amt N_70 usd) * owns bob (amt N_30 usd)
```

#### Example: EVM is Unchanged

The `programs/evm.mde` is **exactly the same as optimism-mde** — no changes needed:

```celf
% EVM Semantics - pure Celf
% (See ~/src/optimism-mde/lib/evm.mde for full version)

pc      : bin -> type.            % Program counter
gas     : bin -> type.            % Gas remaining
sh      : nat -> type.            % Stack height
stack   : nat -> bin -> type.     % Stack slot
storage : bin -> bin -> type.     % Storage mapping
code    : bin -> bin -> type.     % Code at address

stop    : type.
revert  : type.

% STOP (0x00)
evm/stop:
  pc PC *
  code PC N_00 *
  !inc PC PC'
  -o {
    code PC N_00 *
    stop
  }.

% ADD (0x01)
evm/add:
  pc PC *
  code PC N_01 *
  !inc PC PC' *
  sh (s (s SH)) *
  stack (s SH) A *
  stack SH B *
  !plus A B C
  -o {
    code PC N_01 *
    pc PC' *
    sh (s SH) *
    stack SH C
  }.
```

#### File Type Summary

| File | Syntax | Extensions | Purpose |
|------|--------|------------|---------|
| `.calc` | Extended Celf | `@annotations` | Connectives + metadata |
| `.rules` | Celf or Horizontal | `@annotations` | Inference rules |
| `.mde` (lib) | **Pure Celf** | None | Stdlib (types, relations) |
| `.mde` (prog) | **Pure Celf** | None | Domain specifications |

**Key insight**: Only the calculus definition (`.calc`) needs extensions. Everything else is pure Celf, which means optimism-mde works unchanged.

---

### Syntax Extensions: Literals and FFI

Two critical extensions for practical programming:

1. **Literals** — Syntactic sugar for strings, numbers, hex
2. **FFI** — Escape proof search for computational predicates

---

#### 1. Literal Syntax

##### The Problem

In optimism-mde, numbers are written as nested constructors:
```celf
% 5 in binary = 101 = i(o(i(e)))
plus (i(o(i(e)))) (i(i(e))) Result   % 5 + 3 = ?

% This is unreadable for humans
```

##### Solution: Literal Annotations in `.calc`

Define literal syntax in the calculus definition:

```celf
% ============================================================
% Literal Syntax Definitions (in .calc file)
% ============================================================

% Binary numbers with decimal literal syntax
bin : type
  @literal decimal "[0-9]+"           % matches: 42, 100, 0
  @literal binary  "0b[01]+"          % matches: 0b101, 0b1111
  @literal hex     "0x[0-9a-fA-F]+"   % matches: 0xff, 0x1a2b
  @desugar decimal bin_from_decimal   % function name
  @desugar binary  bin_from_binary
  @desugar hex     bin_from_hex.

% Natural numbers
nat : type
  @literal decimal "[0-9]+"
  @desugar decimal nat_from_decimal.  % s(s(s(...z)))

% Strings
string : type
  @literal string "\"[^\"]*\""        % matches: "hello", "foo"
  @desugar string string_from_chars.

% Floating point (for future use)
rational : type
  @literal decimal "[0-9]+\\.[0-9]+"  % matches: 3.14, 0.5
  @desugar decimal rational_from_decimal.
```

##### Desugaring Functions

The desugaring functions are implemented in FFI:

```javascript
// lib/ffi/literals.js

const ffi = {
  bin_from_decimal: {
    // Convert JS number to bin AST
    // 5 → i(o(i(e)))  [binary: 101]
    compute: (n) => {
      if (n === 0) return { tag: 'e' };
      const bit = n % 2;
      const rest = Math.floor(n / 2);
      const restTerm = ffi.bin_from_decimal.compute(rest);
      return bit === 1
        ? { tag: 'i', arg: restTerm }
        : { tag: 'o', arg: restTerm };
    }
  },

  bin_from_hex: {
    compute: (s) => {
      const n = parseInt(s.slice(2), 16);  // Remove "0x"
      return ffi.bin_from_decimal.compute(n);
    }
  },

  nat_from_decimal: {
    // 3 → s(s(s(z)))
    compute: (n) => {
      let result = { tag: 'z' };
      for (let i = 0; i < n; i++) {
        result = { tag: 's', arg: result };
      }
      return result;
    }
  },

  string_from_chars: {
    // "abc" → cons('a', cons('b', cons('c', nil)))
    // Or just store as opaque string term
    compute: (s) => ({ tag: 'string', value: s.slice(1, -1) })
  }
};
```

##### Usage in Programs

```celf
% With literal syntax:
plus 5 3 Result                       % readable!
stack 0 0xff                          % hex literal
owns alice 100 usd                    % decimal

% Parser automatically desugars to:
plus (i(o(i(e)))) (i(i(e))) Result
stack e (i(i(i(i(i(i(i(i(e)))))))))
owns alice (i(i(o(o(i(o(i(e))))))) usd
```

##### Literal Pretty-Printing

For output, convert back to literals:

```celf
% Add @pretty annotation for display
bin : type
  @literal decimal "[0-9]+"
  @pretty  decimal bin_to_decimal.    % For output
```

---

#### 2. FFI Predicates

##### The Problem

Proof search through `plus` rules is slow and pointless when inputs are ground:

```celf
% Query: plus 1000000 2000000 X
% Proof search: 1000000 recursive steps!
% But we just want: X = 3000000
```

##### Solution: FFI Annotation

Mark predicates as FFI in the stdlib:

```celf
% ============================================================
% FFI Predicates (in lib/arithmetic.mde)
% ============================================================

% Plus with FFI acceleration
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus              % FFI function name
  @mode + + -                       % input input output
  @verify true                      % check result
  @fallback axioms.                 % if FFI fails, use axioms

% The axiomatization still exists (for verification, partial instantiation):
plus/z1 : plus e e e.
plus/z2 : plus e (o N) (o N).
% ... etc

% But when both inputs are ground, FFI is used instead
```

##### Multi-Mode FFI

Key insight: A relation like `plus(A, B, C)` where `A + B = C` can be used in **multiple modes**:

| Mode | Meaning | Operation | Example |
|------|---------|-----------|---------|
| `+ + -` | A, B known → compute C | Addition | `plus 5 3 X` → `X = 8` |
| `+ - +` | A, C known → compute B | Subtraction | `plus 5 X 8` → `X = 3` |
| `- + +` | B, C known → compute A | Subtraction | `plus X 3 8` → `X = 5` |
| `- - +` | Only C known | Enumerate | `plus X Y 8` → `(0,8), (1,7), ...` |

##### FFI with Multiple Modes and Failure

```celf
% In .mde file: declare all supported modes
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @modes [
    (+ + -),          % addition
    (+ - +),          % subtraction (C - A = B)
    (- + +)           % subtraction (C - B = A)
  ]
  @fallback axioms.   % for (- - +), (- - -), etc.
```

##### FFI Function Signature with Failure

```javascript
// lib/ffi/arithmetic.js

const ffi = {
  plus: {
    // Multiple mode handlers
    modes: {
      // Mode: + + - (addition)
      '+ + -': {
        canApply: (a, b, c) => isGround(a) && isGround(b),
        compute: (a, b, c) => {
          // Always succeeds for natural numbers
          return { success: true, bindings: { c: a + b } };
        }
      },

      // Mode: + - + (subtraction: find B such that A + B = C)
      '+ - +': {
        canApply: (a, b, c) => isGround(a) && isGround(c),
        compute: (a, b, c) => {
          const result = c - a;
          // CRITICAL: Check if solution exists!
          if (result < 0n) {
            // No natural number B exists where A + B = C
            return { success: false, reason: 'no solution: would be negative' };
          }
          return { success: true, bindings: { b: result } };
        }
      },

      // Mode: - + + (subtraction: find A such that A + B = C)
      '- + +': {
        canApply: (a, b, c) => isGround(b) && isGround(c),
        compute: (a, b, c) => {
          const result = c - b;
          if (result < 0n) {
            return { success: false, reason: 'no solution: would be negative' };
          }
          return { success: true, bindings: { a: result } };
        }
      }
    },

    // Global verification (optional)
    verify: (a, b, c) => a + b === c
  },

  mul: {
    modes: {
      '+ + -': {
        canApply: (a, b, c) => isGround(a) && isGround(b),
        compute: (a, b, c) => ({ success: true, bindings: { c: a * b } })
      },
      '+ - +': {
        canApply: (a, b, c) => isGround(a) && isGround(c),
        compute: (a, b, c) => {
          if (a === 0n) {
            // 0 * B = C only if C = 0
            if (c === 0n) {
              // Infinitely many solutions! Fall back to axioms
              return { success: false, reason: 'infinite solutions' };
            } else {
              return { success: false, reason: 'no solution: 0 * B ≠ C for C > 0' };
            }
          }
          if (c % a !== 0n) {
            return { success: false, reason: 'no solution: not divisible' };
          }
          return { success: true, bindings: { b: c / a } };
        }
      },
      '- + +': {
        canApply: (a, b, c) => isGround(b) && isGround(c),
        compute: (a, b, c) => {
          if (b === 0n) {
            if (c === 0n) {
              return { success: false, reason: 'infinite solutions' };
            } else {
              return { success: false, reason: 'no solution: A * 0 ≠ C for C > 0' };
            }
          }
          if (c % b !== 0n) {
            return { success: false, reason: 'no solution: not divisible' };
          }
          return { success: true, bindings: { a: c / b } };
        }
      }
    },
    verify: (a, b, c) => a * b === c
  },

  gt: {
    modes: {
      '+ + -': {
        canApply: (a, b, r) => isGround(a) && isGround(b),
        compute: (a, b, r) => ({
          success: true,
          bindings: { r: a > b ? 1n : 0n }
        })
      }
    },
    verify: (a, b, r) => (a > b) === (r === 1n)
  },

  // Division with remainder: A = B * Q + R, 0 <= R < B
  divmod: {
    modes: {
      '+ + - -': {
        canApply: (a, b, q, r) => isGround(a) && isGround(b),
        compute: (a, b, q, r) => {
          if (b === 0n) {
            return { success: false, reason: 'division by zero' };
          }
          return {
            success: true,
            bindings: { q: a / b, r: a % b }
          };
        }
      }
    },
    verify: (a, b, q, r) => a === b * q + r && r >= 0n && r < b
  }
};
```

##### FFI Dispatch Logic

```javascript
// In proof search (lib/proofstate.js)

function tryGoal(goal, predicate) {
  // Check if predicate has FFI
  if (predicate.ffi) {
    // Find applicable mode based on which args are ground
    const mode = findApplicableMode(predicate.ffi, goal.args);

    if (mode) {
      // FFI path
      const result = mode.compute(...goal.args);

      if (result.success) {
        // Apply bindings to goal
        const unified = applyBindings(goal, result.bindings);

        // Optionally verify
        if (predicate.ffi.verify) {
          const allValues = getAllGroundValues(unified.args);
          if (!predicate.ffi.verify(...allValues)) {
            throw new Error(`FFI verification failed: ${predicate.name}`);
          }
        }

        return unified;
      } else {
        // FFI says no solution exists!
        // This is a PROOF FAILURE, not an error
        console.log(`FFI: ${predicate.name} - ${result.reason}`);
        return null;  // No proof exists
      }
    }
  }

  // No applicable FFI mode - fall back to axioms
  if (predicate.fallback === 'axioms') {
    return backchain(goal, predicate.axioms);
  } else {
    // No fallback configured
    return null;
  }
}

function findApplicableMode(ffi, args) {
  // Build mode string from groundness
  const modeStr = args.map(a => isGround(a) ? '+' : '-').join(' ');

  // Check if this mode is supported
  if (ffi.modes[modeStr]) {
    const mode = ffi.modes[modeStr];
    if (mode.canApply(...args)) {
      return mode;
    }
  }

  return null;  // No applicable mode
}
```

##### FFI Return Values

| Return | Meaning | Proof search action |
|--------|---------|---------------------|
| `{ success: true, bindings: {...} }` | Solution found | Continue with bindings |
| `{ success: false, reason: '...' }` | No solution exists | Fail this branch |
| No applicable mode | FFI can't handle | Fall back to axioms |

##### Example: Subtraction Failure

```celf
% Query: plus 5 X 3
% Meaning: Find X where 5 + X = 3
% Mode: + - +

% FFI dispatch:
1. Mode '+ - +' matches (5 is ground, X is not, 3 is ground)
2. compute(5, X, 3):
   result = 3 - 5 = -2
   -2 < 0, so no natural number solution exists
3. Return: { success: false, reason: 'no solution: would be negative' }
4. Proof search: this branch FAILS (no proof)

% Compare to: plus 5 X 8
% FFI returns: { success: true, bindings: { X: 3 } }
% Proof continues with X = 3
```
```

##### Multi-Mode FFI + Fallback to Axioms

```celf
% Full FFI declaration with multiple modes:
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @modes [
    (+ + -),          % A + B = ? (addition)
    (+ - +),          % A + ? = C (subtraction)
    (- + +)           % ? + B = C (subtraction)
  ]
  @fallback axioms.   % For modes like (- - +) or (- - -)

% Query 1: plus 5 3 X    → FFI mode (+ + -), computes X = 8
% Query 2: plus 5 X 8    → FFI mode (+ - +), computes X = 3
% Query 3: plus X 3 8    → FFI mode (- + +), computes X = 5
% Query 4: plus 5 X 3    → FFI mode (+ - +), FAILS (would be negative)
% Query 5: plus X Y 8    → No FFI mode, falls back to axioms

% Axioms for non-FFI cases (enumeration):
plus/z1 : plus e e e.
plus/s1 : plus (o M) (o N) (o R) <- plus M N R.
% ...
```

##### Alternative: Inline Mode Handlers

For complex predicates, define mode handlers inline:

```celf
divmod : bin -> bin -> bin -> bin -> type
  @ffi {
    mode (+ + - -) {
      check: B != 0,                    % precondition
      compute: { Q: A / B, R: A % B },  % outputs
      verify: A == B * Q + R && R < B
    }
    % Other modes could enumerate (fall back to axioms)
  }
  @fallback axioms.
```

##### Comparison with optimism-mde

Currently in optimism-mde:
```celf
% Must write all cases manually:
plus/z1: plus e e e.
plus/z2: plus e (o N) (o N).
plus/z3: plus e (i N) (i N).
plus/s1: plus (o M) (o N) (o R) <- plus M N R.
plus/s2: plus (o M) (i N) (i R) <- plus M N R.
% ... many more cases
```

With FFI:
```celf
% Just mark it:
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @mode + + -.

% Axioms optional (for backwards compatibility / verification)
```

---

#### 3. Putting It Together

##### Complete Example: Accounting with FFI

```celf
% ============================================================
% lib/money.mde - Money arithmetic with FFI
% ============================================================

% Amount type with decimal literal support
amount : type
  @literal decimal "[0-9]+(\\.[0-9]+)?"
  @desugar decimal amount_from_decimal.

% Currency
currency : type.
usd : currency.
eur : currency.
btc : currency.

% Money = amount + currency
money : amount -> currency -> type.

% Addition with FFI
money_add : money -> money -> money -> type
  @ffi money.add
  @mode + + -
  @verify true.

% The FFI checks currency match:
% money_add (money 100 usd) (money 50 usd) → money 150 usd
% money_add (money 100 usd) (money 50 eur) → ERROR: currency mismatch

% ============================================================
% programs/transfer.mde - Uses money FFI
% ============================================================

owns : account -> money -> type.

transfer:
  owns From (money Amt C) *
  !money_add (money Amt C) (money 0 C) (money Amt C)  % validation
  -o {
    owns To (money Amt C)
  }.

% Example usage with literals:
init : owns alice (money 100.50 usd).
goal : owns bob (money 100.50 usd).
```

##### FFI for EVM

```celf
% In lib/evm.mde, mark instructions as FFI:

% SHA3 - definitely needs FFI!
sha3 : bin -> bin -> type
  @ffi evm.sha3
  @mode + -.

% ECRECOVER - crypto operation
ecrecover : bin -> bin -> bin -> bin -> bin -> type
  @ffi evm.ecrecover
  @mode + + + + -.

% Even simple ops benefit from FFI:
evm_add : bin -> bin -> bin -> type
  @ffi evm.add
  @mode + + -
  @verify true.
```

---

#### Design Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Literal location | In `.calc` type definition | Types own their syntax |
| FFI location | In `.mde` predicate definition | Predicates own their implementation |
| Mode syntax | `@mode + + -` | Matches Twelf convention |
| Fallback | Optional axioms | Allows hybrid FFI/proof search |
| Verification | Optional but recommended | Catches FFI bugs |

---

#### 5. JavaScript Implementation

##### File Structure

```
lib/
├── ffi/
│   ├── index.js          # FFI registry and dispatch
│   ├── arithmetic.js     # plus, mul, div, gt, etc.
│   ├── strings.js        # concat, length, etc.
│   ├── crypto.js         # sha3, ecrecover (for EVM)
│   └── literals.js       # bin_from_decimal, etc.
├── proofstate.js         # Modified to call FFI
└── node.js               # Term representation
```

##### FFI Registry (`lib/ffi/index.js`)

```javascript
// lib/ffi/index.js

const arithmetic = require('./arithmetic');
const strings = require('./strings');
const literals = require('./literals');

// Global FFI registry
const FFI_REGISTRY = {
  'arithmetic.plus': arithmetic.plus,
  'arithmetic.mul': arithmetic.mul,
  'arithmetic.gt': arithmetic.gt,
  'arithmetic.divmod': arithmetic.divmod,
  'strings.concat': strings.concat,
  'strings.length': strings.length,
  'literals.bin_from_decimal': literals.bin_from_decimal,
  'literals.bin_from_hex': literals.bin_from_hex,
};

/**
 * Get FFI handler for a predicate
 * @param {string} name - FFI function name (e.g., 'arithmetic.plus')
 * @returns {object|null} - FFI handler or null
 */
function getFFI(name) {
  return FFI_REGISTRY[name] || null;
}

/**
 * Check if a term is ground (fully instantiated, no variables)
 * @param {Node} term - AST node
 * @returns {boolean}
 */
function isGround(term) {
  if (!term) return false;
  if (term.isVariable) return false;
  if (term.vals) {
    return term.vals.every(v => isGround(v));
  }
  return true;
}

/**
 * Convert AST Node to JS value (for FFI input)
 * @param {Node} term - Ground term
 * @returns {bigint|string|...} - JS value
 */
function termToValue(term) {
  // Handle bin type: e, i(X), o(X)
  if (term.id === 'bin_e') return 0n;
  if (term.id === 'bin_i') {
    return 2n * termToValue(term.vals[0]) + 1n;
  }
  if (term.id === 'bin_o') {
    return 2n * termToValue(term.vals[0]);
  }

  // Handle nat type: z, s(X)
  if (term.id === 'nat_z') return 0n;
  if (term.id === 'nat_s') {
    return 1n + termToValue(term.vals[0]);
  }

  // Handle string type
  if (term.id === 'string') {
    return term.vals[0];  // Raw string value
  }

  throw new Error(`Cannot convert term to value: ${term.id}`);
}

/**
 * Convert JS value back to AST Node (for FFI output)
 * @param {bigint|string|...} value - JS value
 * @param {string} type - Target type ('bin', 'nat', 'string')
 * @returns {Node}
 */
function valueToTerm(value, type) {
  if (type === 'bin') {
    if (value === 0n) return { id: 'bin_e', vals: [] };
    const bit = value % 2n;
    const rest = value / 2n;
    const restTerm = valueToTerm(rest, 'bin');
    return bit === 1n
      ? { id: 'bin_i', vals: [restTerm] }
      : { id: 'bin_o', vals: [restTerm] };
  }

  if (type === 'nat') {
    if (value === 0n) return { id: 'nat_z', vals: [] };
    return { id: 'nat_s', vals: [valueToTerm(value - 1n, 'nat')] };
  }

  if (type === 'string') {
    return { id: 'string', vals: [value] };
  }

  throw new Error(`Unknown type for valueToTerm: ${type}`);
}

module.exports = {
  getFFI,
  isGround,
  termToValue,
  valueToTerm,
  FFI_REGISTRY
};
```

##### Arithmetic FFI (`lib/ffi/arithmetic.js`)

```javascript
// lib/ffi/arithmetic.js

const { isGround, termToValue, valueToTerm } = require('./index');

const plus = {
  // Metadata (matches @modes in .mde)
  modes: ['+ + -', '+ - +', '- + +'],
  argTypes: ['bin', 'bin', 'bin'],

  // Mode handlers
  handlers: {
    '+ + -': {
      canApply: (a, b, c) => isGround(a) && isGround(b),
      compute: (a, b, c) => {
        const aVal = termToValue(a);
        const bVal = termToValue(b);
        const result = aVal + bVal;
        return {
          success: true,
          bindings: { 2: valueToTerm(result, 'bin') }  // Index 2 = third arg
        };
      }
    },

    '+ - +': {
      canApply: (a, b, c) => isGround(a) && isGround(c),
      compute: (a, b, c) => {
        const aVal = termToValue(a);
        const cVal = termToValue(c);
        const result = cVal - aVal;

        // Check: does a valid solution exist?
        if (result < 0n) {
          return {
            success: false,
            reason: `no solution: ${cVal} - ${aVal} = ${result} < 0`
          };
        }

        return {
          success: true,
          bindings: { 1: valueToTerm(result, 'bin') }  // Index 1 = second arg
        };
      }
    },

    '- + +': {
      canApply: (a, b, c) => isGround(b) && isGround(c),
      compute: (a, b, c) => {
        const bVal = termToValue(b);
        const cVal = termToValue(c);
        const result = cVal - bVal;

        if (result < 0n) {
          return {
            success: false,
            reason: `no solution: ${cVal} - ${bVal} = ${result} < 0`
          };
        }

        return {
          success: true,
          bindings: { 0: valueToTerm(result, 'bin') }  // Index 0 = first arg
        };
      }
    }
  },

  // Optional verification (for debugging/safety)
  verify: (a, b, c) => {
    if (!isGround(a) || !isGround(b) || !isGround(c)) return true;
    return termToValue(a) + termToValue(b) === termToValue(c);
  }
};

const mul = {
  modes: ['+ + -', '+ - +', '- + +'],
  argTypes: ['bin', 'bin', 'bin'],

  handlers: {
    '+ + -': {
      canApply: (a, b, c) => isGround(a) && isGround(b),
      compute: (a, b, c) => {
        const aVal = termToValue(a);
        const bVal = termToValue(b);
        return {
          success: true,
          bindings: { 2: valueToTerm(aVal * bVal, 'bin') }
        };
      }
    },

    '+ - +': {
      canApply: (a, b, c) => isGround(a) && isGround(c),
      compute: (a, b, c) => {
        const aVal = termToValue(a);
        const cVal = termToValue(c);

        // Special case: 0 * B = C
        if (aVal === 0n) {
          if (cVal === 0n) {
            // 0 * B = 0 has infinitely many solutions
            return { success: false, reason: 'infinite solutions: 0 * B = 0' };
          } else {
            // 0 * B = C (C > 0) has no solution
            return { success: false, reason: 'no solution: 0 * B ≠ ' + cVal };
          }
        }

        // Check divisibility
        if (cVal % aVal !== 0n) {
          return {
            success: false,
            reason: `no solution: ${cVal} not divisible by ${aVal}`
          };
        }

        return {
          success: true,
          bindings: { 1: valueToTerm(cVal / aVal, 'bin') }
        };
      }
    },

    '- + +': {
      canApply: (a, b, c) => isGround(b) && isGround(c),
      compute: (a, b, c) => {
        const bVal = termToValue(b);
        const cVal = termToValue(c);

        if (bVal === 0n) {
          if (cVal === 0n) {
            return { success: false, reason: 'infinite solutions: A * 0 = 0' };
          } else {
            return { success: false, reason: 'no solution: A * 0 ≠ ' + cVal };
          }
        }

        if (cVal % bVal !== 0n) {
          return {
            success: false,
            reason: `no solution: ${cVal} not divisible by ${bVal}`
          };
        }

        return {
          success: true,
          bindings: { 0: valueToTerm(cVal / bVal, 'bin') }
        };
      }
    }
  },

  verify: (a, b, c) => {
    if (!isGround(a) || !isGround(b) || !isGround(c)) return true;
    return termToValue(a) * termToValue(b) === termToValue(c);
  }
};

const gt = {
  modes: ['+ + -'],
  argTypes: ['bin', 'bin', 'bin'],  // Result is 0 or 1

  handlers: {
    '+ + -': {
      canApply: (a, b, r) => isGround(a) && isGround(b),
      compute: (a, b, r) => {
        const aVal = termToValue(a);
        const bVal = termToValue(b);
        const result = aVal > bVal ? 1n : 0n;
        return {
          success: true,
          bindings: { 2: valueToTerm(result, 'bin') }
        };
      }
    }
  }
};

const divmod = {
  modes: ['+ + - -'],
  argTypes: ['bin', 'bin', 'bin', 'bin'],  // A, B, Q, R where A = B*Q + R

  handlers: {
    '+ + - -': {
      canApply: (a, b, q, r) => isGround(a) && isGround(b),
      compute: (a, b, q, r) => {
        const aVal = termToValue(a);
        const bVal = termToValue(b);

        if (bVal === 0n) {
          return { success: false, reason: 'division by zero' };
        }

        const quotient = aVal / bVal;
        const remainder = aVal % bVal;

        return {
          success: true,
          bindings: {
            2: valueToTerm(quotient, 'bin'),
            3: valueToTerm(remainder, 'bin')
          }
        };
      }
    }
  },

  verify: (a, b, q, r) => {
    if (!isGround(a) || !isGround(b) || !isGround(q) || !isGround(r)) {
      return true;
    }
    const aVal = termToValue(a);
    const bVal = termToValue(b);
    const qVal = termToValue(q);
    const rVal = termToValue(r);
    return aVal === bVal * qVal + rVal && rVal >= 0n && rVal < bVal;
  }
};

module.exports = { plus, mul, gt, divmod };
```

##### Integration with Proof Search (`lib/proofstate.js`)

```javascript
// In lib/proofstate.js - modifications for FFI support

const { getFFI, isGround } = require('./ffi');

class Proofstate {
  // ... existing code ...

  /**
   * Try to solve a goal, using FFI if applicable
   */
  tryGoal(goal) {
    const predName = goal.predicate;
    const predInfo = this.getPredicateInfo(predName);

    // Check if predicate has FFI
    if (predInfo && predInfo.ffi) {
      const ffiResult = this.tryFFI(predInfo.ffi, goal.args);

      if (ffiResult !== null) {
        // FFI handled it (either success or definite failure)
        return ffiResult;
      }
      // FFI returned null = no applicable mode, fall through to axioms
    }

    // Fall back to normal proof search
    return this.backchain(goal);
  }

  /**
   * Attempt FFI for a goal
   * @returns {object|null} - Result, or null if FFI not applicable
   */
  tryFFI(ffiName, args) {
    const ffi = getFFI(ffiName);
    if (!ffi) return null;

    // Determine current mode based on groundness
    const modeStr = args.map(a => isGround(a) ? '+' : '-').join(' ');

    // Check if this mode is supported
    const handler = ffi.handlers[modeStr];
    if (!handler) return null;

    // Check additional preconditions
    if (!handler.canApply(...args)) return null;

    // Call the FFI
    const result = handler.compute(...args);

    if (result.success) {
      // Apply bindings to create new goal state
      const newArgs = args.map((arg, i) =>
        result.bindings[i] !== undefined ? result.bindings[i] : arg
      );

      // Optionally verify
      if (ffi.verify && !ffi.verify(...newArgs)) {
        console.error(`FFI verification failed: ${ffiName}`);
        return { success: false, reason: 'verification failed' };
      }

      return {
        success: true,
        args: newArgs,
        // Mark as FFI-solved for proof tree
        proofStep: { type: 'ffi', name: ffiName, mode: modeStr }
      };
    } else {
      // FFI explicitly says no solution exists
      return {
        success: false,
        reason: result.reason,
        proofStep: { type: 'ffi-fail', name: ffiName, reason: result.reason }
      };
    }
  }

  /**
   * Get predicate info including FFI annotation
   */
  getPredicateInfo(name) {
    // Look up in calculus definition
    const info = this.calc.predicates[name];
    if (info && info.annotations && info.annotations.ffi) {
      return {
        ffi: info.annotations.ffi,
        modes: info.annotations.modes || [],
        fallback: info.annotations.fallback || 'fail'
      };
    }
    return null;
  }
}
```

##### Literal Desugaring (`lib/ffi/literals.js`)

```javascript
// lib/ffi/literals.js

const { valueToTerm } = require('./index');

/**
 * Convert decimal string to bin term
 * "42" → i(o(i(o(i(e)))))
 */
function bin_from_decimal(str) {
  const n = BigInt(str);
  return valueToTerm(n, 'bin');
}

/**
 * Convert hex string to bin term
 * "0xff" → i(i(i(i(i(i(i(i(e))))))))
 */
function bin_from_hex(str) {
  const n = BigInt(str);  // BigInt handles 0x prefix
  return valueToTerm(n, 'bin');
}

/**
 * Convert binary string to bin term
 * "0b101" → i(o(i(e)))
 */
function bin_from_binary(str) {
  const n = BigInt(str);  // BigInt handles 0b prefix
  return valueToTerm(n, 'bin');
}

/**
 * Convert decimal string to nat term
 * "3" → s(s(s(z)))
 */
function nat_from_decimal(str) {
  const n = BigInt(str);
  return valueToTerm(n, 'nat');
}

/**
 * Convert bin term back to decimal string (for pretty-printing)
 */
function bin_to_decimal(term) {
  const { termToValue } = require('./index');
  return termToValue(term).toString();
}

module.exports = {
  bin_from_decimal,
  bin_from_hex,
  bin_from_binary,
  nat_from_decimal,
  bin_to_decimal
};
```

##### Parser Integration

The parser needs to recognize literals and desugar them:

```javascript
// In parser (Ohm semantics)

semantics.addOperation('toAST', {
  // ... existing rules ...

  // Numeric literals
  decimalLiteral(digits) {
    const str = digits.sourceString;
    const targetType = this.args.expectedType || 'bin';  // Context-dependent

    if (targetType === 'bin') {
      return literals.bin_from_decimal(str);
    } else if (targetType === 'nat') {
      return literals.nat_from_decimal(str);
    }
    throw new Error(`Unknown numeric literal type: ${targetType}`);
  },

  hexLiteral(_0x, digits) {
    const str = '0x' + digits.sourceString;
    return literals.bin_from_hex(str);
  },

  binaryLiteral(_0b, digits) {
    const str = '0b' + digits.sourceString;
    return literals.bin_from_binary(str);
  },

  stringLiteral(_open, chars, _close) {
    return { id: 'string', vals: [chars.sourceString] };
  }
});
```

---

#### Design Summary

| Aspect | Decision |
|--------|----------|
| Multi-mode | Each predicate declares supported modes via `@modes` |
| Failure | FFI returns `{ success: false, reason }` when no solution |
| Fallback | `@fallback axioms` for unsupported modes |
| Multi-output | Bindings object: `{ 2: term, 3: term }` (by arg index) |
| Verification | Optional `verify` function checks result |
| Value conversion | `termToValue` / `valueToTerm` handle AST ↔ JS |
| Registry | Central `FFI_REGISTRY` maps names to handlers |

#### Open Questions

1. **FFI in linear context**: Does FFI correctly consume/produce linear resources?
2. **Enumeration modes**: Should FFI support `(- - +)` that yields multiple solutions?
3. **Performance**: Cache FFI results using content-addressing?
4. **Negative numbers**: Extend to integers? Or keep natural numbers only?
5. **Floating point**: How to handle precision/rounding in rationals?
6. **Type inference**: How does parser know `42` should be `bin` vs `nat`?

---

#### 4. Future Syntax Extensions

These can be added later as needed:

```celf
% List literals
@literal list "\\[.*\\]"
[1, 2, 3]  →  cons 1 (cons 2 (cons 3 nil))

% Tuple literals
@literal tuple "\\(.*\\)"
(a, b, c)  →  pair a (pair b c)

% Record-like syntax (future)
@literal record "\\{.*\\}"
{from: alice, to: bob, amt: 100}

% Pattern macros (future)
@pattern transfer(F, T, A) =
  owns F (money A C) -o { owns T (money A C) }

% Then use as:
transfer(alice, bob, 100)
```

---

### Compilation Pipeline

```
┌─────────────────────────────────────────────────────────────────────┐
│                     EXTENDED CELF SYNTAX                            │
└─────────────────────────────────────────────────────────────────────┘

                    ┌─────────────────────────┐
                    │   linear-logic.calc     │
                    │  (Extended Celf +       │
                    │   @annotations)         │
                    └───────────┬─────────────┘
                                │
                    ┌───────────▼─────────────┐
                    │   linear-logic.rules    │
                    │  (Celf + @pretty)       │
                    └───────────┬─────────────┘
                                │
     ┌──────────────────────────┼──────────────────────────┐
     │                          │                          │
┌────▼────────────┐    ┌────────▼────────┐    ┌───────────▼─────────┐
│  lib/base.mde   │    │ lib/arith.mde   │    │ lib/accounting.mde  │
│  (Pure Celf)    │    │ (Pure Celf)     │    │ (Pure Celf)         │
└────┬────────────┘    └────────┬────────┘    └───────────┬─────────┘
     │                          │                          │
     └──────────────────────────┼──────────────────────────┘
                                │
                    ┌───────────▼─────────────┐
                    │   programs/*.mde        │
                    │   (Pure Celf)           │
                    │   e.g., evm.mde         │
                    └───────────┬─────────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        │                       │                       │
┌───────▼───────┐    ┌──────────▼──────────┐   ┌───────▼───────┐
│   ll.json     │    │   Ohm/tree-sitter   │   │   Isabelle    │
│  (compat)     │    │   (formula parse)   │   │   (verify)    │
└───────┬───────┘    └──────────┬──────────┘   └───────────────┘
        │                       │
        └───────────────────────┘
                      │
          ┌───────────▼───────────┐
          │  CALC Proof Search    │
          │  (lib/proofstate.js)  │
          └───────────────────────┘
```

**Key design choice**: Only `.calc` and `.rules` need `@annotations`. All library and program files (`.mde`) are pure Celf, compatible with optimism-mde.

---

### Type Checking the DSL

The DSL compiler performs these checks:

1. **Kind checking**: Types like `formula`, `structure` are well-formed
2. **Arity checking**: Constructors have correct number of arguments
3. **Metavariable consistency**: Same variable has same type everywhere
4. **Binder well-formedness**: Bound variables in scope
5. **Import resolution**: All imports exist and don't cycle

```javascript
// Pseudocode for type checker
function checkCalc(calc) {
  const typeEnv = new Map();

  // Register type declarations
  for (const decl of calc.types) {
    typeEnv.set(decl.name, { kind: 'type' });
  }

  // Check constructors
  for (const ctor of calc.constructors) {
    const argTypes = ctor.args.map(parseType);
    const retType = parseType(ctor.returnType);

    for (const t of [...argTypes, retType]) {
      if (!typeEnv.has(t.name)) {
        error(`Unknown type: ${t.name}`);
      }
    }

    typeEnv.set(ctor.name, {
      kind: 'constructor',
      args: argTypes,
      returns: retType
    });
  }
}

function checkRules(rules, calcEnv) {
  for (const rule of rules) {
    const metaEnv = new Map();

    // Infer metavariable types from usage
    inferMetaTypes(rule.conclusion, metaEnv, calcEnv);
    for (const premise of rule.premises) {
      inferMetaTypes(premise, metaEnv, calcEnv);
    }

    // Check all metavariables have consistent types
    checkMetaConsistency(metaEnv);
  }
}
```

---

### Open Questions

1. **Module system**: How do imports work? Namespacing?
2. **Versioning**: How to evolve calculus definitions?
3. **Incremental compilation**: Only recompile changed files?
4. **Error recovery**: Good error messages when rules don't parse?
5. **IDE support**: LSP for .calc/.rules/.lib files?

---

## Recommendations

### Phase 1: Prototype DSL Parser (1-2 weeks)

1. **Implement `.calc` parser with Ohm**
   - Type declarations, constructors with metadata
   - Validate: arities, types, metadata fields
   - Export to ll.json for backwards compatibility

2. **Implement `.rules` parser with Ohm**
   - Horizontal line rule format
   - Metavariable extraction and type inference
   - Support both Unicode (⊗, ⊸) and ASCII (*, -o)

3. **Basic `.lib` parser**
   - Celf-style backward-chaining rules
   - Import resolution

### Phase 2: Stdlib and Integration (2-4 weeks)

4. **Port optimism-mde/lib to new format**
   - `base.lib` (nat, bin, bool)
   - `arithmetic.lib` (plus, mul, gt)
   - Validate against existing tests

5. **Connect to existing prover**
   - Generate ll.json from .calc
   - Generate Ohm grammar from .calc
   - Run existing proof search on new format

6. **Add parsing conventions**
   - Numeric literals (#5 → i(o(i e)))
   - Consider list syntax, convenience patterns

### Phase 3: Enhanced Type Checking (1-2 months)

7. **Metavariable type inference in rules**
   - Greek = structure, Latin = formula convention
   - Explicit type annotations where needed
   - Error on inconsistent usage

8. **Connective metadata validation**
   - Check dual pairs exist
   - Validate adjoint relationships
   - Check polarity assignments are consistent

### Phase 4: Tooling and Export (2-3 months)

9. **tree-sitter grammar** for editor support
   - Syntax highlighting for .calc, .rules, .lib
   - LSP server for diagnostics

10. **Multiple export targets**
    - ll.json (backwards compatibility)
    - Isabelle/HOL (verification)
    - LaTeX documentation generation

### Long-term Goals

11. **Content-addressed ASTs** — Merkle-DAG integration (see content-addressed-formulas.md)
12. **Zig port** — tree-sitter + hand-written RD for performance
13. **Twelf/Celf export** — Metatheory verification
14. **Dependent types** — Full LF-style rule typing

---

## Proposed .calc Syntax (Draft)

```calc
-- Comments with --

-- Type declarations
formula : type.
structure : type.
sequent : type.

-- Formula constructors
tensor : formula -> formula -> formula.
  syntax: _ * _.
  latex: _ \otimes _.
  precedence: 50.

loli : formula -> formula -> formula.
  syntax: _ -o _.
  latex: _ \multimap _.
  precedence: 40.

bang : formula -> formula.
  syntax: ! _.
  latex: ! _.

-- Structure constructors
comma : structure -> structure -> structure.
  syntax: _, _.

-- Sequent
turnstile : structure -> structure -> sequent.
  syntax: _ |- _.

-- Rules (backward direction: conclusion <- premises)
rule Tensor_L :
  turnstile (comma ?Gamma (tensor ?A ?B)) ?C
  <- turnstile (comma (comma ?Gamma ?A) ?B) ?C.

rule Tensor_R :
  turnstile (comma ?X ?Y) (tensor ?A ?B)
  <- turnstile ?X ?A
  <- turnstile ?Y ?B.

-- Schemas use ?Name for metavariables
-- Type checker ensures ?A appears with consistent type
```

### Type Checking Rules

1. **Kind checking**: `formula : type` is well-formed
2. **Constructor typing**: `tensor : formula -> formula -> formula` is consistent
3. **Rule typing**: Metavariables have consistent types across premises/conclusion
4. **Arity checking**: All constructors applied to correct number of arguments

---

## End-to-End Example: Opaque Values in DSL, FFI, and DAG

This section traces a complete example from DSL source code through parsing, FFI execution, and DAG storage. This answers the key design questions:

1. **Do we need an `opaque/1` primitive in the logic?** — NO
2. **How is the type stored?** — In the DAG node metadata
3. **When does expansion happen?** — Only when pattern matching requires structure

---

### The Scenario

We trace the execution of this query:

```celf
% In program.mde
plus 42 8 X
```

Where `42` and `8` are decimal literals, and `X` is the variable to be solved.

---

### Step 1: DSL Definition (.calc file)

First, the calculus defines the `bin` type with literal syntax:

```celf
% In lib/types.calc
bin : type
  @literal decimal "[0-9]+"           % Regex for decimal numbers
  @literal hex     "0x[0-9a-fA-F]+"   % Regex for hex numbers
  @storage opaque                      % Store as opaque, not structural
  @opaque_type bigint.                % JS BigInt internally

e : bin.                               % Zero
i : bin -> bin.                        % LSB = 1
o : bin -> bin.                        % LSB = 0
```

**Key annotation:** `@storage opaque` tells the parser to create opaque nodes for literals of this type.

---

### Step 2: FFI Definition (.mde file)

The stdlib defines `plus` with FFI:

```celf
% In lib/arithmetic.mde
plus : bin -> bin -> bin -> type
  @ffi arithmetic.plus
  @modes [(+ + -), (+ - +), (- + +)]
  @fallback axioms.

% Axioms (used when FFI can't apply)
plus/z1 : plus e e e.
plus/s1 : plus (o M) (o N) (o R) <- plus M N R.
% ... etc
```

---

### Step 3: Parsing — Literal to Opaque Node

When the parser sees `plus 42 8 X`:

```
Input: "plus 42 8 X"

Tokenization:
  - "plus" → identifier
  - "42"   → matches @literal decimal → DECIMAL_LITERAL
  - "8"    → matches @literal decimal → DECIMAL_LITERAL
  - "X"    → identifier (variable)

AST before opaque conversion:
  Application(
    pred: "plus",
    args: [DECIMAL_LITERAL("42"), DECIMAL_LITERAL("8"), Variable("X")]
  )
```

The parser then converts literals to opaque nodes:

```javascript
// In parser (pseudo-code)
function processLiteral(token, targetType) {
  if (targetType.storage === 'opaque') {
    // Create opaque node instead of structural
    return new OpaqueNode({
      dataType: 'bin',
      value: BigInt(token.value),  // 42n
      // DO NOT create i(o(i(o(i(o(e))))))
    });
  } else {
    // Create structural representation
    return expandToStructural(token.value, targetType);
  }
}
```

**Result after parsing:**

```javascript
// Internal representation
{
  type: 'application',
  pred: 'plus',
  args: [
    OpaqueNode { dataType: 'bin', value: 42n },
    OpaqueNode { dataType: 'bin', value: 8n },
    Variable { name: 'X' }
  ]
}
```

---

### Step 4: DAG Interning

Each node is interned into the Merkle-DAG:

```javascript
// Interning opaque nodes
const hash42 = interner.internOpaque('bin', 42n);
const hash8  = interner.internOpaque('bin', 8n);
const hashX  = interner.internVariable('X');

// Interning the application
const hashPlus = interner.internApplication('plus', [hash42, hash8, hashX]);
```

**DAG state after interning:**

```
┌─────────────────────────────────────────────────────────────┐
│                     Merkle-DAG Store                        │
├─────────────────────────────────────────────────────────────┤
│ hash: 0xa1b2...   (opaque)                                  │
│   dataType: 'bin'                                           │
│   value: 42n                                                │
│   nodeType: 'opaque'                                        │
├─────────────────────────────────────────────────────────────┤
│ hash: 0xc3d4...   (opaque)                                  │
│   dataType: 'bin'                                           │
│   value: 8n                                                 │
│   nodeType: 'opaque'                                        │
├─────────────────────────────────────────────────────────────┤
│ hash: 0xe5f6...   (variable)                                │
│   name: 'X'                                                 │
│   nodeType: 'variable'                                      │
├─────────────────────────────────────────────────────────────┤
│ hash: 0x7890...   (application)                             │
│   pred: 'plus'                                              │
│   args: [0xa1b2..., 0xc3d4..., 0xe5f6...]                   │
│   nodeType: 'structural'                                    │
└─────────────────────────────────────────────────────────────┘

Total nodes: 4
Compare to structural: 42 = i(o(i(o(i(o(e)))))) = 7 nodes
                        8 = o(o(o(i(e)))) = 5 nodes
                        Would need: 7 + 5 + 1 + 1 = 14 nodes
Savings: 14 - 4 = 10 nodes (71% reduction)
```

---

### Step 5: FFI Execution

Proof search reaches the `plus 42 8 X` goal:

```javascript
// In proof search (lib/proofstate.js)
function tryGoal(goal) {
  const pred = goal.pred;  // 'plus'

  // Check if predicate has FFI
  if (pred.ffi) {
    // Determine mode from groundness
    const mode = determineMode(goal.args);
    // args[0] = opaque(42) → ground (+)
    // args[1] = opaque(8)  → ground (+)
    // args[2] = variable X → not ground (-)
    // mode = '+ + -'

    // Find handler for this mode
    const handler = pred.ffi.handlers[mode];
    if (handler && handler.canApply(...goal.args)) {
      // EXECUTE FFI
      const result = handler.compute(...goal.args);
      // ...
    }
  }
}
```

**Inside the FFI handler:**

```javascript
// lib/ffi/arithmetic.js
const plus = {
  handlers: {
    '+ + -': {
      canApply: (a, b, c) => isOpaque(a) && isOpaque(b),

      compute: (a, b, c) => {
        // Extract raw values from opaque nodes
        // NO EXPANSION NEEDED - we read .value directly!
        const aVal = a.value;  // 42n (BigInt)
        const bVal = b.value;  // 8n  (BigInt)

        // Compute
        const result = aVal + bVal;  // 50n

        // Create new opaque node for result
        // NOT i(o(o(o(i(o(i(e))))))) — stays opaque!
        const resultNode = new OpaqueNode({
          dataType: 'bin',
          value: result  // 50n
        });

        return {
          success: true,
          bindings: { 2: resultNode }  // Bind arg[2] (X) to result
        };
      }
    }
  }
};
```

**FFI trace:**

```
FFI CALL: plus
  Input:  [OpaqueNode(bin, 42n), OpaqueNode(bin, 8n), Variable(X)]
  Mode:   + + -
  Action: 42n + 8n = 50n
  Output: { success: true, bindings: { X: OpaqueNode(bin, 50n) } }

No structural expansion occurred!
```

---

### Step 6: DAG After FFI

The result is interned:

```
┌─────────────────────────────────────────────────────────────┐
│                     Merkle-DAG Store                        │
├─────────────────────────────────────────────────────────────┤
│ hash: 0xa1b2...   (opaque) — 42                             │
│ hash: 0xc3d4...   (opaque) — 8                              │
│ hash: 0xe5f6...   (variable) — X                            │
│ hash: 0x7890...   (application) — plus(42, 8, X)            │
│ hash: 0xabcd...   (opaque) — 50  ← NEW                      │
└─────────────────────────────────────────────────────────────┘

Total nodes: 5
```

---

### Step 7: When Expansion IS Needed

Suppose later we have a rule that pattern-matches on the structure:

```celf
% Rule that needs to inspect bit structure
is_odd : plus (i X) e (i X).   % A number is odd if LSB is 1
```

When matching `50` against `(i X)`:

```javascript
// Smart pattern match (no full expansion)
function matchPattern(opaqueNode, pattern) {
  // Pattern is i(X) — check if value is odd
  if (pattern.constructor === 'bin_i') {
    if (opaqueNode.value % 2n === 1n) {
      // Value IS odd, but 50 is even (50 % 2 = 0)
      return { success: false };
    }
    // If it were odd (e.g., 51):
    // return {
    //   success: true,
    //   bindings: { X: OpaqueNode('bin', (51n - 1n) / 2n) }  // 25
    // };
  }

  if (pattern.constructor === 'bin_o') {
    if (opaqueNode.value > 0n && opaqueNode.value % 2n === 0n) {
      // 50 IS even and > 0
      const rest = opaqueNode.value / 2n;  // 25
      return {
        success: true,
        bindings: { X: new OpaqueNode('bin', rest) }  // OpaqueNode(25)
      };
    }
  }

  // ... etc
}
```

**Key insight:** Even pattern matching doesn't require full expansion! We use arithmetic on the opaque value to determine the match.

---

### Step 8: Full Expansion (When Truly Needed)

Full expansion only happens for:
1. Displaying to user in structural form
2. Axiom-based proof search (no FFI)
3. Export to external system expecting structure

```javascript
// Full expansion (only when necessary)
function expandOpaque(opaqueNode, interner) {
  const value = opaqueNode.value;  // 50n

  if (value === 0n) {
    return interner.internStructural('bin_e', []);
  }

  const bit = value % 2n;
  const rest = value / 2n;
  const restHash = expandOpaque(new OpaqueNode('bin', rest), interner);

  if (bit === 1n) {
    return interner.internStructural('bin_i', [restHash]);
  } else {
    return interner.internStructural('bin_o', [restHash]);
  }
}

// 50 = 0b110010 → o(i(o(o(i(i(e))))))
//
// Expansion trace:
//   50 → o(expand(25))
//   25 → i(expand(12))
//   12 → o(expand(6))
//    6 → o(expand(3))
//    3 → i(expand(1))
//    1 → i(expand(0))
//    0 → e
//
// Result: o(i(o(o(i(i(e))))))
```

**DAG after expansion:**

```
┌─────────────────────────────────────────────────────────────┐
│                     Merkle-DAG Store                        │
├─────────────────────────────────────────────────────────────┤
│ (existing nodes...)                                         │
│ hash: 0xabcd...   (opaque) — 50                             │
│                                                             │
│ (structural expansion of 50 — created only if needed):      │
│ hash: 0x1111...   (structural) — e                          │
│ hash: 0x2222...   (structural) — i(0x1111...)    = i(e)     │
│ hash: 0x3333...   (structural) — i(0x2222...)    = i(i(e))  │
│ hash: 0x4444...   (structural) — o(0x3333...)    = o(i(i(e))│
│ hash: 0x5555...   (structural) — o(0x4444...)              │
│ hash: 0x6666...   (structural) — i(0x5555...)              │
│ hash: 0x7777...   (structural) — o(0x6666...)    = 50      │
│                                                             │
│ expansion_cache[0xabcd...] = 0x7777...                      │
└─────────────────────────────────────────────────────────────┘
```

---

### Summary: No `opaque/1` Wrapper Needed

The design does **NOT** require an explicit `opaque/1` wrapper in the logic because:

| Aspect | Design Decision | Rationale |
|--------|-----------------|-----------|
| **Logical identity** | `42 = i(o(i(o(i(o(e))))))` | Same logical meaning |
| **DAG identity** | Same canonical hash | Opaque hash = structural hash (see below) |
| **Storage** | Implementation detail | Like Python int vs BigInt |
| **Pattern matching** | Smart match without expansion | Arithmetic on opaque value |
| **FFI** | Operates on opaque directly | Never needs expansion |

---

### Canonical Hashing: Opaque = Structural

For DAG consistency, opaque and structural representations must hash identically:

```javascript
// Hash is computed from the NUMERIC VALUE, not the representation
function binCanonicalHash(value) {
  // Same hash whether stored as opaque or structural
  const buffer = new ArrayBuffer(36);
  const view = new DataView(buffer);
  view.setUint32(0, TYPE_BIN);  // Type tag
  // Write value as big-endian bytes
  let v = value;
  for (let i = 31; i >= 0; i--) {
    view.setUint8(4 + i, Number(v & 0xffn));
    v >>= 8n;
  }
  return rapidhash(new Uint8Array(buffer));
}

// Both produce SAME hash:
// opaque(50).hash === structural_of_50.hash === binCanonicalHash(50n)
```

This ensures:
- Lookup works regardless of representation
- No duplicate entries for same value
- Proof sharing across representations

---

### Node Type Metadata

The DAG node metadata distinguishes representations:

```javascript
// Node in DAG store
const dagNode = {
  hash: 0xabcd...,           // Canonical content hash

  // Metadata (not part of hash)
  nodeType: 'opaque',        // or 'structural' or 'variable'
  dataType: 'bin',           // Celf type name
  value: 50n,                // Raw value (only for opaque)

  // Structural nodes have:
  // constructor: 'bin_o',
  // children: [childHash1, ...]
};
```

---

### Complete Data Flow Diagram

```
                           DSL SOURCE
                               │
                               ▼
                    ┌──────────────────┐
                    │     PARSER       │
                    │  - Regex match   │
                    │  - @literal dec  │
                    │  - @storage opa  │
                    └────────┬─────────┘
                             │
              ┌──────────────┴──────────────┐
              │                             │
              ▼                             ▼
     ┌────────────────┐           ┌────────────────┐
     │  OpaqueNode    │           │  Structural    │
     │  dataType:bin  │           │  (if no @opa)  │
     │  value: 42n    │           │  i(o(i(...)))  │
     └───────┬────────┘           └───────┬────────┘
             │                            │
             └────────────┬───────────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │    MERKLE-DAG         │
              │    INTERNER           │
              │  - Canonical hash     │
              │  - Store metadata     │
              │  - Deduplication      │
              └───────────┬───────────┘
                          │
                          ▼
              ┌───────────────────────┐
              │    PROOF SEARCH       │
              │  - Check FFI modes    │
              │  - Apply FFI if can   │
              │  - Fallback to axioms │
              └───────────┬───────────┘
                          │
            ┌─────────────┴─────────────┐
            │                           │
            ▼                           ▼
   ┌─────────────────┐        ┌─────────────────┐
   │    FFI PATH     │        │   AXIOM PATH    │
   │  - Read .value  │        │  - Expand to    │
   │  - JS BigInt    │        │    structural   │
   │  - Return opaq  │        │  - Backchain    │
   │  NO EXPANSION!  │        │  - Pattern match│
   └────────┬────────┘        └────────┬────────┘
            │                          │
            └──────────┬───────────────┘
                       │
                       ▼
              ┌────────────────────┐
              │    RESULT          │
              │  OpaqueNode(50n)   │
              │  or structural     │
              │  Same hash either  │
              │  way!              │
              └────────────────────┘
```

---

### Performance Comparison

For `plus 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff 1 X`:

| Aspect | Without Opaque | With Opaque | Speedup |
|--------|----------------|-------------|---------|
| Nodes created | 256 + 1 + 256 = 513 | 1 + 1 + 1 = 3 | **171×** |
| Hashes computed | 513 | 3 | **171×** |
| FFI value extraction | O(256) traverse | O(1) read .value | **256×** |
| Memory | ~12KB | ~100 bytes | **120×** |
| Pattern match `i(X)` | O(1) after intern | O(1) smart match | **1×** |

---

### Implementation Checklist

- [ ] Add `@storage opaque` annotation to parser
- [ ] Implement `OpaqueNode` class with smart pattern matching
- [ ] Implement canonical hashing for `bin` type
- [ ] Modify FFI to read `.value` directly from opaque nodes
- [ ] Add expansion cache for lazy structural conversion
- [ ] Ensure hash equality between opaque and structural
- [ ] Add tests: opaque creation, FFI, pattern match, expansion

---

## References

### Logical Frameworks

- Harper, Honsell, Plotkin, "[A Framework for Defining Logics](https://www.cs.cmu.edu/~rwh/papers/lfp/jacm.pdf)" (LF)
- Watkins et al., "[A Concurrent Logical Framework](https://www.cs.cmu.edu/~fp/papers/tr02-cl1.pdf)" (CLF)
- [Twelf Wiki](https://twelf.org/wiki/)
- [Celf GitHub](https://clf.github.io/celf/)
- [Celf Syntax Wiki](https://github.com/clf/celf/wiki/Syntax)

### Celf Syntax Elements

From the Celf documentation:
- `A -> B` — Intuitionistic function (persistent)
- `A -o B` — Linear implication (resource-consuming)
- `A * B` — Simultaneous conjunction (tensor ⊗)
- `{A}` — Monadic suspension (forward-chaining)
- `!N` — Use only persistent variables
- `@N` — Use only affine variables
- `<-` — Backward-chaining premise

### Parser Frameworks

- [Ohm.js](https://ohmjs.org/) — PEG parser with visualization
- [Chevrotain](https://chevrotain.io/) — Fast JS parser toolkit
- [tree-sitter](https://tree-sitter.github.io/) — Incremental parsing with Zig bindings
- [Peggy](https://github.com/peggyjs/peggy) — Modern PEG.js fork

### Lean4 Metaprogramming

- [Syntax Chapter](https://leanprover-community.github.io/lean4-metaprogramming-book/main/05_syntax.html)
- [Macros Chapter](https://leanprover-community.github.io/lean4-metaprogramming-book/main/06_macros.html)

Lean 4 notation declarations:
- `infixl:60 " ⊕ " => ...` — Left-associative with precedence 60
- `notation:10 l:10 " X " r:11 => ...` — Parameter precedence constraints
- `syntax:50 term " AND " term : term` — General syntax with precedence

### Calculus Toolbox

- [calculus-toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2)
- [Documentation: Calculi](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculi.html)

### Local Resources

- `~/src/optimism-mde/` — EVM modeled in Celf syntax
  - `lib/bin.mde` — Binary arithmetic stdlib
  - `lib/evm.mde` — Full EVM instruction semantics
  - `lib/helper.mde` — VM boot helpers
- `ll.json` — Current CALC specification
- `lib/parser.js` — Current Jison grammar generator

### Related Research Documents

- `content-addressed-formulas.md` — Merkle-DAG hash consing for formulas
- `benchmarking.md` — Performance analysis and complexity estimates
- `DSL-approaches.md` — Comparison of DSL alternatives

---

*Last updated: 2026-01-31*
