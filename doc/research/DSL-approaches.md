# DSL Approaches for Linear Logic Calculus Specification

Research document comparing different approaches for specifying our linear logic calculus.

See also: [[display-calculus]] | [[QTT]] | [[RESEARCH]]

---

## Table of Contents

1. [Current Approach: ll.json](#current-approach-lljson)
2. [Calculus-Toolbox-2 DSL](#calculus-toolbox-2-dsl)
3. [Isabelle/HOL](#isabellehol)
4. [Lean 4](#lean-4)
5. [Twelf/LF](#twelflf)
6. [Agda](#agda)
7. [YAML/TOML-based DSL](#yamltoml-based-dsl)
8. [Granule-style](#granule-style)
9. [Comparison Matrix](#comparison-matrix)
10. [Recommendations](#recommendations)
11. [Sources](#sources)

---

## Current Approach: ll.json

### Structure Overview

Our current specification uses a JSON schema with three main sections:

```
ll.json
├── calc_name: "LLog"
├── calc_structure: {type_definitions}
├── calc_structure_rules_meta: {polarities, contexts}
└── rules: {inference_rules}
```

### Type Definitions (calc_structure)

Types are nested objects with variants containing:
- `type`: argument types (string, array, or reference to another type)
- `ascii`: parser sugar for text input
- `latex`: LaTeX rendering
- `isabelle`: Isabelle export format
- `precedence`: binding strengths
- `shallow`: internal vs user-facing

**Example - Formula connectives:**
```json
"Formula_Bin_Op" : {
  "Formula_Tensor" : {
    "isabelle" : "*\\<^sub>F",
    "ascii" : "*",
    "latex" : "\\otimes"
  },
  "Formula_Loli" : {
    "isabelle" : "-o\\<^sub>F",
    "ascii" : "-o",
    "latex" : "\\multimap"
  }
}
```

### Inference Rules

Rules are arrays where first element is conclusion, rest are premises:
```json
"Tensor_R" : [
  "?X, ?Y |- -- : [ F?A * F?B ]",
  "?X |- -- : [ F?A ]",
  "?Y |- -- : [ F?B ]"
]
```

### Strengths

| Strength | Details |
|----------|---------|
| Runtime loading | No recompilation needed |
| Multi-format output | Same source → ASCII, LaTeX, Isabelle |
| Parser generation | Generates Jison grammar from spec |
| JavaScript-native | Direct use in Node.js/browser |

### Weaknesses

| Weakness | Details |
|----------|---------|
| No type checking | JSON can't enforce valid signatures |
| Verbose | Lots of repetition for simple connectives |
| No separation | Types, rendering, semantics all mixed |
| Hard to read rules | String-encoded sequents, not structured |
| Limited abstraction | No parameterization, macros, etc. |

---

## Calculus-Toolbox-2 DSL

The [calculus-toolbox-2](https://github.com/goodlyrottenapple/calculus-toolbox-2) has a clean DSL with two-file separation.

### Type Definitions (.calc file)

```
-- Types
default type atprop
type agent                    -- For multimodal extensions
type quantity                 -- For quantitative types

-- Atomic propositions
at : atprop -> formula ("_", NonAssoc, 100, "#1")

-- Formula connectives
tensor : formula -> formula -> formula
    ("_*_", LeftAssoc, 60, "#1 \otimes #2")

loli : formula -> formula -> formula
    ("_-o_", RightAssoc, 50, "#1 \multimap #2")

with : formula -> formula -> formula
    ("_&_", LeftAssoc, 60, "#1 \\& #2")

bang : formula -> formula
    ("!_", NonAssoc, 70, "!#1")

lax : formula -> formula
    ("{_}", NonAssoc, 70, "\\{#1\\}")

-- Structures
comma : structure -> structure -> structure
    ("_,_", LeftAssoc, 20, "#1 , #2")

turnstile : structure -> structure -> sequent
    ("_|-_", NonAssoc, 10, "#1 \\vdash #2")

-- Terms (for term-annotated sequents)
term_any : term ("--", NonAssoc, 100, "\\cdot")
term_formula : term -> formula -> structure
    ("_:_", NonAssoc, 80, "#1 : #2")
```

### Rule Definitions (.rules file)

```
------------ Id
at_A |- at_A

X, A * B |- C
------------- Tensor_L
X, (A, B) |- C

X |- A    Y |- B
---------------- Tensor_R
X, Y |- A * B

X, A |- B
--------- Loli_R
X |- A -o B

X |- A    Y, B |- C
------------------- Loli_L
X, Y, A -o B |- C

X, A |- C
--------- With_L1
X, A & B |- C

X |- A    X |- B
---------------- With_R
X |- A & B

X |- A
---------- Monad_R
X |- {A}
```

### Our ll.json in Calculus-Toolbox-2 Style

**ll.calc:**
```
-- Linear Logic with Terms

default type atprop
type term

-- Atoms
atom : string -> atprop ("_", NonAssoc, 100, "#1_{F}")
atom_var : string -> atprop ("A?_", NonAssoc, 100, "?#1")

-- Terms
term_any : term ("--", NonAssoc, 100, "\\cdot")
term_var : string -> term ("T?_", NonAssoc, 100, "?#1")
term_concat : term -> term -> term ("_._", LeftAssoc, 90, "#1 \\cdot #2")

-- Formulas
at : atprop -> formula ("_", NonAssoc, 100, "#1")
fvar : string -> formula ("F?_", NonAssoc, 100, "?#1")
tensor : formula -> formula -> formula ("_*_", LeftAssoc, 60, "#1 \\otimes #2")
loli : formula -> formula -> formula ("_-o_", RightAssoc, 50, "#1 \\multimap #2")
with : formula -> formula -> formula ("_&_", LeftAssoc, 60, "#1 \\& #2")
bang : formula -> formula ("!_", NonAssoc, 70, "!#1")
monad : formula -> formula ("{_}", NonAssoc, 70, "\\{#1\\}")
lax : formula -> formula ("_lax", NonAssoc, 70, "#1^{\\circ}")
forall : string -> atprop -> formula -> formula
    ("forall_:_._", NonAssoc, 40, "\\forall #1:#2.#3")

-- Focused formulas
focus : formula -> fformula ("[_]", NonAssoc, 90, "[#1]")

-- Structures
struct_formula : formula -> structure ("_", NonAssoc, 100, "#1")
struct_term_formula : term -> formula -> structure ("_:_", NonAssoc, 80, "#1:#2")
struct_term_fformula : term -> fformula -> structure ("_:_", NonAssoc, 80, "#1:#2")
struct_var : string -> structure ("?_", NonAssoc, 100, "?#1")
neutral : structure ("I", NonAssoc, 100, "\\cdot")
comma : structure -> structure -> structure ("_,_", LeftAssoc, 20, "#1,#2")

-- Sequent
seq : structure -> structure -> sequent ("_|-_", NonAssoc, 10, "#1 \\vdash #2")
```

**ll.rules:**
```
-- Identity
------------ Id
-- : at_A |- -- : at_A

-- Cut
X |- -- : A    Z, -- : A |- Y
------------------------------ Cut
X, Z |- Y

-- Tensor
X, (-- : A, -- : B) |- -- : C
------------------------------ Tensor_L
X, -- : A * B |- -- : C

X |- -- : [A]    Y |- -- : [B]
------------------------------ Tensor_R
X, Y |- -- : [A * B]

-- Lollipop
X, -- : A |- -- : B
-------------------- Loli_R
X |- -- : A -o B

X |- -- : [A]    Y, -- : [B] |- -- : C
--------------------------------------- Loli_L
X, Y, -- : [A -o B] |- -- : C

-- With
X, -- : [A] |- -- : C
---------------------- With_L1
X, -- : [A & B] |- -- : C

X, -- : [B] |- -- : C
---------------------- With_L2
X, -- : [A & B] |- -- : C

X |- -- : A    X |- -- : B
--------------------------- With_R
X |- -- : A & B

-- Monad
X |- -- : A lax
---------------- Monad_R
X |- -- : {A}

-- Bang
I |- -- : [A]
-------------- Bang_R
I |- -- : [!A]

X |- -- : B
--------------- Bang_L
X, -- : !A |- -- : B
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★★ | Natural deduction style, very clear |
| Type safety | ★★★☆☆ | Haskell parser validates structure |
| Extensibility | ★★★★☆ | Multi-type support built-in |
| Proof search | ★★☆☆☆ | No built-in, would need integration |
| Isabelle export | ★★★★★ | First-class support |
| Quantitative types | ★★☆☆☆ | Would need DSL extension |

---

## Isabelle/HOL

Isabelle uses inductive definitions for proof systems.

### Formula and Structure Types

```isabelle
datatype formula =
    Atprop string
  | Tensor formula formula    (infixl "⊗" 65)
  | Loli formula formula      (infixr "⊸" 60)
  | With formula formula      (infixl "&" 65)
  | Bang formula              ("!" 70)
  | Monad formula             ("{_}" 70)

datatype structure =
    SFormula formula          ("⟨_⟩")
  | SNeutral                  ("I")
  | SComma structure structure (infixl "," 50)
  | SVar string               ("?_")

datatype sequent =
    Seq structure structure   (infix "⊢" 40)
```

### Inductive Derivability

```isabelle
inductive deriv :: "sequent ⇒ bool" ("⊢ _" 300)
where
  Id: "⊢ ⟨Atprop p⟩ ⊢ ⟨Atprop p⟩"

| Tensor_L: "⊢ (X, (⟨A⟩, ⟨B⟩)) ⊢ C ⟹ ⊢ (X, ⟨A ⊗ B⟩) ⊢ C"

| Tensor_R: "⟦ ⊢ X ⊢ ⟨A⟩; ⊢ Y ⊢ ⟨B⟩ ⟧ ⟹ ⊢ (X, Y) ⊢ ⟨A ⊗ B⟩"

| Loli_R: "⊢ (X, ⟨A⟩) ⊢ ⟨B⟩ ⟹ ⊢ X ⊢ ⟨A ⊸ B⟩"

| Loli_L: "⟦ ⊢ X ⊢ ⟨A⟩; ⊢ (Y, ⟨B⟩) ⊢ C ⟧ ⟹ ⊢ (X, Y, ⟨A ⊸ B⟩) ⊢ C"

| With_L1: "⊢ (X, ⟨A⟩) ⊢ C ⟹ ⊢ (X, ⟨A & B⟩) ⊢ C"
| With_L2: "⊢ (X, ⟨B⟩) ⊢ C ⟹ ⊢ (X, ⟨A & B⟩) ⊢ C"

| With_R: "⟦ ⊢ X ⊢ ⟨A⟩; ⊢ X ⊢ ⟨B⟩ ⟧ ⟹ ⊢ X ⊢ ⟨A & B⟩"

| Monad_R: "⊢ X ⊢ ⟨A⟩ ⟹ ⊢ X ⊢ ⟨Monad A⟩"

| Cut: "⟦ ⊢ X ⊢ ⟨A⟩; ⊢ (Z, ⟨A⟩) ⊢ Y ⟧ ⟹ ⊢ (X, Z) ⊢ Y"
```

### Proof Example

```isabelle
lemma example: "⊢ ⟨P ⊗ Q⟩ ⊢ ⟨Q ⊗ P⟩"
  apply (rule Tensor_L)
  apply (rule Tensor_R)
   apply (rule Id)
  apply (rule Id)
  done
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★☆ | Unicode helps, verbose but precise |
| Type safety | ★★★★★ | Full dependent types, type inference |
| Extensibility | ★★★★★ | Locales, type classes, very flexible |
| Proof search | ★★★★☆ | Sledgehammer, auto, etc. |
| Isabelle export | ★★★★★ | Native |
| Quantitative types | ★★★★☆ | Can add semiring parameter |

---

## Lean 4

Lean 4 uses inductive types with propositions-as-types.

### Type Definitions

```lean
-- Atomic propositions
abbrev AtProp := String

-- Formulas
inductive Formula where
  | atom : AtProp → Formula
  | tensor : Formula → Formula → Formula
  | loli : Formula → Formula → Formula
  | with_ : Formula → Formula → Formula
  | bang : Formula → Formula
  | monad : Formula → Formula

notation:65 A " ⊗ " B => Formula.tensor A B
notation:60 A " ⊸ " B:60 => Formula.loli A B
notation:65 A " & " B => Formula.with_ A B
notation:70 "!" A => Formula.bang A
notation:70 "{" A "}" => Formula.monad A

-- Structures (multisets for focused proof search)
inductive Structure where
  | formula : Formula → Structure
  | neutral : Structure
  | comma : Structure → Structure → Structure
  | var : String → Structure

notation:50 X " , " Y => Structure.comma X Y

-- Sequents
inductive Sequent where
  | mk : Structure → Structure → Sequent

notation:40 X " ⊢ " Y => Sequent.mk X Y
```

### Inductive Derivability

```lean
inductive Deriv : Sequent → Prop where
  | id : ∀ p, Deriv (Structure.formula (Formula.atom p) ⊢
                     Structure.formula (Formula.atom p))

  | tensor_l : ∀ X A B C,
      Deriv ((X, (Structure.formula A, Structure.formula B)) ⊢ C) →
      Deriv ((X, Structure.formula (A ⊗ B)) ⊢ C)

  | tensor_r : ∀ X Y A B,
      Deriv (X ⊢ Structure.formula A) →
      Deriv (Y ⊢ Structure.formula B) →
      Deriv ((X, Y) ⊢ Structure.formula (A ⊗ B))

  | loli_r : ∀ X A B,
      Deriv ((X, Structure.formula A) ⊢ Structure.formula B) →
      Deriv (X ⊢ Structure.formula (A ⊸ B))

  | loli_l : ∀ X Y A B C,
      Deriv (X ⊢ Structure.formula A) →
      Deriv ((Y, Structure.formula B) ⊢ C) →
      Deriv ((X, Y, Structure.formula (A ⊸ B)) ⊢ C)

  | with_l1 : ∀ X A B C,
      Deriv ((X, Structure.formula A) ⊢ C) →
      Deriv ((X, Structure.formula (A & B)) ⊢ C)

  | with_l2 : ∀ X A B C,
      Deriv ((X, Structure.formula B) ⊢ C) →
      Deriv ((X, Structure.formula (A & B)) ⊢ C)

  | with_r : ∀ X A B,
      Deriv (X ⊢ Structure.formula A) →
      Deriv (X ⊢ Structure.formula B) →
      Deriv (X ⊢ Structure.formula (A & B))

  | monad_r : ∀ X A,
      Deriv (X ⊢ Structure.formula A) →
      Deriv (X ⊢ Structure.formula {A})
```

### Proof Example

```lean
theorem example : Deriv (Structure.formula (Formula.atom "P" ⊗ Formula.atom "Q") ⊢
                         Structure.formula (Formula.atom "Q" ⊗ Formula.atom "P")) := by
  apply Deriv.tensor_l
  apply Deriv.tensor_r
  · exact Deriv.id "Q"
  · exact Deriv.id "P"
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★☆ | Clean notation, good Unicode |
| Type safety | ★★★★★ | Full dependent types |
| Extensibility | ★★★★★ | Type classes, macros, very modern |
| Proof search | ★★★★☆ | Tactics, Aesop, simp |
| Isabelle export | ★★☆☆☆ | Would need translation layer |
| Quantitative types | ★★★★★ | Native QTT support possible |

---

## Twelf/LF

The Logical Framework approach: represent judgments as types.

### Type Declarations

```twelf
% Types
formula : type.
structure : type.
sequent : type.

% Formula constructors
atom : string -> formula.
tensor : formula -> formula -> formula.
loli : formula -> formula -> formula.
with : formula -> formula -> formula.
bang : formula -> formula.
monad : formula -> formula.

% Structure constructors
s_formula : formula -> structure.
s_neutral : structure.
s_comma : structure -> structure -> structure.

% Sequent constructor
seq : structure -> structure -> sequent.
```

### Judgment (Derivability)

```twelf
deriv : sequent -> type.

% Identity
d_id : deriv (seq (s_formula (atom P)) (s_formula (atom P))).

% Tensor Left
d_tensor_l : deriv (seq (s_comma X (s_formula (tensor A B))) C)
          <- deriv (seq (s_comma X (s_comma (s_formula A) (s_formula B))) C).

% Tensor Right
d_tensor_r : deriv (seq (s_comma X Y) (s_formula (tensor A B)))
          <- deriv (seq X (s_formula A))
          <- deriv (seq Y (s_formula B)).

% Lollipop Right
d_loli_r : deriv (seq X (s_formula (loli A B)))
        <- deriv (seq (s_comma X (s_formula A)) (s_formula B)).

% Lollipop Left
d_loli_l : deriv (seq (s_comma (s_comma X Y) (s_formula (loli A B))) C)
        <- deriv (seq X (s_formula A))
        <- deriv (seq (s_comma Y (s_formula B)) C).

% With Left (1)
d_with_l1 : deriv (seq (s_comma X (s_formula (with A B))) C)
         <- deriv (seq (s_comma X (s_formula A)) C).

% With Left (2)
d_with_l2 : deriv (seq (s_comma X (s_formula (with A B))) C)
         <- deriv (seq (s_comma X (s_formula B)) C).

% With Right
d_with_r : deriv (seq X (s_formula (with A B)))
        <- deriv (seq X (s_formula A))
        <- deriv (seq X (s_formula B)).

% Monad Right
d_monad_r : deriv (seq X (s_formula (monad A)))
         <- deriv (seq X (s_formula A)).
```

### Key Feature: Higher-Order Abstract Syntax

Twelf handles variable binding via LF's lambda:
```twelf
% Hypothetical judgment: if we assume A, then B is derivable
hyp : deriv (seq (s_formula A) (s_formula B))
   -> deriv (seq X (s_formula (loli A B)))
   <- ({x : deriv (seq (s_formula A) (s_formula A))}
       deriv (seq (s_comma X (s_formula A)) (s_formula B))).
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★☆☆ | Learning curve, but elegant |
| Type safety | ★★★★★ | Intrinsically well-formed proofs |
| Extensibility | ★★★★☆ | Good for meta-theoretic reasoning |
| Proof search | ★★★★★ | Built-in logic programming |
| Isabelle export | ★★☆☆☆ | Would need manual translation |
| Quantitative types | ★★☆☆☆ | Not well-suited for semiring tracking |

---

## Agda

Dependently-typed programming with explicit proof terms.

### Type Definitions

```agda
module LinearLogic where

open import Data.String using (String)
open import Data.Product using (_×_; _,_)

-- Atomic propositions
AtProp = String

-- Formulas
data Formula : Set where
  atom : AtProp → Formula
  _⊗_ : Formula → Formula → Formula
  _⊸_ : Formula → Formula → Formula
  _&_ : Formula → Formula → Formula
  !_ : Formula → Formula
  {_} : Formula → Formula

infixl 7 _⊗_
infixr 6 _⊸_
infixl 7 _&_

-- Contexts (linear = lists with usage tracking)
data Context : Set where
  ∅ : Context
  _,_ : Context → Formula → Context

-- Sequent judgment
data _⊢_ : Context → Formula → Set where

  -- Identity
  id : ∀ {A} → (∅ , A) ⊢ A

  -- Tensor
  ⊗L : ∀ {Γ A B C} →
       (Γ , A , B) ⊢ C →
       (Γ , (A ⊗ B)) ⊢ C

  ⊗R : ∀ {Γ Δ A B} →
       Γ ⊢ A → Δ ⊢ B →
       (Γ ++ Δ) ⊢ (A ⊗ B)  -- context split!

  -- Lollipop
  ⊸R : ∀ {Γ A B} →
       (Γ , A) ⊢ B →
       Γ ⊢ (A ⊸ B)

  ⊸L : ∀ {Γ Δ A B C} →
       Γ ⊢ A → (Δ , B) ⊢ C →
       (Γ ++ Δ , (A ⊸ B)) ⊢ C

  -- With
  &L₁ : ∀ {Γ A B C} →
        (Γ , A) ⊢ C →
        (Γ , (A & B)) ⊢ C

  &L₂ : ∀ {Γ A B C} →
        (Γ , B) ⊢ C →
        (Γ , (A & B)) ⊢ C

  &R : ∀ {Γ A B} →
       Γ ⊢ A → Γ ⊢ B →
       Γ ⊢ (A & B)  -- context shared!

  -- Monad
  {}R : ∀ {Γ A} →
        Γ ⊢ A →
        Γ ⊢ { A }
```

### The "Typing with Leftovers" Approach

For proper linear logic, Agda formalizations often use bidirectional typing with explicit resource tracking:

```agda
-- Leftovers-based approach (Allais, TYPES 2017)
data _⊢_⊣_ : Context → Formula → Context → Set where
  -- A term consumes input context, produces output "leftovers"
  id : ∀ {A} → (A ∷ Γ) ⊢ A ⊣ Γ

  ⊗I : ∀ {Γ Δ Θ A B} →
       Γ ⊢ A ⊣ Δ →
       Δ ⊢ B ⊣ Θ →
       Γ ⊢ (A ⊗ B) ⊣ Θ
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★☆ | Very clean Unicode syntax |
| Type safety | ★★★★★ | Full dependent types, totality checking |
| Extensibility | ★★★★★ | Modules, records, very expressive |
| Proof search | ★★☆☆☆ | Manual proof construction (no Sledgehammer) |
| Isabelle export | ★★☆☆☆ | Would need translation |
| Quantitative types | ★★★★★ | Excellent - see Allais's work |

---

## YAML/TOML-based DSL

A custom configuration-language approach, similar to ll.json but more readable.

### YAML Version

```yaml
calculus:
  name: LLog
  version: 1.0

types:
  atprop:
    description: Atomic propositions
    syntax:
      ascii: "_"
      latex: "#1_{F}"

  formula:
    description: Linear logic formulas
    constructors:
      atom:
        args: [atprop]
        syntax: { ascii: "_", latex: "#1" }

      tensor:
        args: [formula, formula]
        syntax: { ascii: "_ * _", latex: "#1 \\otimes #2" }
        precedence: 60
        associativity: left
        polarity: positive

      loli:
        args: [formula, formula]
        syntax: { ascii: "_ -o _", latex: "#1 \\multimap #2" }
        precedence: 50
        associativity: right
        polarity: negative

      with:
        args: [formula, formula]
        syntax: { ascii: "_ & _", latex: "#1 \\& #2" }
        precedence: 60
        associativity: left
        polarity: negative

      bang:
        args: [formula]
        syntax: { ascii: "! _", latex: "!#1" }
        polarity: positive

      monad:
        args: [formula]
        syntax: { ascii: "{ _ }", latex: "\\{#1\\}" }
        polarity: positive

  structure:
    description: Structural layer
    constructors:
      formula: { args: [formula] }
      neutral: { syntax: { ascii: "I", latex: "\\cdot" } }
      comma:
        args: [structure, structure]
        syntax: { ascii: "_ , _", latex: "#1 , #2" }
        precedence: 20

rules:
  identity:
    - name: Id
      conclusion: "A |- A"
      premises: []
      latex: "\\text{Id}"

  tensor:
    - name: Tensor_L
      conclusion: "X, A * B |- C"
      premises: ["X, A, B |- C"]
      latex: "\\otimes_L"

    - name: Tensor_R
      conclusion: "X, Y |- A * B"
      premises: ["X |- A", "Y |- B"]
      latex: "\\otimes_R"

  loli:
    - name: Loli_R
      conclusion: "X |- A -o B"
      premises: ["X, A |- B"]
      latex: "\\multimap_R"

    - name: Loli_L
      conclusion: "X, Y, A -o B |- C"
      premises: ["X |- A", "Y, B |- C"]
      latex: "\\multimap_L"

  with:
    - name: With_L1
      conclusion: "X, A & B |- C"
      premises: ["X, A |- C"]

    - name: With_L2
      conclusion: "X, A & B |- C"
      premises: ["X, B |- C"]

    - name: With_R
      conclusion: "X |- A & B"
      premises: ["X |- A", "X |- B"]

  monad:
    - name: Monad_R
      conclusion: "X |- {A}"
      premises: ["X |- A"]

extensions:
  quantitative:
    enabled: false
    semiring: "0-1-ω"  # or "ℝ≥0" or custom

  multimodal:
    enabled: false
    agents: []
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★★ | Very human-readable |
| Type safety | ★★☆☆☆ | Schema validation only |
| Extensibility | ★★★☆☆ | Easy to add fields, hard to add semantics |
| Proof search | ★☆☆☆☆ | Need full parser/engine |
| Isabelle export | ★★★☆☆ | Easy template generation |
| Quantitative types | ★★★☆☆ | Can add fields, need engine support |

---

## Granule-style

[Granule](https://granule-project.github.io/) has a specialized syntax for graded/quantitative types.

### Example Syntax

```granule
-- Graded modality: □_r means "r copies available"
dup : □_2 Int -> (Int, Int)
dup [x] = (x, x)

-- Grade polymorphism
id : forall {r : Nat} . □_r a -> □_r a
id [x] = [x]

-- Linear function
swap : (a, b) -> (b, a)
swap (x, y) = (y, x)  -- x and y used exactly once

-- Security levels
secret : □_Secret Int -> □_Public Int
secret [x] = [0]  -- can't leak x, return constant
```

### Hypothetical Linear Logic in Granule-style

```granule
-- Formulas as types with resource annotations

-- Tensor: both A and B consumed
tensor_intro : A -> B -> A ⊗ B
tensor_intro a b = (a, b)

tensor_elim : A ⊗ B -> (A -> B -> C) -> C
tensor_elim (a, b) k = k a b

-- Lollipop: linear function
loli_intro : (A -> B) -> A ⊸ B
loli_intro f = f

loli_elim : (A ⊸ B) -> A -> B
loli_elim f a = f a

-- With: choice (non-deterministic)
with_intro : A -> B -> A & B
with_intro a b = <a, b>

with_elim1 : A & B -> A
with_elim1 <a, _> = a

-- Bang: unlimited copies
bang_intro : □_ω A -> !A
bang_intro [a] = !a

bang_elim : !A -> □_ω A
bang_elim !a = [a]

-- Quantitative: semiring-indexed
owns : Agent -> □_r Asset -> Prop
transfer : □_r Asset @ Alice -> □_r Asset @ Bob
```

### Assessment

| Aspect | Rating | Notes |
|--------|--------|-------|
| Readability | ★★★★★ | Designed for practical use |
| Type safety | ★★★★★ | Z3 constraint solving |
| Extensibility | ★★★★☆ | Grade polymorphism is powerful |
| Proof search | ★★☆☆☆ | Type checking, not proof search |
| Isabelle export | ★★☆☆☆ | Different paradigm |
| Quantitative types | ★★★★★ | Core feature |

---

## Comparison Matrix

### Overall Comparison

| Approach | Readability | Type Safety | Proof Search | Extensibility | Isabelle | Quant. Types |
|----------|-------------|-------------|--------------|---------------|----------|--------------|
| **ll.json** | ★★☆ | ★☆☆ | ★★★ | ★★☆ | ★★★ | ★★☆ |
| **Calc-Toolbox-2** | ★★★★★ | ★★★ | ★★ | ★★★★ | ★★★★★ | ★★ |
| **Isabelle** | ★★★★ | ★★★★★ | ★★★★ | ★★★★★ | ★★★★★ | ★★★★ |
| **Lean 4** | ★★★★ | ★★★★★ | ★★★★ | ★★★★★ | ★★ | ★★★★★ |
| **Twelf/LF** | ★★★ | ★★★★★ | ★★★★★ | ★★★★ | ★★ | ★★ |
| **Agda** | ★★★★ | ★★★★★ | ★★ | ★★★★★ | ★★ | ★★★★★ |
| **YAML DSL** | ★★★★★ | ★★ | ★ | ★★★ | ★★★ | ★★★ |
| **Granule** | ★★★★★ | ★★★★★ | ★★ | ★★★★ | ★★ | ★★★★★ |

### By Use Case

| Use Case | Best Approach | Runner-up |
|----------|---------------|-----------|
| Quick prototyping | YAML/ll.json | Calc-Toolbox-2 |
| Formal verification | Isabelle | Lean 4 |
| Research frontier | Lean 4 + Agda | Twelf |
| Multi-format output | Calc-Toolbox-2 | ll.json |
| Quantitative types | Granule | Lean 4 |
| Proof search | Twelf | Isabelle |
| Teaching | Calc-Toolbox-2 | YAML |

---

## Recommendations

### For Our Project Goals

Given our research goals (accounting with multimodal quantitative linear types):

#### Short-term: Improve ll.json

1. **Add JSON Schema** for validation
2. **Separate concerns**: types.json, rules.json, rendering.json
3. **Add polarity/quantitative fields** explicitly

```json
// types.json
{
  "Formula_Tensor": {
    "args": ["Formula", "Formula"],
    "polarity": "positive",
    "quantitative": {
      "splits_context": true,
      "coefficient_operation": "multiply"
    }
  }
}
```

#### Medium-term: Custom DSL

Design a DSL that combines:
- **Calc-Toolbox-2**: Human-readable rule syntax
- **Granule**: Quantitative annotations
- **Our needs**: Multi-agent ownership

```
-- Proposed syntax (hybrid)

@types
  agent: Alice, Bob, Charlie
  quantity: ℝ≥0
  asset: USD, BTC

@connectives
  owns[a: agent, q: quantity] : asset -> formula
    ("_ owns _q _", NonAssoc, 80, "#1 \\owns_{#3}^{#2}")
    { quantitative: splits(q) }

@rules
  -- Transfer rule: Alice's q units go to Bob
  Γ |- Alice owns[q] A
  --------------------- Transfer(Alice → Bob)
  Γ |- Bob owns[q] A
```

#### Long-term: Lean 4 Formalization

For verified implementation:
1. Define calculus in Lean 4
2. Prove meta-properties (cut elimination, type safety)
3. Extract executable code

```lean
-- Future: Full formalization with quantitative types
structure QContext (R : Semiring) where
  formulas : List (Formula × R)

inductive QDeriv {R : Semiring} : QContext R → Formula → Prop where
  | tensor_r : QDeriv Γ A → QDeriv Δ B → QDeriv (Γ + Δ) (A ⊗ B)
  -- etc.
```

### Decision Framework

```
                    ┌─────────────────────────┐
                    │ What's the primary goal? │
                    └───────────┬─────────────┘
                                │
        ┌───────────────────────┼───────────────────────┐
        ▼                       ▼                       ▼
┌───────────────┐      ┌───────────────┐      ┌───────────────┐
│ Rapid         │      │ Formal        │      │ Research      │
│ Prototyping   │      │ Verification  │      │ Frontier      │
└───────┬───────┘      └───────┬───────┘      └───────┬───────┘
        │                      │                      │
        ▼                      ▼                      ▼
  ll.json/YAML           Isabelle/Lean         Lean 4 + Agda
  + Calc-TB-2            + Coq                 + Twelf
```

---

## Sources

### Calculus-Toolbox-2
- [GitHub Repository](https://github.com/goodlyrottenapple/calculus-toolbox-2)
- [Documentation: Calculi](https://goodlyrottenapple.github.io/calculus-toolbox/doc/calculi.html)

### Isabelle/HOL
- [Official Tutorial](https://isabelle.in.tum.de/doc/tutorial.pdf)
- [SeCaV: Sequent Calculus Verifier](https://www.researchgate.net/publication/359865142_SeCaV_A_Sequent_Calculus_Verifier_in_IsabelleHOL)
- [Formalization of Sequent Calculus (2024)](https://backend.orbit.dtu.dk/ws/files/383716082/Isabelle_2024_paper_5.pdf)

### Lean 4
- [Theorem Proving in Lean 4: Inductive Types](https://lean-lang.org/theorem_proving_in_lean4/inductive_types.html)
- [Lean Reference: Inductive Types](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
- [Brandon Rozek's Lean 4 Tutorial](https://brandonrozek.com/blog/lean4-tutorial/)

### Twelf/LF
- [System Description: Twelf](https://www.cs.cmu.edu/~fp/papers/cade99.pdf)
- [Logical Frameworks - Frank Pfenning](https://www.cs.cmu.edu/~fp/papers/handbook00.pdf)
- [Twelf Wiki](https://twelf.org)
- [nLab: Logical Framework](https://ncatlab.org/nlab/show/logical+framework)

### Agda
- [Typing with Leftovers (TYPES 2017)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.TYPES.2017.1)
- [Papers Using Agda](https://wiki.portal.chalmers.se/agda/Main/PapersUsingAgda)
- [Proof-Carrying Plans](https://arxiv.org/abs/2008.04165)

### Granule
- [Granule Project](https://granule-project.github.io/)
- [Quantitative Program Reasoning with Graded Modal Types (ICFP 2019)](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)
- [Gerty Implementation](https://github.com/granule-project/gerty)

### YAML/DSL Design
- [Advocating YAML as DSL](https://medium.com/@pavelpotapenkov/advocating-yaml-as-dsl-7f5fe695fba9)
- [YAML vs DSL: ast-grep comparison](https://ast-grep.github.io/blog/yaml-vs-dsl.html)
- [DSL Guide - Martin Fowler](https://martinfowler.com/dsl.html)

---

*Last updated: 2026-01-22*
