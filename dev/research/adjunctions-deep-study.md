# Adjunctions: A Deep Study

This document provides a comprehensive treatment of adjunctions from both categorical and proof-theoretic perspectives, with emphasis on their relevance to CALC.

---

## Part I: Categorical Adjunctions

### Definition via Hom-Set Isomorphism

An **adjunction** between categories C and D is a pair of functors:
- F : C → D (left adjoint)
- G : D → C (right adjoint)

together with a **natural bijection**:

```
Hom_D(F(X), Y) ≅ Hom_C(X, G(Y))
```

for all objects X in C and Y in D.

**Notation**: We write F ⊣ G to indicate F is left adjoint to G.

**Intuition**: "Morphisms out of F(X)" correspond to "morphisms into G(Y)." The left adjoint is "free," the right adjoint is "forgetful."

### Definition via Unit and Counit

Equivalently, an adjunction F ⊣ G consists of:
- **Unit**: η : Id_C → G ∘ F (natural transformation)
- **Counit**: ε : F ∘ G → Id_D (natural transformation)

satisfying the **triangle identities** (zig-zag equations):

```
(ε_F) ∘ (F η) = Id_F     -- "straighten left zig-zag"
(G ε) ∘ (η_G) = Id_G     -- "straighten right zig-zag"
```

**In string diagrams**: These say we can "pull the string straight" through a bend.

### Reconstructing the Bijection

Given unit η and counit ε, the bijection is:

```
φ : Hom_D(F(X), Y) → Hom_C(X, G(Y))
    φ(f) = G(f) ∘ η_X

ψ : Hom_C(X, G(Y)) → Hom_D(F(X), Y)
    ψ(g) = ε_Y ∘ F(g)
```

The triangle identities ensure φ and ψ are inverses.

---

## Part II: Key Examples

### 1. Free ⊣ Forgetful

The paradigmatic example. For any algebraic structure:

```
Free : Set → Mon     (free monoid on a set)
U : Mon → Set        (underlying set of a monoid)

Free ⊣ U
```

**Unit**: η_X : X → U(Free(X)) embeds a set into its free monoid (singleton words).

**Counit**: ε_M : Free(U(M)) → M evaluates words in a monoid.

**The bijection**: Monoid homomorphisms from Free(X) to M correspond to functions from X to U(M). "To define a homomorphism from a free monoid, just say where generators go."

**Generalization**: Every "free construction" is a left adjoint to a forgetful functor.

### 2. Product ⊣ Diagonal ⊣ Coproduct

The diagonal functor Δ : C → C × C sends X to (X, X).

```
+ ⊣ Δ ⊣ ×

Coproduct (Sum)  ⊣  Diagonal  ⊣  Product
```

**Product adjunction**:
```
Hom(Z, X × Y) ≅ Hom(Z, X) × Hom(Z, Y)
```
"A morphism into a product = a pair of morphisms."

**Coproduct adjunction**:
```
Hom(X + Y, Z) ≅ Hom(X, Z) × Hom(Y, Z)
```
"A morphism from a coproduct = a pair of morphisms."

### 3. Curry ⊣ Eval (Exponential Adjunction)

In a cartesian closed category:

```
(−) × A  ⊣  (−)^A

Product with A  ⊣  Exponential (function space)
```

**The bijection** (currying):
```
Hom(X × A, B) ≅ Hom(X, B^A)
```

**In types**: `(X × A) → B ≅ X → (A → B)`

**Counit**: ε : B^A × A → B is **evaluation** (apply function to argument).

**Unit**: η : X → (X × A)^A is **pairing** (λa. (x, a)).

### 4. Limits and Colimits as Adjoints

For diagram shape J, the **diagonal functor** Δ : C → C^J sends X to the constant diagram.

```
colim_J  ⊣  Δ  ⊣  lim_J
```

**Limit**: Right adjoint to diagonal — "universal cone."
**Colimit**: Left adjoint to diagonal — "universal cocone."

**Products, equalizers, pullbacks** are all limits.
**Coproducts, coequalizers, pushouts** are all colimits.

---

## Part III: Properties of Adjoint Functors

### RAPL: Right Adjoints Preserve Limits

**Theorem**: If G is a right adjoint (G = R in L ⊣ R), then G preserves all limits that exist.

```
G(lim D) ≅ lim (G ∘ D)
```

**Dually**: Left adjoints preserve colimits (LAPC).

**Intuition**: Right adjoints are "continuous" (preserve limits); left adjoints are "cocontinuous" (preserve colimits).

### Adjoint Functor Theorem

**Converse question**: If G preserves limits, is G a right adjoint?

**General AFT**: A functor G : D → C has a left adjoint if:
1. G preserves all small limits
2. G satisfies the **solution set condition**

**For locally presentable categories**: G has a left adjoint iff G preserves limits and is accessible.

### Uniqueness

Adjoints are unique up to unique isomorphism. If F ⊣ G and F ⊣ G', then G ≅ G'.

---

## Part IV: Adjunctions, Monads, and Comonads

### Every Adjunction Induces a Monad and Comonad

Given F ⊣ G with unit η and counit ε:

**Monad** T = G ∘ F on C:
- Unit: η : Id → T
- Multiplication: μ = G ε F : T² → T

**Comonad** D = F ∘ G on D:
- Counit: ε : D → Id
- Comultiplication: δ = F η G : D → D²

### Kleisli and Eilenberg-Moore Categories

**Question**: Does every monad arise from an adjunction?

**Answer**: Yes, in two canonical ways!

**Kleisli category** C_T:
- Objects: same as C
- Morphisms: X → T(Y) in C
- The "free T-algebra" adjunction

**Eilenberg-Moore category** C^T:
- Objects: T-algebras (X, α : T(X) → X)
- Morphisms: algebra homomorphisms
- The "all T-algebras" adjunction

**Universal property**: Kleisli is initial and Eilenberg-Moore is terminal among all adjunctions inducing T.

### The ! Modality as a Comonad

In linear logic, ! (of-course/bang) is a **comonad**:

```
ε : !A → A          (dereliction)
δ : !A → !!A        (digging)
```

**Two approaches to modeling !**:

1. **As a comonad** on a symmetric monoidal category
2. **As an adjunction** between cartesian and linear categories (Benton's LNL)

The adjunction approach: ! = F ∘ G where F ⊣ G bridges linear and cartesian worlds.

---

## Part V: Adjunctions vs Galois Connections vs Residuation

### Galois Connections (Order-Theoretic)

For posets P and Q, a **Galois connection** is a pair of monotone functions:

```
f : P → Q    (left adjoint)
g : Q → P    (right adjoint)

f(x) ≤ y  iff  x ≤ g(y)
```

This is exactly a categorical adjunction where categories are posets and functors are monotone functions.

**Two types**:
- **Monotone (covariant)**: Both order-preserving — these are adjunctions
- **Antitone (contravariant)**: Both order-reversing — called "polarities"

### Residuation

In a partially ordered algebraic structure, **residuation** is:

```
a · b ≤ c   iff   a ≤ c / b   iff   b ≤ a \ c
```

The operations `/` (right residual) and `\` (left residual) are adjoint to multiplication.

**In residuated lattices**: The residuals form a Galois connection with the product.

### The Residuation Condition in Logic

The **deduction theorem** is residuation:

```
Γ, A ⊢ B   iff   Γ ⊢ A → B
```

"A together with Γ proves B" iff "Γ alone proves A implies B."

**This expresses an adjunction**:
```
(−) ⊗ A  ⊣  A → (−)

Tensor with A  ⊣  Implication from A
```

### Comparison Table

| Concept | Setting | Notation |
|---------|---------|----------|
| Adjunction | Categories | F ⊣ G |
| Galois connection | Posets | f ⊣ g |
| Residuation | Residuated lattices | · ⊣ / ⊣ \ |
| Deduction theorem | Logic | ⊗ ⊣ → |

**Key insight**: These are all the same mathematical structure at different levels of generality!

---

## Part VI: Proof-Theoretic Adjunctions

### Adjunctions in Sequent Calculus

In sequent calculus, adjunctions manifest as **bidirectional rules**:

```
Tensor-Implication Residuation:
─────────────────────────────
Γ, A ⊗ B ⊢ C    ⟺    Γ, A ⊢ B ⊸ C
```

This is the proof-theoretic form of the adjunction (−) ⊗ B ⊣ B ⊸ (−).

### Display Postulates

In **display calculus**, adjunctions appear as display postulates:

```
X ; Y ⊢ Z    ⟺    X ⊢ Y > Z
```

The structural connective `;` (semicolon) and `>` (arrow) are adjoint at the structure level.

**Belnap's insight**: Display postulates encode residuation, which enables the display property and guarantees cut elimination.

### The LNL Decomposition

**Benton's LNL** decomposes ! via an adjunction:

```
Categories:  C (Cartesian)  ⟷  M (Linear/Monoidal)

Functors:    F : C → M      (embed cartesian into linear)
             G : M → C      (extract cartesian from linear)

Adjunction:  F ⊣ G

Comonad:     ! = F ∘ G
```

**Why this works**: The adjunction F ⊣ G induces a comonad on M. This comonad IS the ! modality.

**In CALC**:
- persistent_ctx = the cartesian category C
- linear_ctx = the linear category M
- Bang_L = the F functor
- Implicit dereliction = the G functor

### Adjoint Logic Generalization

**Adjoint logic** (Pruiksma-Pfenning) generalizes LNL to arbitrary mode preorders:

```
Modes: {m, n, ...} with preorder m ≥ n
Each m ≥ n induces an adjunction: ↓ᵐₙ ⊣ ↑ⁿₘ
```

**Examples encoded**:
- LNL: modes {U, L}, U > L
- S4: modes {V, U}, □ = ↓ ↑
- Lax logic: modes {U, X}, ○ = ↑ ↓

---

## Part VII: Curry-Howard-Lambek

### The Three-Way Correspondence

| Logic | Type Theory | Category Theory |
|-------|-------------|-----------------|
| Proposition | Type | Object |
| Proof | Term/Program | Morphism |
| Implication A → B | Function type A → B | Exponential B^A |
| Conjunction A ∧ B | Product type A × B | Product A × B |
| Disjunction A ∨ B | Sum type A + B | Coproduct A + B |
| True | Unit type () | Terminal object 1 |
| False | Empty type ⊥ | Initial object 0 |

### Adjunctions in Curry-Howard

Every fundamental datatype arises from an adjunction:

| Type | Left Adjoint | Right Adjoint |
|------|--------------|---------------|
| Products | Diagonal Δ | Product × |
| Sums | Sum + | Diagonal Δ |
| Functions | Product (−) × A | Exponential (−)^A |
| Lists | Free monoid | Forgetful |

**The exponential adjunction** gives currying:
```
(X × A → B)  ≅  (X → (A → B))
```

### Monads in Programming

Monads arise from adjunctions. The **State monad** comes from:

```
(−) × S  ⊣  (−)^S

State S A  =  S → (A, S)  =  (S → A × S)
```

The **Reader monad** comes from:
```
Δ  ⊣  (−)^E

Reader E A  =  E → A
```

---

## Part VIII: String Diagrams

### Basic Elements

In string diagrams for a 2-category:
- **0-cells** (objects): Regions of the plane
- **1-cells** (morphisms): Strings/wires
- **2-cells** (2-morphisms): Nodes/boxes

### Adjunction in String Diagrams

An adjunction L ⊣ R is drawn with:
- Wire for L going "up" (left to right)
- Wire for R going "down" (right to left)
- Unit η as a "cup" (∪)
- Counit ε as a "cap" (∩)

### The Zig-Zag Identities

The triangle identities say we can straighten zig-zags:

```
    ╭───╮
 L──┤   │──L   =   L──────L
    │   ╰─╮
    ╰─────╯

    ╭─────╮
    │   ╭─╯
 R──┤   │──R   =   R──────R
    ╰───╯
```

### Monads from Adjunctions (Diagrammatically)

Given L ⊣ R, the monad T = R ∘ L is visualized as:
- Unit η: a cup
- Multiplication μ: composition of cups

The monad laws (associativity, unit) follow immediately from the zig-zag identities!

---

## Part IX: Relevance to CALC

### What CALC Already Has

**CALC's LNL implementation IS an adjunction**:

```
persistent_ctx  ≅  Cartesian category C
linear_ctx      ≅  Linear category M

Bang_L rule implements F : C → M
Implicit dereliction implements G : M → C
```

The adjunction F ⊣ G gives the ! comonad.

### Why Adjunctions Matter for CALC

1. **Cut elimination**: Adjunction structure guarantees cut admissibility
2. **Modularity**: Add new modalities by adding new adjunctions
3. **Semantic foundation**: Categorical models via adjunctions
4. **Resource management**: Residuation tracks resources

### Potential Extensions

**Principal modes as adjunctions**:
```
Could [Alice] ↔ [Bob] transfer be an adjunction?
Transfer_AB ⊣ Transfer_BA ?
```

This would require careful design of what the unit and counit mean.

**Graded adjunctions**:
```
Graded modality □_r could arise from graded adjunction
where the adjunction varies with the grade r.
```

### The Adjunction Checklist

When designing new modalities for CALC, check:

1. **Is there a residuation?** `Γ, F(A) ⊢ B ↔ Γ ⊢ G(B)`?
2. **What are unit/counit?** What do they mean semantically?
3. **Do triangle identities hold?** This ensures soundness.
4. **What does the induced monad/comonad capture?**

---

## Summary

### Key Takeaways

1. **Adjunctions are everywhere**: Products, coproducts, exponentials, limits, colimits, free constructions — all are adjunctions.

2. **Three equivalent definitions**:
   - Hom-set isomorphism
   - Unit + counit + triangle identities
   - Universal property

3. **Adjunctions generate structure**:
   - Every adjunction induces a monad and comonad
   - Monads model computation; comonads model context

4. **Proof-theoretic view**:
   - Residuation is adjunction
   - Display postulates encode adjunctions
   - LNL decomposes ! via adjunction

5. **CALC connection**:
   - Current LNL implementation IS an adjunction
   - New modalities should be designed as adjunctions
   - Guarantees cut elimination and semantic soundness

### Open Questions for CALC

1. **Can ownership transfer be an adjunction?**
   - What category structure underlies principals?
   - What would unit/counit mean?

2. **Graded adjunctions for quantities?**
   - How to grade the F ⊣ G adjunction?
   - Connection to graded comonads?

3. **Composite principals as categorical products?**
   - [A ∧ B] as product in a category of principals?
   - Would give introduction/elimination rules

---

## References

### Category Theory
- [nLab: Adjunction](https://ncatlab.org/nlab/show/adjunction)
- [Wikipedia: Adjoint functors](https://en.wikipedia.org/wiki/Adjoint_functors)
- [Math3ma: What is an Adjunction?](https://www.math3ma.com/blog/what-is-an-adjunction-part-2)
- [Milewski: The Power of Adjunctions](https://bartoszmilewski.com/2019/09/20/the-power-of-adjunctions/)

### Linear Logic and LNL
- [Benton, "A Mixed Linear and Non-Linear Logic" (1994)](https://www.researchgate.net/publication/221558077)
- [nLab: !-modality](https://ncatlab.org/nlab/show/!-modality)
- [Schalk, "What is a categorical model for Linear Logic?"](http://www.cs.man.ac.uk/~schalk/notes/llmodel.pdf)

### Proof Theory
- [SEP: Substructural Logics](https://plato.stanford.edu/entries/logic-substructural/)
- [nLab: Adjoint functor theorem](https://ncatlab.org/nlab/show/adjoint+functor+theorem)

### Adjoint Logic
- [Pruiksma et al., "Adjoint Logic" (2018)](https://ncatlab.org/nlab/files/PCPR18-AdjointLogic.pdf)
- [Licata & Shulman, "Adjoint Logic with a 2-Category of Modes"](https://link.springer.com/chapter/10.1007/978-3-319-27683-0_16)

### Curry-Howard-Lambek
- [Wikipedia: Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence)
- [HaskellWiki: Curry-Howard-Lambek](https://wiki.haskell.org/Curry-Howard-Lambek_correspondence)

### String Diagrams
- [Wikipedia: String diagram](https://en.wikipedia.org/wiki/String_diagram)
- [Baez: This Week's Finds #174](https://math.ucr.edu/home/baez/week174.html)

### Related CALC Research
- [[adjoint-logic-unifying-framework]] — Adjoint logic assessment
- [[multi-type-display-calculus]] — Display calculus and LNL
- [[residuation]] — Residuation in substructural logics

---

*Last updated: 2026-01-29*
