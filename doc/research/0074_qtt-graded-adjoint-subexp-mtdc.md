---
title: "QTT, Graded Types, Adjoint Logic, Subexponentials, MTDC: Expressiveness Hierarchy"
created: 2026-03-02
modified: 2026-03-03
summary: "Deep survey of five frameworks for resource-sensitive logic and their exact subsumption relationships"
tags: [QTT, graded-types, adjoint-logic, subexponentials, MTDC, linear-logic, proof-theory, semiring, modalities, display-calculus, dependent-types, exponentials, multimodal, focusing, research]
category: "Multi-Type Framework"
---

## 1. Quantitative Type Theory (QTT)

**Key papers:** Atkey 2018 "Syntax and Semantics of QTT"; McBride 2016 "I Got Plenty o' Nuttin'"; Brady 2021 "Idris 2: QTT in Practice"

### Core idea

QTT annotates every variable binding in a dependent type theory with a **usage quantity** drawn from a partially-ordered semiring (R, +, *, 0, 1). The typing judgement has the form:

```
sigma ; Gamma |- t : A
```

where `sigma` is either 0 or 1 (the "subject" annotation) and `Gamma` maps each variable to a quantity from R. sigma=0 means "erased/type-level only"; sigma=1 means "computationally relevant".

### The semiring

A semiring (R, +, *, 0, 1) where:
- **Addition** sums variable usages across subterms (e.g. in application `f x`, sum usage of each variable across f and x)
- **Multiplication** scales usage through binders (e.g. if a function uses its argument r times and is itself used s times, the argument is used s*r times)
- **0** = not used at runtime (erased / type-level)
- **1** = multiplicative unit

Idris 2 uses the **zero-one-many** semiring {0, 1, omega} where omega+omega = omega, omega*1 = omega, etc. This gives three usage classes:
- **0**: erased (parametric polymorphism, type indices)
- **1**: linear (used exactly once — session types, protocols, resource safety)
- **omega**: unrestricted (classical usage)

### Key typing rules

**Variable rule:** `sigma ; 0*Gamma, x:sigma*pi*A |- x : A` — variable x contributes sigma*pi usage, all other variables contribute 0.

**Function introduction:** `sigma ; Gamma |- lambda x.t : (pi x:A) -> B` where x has usage sigma*pi in the body t.

**Function elimination:** `sigma ; Gamma1+pi*Gamma2 |- f s : B[s/x]` where `sigma;Gamma1 |- f : (pi x:A)->B` and `sigma;Gamma2 |- s : A`. The argument's context is scaled by the function's declared usage pi.

**The 0-trick (McBride's insight):** Types are checked at sigma=0, so variables used only in types cost 0 usage. This is what lets dependent types coexist with linearity — type-level usage does not count against resource budgets.

### What QTT gives you

1. **Dependent types + linearity** — the historic combination problem solved cleanly
2. **Erasure** — 0-annotated terms are guaranteed absent at runtime
3. **Parametric polymorphism** — via 0-quantity type arguments: `(0 a : Type) -> a -> a`
4. **Resource tracking** — 1-quantity enforces single-use protocols

### What QTT lacks

- **No quantity polymorphism** (as of 2026). Cannot write a single `map` that works at all multiplicities. Idris 2 documents this as a known limitation. Workaround: separate definitions for each multiplicity, or default to omega.
- **No additive types in the original formulation.** Sefl & Svoboda (WoLLIC 2022) extended QTT with additive pairs, unit, union, and zero — these were non-trivial to add.
- **Fixed to one semiring instance.** You choose your semiring at system design time; cannot mix semirings within one program.

### Implementations beyond Idris 2

1. **Gerty** (Granule project, Haskell): minimal dependently-typed language implementing GrTT (Graded Modal Dependent Type Theory, Moon/Eades/Orchard ESOP 2021). Variables annotated with grade pairs (computational, type-level). Z3-backed type checking. 65 GitHub stars, v0.1.0 (2021), moderately active.

2. **Abel-Danielsson-Eriksson GrTT** (ICFP 2023): A graded modal dependent type theory with a universe and erasure, **fully formalized in 49,000 lines of Agda**. Proves subject reduction, consistency, normalization, decidability of definitional equality. Establishes sound extraction (programs of nat type have same value before and after erasing 0-graded content). Parameterized by a modality (partially-ordered semiring). The most rigorous metatheoretic treatment of graded dependent types to date.

3. **Yaffle** (Brady, WITS/POPL 2024): A new core language for Idris 2, redesigning the elaboration core. Still based on QTT with {0, 1, omega}. In active development as of 2024; aims to improve Idris 2's elaboration performance and correctness.

4. **qtt-ts** (GitHub): Experimental TypeScript implementation of QTT for exploration/education.

5. **Choudhury et al. Grad** (POPL 2021): A graded dependent type system that does not treat types specially (unlike QTT's sigma trick), applicable to a wider range of semirings.

---

## 2. Graded Modal Types (Granule, Orchard et al.)

**Key papers:** Orchard, Liepelt, Eades 2019 "Quantitative Program Reasoning with Graded Modal Types" (ICFP); Vollmer, Marshall, Eades, Orchard 2024 "A Mixed Linear and Graded Logic" (CSL 2025)

### Core idea

A graded modality is an indexed family of modalities `[]_r` where r ranges over a graded algebra (typically a semiring). The graded comonad `!_r A` means "a value of type A available for r uses." Different semiring instantiations give different analyses:

- **Natural numbers**: bounded reuse (Bounded Linear Logic)
- **{0,1,omega}**: exactness/linearity/unrestricted (same as QTT)
- **Security lattice {Public, Private}**: information flow
- **Effect sets**: side-effect tracking

### Granule language specifics

Granule is built on the **linear lambda-calculus** augmented with graded modal types. 703 GitHub stars, 3916 commits, v0.9.6.0 (Nov 2024). Haskell implementation (83% of codebase). Research vehicle, explicitly "not stable."

**Key features:**
- Graded necessity `[]_r A`: a boxed value usable according to grade r. Syntax: `a [n]` in types, `[x]` pattern to unbind.
- Graded possibility `<e> A`: effectful computation producing A with effect e
- **Coeffect polymorphism**: functions generic over the grade itself AND polymorphic over the semiring
- **Z3 backend** for constraint discharge on grades
- User-definable semirings/graded algebras
- Indexed types (sized vectors) — lightweight dependent types
- Haskell and experimental LLVM compilation backends

**Three built-in modalities:**
1. BLL-style resource-bounded (natural number grades, tracking exact reuse)
2. Security lattice ({Public, Private}, preventing information leaks)
3. Effect-graded possibility for I/O (`echo : () <{Stdin, Stdout}>`)

**Concrete example — coeffect polymorphism:**
```
twice : forall {a : Type, b : Type, c : Nat} .
  (a [c] -> b) [2] -> a [2 * c] -> (b, b)
twice [g] [x] = (g [x], g [x])
```
Grade `c` is polymorphic; resource consumption scales proportionally.

**Practical limitations:**
- Research language, not production-ready ("don't write your next spaceship controller in Granule yet")
- Interface and code not stable
- Limited to functional programming paradigm
- No dependent types (only indexed types as approximation)
- 41 open issues as of 2024

### Relationship to QTT

**QTT and graded types are closely related but not identical.**

| Aspect | QTT | Graded modal types |
|--------|-----|--------------------|
| Base theory | Full dependent types | Simple/indexed types (Granule); dependent in GrTT |
| Grading mechanism | Annotations on context variables | Explicit graded modality `[]_r A` |
| Where grades live | On every binding in context | On modal types only |
| Semiring scope | One fixed semiring per system | Multiple semirings simultaneously (Granule) |
| Dependent types | Yes (the point) | Partial (Gaboardi-style indices in Granule; full in GrTT) |

The key structural distinction: in QTT, grades are **pervasive** — every variable carries a quantity annotation. In Granule-style systems, the base is **linear** and grading appears only through the `!_r` modality. Vollmer et al. (2024) showed these are two sides of the same coin via a **mixed graded/linear logic (mGL)** where a linear fragment connects to a graded fragment through modal operators.

### Decomposition theorem (Fujii-Katsumata-Mellies 2016)

Every graded comonad decomposes into an adjunction + strict action. This means:
- Benton's LNL decomposition (! = F compose G across an adjunction) generalizes to the graded setting
- The graded `!_r` splits into two modal operators connecting a linear world to a graded world

This is the categorical foundation linking graded types to adjoint logic.

---

## 3. QTT vs ILL: Expressiveness Comparison

### Can you encode ILL in QTT?

**Yes, straightforwardly.** With the {0, 1, omega} semiring:
- Linear implication `A -o B` = `(1 x : A) -> B`
- Tensor `A * B` = dependent pair with both components at multiplicity 1
- Bang `!A` = `(omega x : A)` — unrestricted usage
- Additive with `A & B` = pair where you use at most one component (needs additive extension, Sefl/Svoboda 2022)
- Additive oplus `A + B` = sum type (same additive extension caveat)
- One (multiplicative unit) = unit type at multiplicity 1

QTT is **strictly more expressive than ILL** because it additionally has:
- Dependent types (Pi-types, Sigma-types with quantity annotations)
- Erasure (0-quantity) — no ILL analogue
- Arbitrary semiring instantiation

### Can you encode QTT in ILL?

**No, not faithfully.** ILL lacks:
- Dependent types entirely
- The 0-quantity / erasure distinction
- Arbitrary semirings (ILL has exactly one exponential `!`)

You could encode the *resource-tracking fragment* of QTT (just {1, omega} with no dependency) as ILL, but you lose the dependent types and erasure that are QTT's raison d'etre.

### The precise relationship

ILL embeds into QTT as the fragment where:
- The semiring is {0, 1, omega}
- No dependent types are used (all Pi-types are non-dependent function types)
- 0 is only used for type-level terms

QTT is an extension of the Curry-Howard reading of ILL into a dependently-typed setting, with the semiring generalizing the single `!` to a family of modalities.

---

## 4. QTT and Polymorphism

### Parametric polymorphism via 0-quantity

QTT encodes parametric polymorphism directly:
```
id : (0 a : Type) -> (1 _ : a) -> a
```
The type argument `a` has quantity 0 — it exists only for type checking and is erased at runtime. This is the standard encoding in Idris 2.

### Quantity polymorphism: the gap

QTT does **not** currently support quantity polymorphism — the ability to write:
```
map : (0 a : Type) -> (0 b : Type) -> (q _ : a -> b) -> List a -> List b
```
where `q` is a quantity variable. Brady notes this as a known limitation of Idris 2. The workaround is to provide separate definitions for each multiplicity, or to default to omega.

Granule handles this better via **coeffect polymorphism** where grade variables range over the semiring.

### Semiring polymorphism

A more radical form: abstracting over the semiring itself. Neither QTT nor Granule directly support this. The Licata-Shulman-Riley framework (adjoint logic) comes closest by parameterizing over an arbitrary mode theory.

---

## 5. Adjoint Logic (Reed, Pfenning, Licata-Shulman, Pruiksma)

**Key papers:** Reed 2009; Licata & Shulman 2016 "Adjoint Logic with a 2-Category of Modes"; Licata, Shulman & Riley 2017 "A Fibrational Framework for Substructural and Modal Logics"; Pruiksma & Pfenning 2019/2021 "A Message-Passing Interpretation of Adjoint Logic"; Pruiksma 2024 PhD thesis "Adjoint Logic with Applications"

### Core idea

Adjoint logic is parameterized by a **mode theory** — a structured collection of modes, each of which determines a logic with specific structural properties. Between modes, there are **adjoint pairs of modalities** (functors) that transport propositions from one mode to another.

### Mode theory

A mode theory consists of:
- A set of **modes** M = {m, k, ...}
- For each mode m, a set of structural properties sigma(m) subset {W, C} where:
  - **W** = weakening allowed (assumptions can be dropped)
  - **C** = contraction allowed (assumptions can be duplicated)
- A **preorder** on modes: m >= k
- **Monotonicity:** m >= k implies sigma(m) superset sigma(k) (moving "up" gains structural rules)

This gives a spectrum:
- sigma = {} : **linear** (neither W nor C)
- sigma = {W} : **affine** (can drop, cannot duplicate)
- sigma = {C} : **strict/relevant** (cannot drop, can duplicate)
- sigma = {W,C} : **intuitionistic/cartesian** (full structural rules)

### Adjoint modalities

For modes m >= k, there is an adjunction:
- **Shift-up** (F): m -> k — moves a proposition from mode m up to mode k
- **Shift-down** (G): k -> m — moves from k down to m

The composition G(F(A)) at mode m gives a comonad (like `!`), and F(G(A)) at mode k gives a monad (like the lax modality).

### What adjoint logic can express

The Licata-Shulman-Riley framework is remarkably general. Specific mode theories recover:
- **Linear logic:** two modes (linear, cartesian) with one adjunction
- **S4 modal logic:** truth and validity modes (Pfenning-Davies)
- **Lax logic:** truth and lax-truth modes
- **Non-associative, ordered, affine, relevant logics:** different structural property assignments
- **Bunched implications (BI):** multiple context formers
- **n-linear variables:** intermediate usage counts
- **Comonads and monads** (both monoidal and non-monoidal)

### Relationship to linear logic

ILL is the special case with two modes:
- Mode `L` (linear): sigma = {}
- Mode `U` (unrestricted): sigma = {W, C}
- One adjunction L <= U

The bang modality `!A` decomposes as G_U(F_L(A)) — shift up to unrestricted, then back down.

### The three sequent calculus formulations (Pruiksma 2018 / 2024 thesis)

Pruiksma et al. developed adjoint logic in three equivalent sequent calculus presentations:

1. **ADJE (explicit structural rules):** Weakening and contraction are explicit rules, applied when the mode permits. The sequent form is `Gamma =>_m A` where m is the mode of the succedent, and the independence constraint `Gamma >= m` ensures all antecedents are at modes at least as high as m in the preorder.

2. **ADJI (implicit structural rules):** Structural rules are built into the other rules. This is the "working" system for most proofs.

3. **ADJF (focused system):** A focused variant analogous to Andreoli's system. The identity rule splits into `id+` (positive) and `id-` (negative). Focusing phases work as in standard focused linear logic, with positive and negative propositions determining the phase structure. **Shifts are the polarity changers:** inserting a shift stabilizes the sequent during focusing.

Cut elimination is proved for all three, and all three are shown equivalent in provability.

### Focused proof search (ADJF)

**Correction to the earlier draft:** Adjoint logic *does* have a focused proof system (ADJF), developed in Pruiksma et al. 2018 and elaborated in Pruiksma's 2024 PhD thesis. The ADJF system:
- Splits propositions into positive and negative polarity
- Uses focusing phases (synchronous/asynchronous) analogous to Andreoli
- Shifts between modes act as polarity boundaries — they force phase transitions
- The `id+` and `id-` rules replace the standard identity
- Erasure (removing focusing/suspension brackets) recovers the unfocused system

The 2024 adjoint *natural deduction* paper (Pruiksma et al., FSCD 2024) does note that its natural deduction formulation lacks focusing, but the sequent calculus formulation does have it.

### Adjoint Logic, Lax Monad, and Quiescence

Ceptre needs the extra-logical `qui` predicate because it's forward-only — no backward chaining to detect "phase done." In CLF/LolliMon/CALC, quiescence detection is **implicit**: the forward engine returns when no rule matches, backward chaining naturally sequences phases.

The lax monad `{A}` IS the stage boundary. Adjoint logic generalizes: `{A} = ↑(↓A)`, where ↑ (exit mode) fires when the mode reaches quiescence via the same implicit mechanism.

| System | Needs `qui`? | Why / why not |
|--------|-------------|---------------|
| **Ceptre** | Yes | Forward-only — no natural "phase done" mechanism |
| **CLF/LolliMon** | No | Backward chaining orchestrates, monad exits on quiescence |
| **Adjoint logic** | No | ↑ shift exits mode on quiescence, generalizes monad |

**What adjoint logic adds over the bare lax monad:**
- **Type safety on transitions:** Only modes with declared adjunctions can shift
- **Per-mode structural rules:** Each mode has its own discipline (linear, affine, cartesian)
- **Composability:** `↑_A(↓_B(↑_C(...)))` valid only if A ≥ B ≥ C. Ceptre stages are flat.
- **N modes, not just 2.** The lax monad has backward/forward. Adjoint logic has arbitrary modes.

**In CALC:** Each mode would have its own rule set. `forward.run()` fires mode-M rules until quiescence (`if (!match) break`). The ↑ shift fires, returning to the orchestrating backward chainer (or an outer mode). No `qui` needed.

### Semi-Axiomatic Sequent Calculus (SAX)

DeYoung, Pfenning, Pruiksma (FSCD 2020) developed SAX, which blends sequent calculus features with axiomatic presentations. SAX has been extended to adjoint logic, providing:
- A Curry-Howard correspondence with a type theory for futures (shared-memory concurrency)
- An implementation of message-passing concurrent processes (2024 implementation paper)
- Shift propositions from adjoint logic within the SAX framework

This gives adjoint logic both a focused proof-theoretic foundation (ADJF) and a computational interpretation (SAX), making it more feasible for implementation than previously thought.

---

## 6. Subexponentials (Nigam & Miller, SELL)

**Key papers:** Nigam & Miller 2009 "Algorithmic Specifications in Linear Logic with Subexponentials"; Nigam & Miller 2011 "Specifying Proof Systems in Linear Logic with Subexponentials"; Nigam, Olarte et al. 2013/2017 "On Subexponentials, Focusing and Modalities"

### Core idea

SELL (Subexponential Linear Logic) replaces the single exponential `!` of linear logic with a **family of subexponentials** `!_a`, `?_a` indexed by labels from a set I. Different subexponentials may or may not permit weakening and contraction.

### Subexponential signature

A signature Sigma = <I, <=, W, C> where:
- **I** = set of subexponential labels
- **<=** = preorder on I
- **W subset I** = labels allowing weakening
- **C subset I** = labels allowing contraction
- **Upward closure:** if a in W and a <= b then b in W (same for C)
- **Distinguished element:** infinity in I with infinity in W intersect C (the "classical" subexponential, equivalent to standard `!`)

### Key results

1. **Cut elimination** holds for any signature Sigma
2. **Focused proof search** (SELLF): Chaudhuri, Nigam, Miller extended Andreoli focusing to SELL. Focused proofs are normal forms for proof search.
3. **Algorithmic expressiveness:** subexponentials can "locate" data (each subexponential is a named storage zone). Promotion (`!_a` introduction) tests a zone for emptiness. This enables:
   - Encoding of CCP (concurrent constraint programming)
   - Temporal, spatial, epistemic modalities (SELL-cap)
   - Specification of other proof systems as SELL theories

### SELL as a logical framework

SELL can encode:
- G1m (minimal logic)
- mLJ (multi-conclusion intuitionistic logic)
- LJQ* (focused intuitionistic logic)
- CCP with spatial and epistemic modalities

The key insight: **subexponentials are named contexts with controlled structural rules.** Each subexponential label identifies a zone of the proof state, and the signature controls what structural operations are available in each zone.

### Relationship to forward chaining

SELL's focused proof search is directly relevant to forward chaining engines. In CALC's terms:
- **Linear zone** = linear facts (consumed on use)
- **Persistent zone** = facts under `!_infinity` (bang)
- **Subexponentials** would give intermediate zones: e.g., affine facts (droppable but not duplicable), relevant facts (duplicable but not droppable)

SELLF's focusing discipline matches CALC's existing Andreoli-style focusing in the backward prover.

---

## 7. Multi-Type Display Calculus (MTDC) — Greco & Palmigiano

**Key papers:** Greco & Palmigiano 2016/2023 "Linear Logic Properly Displayed" (ACM TOCL); Frittella, Greco, Kurz, Palmigiano 2014 "Multi-type Display Calculus for Dynamic Epistemic Logic"; Frittella, Greco et al. 2016 "Multi-type Display Calculus for PDL"

### Core idea

MTDC is a proof-theoretic methodology for designing sequent calculi for logics that resist standard Gentzen-style treatment. The key innovation is introducing **multiple syntactic types** at the structural level, so that connectives operating across different domains can be given proper introduction/elimination rules.

### The display property and Belnap's problem

**Display calculi** (Belnap 1982) have a key property: any substructure of a sequent can be "displayed" — isolated on one side of the turnstile. This enables a general cut-elimination theorem.

**The exponential problem:** When you add exponentials (!,?) to linear logic in a display calculus, you lose the display property. The issue: exponentials are not residuated (! and ? don't form an adjoint pair within the linear world). Display rules for the structural counterparts of !,? would be unsound.

### The multi-type solution

MTDC resolves this by introducing **multiple types of structures:**
- **Linear type** = multiplicative linear logic structures
- **Classical/intuitionistic type** = structures with full structural rules
- **Bridge connectives** = adjoint operators between types

Exponentials decompose as: `!A = G(F(A))` where F takes linear structures to classical ones and G goes back. F and G form an adjoint pair, and their structural counterparts *do* have valid display rules because they are residuated.

This follows Girard's original intuition: linear logic arises from decomposing classical/intuitionistic connectives, and `!` is the composition of the two halves of this decomposition.

### Properties achieved

- **Soundness and completeness** w.r.t. the target logic
- **Conservativity** over the original logic
- **Cut elimination** via Belnap's general theorem
- **Subformula property**
- **Properness** = closure under uniform substitution of all parametric parts in rules (the strongest meta-property, enabling modular extensions)

### What MTDC can handle

MTDC has been applied to:
- Intuitionistic, bi-intuitionistic, and classical linear logic with exponentials
- Propositional Dynamic Logic (PDL)
- Dynamic Epistemic Logic (DEL)
- Semi-De Morgan Logic
- Inquisitive Logic
- Lattice Logic

### Relationship to adjoint logic

MTDC and adjoint logic share the same core insight: **exponentials decompose into adjoint pairs across type/mode boundaries.** The difference is in the proof-theoretic framework:
- **Adjoint logic** uses sequent calculus with modes on propositions and explicit shift operators
- **MTDC** uses display calculus with multiple structural types and bridge connectives

Both can express the same decomposition `! = G compose F`, but MTDC's display property gives stronger meta-theoretic guarantees (cut-elimination for free via Belnap's theorem).

### Relationship to subexponentials

MTDC can express multiple exponentials by having multiple classical-type zones, each bridged to the linear zone by its own adjoint pair. This is analogous to SELL's subexponential signature, but expressed within a framework that guarantees cut-elimination by construction.

The crucial advantage of MTDC: you don't need to prove cut-elimination for each new signature — Belnap's general theorem gives it automatically, as long as the rules satisfy the (easily checkable) display conditions.

---

## 8. Expressiveness Hierarchy

### Subsumption relationships

```
ILL  <  SELL  <=  Adjoint Logic (LSR)  ~  MTDC
                        |
                   QTT / Graded Types (orthogonal axis: dependent types)
```

**ILL < SELL:** SELL strictly extends ILL by replacing one `!` with a parameterized family. ILL is the single-subexponential special case.

**SELL <= Adjoint Logic:** Adjoint logic (Licata-Shulman-Riley) can encode SELL by creating one mode per subexponential label, with the preorder on modes matching the SELL preorder, and structural properties (W, C) matching the SELL signature. Adjoint logic may be strictly more general because it also handles non-commutative and ordered cases, bunched implications, etc.

**Adjoint Logic ~ MTDC:** These are roughly equi-expressive at the logical level — both decompose modalities via adjoint pairs across mode/type boundaries. They differ in proof-theoretic presentation:
- Adjoint logic → sequent calculus / natural deduction / process interpretation
- MTDC → display calculus with Belnap-style cut-elimination

MTDC has stronger proof-theoretic meta-properties (properness, modular cut-elimination) but is less directly computational (no Curry-Howard / process interpretation yet).

**QTT / Graded Types are on an orthogonal axis:** They combine resource tracking with **dependent types**, which none of the pure logic frameworks (SELL, adjoint logic, MTDC) handle natively.

### Detailed comparison table

| Feature | ILL | SELL | Adjoint Logic (LSR) | MTDC | QTT | Graded (Granule) |
|---------|-----|------|---------------------|------|-----|-------------------|
| Multiple exponentials | No | Yes | Yes (via modes) | Yes (via types) | No (one semiring) | Yes (multiple semirings) |
| Structural property control | Fixed (L vs !) | Per subexp | Per mode | Per type | Per semiring element | Per grade |
| Dependent types | No | No | No | No | Yes | Partial (GrTT) |
| Focused proof search | Yes (Andreoli) | Yes (SELLF) | Yes (ADJF) | No | N/A | N/A |
| Cut elimination | Yes | Yes | Yes | Yes (Belnap) | N/A | N/A |
| Process interpretation | Partial | No | Yes (session types) | No | No | No |
| Forward chaining | Yes (CLF, Ceptre, CALC) | Yes (SELLF) | Possible | Not explored | Not directly | Not directly |
| Polymorphism | No | Quantification over subexps | Mode-polymorphic | Not explored | Via 0-quantity | Coeffect poly |
| Erasure | No | No | No | No | Yes (0) | No |

### What subsumes what — precise claims

1. **SELL strictly subsumes ILL.** (Add one subexponential with W+C to get standard `!`)
2. **Adjoint logic (LSR) subsumes SELL.** (Modes = subexponential labels, structural properties match, preorder matches. Shown in Pruiksma et al.)
3. **Adjoint logic (LSR) subsumes ILL.** (Corollary of 1+2, or directly: two modes with one adjunction)
4. **MTDC is equi-expressive with adjoint logic for pure logics** (both decompose exponentials/modalities via adjunctions), but with different proof-theoretic presentations
5. **QTT subsumes ILL** (as a type theory, with {0,1,omega} semiring and no dependency)
6. **QTT does not subsume SELL** (QTT has one semiring, cannot express named zones / multiple subexponentials)
7. **Graded types (Granule-style) with multiple semirings approximate SELL** but the correspondence is informal — no precise encoding theorem exists
8. **The Glad system (Hanukaev & Eades 2023) combines graded types + adjoint logic** — each mode gets its own graded semiring, with adjoint operators between modes. This is the current state-of-the-art unification.

### The unification picture

```
                    MTDC (proof theory)
                      |
                      | (same logical content, different presentation)
                      |
Adjoint Logic --------+-------- Graded Types
 (modes, adjunctions)            (semirings, modalities)
        |                              |
        +--- unified by Glad ----------+
        |    (modes + grades)          |
        |                              |
      SELL                           QTT
  (subexponentials)            (dep types + semiring)
        |                              |
       ILL                        ILL fragment
  (one exponential)            (non-dependent fragment)
```

The **Glad** system (2023) represents the best current unification: it parameterizes over a mode theory (adjoint logic style) where each mode carries its own preordered semiring (graded type style). This gives:
- Multiple structural zones (from modes)
- Fine-grained resource tracking within each zone (from grades)
- Adjoint modalities between zones (from adjoint logic)
- Dependent types (from the dependent type theory base)

---

## 9. Relevance to CALC's Forward-Chaining Engine

### Current state

CALC implements ILL forward chaining with:
- Linear facts (consumed on use)
- Persistent facts (under `!`, duplicable + droppable)
- Andreoli focusing in the backward prover
- No intermediate structural regimes

### What each framework would add

**SELL / Subexponentials:**
- Named storage zones with controlled structural rules
- Most directly applicable: add subexponential labels to CALC's state model
- SELLF focusing is directly compatible with CALC's existing focused prover
- Implementation: extend FactSet with a zone tag per group, parameterize structural rules per zone

**Adjoint Logic:**
- Multi-modal state with typed transitions between modes
- Session-type interpretation for concurrent/distributed protocols
- Has focused proof search (ADJF, Pruiksma 2018/2024) — compatible with CALC's focused prover
- Implementation: heavier — need mode annotations on all propositions, shift operators in rules

**MTDC:**
- Powerful meta-theory (modular cut-elimination)
- No computational interpretation / no direct forward-chaining model
- Primarily valuable as a *design tool* for proving properties of CALC's calculus
- Not directly implementable as a forward engine

**QTT / Graded Types:**
- Dependent types for richer specifications
- Erasure for compile-time-only type information
- Quantity polymorphism (eventually) for generic resource code
- Not directly a logic for forward chaining — QTT is a type theory, not a proof search system
- Potential bridge: use QTT to *type-check* CALC programs / proofs

### Recommended path for CALC

**Subexponentials (SELL)** are the most directly actionable extension:
1. Already compatible with CALC's focused proof search
2. Extend `State = { linear: FactSet, persistent: FactSet }` to `State = { zones: Map<Label, FactSet> }` with a signature specifying W/C per zone
3. Compile subexponential rules to the existing forward engine
4. Use SELLF focusing in the backward prover

**Graded annotations** as a second step:
1. Annotate facts with semiring grades (usage counts, security levels, etc.)
2. Integrate with constraint solver (already exists: EqNeqSolver)
3. This approximates the Glad system's per-mode grading

**Full adjoint logic** is a longer-term goal requiring:
1. Mode annotations on all formulas
2. Shift operators in the rule language
3. A focused sequent calculus for adjoint logic (open research problem)

---

## 10. QTT Grade 0: Requires Dependent Types

The {0,1,ω} semiring has three grades. CALC already has {1,ω} (linear/persistent). What would grade 0 add?

**Grade 0 = "exists at the type level, erased at runtime."** Example in Idris 2:
```idris
length : {0 n : Nat} -> Vect n a -> Nat
```
Here `n` has grade 0: it constrains the type `Vect n a` but the function doesn't inspect `n` at runtime.

**Grade 0 requires dependent types to be meaningful.** Its purpose is "mention in types but don't use in computation." Without dependent types, there ARE no types to mention it in. In CALC's untyped setting, there's no analogue — no notion of "this fact exists at the type level but cannot be used."

If CALC ever got dependent types (Phase 4), grade 0 would mean: facts that constrain rule applicability (type-level) but are not consumed or produced (erased). Like phantom types in Haskell.

**Practical answer:** Don't pursue grade 0 until dependent types exist. It's genuinely meaningless without them.

---

## 11. Definitional Equality: Why It Matters (and Doesn't) for CALC

### What It Is

**Definitional equality** = what the computer considers "the same" by just computing (no proof needed):
- `2 + 3 ≡ 5` (compute the addition)
- `(λx. x)(y) ≡ y` (beta reduction)
- `let x = 3 in x+1 ≡ 4` (substitute and compute)

**Propositional equality** = what you can PROVE is the same, but the computer can't just compute:
- `n + 0 = n` for all n (needs induction)
- `rev(rev(xs)) = xs` (needs a proof)

### Why CLF Cares

CLF's definitional equality includes **commuting conversions** for the monad:
```
let {x} = (let {y} = M in N) in P  ≡  let {y} = M in (let {x} = N in P)
```
(when y ∉ FV(P)). This says: reordering independent concurrent steps doesn't change the computation. The type checker decides this automatically.

CLF restricts what goes inside `{...}` to: tensor (⊗), one (1), bang (!), existential (∃). No loli, no oplus. Adding loli would need:
```
let {x} = (λy. M) in N  ≡?  λy. (let {x} = M in N)
```
Adding oplus would need:
```
let {x} = (case M of inl a => N₁ | inr b => N₂) in P
≡? case M of inl a => (let {x} = N₁ in P) | inr b => (let {x} = N₂ in P)
```

Each new connective inside `{...}` adds commuting conversions. Making these decidable risks undecidability.

### Why CALC Doesn't Need to Worry

CALC's forward engine already has loli and oplus inside the monadic part — it works **operationally** because CALC doesn't decide proof-term equality. The concern is about proof-theoretic cleanliness, not about CALC breaking. CALC doesn't have a type checker that needs to compare proof terms.

If CALC ever implements a type checker (Phase 4), this becomes relevant. For Phases 1-3, it's a non-issue.

---

## 12. Adjoint Logic vs MTDC: Different Levels of Abstraction

The previous survey (RES_0073, TODO_0064) was imprecise about this. Corrected framing:

**Adjoint logic** = a **specific logic** with concrete connectives (↑, ↓, shifts between modes), concrete rules, concrete implementation. You write code for ↑ and ↓.

**MTDC** = a **meta-framework** for DESIGNING calculi with guaranteed good properties (cut elimination, display property). You don't "implement MTDC" — you use MTDC theory to verify your calculus is well-designed.

| | Adjoint Logic | MTDC |
|---|---|---|
| **What it is** | A specific logic | A design recipe |
| **You implement** | Connectives, rules, proof search | Nothing directly |
| **You get** | New logical operators | Meta-theorems about your calculus |
| **Analogy** | "Implement quicksort" | "Use master theorem to verify complexity" |

When TODO_0064 says "CALC almost has MTDC," it means: CALC's two-zone context (linear D; cartesian G) with different structural rules per zone is the beginning of the multi-type display pattern. Specifically: no weakening/contraction in the linear zone, full structural rules in the cartesian zone. MTDC theory tells us this design gives cut elimination.

**What to do:** Implement adjoint logic (concrete connectives). Use MTDC theory (paper-and-pencil) to verify the extended calculus has good properties. They're at different levels, not competing alternatives.

---

## 13. Concrete Graded Types Example for CALC

### Current CALC — two zones, implicit grades {1, ω}

```
% ill.rules (current)
tensor_r: G ; D, D' |- A * B       % D split between premises (grade 1)
  <- G ; D |- A                     % G shared (grade ω)
  <- G ; D' |- B

bang_r:   G ; |- !A                 % empty linear context
  <- G ; |- A                       % only cartesian survives

bang_l:   G ; D, !A |- C            % consume !A from linear
  <- G, A ; D |- C                  % move A to cartesian (1 → ω)
```

### Hypothetical Graded CALC — single zone, explicit grades {0, 1, ω}

```
% ill-graded.rules (hypothetical)
@grades { 0, 1, omega }

id: ; x:_1 A |- A                   % use x exactly once (grade 1)

tensor_r: Gamma + Delta |- A * B    % ADDITIVE split: sum grades
  <- Gamma |- A
  <- Delta |- B
  % if x appears in both, its grade = Gamma(x) + Delta(x)

loli_r: Gamma |- A -o B             % bind A with grade 1
  <- Gamma, x:_1 A |- B

with_r: Gamma |- A & B              % SAME context both premises
  <- Gamma |- A                     % grades must match exactly
  <- Gamma |- B

bang_r: omega * Gamma |- !A         % all grades must be omega
  <- omega * Gamma |- A             % (or 0 — erased is ok too)

bang_l: Gamma, x:_1 (!A) |- C      % consume one !A
  <- Gamma, x:_omega A |- C        % get unlimited A (grade ω)
```

### What changes in the engine

| Component | Current | Graded |
|-----------|---------|--------|
| Context | Two zones: `G` (ω), `D` (1) | One zone: `Γ` with per-variable grades |
| Splitting | Multiset partition of `D` | Additive: sum grades from premises |
| Structural rules | Explicit copy/weaken in `G` only | Implicit: ω allows copy, 0 allows weaken |
| Rule matching | Check linear consumption | Check grade arithmetic: `Γ₁ + Γ₂ = Γ` |

### Assessment

~1500 LOC to switch from two-zone to fully graded. The big change is replacing context management with grade tracking. CALC's two-zone system already gives {1,ω}, which covers all current use cases. Unless you specifically need affine types or custom resource disciplines, keep the two-zone approach and invest in stages/modes/fixed-points instead.

---

## 14. Key References

1. Atkey 2018 — *Syntax and Semantics of QTT* (LICS)
2. McBride 2016 — *I Got Plenty o' Nuttin'* (semiring-annotated dependent types)
3. Brady 2021 — *Idris 2: QTT in Practice* (ECOOP)
4. Orchard, Liepelt, Eades 2019 — *Quantitative Program Reasoning with Graded Modal Types* (ICFP)
5. Vollmer, Marshall, Eades, Orchard 2024 — *A Mixed Linear and Graded Logic* (CSL 2025)
6. Fujii, Katsumata, Mellies 2016 — *Towards a Formal Theory of Graded Monads* (FoSSaCS)
7. Sefl, Svoboda 2022 — *Additive Types in QTT* (WoLLIC)
8. Reed 2009 — *A Judgmental Deconstruction of Modal Logic* (first adjoint logic)
9. Licata, Shulman 2016 — *Adjoint Logic with a 2-Category of Modes* (LFCS)
10. Licata, Shulman, Riley 2017 — *A Fibrational Framework for Substructural and Modal Logics* (FSCD)
11. Pruiksma, Pfenning 2021 — *A Message-Passing Interpretation of Adjoint Logic* (JLAMP)
12. Pruiksma 2024 — *Adjoint Logic with Applications* (CMU PhD thesis)
13. Nigam, Miller 2009 — *Algorithmic Specifications in Linear Logic with Subexponentials* (PPDP)
14. Nigam, Olarte et al. 2017 — *On Subexponentials, Focusing and Modalities* (TCS)
15. Greco, Palmigiano 2023 — *Linear Logic Properly Displayed* (ACM TOCL)
16. Frittella, Greco, Kurz, Palmigiano 2014 — *Multi-type Display Calculus for DEL*
17. Hanukaev, Eades 2023 — *Combining Dependency, Grades, and Adjoint Logic* (TyDe)
