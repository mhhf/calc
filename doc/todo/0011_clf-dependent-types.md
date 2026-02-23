---
title: "CLF Dependent Types"
created: 2026-02-18
modified: 2026-02-23
summary: "Add Pi and existential types for full LF/LLF/CLF compatibility"
tags: [clf, dependent-types, type-theory, lf, llf, pi-types, adequacy]
type: research
cluster: CLF
status: researching
priority: 2
depends_on: [TODO_0006]
required_by: []
---

# CLF Dependent Types (Pi, exists)

For full LF/LLF/CLF compatibility. Requires type-checking terms (not just formulas), capture-avoiding substitution, kind system.

---

## 1. The LF / LLF / CLF Type Theory Hierarchy

Three layers, each a conservative extension of the previous.

### 1.1 LF (Edinburgh Logical Framework, Harper-Honsell-Plotkin 1993)

LF is a dependently-typed lambda-calculus with three syntactic levels:

```
Kinds:    K ::= type | Pi x:A. K
Types:    A ::= a | A M | Pi x:A1. A2
Objects:  M ::= c | x | lam x:A. M | M1 M2
```

- **Kinds** classify type families. `type` is the base kind. `Pi x:A. K` is a dependent kind (a family of kinds indexed by terms of type A).
- **Types** classify objects. `a` is an atomic type constant. `A M` is a type family applied to a term. `Pi x:A1. A2` is the dependent function type.
- **Objects** are terms. Constants `c`, variables `x`, lambda abstraction, and application.

The **Pi type** `Pi x:A. B` is the core innovation: the return type `B` can depend on the argument value `x`. When `B` doesn't mention `x`, this degenerates to the simple arrow `A -> B`.

**Key properties:**
- All well-typed terms are strongly normalizing
- Type checking is decidable
- Definitional equality is beta-conversion
- In the **canonical forms** presentation (used by Twelf), all terms are beta-normal, eta-long, and hereditary substitution replaces ordinary substitution to maintain this invariant

### 1.2 LLF (Linear Logical Framework, Cervesato-Pfenning 1996)

LLF = LF + linear types. Notation: lambda-Pi-lolli-with-top.

```
Types:    A ::= ... | A1 -o A2 | A1 & A2 | top
```

Adds to LF:
- **Linear function type** `A -o B`: consume exactly one `A` to produce `B`
- **Additive conjunction** `A & B`: use the context as A or as B (not both)
- **Additive truth** `top`: always provable, absorbs context

LLF is a conservative extension of LF. The Pi type remains and interacts with linearity: `Pi x:A. B` is intuitionistic (the argument can be used multiple times in the type), while `A -o B` is linear.

**What linearity adds:** Direct representation of stateful systems. In LF, encoding mutable state requires awkward continuation-passing. In LLF, linear hypotheses naturally model resources that are consumed.

### 1.3 CLF (Concurrent Logical Framework, Watkins-Cervesato-Pfenning-Walker 2002-2004)

CLF = LLF + monad + synchronous connectives. Notation: lambda-Pi-lolli-with-top-{exists-tensor-one-bang}.

```
Types:    A ::= ... | {S}
Sync:     S ::= A1 * A2 | 1 | !A | exists x:A. S
Monadic:  E ::= let {p} = R in E | M
Patterns: p ::= x | p1 * p2 | () | !p | [x, p]
```

Adds to LLF:
- **Monadic type** `{S}`: encapsulates synchronous (forward-chaining) computation
- **Tensor** `A1 * A2`: simultaneous linear resources (inside monad)
- **Unit** `1`: empty resource (inside monad)
- **Bang** `!A`: persistent (reusable) resource (inside monad)
- **Existential** `exists x:A. S`: witness production (inside monad)
- **Monadic expressions** `E`: let-bindings that decompose synchronous results

**The monad is the key architectural innovation.** Outside the monad: backward chaining with backtracking (goal-directed, Prolog-style). Inside the monad: forward chaining with committed choice (data-driven, multiset rewriting). Definitional equality inside the monad identifies computations that differ only in execution order of independent steps.

### 1.4 Summary Table

| Layer | Notation | Adds | Purpose |
|-------|----------|------|---------|
| LF | lambda-Pi | Dependent types (Pi) | Encode syntax + judgments |
| LLF | lambda-Pi-lolli-with-top | Linear types | Encode state |
| CLF | lambda-Pi-lolli-with-top-{exists-tensor-one-bang} | Monad + sync connectives | Encode concurrency |

---

## 2. What Dependent Types Buy You

### 2.1 Type Families Indexed by Terms

The Pi type enables **type families**: types parameterized by values. Classic example:

```
nat : type.
z : nat.
s : nat -> nat.

vec : nat -> type.
vnil : vec z.
vcons : Pi n:nat. nat -> vec n -> vec (s n).
```

Here `vec` is not a single type but a *family* of types indexed by natural numbers. `vec z` is the type of empty vectors, `vec (s (s z))` is the type of 2-element vectors. The type system statically tracks lengths.

Without Pi, `vec` would just be `type` and length constraints would need external predicates or runtime checks.

### 2.2 Adequate Encodings (The Bijection Property)

An LF encoding is **adequate** if there is a compositional bijection between:
- The informal mathematical objects being represented
- The canonical forms of the corresponding LF type

This means every object is represented exactly once, and every LF term of the right type corresponds to a valid object. No junk (spurious terms), no confusion (ambiguous encodings).

**Example: encoding natural deduction for propositional logic.**

```
o : type.                          % propositions
imp : o -> o -> o.                 % implication

nd : o -> type.                    % judgment: "A is provable" -- DEPENDENT TYPE
imp_i : (Pi A:o. Pi B:o.          % for all propositions A, B:
          (nd A -> nd B)           %   given a proof of A yields proof of B
          -> nd (imp A B)).        %   we get a proof of A => B
imp_e : (Pi A:o. Pi B:o.          % modus ponens:
          nd (imp A B) -> nd A     %   proof of A=>B and proof of A
          -> nd B).                %   yields proof of B
```

The type `nd A` is indexed by the proposition `A` -- this is the **judgments-as-types** principle. A term of type `nd A` is a proof of `A`. The Pi type is essential: without it, `nd` cannot be indexed by the proposition, and the type system cannot enforce that `imp_e` receives a proof of `A => B` and a proof of `A` (with matching `A`).

**Adequacy theorem:** There is a bijection between canonical LF terms of type `nd A` and natural deduction derivations of `A`. This is stronger than mere soundness -- it's a full isomorphism.

### 2.3 Judgments-as-Types

The core LF methodology:
1. Syntactic categories become LF types (e.g., `o : type`)
2. Constructors become LF constants (e.g., `imp : o -> o -> o`)
3. **Judgments become type families** (e.g., `nd : o -> type`) -- requires Pi
4. **Inference rules become constants of dependent types** (e.g., `imp_i` with type involving `nd A`)
5. Proof checking reduces to LF type checking

Step 3 is where Pi becomes essential. Without dependent types, judgments cannot be parameterized by their subjects, and the type system cannot enforce that proofs match their conclusions.

### 2.4 Mechanized Metatheory (Twelf's Totality Checker)

Twelf exploits the judgments-as-types methodology for automated metatheory:

1. Encode a formal system as an LF signature
2. Express a metatheorem as a type family relating input and output judgments
3. Write the proof as a set of LF constants (a "logic program")
4. Twelf checks **totality**: coverage (all cases handled), termination (recursive calls decrease), and world-checking (context invariants)

This requires dependent types throughout: the metatheorem statement, the proof terms, and the type-checker that verifies them all use Pi.

### 2.5 What You Lose Without Pi (First-Order Terms + Predicates)

CALC's current system has:
- First-order terms (content-addressed hashes via Store)
- Universal quantification (forall with de Bruijn indices)
- Existential quantification (exists with de Bruijn indices)
- Unification of first-order terms
- Predicate tags (user-defined via dynamic tag registration)

**What this CAN do:**
- Pattern matching on term structure
- Forward/backward chaining over predicates
- First-order unification and instantiation
- Represent and execute most practical systems (EVM, arithmetic, protocols)

**What this CANNOT do without Pi:**
- Express type-level dependencies (type families indexed by values)
- Guarantee adequacy of encodings (no bijection theorem)
- Use the type system to enforce proof correctness
- Mechanize metatheory via totality checking
- Encode polymorphic rules cleanly (e.g., "for any type T, ...")

**Crucial distinction:** CALC can *run* programs over linear resources without Pi. It *cannot verify* that those programs are correct at the type level without Pi. The question is whether CALC needs the latter for its domain.

---

## 3. Implementation Complexity

### 3.1 Type-Checking LF (Hereditary Substitution + Bidirectional Checking)

The canonical forms presentation of LF yields a clean type-checking algorithm:

**Hereditary substitution** replaces ordinary substitution. When substituting `M` for `x` in `N`, any beta-redexes created are immediately reduced. This maintains the invariant that all terms are canonical (beta-normal, eta-long). Termination of hereditary substitution follows from the type of `M` decreasing at each recursive call -- no separate normalization pass needed.

**Bidirectional type checking** splits into two modes:
- **Check** (against a given type): `check(ctx, M, A)` -- for lambdas, pairs
- **Synthesize** (infer the type): `synth(ctx, R) = A` -- for variables, applications, constants

The algorithm is deterministic and decidable. Key rules:
```
check(ctx, lam x. M, Pi x:A. B) = check(ctx + x:A, M, B)
synth(ctx, x) = lookup(ctx, x)
synth(ctx, R M) = let Pi x:A. B = synth(ctx, R) in
                  check(ctx, M, A); return [M/x]B  -- hereditary subst
```

### 3.2 Higher-Order Pattern Unification

Full higher-order unification (Huet) is undecidable and involves branching/backtracking. However, Miller identified the **pattern fragment**: unification problems where every metavariable is applied to distinct bound variables. In this fragment:

- Unification is **decidable**
- Time complexity is **linear** (same as first-order!)
- The algorithm is **deterministic** (no backtracking)
- With de Bruijn indices, it reduces to essentially first-order unification

Practical systems (Twelf, Beluga, Agda) use **dynamic pattern unification**: solve pattern problems eagerly, delay non-pattern problems until more information arrives.

**Comparison with CALC's current first-order unification:**

| | CALC (first-order) | LF (higher-order pattern) |
|---|---|---|
| Decidable | Yes | Yes (pattern fragment) |
| Complexity | Linear | Linear (pattern fragment) |
| Backtracking | No | No (pattern fragment) |
| Lambda terms | No | Yes |
| Type-directed | No | Yes (eta-expansion) |
| Implementation | ~200 LOC | ~500-1000 LOC |

The main additional complexity for higher-order pattern unification: tracking bound variable scopes, performing eta-expansion/contraction guided by types, and implementing the occurs check with respect to binding depth.

### 3.3 Normalization Requirements

LF requires **strong normalization**: every reduction sequence terminates. This is guaranteed by the type system (no general recursion, no fix-points). The canonical forms presentation avoids normalization entirely by only admitting normal forms.

CLF extends this with the monad, where definitional equality identifies computations differing in execution order. This requires a notion of canonical forms for monadic expressions that quotients by concurrent permutations.

### 3.4 What Twelf's Implementation Looks Like

Twelf (Standard ML, ~50k LOC total) implements:
- LF type theory with canonical forms
- Hereditary substitution
- Bidirectional type checking
- Higher-order pattern unification (with constraint delay)
- Logic programming interpretation (backward chaining)
- Totality checker (coverage, termination, worlds)
- Mode checker (input/output analysis)
- Subordination analysis (dead-code-like optimization for types)

The core type checker is relatively compact. The totality/coverage checker is the complex part.

### 3.5 What Beluga Adds

Beluga (OCaml, ~30k LOC) implements:
- LF as the data level (same as Twelf)
- Contextual modal type theory as the reasoning level
- First-class contexts and context schemas
- Higher-order pattern matching (recursive case analysis on LF terms)
- Harpoon interactive proof engine

Beluga's innovation: instead of Twelf's implicit proofs-as-logic-programs, Beluga provides explicit pattern matching over contextual LF objects. More programmer-friendly, but same underlying LF type theory.

### 3.6 Estimated Implementation Effort for CALC

Adding full LF-style dependent types to CALC would require:

1. **Kind system** (~200 LOC): Add `type` and `Pi x:A. K` to the kind level
2. **Dependent function types** (~300 LOC): Extend `Store` with `pi` tag, modify type formation
3. **Hereditary substitution** (~200 LOC): Replace or augment `debruijnSubst`
4. **Bidirectional type checker** (~400 LOC): New module, check/synth modes
5. **Higher-order pattern unification** (~400 LOC): Extend `unify.js` with lambda handling
6. **Canonical forms enforcement** (~200 LOC): Stratify terms into atomic/normal
7. **Type reconstruction** (~500 LOC): Implicit argument inference

**Total estimate: ~2200 LOC**, plus tests and integration. This is a significant but bounded effort.

---

## 4. Alternatives to Full Dependent Types

### 4.1 What CALC Has Now: Simple Types + First-Order Terms

CALC's current type system is essentially untyped at the term level: all formulas have kind `formula`, connectives are `formula -> formula -> formula`, etc. Terms (atoms, predicates) are first-order with no type discipline beyond tag matching.

Quantifiers (forall/exists) use de Bruijn indices and handle binding, but there are no type families, no dependent functions, no kind-level indexing.

### 4.2 Refinement Types (Lighter Than Full Pi)

Refinement types add subtyping constraints to existing types without full dependency:

```
% Instead of dependent type:  nd : o -> type
% Refinement type:            nd : type  refined by  {nd_imp, nd_and, ...}
```

Lovas-Pfenning (2009) showed that refinement types for LF are decidable even with intersection types. They provide proof irrelevance (erased at runtime) and finer type distinctions without the full complexity of Pi.

**Relevance to CALC:** A refinement system could add type constraints to predicates (e.g., "this predicate only applies to natural numbers") without dependent function spaces. This could catch many errors that Pi catches, at lower implementation cost.

### 4.3 Indexed Families Without Full Dependency (GADTs)

GADTs (Generalized Algebraic Data Types) allow constructors to refine the type index:

```
% GADT-style (no Pi, but indexed):
step : state -> state -> type.
step_add : step (running S) (running S').  -- S, S' are specific states
```

This gives some of Pi's power (type-level tracking of values) without dependent function spaces. The type indices are restricted to constructor patterns rather than arbitrary terms.

**Relevance to CALC:** CALC's tagged predicate system (`Store.put('step', [s1, s2])`) already resembles GADTs structurally. The predicates act as indexed families. What's missing is type-level enforcement that the indices satisfy certain constraints.

### 4.4 Sort Systems (Twelf's Subordination)

Twelf's subordination analysis determines which type families can depend on which:

```
% nat is subordinate to nat and vec
% o is NOT subordinate to nat
% Therefore nat values can never appear inside propositions
```

This is a coarse but useful analysis. It partitions the type namespace into "sorts" with restricted interaction. CALC's `PRED_BOUNDARY` already implements a binary version of this (built-in tags vs. user predicates).

A richer sort system could give CALC some benefits of dependent types (preventing nonsensical type combinations) without Pi.

### 4.5 The Ceptre Precedent: Full System Without Pi

Ceptre (Chris Martens, 2015) is the strongest evidence that dependent types are not required for practical linear logic programming:

- Ceptre drops Pi entirely (simple types only)
- Uses first-order terms with predicates
- Successfully models game mechanics, interactive narratives, process algebras
- Has stages for structured computation
- Forward chaining with committed choice

**What Ceptre sacrifices:** No adequacy theorems, no mechanized metatheory, no type-level enforcement of invariants. Programs can be ill-formed in ways the type system cannot catch.

**What Ceptre keeps:** All the operational power. Programs run correctly if written correctly. The type system provides basic arity/sort checking.

### 4.6 Can CALC Get Most Benefits Without Full Pi?

**Yes, for its current domain (financial logic, EVM, protocol analysis).**

CALC's forward engine operates on multiset rewriting rules over linear resources. The rules are first-order patterns with predicate matching. The proofs are execution traces, not formal derivations requiring type-level correctness certificates.

A **graduated approach** could provide increasing type safety:

| Level | What | Implementation Cost | Benefit |
|-------|------|-------------------|---------|
| 0 (current) | Untyped terms, tag matching | Done | Operational correctness |
| 1 | Sort system (multi-sort boundary) | ~200 LOC | Prevent nonsense combinations |
| 2 | Refinement types on predicates | ~500 LOC | Constrain predicate arguments |
| 3 | Indexed families (GADT-like) | ~800 LOC | Type-track state invariants |
| 4 | Full Pi types | ~2200 LOC | Adequate encodings, metatheory |

---

## 5. What CALC Specifically Needs from CLF Compatibility

### 5.1 Encoding Inference Rules as LF Signatures

In CLF, inference rules are LF constants with dependent types:

```
% CLF-style rule encoding (with Pi):
tensor_r : Pi A:o. Pi B:o. Pi G:ctx. Pi D:ctx. Pi D':ctx.
           nd G D A -> nd G D' B -> nd G (merge D D') (tensor A B).
```

Without Pi, CALC encodes rules as descriptors (first-order data):
```javascript
// CALC-style rule encoding (without Pi):
{ connective: 'tensor', side: 'right', arity: 2,
  contextSplit: true, premises: [...] }
```

**Both work operationally.** The CLF encoding additionally guarantees that any well-typed rule application is valid (type safety = soundness). CALC's encoding relies on the rule interpreter and kernel (L1) for runtime verification.

### 5.2 Representing Proof Terms

CLF proof terms are LF terms of the appropriate type. CALC proof terms are `ProofTree` objects (data structures, not typed terms). Both represent the same information; CLF's are intrinsically typed (ill-typed proof terms are impossible), CALC's are extrinsically verified (the kernel checks them).

### 5.3 Type-Checking Forward Chaining Derivations

In Celf, forward chaining produces well-typed monadic terms. Each step is type-checked. In CALC, forward chaining produces execution traces verified by the prover kernel.

**For CALC's current use cases (EVM, financial logic):** Runtime verification suffices. The rules are fixed and well-tested. The system is not generating novel proofs that need trust guarantees.

**Where Pi would matter:** If CALC becomes a platform for users to define arbitrary logics (like Twelf), then type-level guarantees become important. User-defined rules could be malformed, and Pi types would catch this at definition time rather than at runtime.

### 5.4 The Domain Question

CALC's current domains:
- **EVM analysis:** 44 forward rules, arithmetic FFI, execution traces. All rules are ground and well-tested. No dependent types needed.
- **Financial logic (multisig, authorization):** Predicate-based, first-order. Correctness comes from the logic design, not type-level enforcement.
- **Protocol verification:** Could benefit from type-level state tracking (e.g., "this message can only be sent in state S3"). This is where indexed families or dependent types would add value.

**Verdict:** CALC does not need Pi for its current operational use cases. Pi becomes valuable if CALC evolves into a framework for defining and verifying arbitrary logics, or if it needs to provide formal correctness certificates for its derivations.

---

## 6. Recent Developments (2020-2026)

### 6.1 Beluga and Harpoon (McGill, Pientka et al.)

Beluga uses contextual modal type theory (CMTT) over LF as its foundation:
- **Harpoon** (2021): Interactive proof engine with tactics, automation for trivial subgoals
- **Focusing calculus** (Schwartzentruber et al., 2023): Sound and complete focusing for Beluga's two-level logic
- **Contextual refinement types** (Gaulin, 2023): Datasort-style subtyping on context schemas
- **Polymorphic contexts** (2023): Lambda-forall-box calculus extending CMTT with parametric polymorphism over contexts

Beluga's approach is relevant to CALC: it separates the data level (LF) from the computation level (pattern matching, recursion). CALC could adopt a similar two-level structure without full Pi at the data level.

### 6.2 Dedukti and Lambdapi (INRIA, Deducteam)

Dedukti extends LF with **rewriting modulo theory**: user-defined rewrite rules on types, enabling compact encoding of richer type theories (Calculus of Constructions, HOL, etc.).

- **Impredicativity + cumulativity** (FSCD 2024): Solved a longstanding open problem in encoding universe hierarchies
- **BiTTs** (Felicissimo): Customized bidirectional typing for the framework
- **Proof interoperability:** Translating proofs between Lean, Coq, HOL Light via Dedukti as an intermediate

**Relevance to CALC:** Dedukti shows that rewriting rules can substitute for some uses of dependent types. CALC's rule descriptors + engine already function as a rewriting system. Dedukti's approach of "LF + rewriting" is a middle ground between CALC's current system and full CLF.

### 6.3 Other Developments

- **Dependent Types Simplified** (Bice, 2025): Proposes a simplified presentation of dependent type theory
- **Linear Dependent Type Theory** (2020): Explores interaction between linearity and dependency for quantum programming
- **First-Order Logic with Dependent Types** (DFOL, Rabe): Shows DFOL has same expressivity as FOL, suggesting dependency doesn't always add power at the first-order level

---

## 7. Recommendation for CALC

### 7.1 Do Not Implement Full Pi Types Now

**Rationale:**
1. CALC's operational domains (EVM, financial logic) don't require type-level enforcement
2. The forward engine's correctness comes from the prover kernel (L1), not from typing
3. Implementation cost (~2200 LOC) is high relative to the benefit for current use cases
4. Ceptre demonstrates that practical linear logic programming works without Pi

### 7.2 Graduated Path Forward

**TODO_0011.Stage_1 -- Sort System Enhancement** (low cost, moderate benefit)
- Extend `PRED_BOUNDARY` to a multi-level sort system
- Define which predicate sorts can appear as arguments to which connectives
- Catches nonsensical formula combinations at parse time
- Estimated: ~200 LOC

**TODO_0011.Stage_2 -- Predicate Arity/Signature Checking** (low cost, high benefit)
- Each predicate tag declares its expected argument count and sorts
- Type-check at rule compilation time (`compile.js`)
- Catches malformed rules before execution
- Estimated: ~300 LOC

**TODO_0011.Stage_3 -- Indexed Predicate Families** (moderate cost, moderate benefit)
- Allow predicates to declare index constraints
- E.g., `step : state -> state -> pred` with sort constraints on arguments
- GADT-like type refinement without full Pi
- Estimated: ~800 LOC

**TODO_0011.Stage_4 -- Full Pi Types** (high cost, high benefit for framework use)
- Only if CALC becomes a general logical framework
- Requires: kind system, hereditary substitution, bidirectional checking, higher-order pattern unification
- Enables: adequate encodings, mechanized metatheory, Twelf-like functionality
- Estimated: ~2200 LOC

### 7.3 The Decision Criterion

Implement Pi when CALC needs to answer: "Is this user-defined logic sound?" Until then, the prover kernel + runtime verification is sufficient.

---

## 8. Key Technical References

- [A Framework for Defining Logics](https://homepages.inf.ed.ac.uk/gdp/publications/Framework_Def_Log.pdf) -- Harper, Honsell, Plotkin (1993). The original LF paper.
- [A Linear Logical Framework](https://www.cs.cmu.edu/~iliano/papers/ic02.pdf) -- Cervesato, Pfenning (2002). LLF = LF + linearity.
- [CLF: A Dependent Logical Framework for Concurrent Computations](https://www.cs.cmu.edu/~fp/papers/clf04.pdf) -- Watkins et al. (2004). The CLF paper.
- [On Equivalence and Canonical Forms in the LF Type Theory](https://www.cs.cmu.edu/~rwh/papers/lf-theory/lf-theory.pdf) -- Harper, Pfenning. Canonical forms + hereditary substitution.
- [Mechanizing Metatheory in a Logical Framework](https://www.cs.cmu.edu/~rwh/papers/mech/jfp07.pdf) -- Harper, Licata (2007). Twelf's totality checker.
- [Optimizing Higher-Order Pattern Unification](https://www.cs.cmu.edu/~fp/papers/optunif03.pdf) -- Pfenning et al. Miller patterns in practice.
- [Refinement Types as Proof Irrelevance](https://www.cs.cmu.edu/~fp/papers/tlca09.pdf) -- Lovas, Pfenning (2009). Lightweight alternative to Pi.
- [Beluga: Programming with Dependent Types](https://www.cs.mcgill.ca/~bpientka/papers/flops.pdf) -- Pientka. Contextual modal type theory.
- [Ceptre: A Language for Modeling Generative Interactive Systems](https://www.cs.cmu.edu/~cmartens/ceptre.pdf) -- Martens (2015). CLF without Pi.
- [Logical Frameworks -- A Brief Introduction](https://www.cs.cmu.edu/~fp/papers/mdorf01.pdf) -- Pfenning. Best introductory overview.
- [Dedukti: a Logical Framework based on the lambda-Pi-Calculus Modulo Theory](https://arxiv.org/abs/2311.07185) -- Assaf et al. LF + rewriting.
- [A Tutorial Implementation of Dynamic Pattern Unification](https://adam.gundry.co.uk/pub/pattern-unify/) -- Gundry et al. Practical implementation guide.
- [Checking Dependent Types with Normalization by Evaluation](https://davidchristiansen.dk/tutorials/implementing-types-hs.pdf) -- Christiansen. Implementation tutorial.
