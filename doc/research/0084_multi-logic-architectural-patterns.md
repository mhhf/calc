---
title: "Multi-Logic Architectural Patterns: Ceptre, Celf, Twelf/Beluga, Isabelle, Maude, LF"
created: 2026-03-04
modified: 2026-03-04
summary: "Concrete implementation patterns for multi-calculus / multi-logic support across six systems, focused on term stores, connective roles, capability detection, structural rules, and minimal logic interfaces."
tags: [architecture, logical-framework, clf, Ceptre, Celf, multi-logic, adjoint-logic, implementation, prover-architecture, research]
category: "Implementation"
---

# Multi-Logic Architectural Patterns

Survey of how six systems handle multiple logics / multi-calculus support.
Focused on concrete architectural patterns applicable to CALC's modular refactor (TODO_0066).

---

## 1. Ceptre (Martens)

**Source:** SML, [github.com/chrisamaphone/interactive-lp](https://github.com/chrisamaphone/interactive-lp)

### Architecture

Ceptre is a forward-chaining linear logic programming language with **stages** as the primary multi-mode mechanism. All execution is forward chaining (no backward mode).

### Stage System

Stages are **named rule subsets** that partition the forward rule set:

```ceptre
stage setup = {
  settle : init_settlement P * available_land X -o has_settlement P X.
}
stage roll = {
  roll_die : die -o rolled (random 6).
}
```

**Key properties:**
- Rules in different stages share the **same global state** (one multiset of facts)
- A stage runs to **quiescence** (no more rules apply), then transitions
- Transitions are themselves rules over the `qui` (quiescence) and `stage` predicates:

```ceptre
setup_to_roll : qui * stage setup -o stage roll * die.
roll_to_prod  : qui * stage roll  -o stage produce.
```

### Persistent vs Linear Predicates

Predicates are classified at declaration time:
- **Linear** (default): consumed by rules
- **Persistent** (`$` prefix in rules): survive consumption, always available

```ceptre
$on_team Player Team  % persistent — reusable across rules
holds Player Resource  % linear — consumed
```

### Minimal Interface: What a "Stage" Must Provide

1. A name
2. A set of rules (each rule: linear antecedents, persistent antecedents, consequent)
3. Classification of each predicate as persistent or linear

### Relevance to CALC

- **Global shared state across stages:** one FactSet, different rule subsets active per stage. CALC already has `calc.forwardRules` — stages would be a partition of this array.
- **Quiescence as stage boundary:** CALC's `forward.run()` already detects quiescence. Stage transitions = swap active rule set + fire transition rule.
- **No capability detection:** all stages use the same execution mode (forward). No backward chaining.
- **No separate term store per stage:** single global multiset throughout.

---

## 2. Celf (Schack-Nielsen & Schurmann)

**Source:** SML, [github.com/clf/celf](https://github.com/clf/celf)

### Architecture

Celf implements CLF (Concurrent LF). The central pattern is **dual-mode proof search** triggered by type synchronicity.

### Dual-Mode Execution

```
Outside monad {}: backward chaining (goal-directed, backtracking)
Inside monad {}:  forward chaining (committed choice, multiset rewriting)
```

**Mode switch mechanism (OpSem.sml):** The `solve` function handles backward search. When it encounters a monadic type `TMonad S`:

```sml
| TMonad S => forwardChain (!fcLimit, ctx, S,
    fn (E, ctxo) => sc (Monad' E, ctxo))
```

This is a **hard-coded pattern match** on the `TMonad` constructor. No descriptor lookup, no mode theory — just a case in the search function.

### Context Management (Context.sml)

Celf tracks three modalities per context entry:

```sml
datatype modality = INT | AFF | LIN
type 'a context = (string * 'a * modality option) RAList.ralist
```

- **INT** (intuitionistic): weakening + contraction
- **AFF** (affine): weakening only
- **LIN** (linear): no structural rules

Key operations:
- `ctxIntPart`: extract only persistent resources
- `ctxAffPart`: extract persistent + affine
- `ctxAddJoin`: merge contexts, error if linear variable used asymmetrically
- Linear resource consumption: `linDiff` computes consumed variables between input/output contexts

### How Persistent Resources Work

In hypothesis selection: `if modality=INT then ctx else removeHyp(ctx, k)` — persistent (INT) variables are preserved in context after use, linear/affine are removed.

### Term Store

**Global signature** (SignaturTable.sml): one global mutable table mapping names to types. All declarations share one namespace. No per-logic or per-mode stores.

### Minimal Interface: What the Monad Boundary Provides

1. Type classification (synchronous vs asynchronous) triggers mode switch
2. Context partitioning (linear consumed, persistent preserved)
3. Quiescence detection (forward chaining terminates when no rules fire)
4. Result return to backward prover via continuation

### Relevance to CALC

- **Celf hardcodes the mode switch in `solve`** — CALC's descriptor + mode theory approach (TODO_0066 D2.5) is strictly more general
- **Three modalities in context entries** — CALC currently has two zones (linear/cartesian). Adding affine = adding a zone with `{ weakening: true, contraction: false }`, which aligns with the mode theory design
- **Global signature, not per-logic store** — confirms CALC's shared Store approach
- **No capability detection** — the mode switch is structural (type-driven), not capability-based

---

## 3. Twelf / Beluga

### Twelf

**Source:** SML, [github.com/standardml/twelf](https://github.com/standardml/twelf)

Twelf implements LF (Edinburgh Logical Framework). Object logics are encoded as **LF signatures** using the judgments-as-types methodology.

### Encoding Pattern

An object logic is encoded by declaring:
1. **Types** for syntactic categories (e.g., `tp : type`, `tm : type`)
2. **Constants** for constructors (e.g., `arr : tp -> tp -> tp`)
3. **Type families** for judgments (e.g., `of : tm -> tp -> type`)
4. **Constants** for inference rules (e.g., `of/app : of E1 (arr T1 T2) -> of E2 T1 -> of (app E1 E2) T2`)

**Structural rules come free from LF.** Weakening, exchange, substitution for hypothetical judgments are inherited from LF's binding mechanism (HOAS). The object logic does NOT declare structural rules — LF provides them.

### Multiple Logics

Twelf handles multiple logics by having **separate signature files**. Each file declares a new set of types and constants. There is no module system in core Twelf — signatures are loaded sequentially and share one global namespace. (A module system was proposed by Rabe/Schurmann but not widely adopted.)

**Adequacy** is the key property: the encoding must be a compositional bijection between the object logic and LF terms. Proving adequacy ensures the encoding faithfully represents the logic.

### Beluga

**Source:** OCaml, [github.com/Beluga-lang/Beluga](https://github.com/Beluga-lang/Beluga)

Beluga extends LF with **contextual modal type theory**. Key differences from Twelf:
- **Explicit contexts:** `[g |- M]` — terms carry their context
- **Context variables:** abstract over concrete contexts
- **Computation language:** recursive functions over contextual objects

For multi-logic: Beluga's explicit contexts mean different logics can use different context schemas. The LF layer (data) is shared; the computation layer (reasoning) can be parameterized by context schema.

### Relevance to CALC

- **Judgments as types:** CALC's descriptors play a similar role — they encode what inference rules do without hardcoding logic-specific behavior
- **Structural rules from the framework:** LF provides weakening/exchange/substitution. CALC's mode theory provides structural rules per mode. Same principle: the framework, not the object logic, determines structural behavior.
- **Global namespace, no per-logic stores**
- **No capability detection** — LF signatures don't declare "I support forward execution"

---

## 4. Isabelle

**Source:** SML/Scala, [isabelle.in.tum.de](https://isabelle.in.tum.de)

### Architecture

Isabelle implements a **metalogic (Pure)** in which object logics (HOL, FOL, ZF) are axiomatized. This is the most mature multi-logic architecture.

### Pure Metalogic

Pure provides exactly three meta-connectives:
- `==>` (meta-implication)
- `!!` (meta-universal quantification, written `\<And>`)
- `==` (meta-equality)

Plus one type: `prop` (meta-propositions).

### Object Logic Definition

An object logic embeds into Pure via a **judgment constant**:

```isabelle
typedecl bool                          (* object-level truth values *)
judgment Trueprop :: "bool => prop"     (* lifts bool into Pure prop *)
```

Then connectives are axiomatized:

```isabelle
axiomatization
  imp :: "bool => bool => bool"  (infixr "-->" 25)
where
  impI: "(P ==> Q) ==> Trueprop (P --> Q)"
  impE: "[| Trueprop (P --> Q); Trueprop P |] ==> Trueprop Q"
```

**Remarkably little is needed.** A full HOL requires only:
1. A boolean type
2. Object-level implication (defined via meta-implication)
3. Object-level universal quantifier (defined via meta-quantification)
4. Falsity (defined as `\<forall>p. p`)
5. All other connectives derive from these

### Theory Graph

Theories form an **acyclic directed graph**. Each theory:
- Has a name
- Imports parent theories
- Declares types, constants, axioms
- Carries a certificate (unique ID for sub-theory checks)

The `thm` abstract type carries a theory certificate. You cannot combine theorems from incompatible theories.

### Shared Kernel, Different Logics

All object logics share:
- The same kernel (abstract `thm` type, ~2500 LOC)
- The same term representation (`term` datatype)
- The same unification, rewriting, simplification infrastructure
- The same proof language (Isar)

Each object logic provides:
- Its own axioms (via `axiomatization`)
- Its own constants and types
- Its own tactics and proof methods (ML functions producing `thm` values)

### Connective Roles

Isabelle does **not** have a notion of "this connective is the product" or "this connective is the exponential." Each object logic axiomatizes its own connectives. The kernel doesn't know what `&` or `|` mean — it only knows meta-implication, meta-quantification, and meta-equality. Simplifier rules and tactics are registered per-logic.

### Structural Rules

Structural rules are **implicit in Pure's meta-quantification**. Pure's `!!` already has weakening (you can ignore a universally quantified variable) and exchange. Object logics don't declare structural rules — they inherit them from Pure.

For logics that need different structural rules (e.g., linear logic in Isabelle), the structural rules must be encoded explicitly in the axioms — Pure doesn't provide a way to restrict its own structural rules per-logic.

### Relevance to CALC

- **Shared term representation + kernel, per-logic axioms:** maps to CALC's shared Store + per-calculus `.rules`/`.calc` files
- **Theory graph with certificates:** CALC could use a similar pattern — each calculus is a node, with dependencies
- **No connective role detection:** Isabelle's automation (simp, auto) is configured per-logic via registration, not introspection. CALC's `polarity` and `contextFlow` in descriptors serve a similar role — they're registered metadata, not intrinsic properties of the kernel.
- **Structural rules from the framework, not the logic:** validates CALC's mode theory approach where structural rules come from the mode, not from the calculus definition

---

## 5. Maude

**Source:** C++, [github.com/maude-lang/Maude](https://github.com/maude-lang/Maude)

### Architecture

Maude implements **rewriting logic**. The module system is the primary multi-theory mechanism.

### Module Types

Three module types with increasing power:

| Type | Keyword | Contains | Semantics |
|------|---------|----------|-----------|
| Functional | `fmod` | sorts, operators, equations | Confluent + terminating |
| System | `mod` | + rewrite rules | Non-deterministic |
| Object-oriented | `omod` | + classes, messages | Distributed objects |

### Theories (Interfaces)

Theories define the **minimal interface** for parameterized modules:

```maude
fth TRIV is
  sort Elt .
endfth

fth MONOID is
  sort M .
  op e : -> M .
  op _*_ : M M -> M [assoc id: e] .
endfth
```

A theory declares: sorts, operators, and their equational properties (associativity, commutativity, identity). It does NOT provide implementations.

### Views (Mappings)

Views map between theory requirements and module implementations:

```maude
view NatAsMonoid from MONOID to NAT is
  sort M to Nat .
  op e to 0 .
  op _*_ to _+_ .
endv
```

### Parameterized Modules

```maude
fmod LIST{X :: TRIV} is
  sort List{X} .
  op nil : -> List{X} .
  op _::_ : X$Elt List{X} -> List{X} .
endfm
```

Instantiation: `LIST{NatAsMonoid}` — the view maps the parameter theory to the actual module.

### Import Modes

Three import modes with semantic guarantees:

| Mode | Guarantee |
|------|-----------|
| `protecting` | No junk (new elements), no confusion (new equalities) |
| `extending` | No confusion (junk allowed) |
| `including` | No guarantees |

These are **promises by the user** — Maude does not check them.

### META-LEVEL: Modules as Data

Maude's reflection capability reifies modules as terms:

```maude
op metaReduce  : Module Term -> ResultPair .
op metaRewrite : Module Term Bound -> ResultPair .
op metaApply   : Module Term Qid Substitution Nat -> ResultTriple .
```

Modules (including their sorts, operators, equations, rules) are represented as **terms in the META-LEVEL sort hierarchy**. You can programmatically inspect and transform module structure.

### Relevance to CALC

- **Theory = minimal interface:** maps to what a CALC "calculus definition" must provide (sorts/types, connectives/operators, rules, structural properties)
- **View = mapping between theory and implementation:** CALC could use views to map between abstract connective roles and concrete implementations (e.g., "the tensor in this logic is `*`")
- **Import modes (protecting/extending/including):** useful pattern for calculus extension — "this logic extends ILL with new connectives, protecting existing ones"
- **Modules as data (META-LEVEL):** CALC already has `calc` objects with `calc.rules`, `calc.forwardRules`, etc. This is essentially the same pattern — calculus descriptions are runtime data, not hardcoded behavior
- **Separate structural properties per module:** each Maude module declares its own equational axioms (assoc, comm, id). Maps to CALC's per-mode structural rules

---

## 6. LF Frameworks: General Pattern

### The Minimal Interface a Logic Must Provide

Across all LF-family systems (Twelf, Beluga, Celf), the encoding of an object logic requires:

1. **Types for syntactic categories** (propositions, terms, contexts)
2. **Constructors for each connective** (tensor, loli, bang, etc.)
3. **Type families for judgments** (typing, evaluation, reduction)
4. **Constants for inference rules** (one per rule, with dependent types encoding premises)

Structural rules (weakening, exchange, substitution) come from the framework, not the logic.

### Adequacy: The Correctness Criterion

An encoding is adequate iff there is a **compositional bijection** between:
- Objects of the original logic
- Canonical LF terms of the corresponding type

This means LF substitution correctly models object-logic substitution.

---

## 7. Cross-Cutting Analysis

### Q1: Global Term Store vs Per-Logic Stores?

**Every system uses a global shared store.**

| System | Store | Sharing |
|--------|-------|---------|
| Ceptre | Global multiset of facts | Shared across stages |
| Celf | Global SignaturTable | Shared across backward/forward |
| Twelf | Global signature | Shared across all encodings |
| Isabelle | Global `term` datatype | Shared across all object logics |
| Maude | Per-module sort/operator namespace, but META-LEVEL can access all | Module-scoped but composable |

**Pattern for CALC:** Keep one shared Store. Different calculi register different tags (connectives) in the same Store. Tag namespace separation (PRED_BOUNDARY) already handles this.

### Q2: Connective Roles?

**No system uses intrinsic connective role detection.** Instead:

| System | How roles are assigned |
|--------|----------------------|
| Ceptre | Implicit: all connectives are linear logic connectives by construction |
| Celf | Implicit: CLF type grammar determines synchronous/asynchronous |
| Twelf | Explicit: the encoding declares what each constant represents |
| Isabelle | Explicit: axioms + registered simp/auto rules |
| Maude | Explicit: operator attributes (assoc, comm, id) declared per operator |

**Pattern for CALC:** Connective roles come from the **calculus definition** (`.calc` file + `.rules` file), not from introspection. The descriptor's `polarity`, `contextFlow`, `invertible` fields ARE the role declaration. This is already the correct design.

### Q3: Capability Detection?

**No system uses "this logic supports forward execution" style capability flags.** Instead:

| System | How capabilities are determined |
|--------|-------------------------------|
| Celf | Type structure: monadic types trigger forward, non-monadic stay backward |
| Ceptre | Everything is forward; stages select rule subsets |
| Isabelle | Tactics/methods registered per-logic; kernel doesn't know about automation |
| Maude | Module type (fmod/mod/omod) determines available operations |

**Pattern for CALC:** Mode theory determines capabilities. If a calculus has a `forward` mode with a shift connective, it supports forward execution. If not, it's backward-only. The mode theory IS the capability declaration.

### Q4: Different Structural Rules Per Logic?

| System | How structural rules vary |
|--------|--------------------------|
| Ceptre | Fixed (linear for facts, persistent for $-prefixed) |
| Celf | Per-entry modality (INT/AFF/LIN) in context |
| Twelf | Inherited from LF (always weakening + exchange) |
| Isabelle | Inherited from Pure (always weakening + exchange); linear must be encoded |
| Maude | Per-module: equations + attributes determine equational properties |

**Pattern for CALC:** Per-mode structural rules (TODO_0066 Decision 4). Each mode declares `{ weakening, contraction }`. This is more flexible than Celf's per-entry modality (which is fixed at declaration time) and more explicit than Isabelle's (which can't restrict structural rules).

### Q5: Minimal Interface a Logic Must Provide?

Synthesizing across all systems:

| Component | Purpose | CALC Equivalent |
|-----------|---------|----------------|
| Type/sort declarations | Syntactic categories | `.calc` connective definitions |
| Constructors/operators | Connective symbols | Store tags (registered at load) |
| Inference rules | How to decompose/compose | `.rules` descriptors |
| Structural properties | Weakening, contraction, exchange | Mode theory `structural` field |
| Polarity / sync classification | Focusing behavior | Descriptor `polarity` + `contextFlow` |
| Judgments | What counts as a proposition | `Trueprop`-style (implicit in CALC: sequent structure) |

---

## 8. Patterns Applicable to CALC Phase 4

### Pattern 1: Calculus-as-Data (Maude + Isabelle)

A calculus definition is a **runtime data structure**, not hardcoded behavior:

```javascript
const calculus = {
  name: 'ILL',
  connectives: { tensor: {...}, loli: {...}, bang: {...}, ... },
  rules: { tensor_r: descriptor, tensor_l: descriptor, ... },
  modeTheory: { modes: {...}, shifts: [...] },
  structural: { copy: { from: 'cartesian', to: 'linear' } },
  polarity: { tensor: 'positive', loli: 'negative', ... }
};
```

CALC already does this. The `.calc` + `.rules` files produce exactly this structure. TODO_0066's mode theory adds the missing piece (modes + shifts).

### Pattern 2: Stages as Rule Partitions (Ceptre)

For multi-phase forward execution, partition `forwardRules` by stage:

```javascript
const stages = {
  deploy: forwardRules.filter(r => r.stage === 'deploy'),
  execute: forwardRules.filter(r => r.stage === 'execute'),
};
// Stage transitions via quiescence + backward orchestration (TODO_0066 Phase 2)
```

This is strictly weaker than CALC's planned monad-based orchestration (TODO_0066 Phase 2.3, monad_l for multi-phase). Ceptre's stages are subsumed by backward reasoning between forward phases.

### Pattern 3: Mode Switch via Type/Descriptor (Celf)

Celf hardcodes `TMonad S => forwardChain(...)` in `solve`. CALC generalizes this via `modeShift` field in descriptors. The pattern is the same: when proof search encounters a shift connective, transfer control to the target mode's search strategy.

### Pattern 4: Structural Rules from Mode, Not Logic (Isabelle + Celf)

Isabelle: Pure provides weakening/exchange; object logics inherit them.
Celf: Modality annotations (INT/AFF/LIN) determine per-entry structural rules.
CALC (TODO_0066): Mode theory `{ structural: { weakening, contraction } }` per mode.

CALC's approach is the cleanest: structural rules are data in the mode theory, not inherited from a fixed metalogic (Isabelle) or per-entry annotations (Celf).

### Pattern 5: Theory/View for Calculus Extension (Maude)

For a future multi-calculus scenario:

```javascript
// Theory: what a "multiplicative logic" must provide
const multiplicativeTheory = {
  requires: {
    sorts: ['prop'],
    connectives: [
      { role: 'tensor', arity: 2 },
      { role: 'unit', arity: 0 },
    ],
    rules: ['tensor_r', 'tensor_l', 'unit_r', 'unit_l'],
  }
};

// View: ILL satisfies the multiplicative theory
const illMultiplicativeView = {
  theory: 'multiplicative',
  module: 'ILL',
  mapping: {
    tensor: 'tensor',   // ILL's tensor IS the multiplicative tensor
    unit: 'one',        // ILL's one IS the multiplicative unit
  }
};
```

This is aspirational — CALC doesn't need this yet. But if CALC ever supports classical linear logic alongside ILL, views would map between their shared connective vocabulary.

### Pattern 6: Global Store with Tag Namespace (All Systems)

Every system uses a single global term representation. CALC's content-addressed Store with tag-based namespace separation (PRED_BOUNDARY) is already the right design. Multiple calculi would register different tag ranges. The Store is calculus-agnostic; tags carry calculus-specific meaning.

---

## 9. Implications for TODO_0066

The survey confirms TODO_0066's design decisions:

1. **Decision 4 (2-mode adjoint):** Validated by Celf's dual-mode pattern, but CALC's descriptor-based approach is more extensible than Celf's hardcoded pattern match.

2. **Decision 1 (one code path + hooks):** No surveyed system has parallel core/optimized implementations. All use one code path. Isabelle separates kernel from tactics via the abstract `thm` type, but doesn't duplicate code.

3. **Mode theory as data:** Maude's module-as-data pattern (META-LEVEL) and Isabelle's theory graph confirm this approach. Calculus descriptions should be runtime data, not hardcoded control flow.

4. **Shared Store:** Universal pattern. No system partitions its term representation per logic.

5. **Structural rules from mode theory:** Validated by Isabelle (from Pure) and Celf (from modality). CALC's per-mode approach is a clean generalization.

**What CALC does differently from all surveyed systems:** descriptor-driven rule interpretation. No surveyed system uses a generic descriptor format that encodes connective behavior (arity, side, polarity, contextFlow, modeShift) as data. Celf and Ceptre hardcode connective behavior in ML pattern matches. Isabelle axiomatizes. Maude uses equational attributes. CALC's descriptor approach is more uniform and machine-manipulable.
