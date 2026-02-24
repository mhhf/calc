---
title: "Hypersequent Classical Processes: CLL, Session Types, and Deadlock-Free Concurrency"
created: 2026-02-24
modified: 2026-02-24
summary: "Deep analysis of HCP (Hypersequent Classical Processes) — its relationship to CP, CLL, and ILL — with a concrete assessment of what CALC would gain and lose from hypersequent extensions, session-typed forward execution, and deadlock-free concurrency modeling."
tags: [HCP, classical-linear-logic, session-types, hypersequents, deadlock-freedom, parallel-composition, mix-rule, CP, pi-calculus, proof-as-process, duality]
category: "Proof Theory"
---

# Hypersequent Classical Processes: CLL, Session Types, and Deadlock-Free Concurrency

---

## 1. What HCP Is

### 1.1 The Problem HCP Solves

The "proofs as processes" paradigm (Abramsky 1994, Bellin & Scott 1994) establishes a correspondence between linear logic proofs and concurrent processes. Wadler's CP (Classical Processes, ICFP 2012) made this precise: CLL proofs are session-typed pi-calculus processes, cut elimination is communication, and deadlock freedom follows from cut elimination.

But CP has a fundamental mismatch: **the pi-calculus operator for parallel composition (`P | Q`) does not correspond to any rule of linear logic.** In CP, parallel composition is fused with channel creation inside the cut rule. This conflation means:

1. Two independent processes cannot be typed without connecting them via a shared channel.
2. The process topology is forced to be **tree-structured** (every composition creates a new channel binding).
3. The operational semantics diverge from standard pi-calculus intuitions about independence.

HCP (Hypersequent Classical Processes), introduced by Kokke, Montesi, and Peressotti (2019), solves this by extending CLL's proof theory with **hypersequents** -- multisets of sequents separated by `|`. The `|` internalizes parallel composition as a structural feature of the proof system, not an ad-hoc process combinator.

### 1.2 The CP to HCP Evolution

| | CP (Wadler 2012) | HCP (Kokke et al. 2019) |
|---|---|---|
| **Logic** | CLL (one-sided sequent calculus) | CLL + hypersequents |
| **Parallel composition** | Fused with cut: `(nu xy)(P \| Q)` | Separate: `P \| Q` via H-MIX |
| **Process topology** | Tree-structured only | DAG / graph topologies |
| **Typing judgment** | Single sequent `P |- Gamma` | Hypersequent `P |- G1 \| G2 \| ... \| Gn` |
| **Deadlock freedom** | From cut elimination | From hypersequent structure + cut elimination |
| **Operational semantics** | Non-standard (no free parallel composition) | Standard pi-calculus with mix |
| **Properties** | Subject reduction, progress, termination | Same, plus fully abstract LTS semantics |

### 1.3 The Three-Way Correspondence

HCP maintains and extends the correspondence:

```
Propositions       <-->  Session Types     <-->  Process Behavior
-----------------------------------------------------------------
A tensor B                send A, continue B       output
A par B                   receive A, continue B     input
A oplus B                 select branch             internal choice
A & B                     offer choice              external choice
!A                        server (replicated)       replication
?A                        client                    dereliction
A^perp                    dual session type         dual endpoint
cut                       channel connection        communication
mix                       independent parallel      independence
hypersequent |            parallel composition      P || Q
```

### 1.4 What Hypersequents Add

A **hypersequent** is a multiset of sequents: `G1 | G2 | ... | Gn`. In HCP, each component `Gi` is an environment (mapping channel names to types). The `|` separator records that the processes typed by different components are **independent** -- they share no channels and do not communicate.

This gives the proof system an explicit representation of parallelism that plain sequent calculus lacks. Two key rules operate on the hypersequent structure:

- **H-MIX**: `G |- P` and `H |- Q` implies `G | H |- P || Q` -- compose two independent processes.
- **H-CUT**: Takes a hypersequent where two components share a channel name (with dual types) and merges them, connecting the processes via that channel. This is the standard cut rule, but it operates **across** hypersequent components.

The separation between MIX (independence) and CUT (connection) is the key insight: in CP, these are conflated into a single rule.

---

## 2. Background: CP (Classical Processes)

### 2.1 Wadler's Propositions-as-Sessions

Wadler (ICFP 2012, JFP 2014) established a Curry-Howard correspondence between Classical Linear Logic (CLL) and a session-typed pi-calculus called CP:

- **Propositions = session types**: CLL formulas describe communication protocols.
- **Proofs = typed processes**: CLL proofs are well-typed concurrent processes.
- **Cut elimination = communication**: Reducing a cut corresponds to a communication step.
- **Cut-free proofs = values**: Processes in normal form have completed all communications.

### 2.2 The Duality Insight

CLL's involutive negation gives every type a **dual**: `(A^perp)^perp = A`. In session types, duality means that if one endpoint of a channel has type `A`, the other endpoint has type `A^perp`. The dualities are:

| Type | Dual | Session meaning |
|---|---|---|
| `A tensor B` | `A^perp par B^perp` | send vs receive |
| `A oplus B` | `A^perp & B^perp` | select vs offer |
| `!A` | `?A^perp` | server vs client |
| `1` | `bot` | close vs wait |

This is absent in ILL: loli `A -o B` is not self-dual. ILL captures the **input side** of sessions (via the Caires-Pfenning interpretation) but cannot express both endpoints symmetrically.

### 2.3 Cut = Communication

The cut rule in CLL:

```
  Gamma |- A    Delta, A^perp |-
  -------------------------------- cut
       Gamma, Delta |-
```

In CP, this becomes: create a channel with endpoints `x : A` and `y : A^perp`, run process P (using x) in parallel with process Q (using y). Communication happens when P sends on x and Q receives on y -- this is cut reduction.

### 2.4 CP's Limitation: Tree Topology

CP forces every parallel composition to go through cut: `(nu xy)(P | Q)` where P uses x and Q uses y. There is no way to type `P | Q` without connecting them. This means:

- Every process network is a **tree**: each cut introduces one channel, creating a parent-child relationship.
- No **independent** parallel composition: two processes that share no channels cannot be typed.
- The operational semantics is **non-standard**: pi-calculus `P | Q` (where P and Q might not interact) has no direct CP typing.

---

## 3. Hypersequent Calculus

### 3.1 Avron's Framework

Hypersequents were introduced independently by Pottinger (1983) and Avron (1987, 1991) as a generalization of Gentzen's sequent calculus. A hypersequent is a finite multiset of ordinary sequents:

```
G1 | G2 | ... | Gn
```

where each `Gi` is a sequent `Gamma_i |- Delta_i`. The `|` is read as "in parallel with" or "independently." The hypersequent is valid if at least one component is valid (disjunctive reading) or if all components are compatible (parallel reading, used in HCP).

### 3.2 The Mix Rule

The mix rule combines two independent derivations:

```
  G |-           H |-
  --------------------- H-MIX
       G | H |-
```

In standard CLL, mix is **admissible but not derivable** -- it holds in most models but is not a primitive rule. Girard (1987) discussed and dismissed it as "not proof-theoretically terrible" but unnecessary. However, for process calculi, mix is essential: it types the composition of processes that share **no** channels.

In the mix rule, `G` and `H` are disjoint -- no channel name appears in both. The resulting hypersequent `G | H` records that the two processes are independent.

### 3.3 Cut Across Components

HCP's cut rule connects two processes by identifying a channel across hypersequent components:

```
  G | Gamma, x:A | Delta, y:A^perp | H |-
  ------------------------------------------ H-CUT
       G | Gamma, Delta | H |-
```

This merges the two components containing the dual channel endpoints, connecting the processes. The `|` separators for the uninvolved components (`G`, `H`) are preserved -- the connection only affects the two components being linked.

### 3.4 DAG/Graph Topologies

With mix and cross-component cut, HCP can type **arbitrary** process topologies:

1. **Independent processes**: `P || Q` via H-MIX (no shared channels).
2. **Pairwise connected**: `(nu xy)(P || Q)` via H-CUT after H-MIX.
3. **Multi-way connections**: Multiple H-CUT applications on a multi-component hypersequent create graph structures.
4. **Cycles prevented**: The hypersequent structure prevents circular dependencies because H-CUT always merges two distinct components. A cycle would require a single component to have a channel connected to itself, which the typing rules forbid.

---

## 4. HCP: The Synthesis

### 4.1 Process Terms

HCP's process language is a variant of the typed pi-calculus:

| Process | Notation | Logic Rule |
|---|---|---|
| Link (forwarder) | `x <-> y` | Axiom/Identity |
| Terminated | `0` | (empty hypersequent) |
| Name restriction | `(nu xx')P` | Cut |
| Parallel composition | `P \|\| Q` | Mix |
| Output | `x[y].P` | Tensor |
| Input | `x(y).P` | Par |
| Halt (close) | `x[].0` | One |
| Wait | `x().P` | Bottom |
| Select left | `x <| inl.P` | Oplus-left |
| Select right | `x <| inr.P` | Oplus-right |
| Offer | `x |> {inl: P; inr: Q}` | With |

### 4.2 HCP Typing Rules (Key Ones)

**Axiom (Link):** A forwarder connects two channel endpoints.
```
  -------------------- Ax
  x <-> y |- x:A, y:A^perp
```

**Tensor (Output):** Send channel y on x, continue as P.
```
  P |- G | Gamma, x:A, y:B
  --------------------------------- tensor
  x[y].P |- G | Gamma, x:A tensor B
```

**Par (Input):** Receive channel y on x, continue as P.
```
  P |- G | Gamma, x:A, y:B
  ----------------------------- par
  x(y).P |- G | Gamma, x:A par B
```

**H-MIX (Parallel):** Compose independent processes.
```
  P |- G       Q |- H
  ---------------------- H-MIX
  P || Q |- G | H
```

**H-CUT (Connect):** Link two processes via a shared channel.
```
  P |- G | Gamma, x:A | Delta, y:A^perp | H
  --------------------------------------------- H-CUT
  (nu xy)P |- G | Gamma, Delta | H
```

### 4.3 Deadlock Freedom from Structure

HCP prevents deadlocks structurally:

1. **H-CUT merges two distinct components.** A cycle requires a circular chain of dependencies: P waits for Q waits for R waits for P. But each H-CUT reduces the number of hypersequent components by one (merging two into one). A circular dependency would require connecting a component to itself, which H-CUT forbids (it requires two distinct components containing the dual endpoints).

2. **The hypersequent records independence.** Components separated by `|` cannot deadlock with each other because they share no channels. Only H-CUT introduces sharing, and it does so in a controlled way (one channel at a time, merging the components).

3. **Cut elimination terminates.** HCP enjoys subject reduction (typing preserved under reduction), progress (well-typed processes can always reduce or are values), and termination (no infinite reduction sequences). These combine to give deadlock freedom.

### 4.4 The Fully Abstract Semantics

Kokke, Montesi, and Peressotti (POPL 2019, "Better Late Than Never") gave HCP a fully abstract semantics:

- An **LTS (labelled transition system)** extracted from proof rewritings.
- **Bisimilarity**, **denotational equivalence** (via Brzozowski derivatives), and **barbed congruence** all coincide.
- This is the first time a labelled transition system semantics was extracted from proof rewritings in the proofs-as-processes setting.

---

## 5. CLL vs ILL: What CALC Would Gain and Lose

This is the central question for CALC. CALC uses ILL (intuitionistic linear logic) with single-succedent sequents. HCP uses CLL (classical linear logic) with hypersequents. What are the trade-offs?

### 5.1 What CLL Adds

| Feature | CLL | ILL (CALC) |
|---|---|---|
| **Par (par)** | Yes -- multiplicative disjunction, dual of tensor | No -- loli replaces par for the intuitionistic fragment |
| **Linear negation** | Yes -- involutive: `(A^perp)^perp = A` | No -- no negation; loli is not self-dual |
| **Two-sided sequents** | Yes -- `Gamma |- Delta` (multiple conclusions) | No -- `Gamma |- A` (single conclusion) |
| **Duality** | Full: every type has a dual | Partial: no dual of loli, tensor, etc. |
| **Session type duality** | Both channel endpoints typed symmetrically | Only one endpoint typed (provider side) |
| **Parallel composition** | Typed via mix + hypersequents (HCP) | No native parallel composition |

**What duality gives you:** In CLL, if a channel has type `A tensor B` on one end, the other end automatically has type `A^perp par B^perp`. This **symmetric** view of communication is essential for reasoning about both sides of a protocol simultaneously. In ILL, the Caires-Pfenning approach types only the **provider** side; the client's behavior is implicit.

**What par gives you:** Par models "receive, then continue" -- the passive/reactive side of communication. Without par, CALC models reactivity via loli (`A -o B` = consume A to produce B), which is operationally similar but lacks the logical symmetry. Par also enables the multiplicative identity `A par A^perp` (always provable in CLL), which corresponds to a process that forwards between two endpoints.

### 5.2 What ILL Has That CLL Complicates

| Property | ILL (CALC) | CLL |
|---|---|---|
| **Proof search** | Well-behaved: focusing reduces nondeterminism | Harder: multiple conclusions increase branching |
| **Focusing** | Clean positive/negative partition | Same partition, but par adds negative connective |
| **Decidability** | Propositional fragment decidable | Same (propositional MALL decidable) |
| **Resource intuition** | Clear: "consume A to produce B" | Less clear: par lacks intuitive resource reading |
| **Forward chaining** | Natural: multiset rewriting | Less natural: two-sided rewriting needed |
| **Implementation** | Single succedent = simpler data structures | Multiple succedent = more complex state |

**The proof search cost:** CALC's backward prover (L1-L3) works by decomposing a single goal formula. With CLL's multiple conclusions, the prover must manage multiple goals simultaneously, and the choice of which conclusion to decompose introduces branching. Focusing helps (it controls which formula to decompose), but the search space is inherently larger.

**The forward chaining issue:** CALC's forward engine operates by multiset rewriting: consume linear facts, produce new facts. This maps to ILL's monad `{A}` (CLF). CLL's two-sided nature makes forward chaining less direct -- you would need to rewrite both the "have" side and the "need" side simultaneously.

### 5.3 The Practical Trade-Off

**CLL is better for concurrency modeling.** If the goal is to verify concurrent protocols, model multi-party interactions, or reason about both sides of a communication channel, CLL's duality is essential. HCP demonstrates this for session types.

**ILL is better for resource verification.** If the goal is to track resource consumption, verify conservation laws, and do exhaustive state-space exploration, ILL's single-succedent, multiset-rewriting model is simpler and more efficient. CALC's forward engine thrives on this.

### 5.4 Could CALC Support Both?

CALC's architecture is explicitly **calculus-generic**: the prover layers (L1-L3) are parameterized by the calculus object loaded from `.calc` + `.rules` files. Adding CLL as a **second calculus definition** alongside ILL is architecturally straightforward:

1. Define `cll.calc` with par, bot, why-not, linear negation.
2. Define `cll.rules` with the two-sided sequent rules.
3. The prover layers pick up the new connectives automatically.
4. Polarity/invertibility are inferred from the rules (par is negative, etc.).

The main engineering challenge is the **sequent representation**: CALC's `sequent.js` currently stores `{ contexts: { linear: [...], cartesian: [...] }, succedent: hash }` with a single succedent. CLL requires `{ antecedent: [...], succedent: [...] }` or the one-sided `{ formulas: [...] }`. This requires generalizing the sequent data structure.

The forward engine is ILL-specific (multiset rewriting maps to ILL's monad). A CLL forward engine would need different operational semantics -- closer to process reduction than multiset rewriting.

---

## 6. Hypersequents for CALC

### 6.1 Could CALC's Sequent Representation Be Extended?

A hypersequent in CALC would be a multiset of sequents:

```javascript
// Current CALC sequent
{ contexts: { linear: [h1, h2], cartesian: [h3] }, succedent: h4 }

// Hypothetical hypersequent
{
  components: [
    { contexts: { linear: [h1, h2], cartesian: [h3] }, succedent: h4 },
    { contexts: { linear: [h5], cartesian: [] }, succedent: h6 }
  ]
}
```

### 6.2 What Would Change in the Kernel

**L1 (kernel.js):** `verifyStep` would need to handle hypersequent rules: H-MIX (composing two hypersequents), H-CUT (merging components). The rule-interpreter would need to support rules that operate across components.

**L2 (generic.js):** `applicableRules` would need to enumerate rules applicable to specific components within the hypersequent. Context threading (Hodas-Miller) would operate within components, not across them.

**L3 (focused.js):** Focusing would apply per-component: find invertible formulas within each component, choose focus targets within components. The hypersequent structure adds a new level of choice: which component to work on.

**sequent.js:** Generalize from single sequent to hypersequent. Add component-level operations (split, merge, select).

### 6.3 Execution Tree Branches as Hypersequent Components

CALC's execution tree (THY_0001) has **branch nodes** where multiple rules can fire independently. These branches could be interpreted as hypersequent components:

| Execution Tree | Hypersequent |
|---|---|
| Branch (multiple rules applicable) | Multiple components, each with applicable rules |
| Fork (oplus in consequent) | Single component with additive choice |
| Leaf (quiescent) | Component with no applicable rules |
| Step (deterministic) | Single component, one rule applied |

The mix rule for hypersequents corresponds to CALC's **embarrassingly parallel branches**: after a branch node, each child explores an independent subspace. If two branches share no linear resources, they could be typed as separate hypersequent components composed via H-MIX.

### 6.4 The Mix Rule for Independent Parallel Branches

CALC currently explores branches sequentially (DFS with mutation/undo in symexec.js). If two branches share no linear facts, they are **logically independent** -- the mix rule applies. This observation could:

1. **Enable parallel exploration**: Independent branches can be explored on separate threads without synchronization (they share no mutable state).
2. **Simplify bisimulation**: Independent branches are trivially bisimilar to their parallel composition (mix is a structural rule, not a computational one).
3. **Compress execution trees**: If multiple branches are independent, the tree can be factored into a product of smaller trees (one per mix component).

### 6.5 Impact on Proof Search

Hypersequent rules increase the branching factor of proof search:

- **Component selection**: Which component of the hypersequent to decompose?
- **Cross-component cut**: Which pair of components to connect?
- **Mix introduction**: When to split the goal into independent components?

Focusing helps control this: invertible rules apply eagerly within components (no choice), and focus targets are selected within a single component. The hypersequent level adds a **macro-level** choice (which component) on top of the **micro-level** choice (which formula within a component).

For CALC's backward prover, this is manageable. For the forward engine, the impact is minimal -- forward rules already operate on a flat multiset state, and the hypersequent structure would be a post-hoc analysis (identifying independent subsets of the state) rather than a core operational feature.

---

## 7. Session Types from Forward Execution

### 7.1 CALC's Loli Continuations Are Session-Like

CALC's forward engine already has session-like behavior via **loli continuations** (THY_0001, Extension 1):

```ill
evm/iszero: ... -o {
  ... * ((!eq V 0 -o { stack SH 1 }) + (!neq V 0 -o { stack SH 0 }))
}.
```

A loli `!G -o { B }` in the state is a **latent rule** that fires when its guard `G` becomes available. This is operationally a **session continuation**: "when you send me evidence of G, I will produce B." The correspondence:

| CALC Forward | Session Types |
|---|---|
| Loli `A -o { B }` in state | Channel expecting input A, then outputting B |
| Loli firing (matchLoli) | Receive message A, send message B |
| Persistent antecedent `!P` | Server process (replicated) |
| Linear consumption | One-shot channel (used once) |
| oplus in consequent | Internal choice (select branch) |
| Forward rule | Protocol step |

### 7.2 Execution Traces as Session Transcripts

A CALC execution trace (root-to-leaf path in the execution tree) records a sequence of rule applications with their consumed/produced facts. This IS a session transcript:

```
State_0 --[rule_1, theta_1]--> State_1 --[rule_2, theta_2]--> ... ---> State_n (leaf)
```

Each step consumes linear facts (input) and produces new facts (output). The sequence of inputs and outputs forms a **session transcript** -- a concrete instantiation of an abstract session type.

### 7.3 Type-Checking Against Session Specifications

Could the forward engine verify that execution traces conform to a session type specification? The idea:

1. **Define a session type** as a sequence of expected inputs/outputs.
2. **Run the forward engine** to produce execution traces.
3. **Check each trace** against the session type: does the sequence of consumed/produced facts match the expected protocol?

This would connect CALC's exhaustive exploration (RES_0055) with session type verification. The execution tree explores **all possible sessions**; checking against a session type verifies that **every possible session** conforms to the protocol.

### 7.4 Deadlock Detection

A deadlock in CALC's forward engine occurs when:
- The state contains loli continuations `A -o { B }` that cannot fire (their triggers are never produced).
- The state is **stuck**: no forward rules can fire, but the state is not quiescent (unfired lolis remain).

Currently, CALC detects this as a **leaf with remaining lolis** -- a "stuck" state. HCP's hypersequent framework provides a structural explanation: a stuck state corresponds to a hypersequent where two components need to exchange on a channel, but no H-CUT can be performed because the channel types don't match.

Formalizing this connection would let CALC report deadlocks with **logical explanations**: "Process A is waiting to receive X on channel c, but no process is offering to send X on c."

---

## 8. Connections to Other CALC Research

### 8.1 RES_0053 (Bisimulation via Execution Trees)

HCP's fully abstract semantics shows that **bisimilarity = denotational equivalence = barbed congruence** for well-typed processes. This means:

- CALC's tree-based bisimulation (RES_0053) corresponds to HCP's bisimilarity when the programs are session-typed.
- HCP's LTS extraction from proof rewritings provides an alternative to CALC's direct tree comparison: extract an LTS from the execution tree, then apply standard bisimulation algorithms.
- **Up-to techniques** (RES_0053 Section 4) apply directly: HCP's type structure provides a natural congruence for bisimulation up-to context.

### 8.2 RES_0054 (Graded Resources) and RES_0056 (QTT)

Graded session types combine HCP's session discipline with quantitative grades:

- **Nomos** (RES_0033) implements resource-aware session types with automatic amortized resource analysis (AARA). Its potential annotations `|{q}>` are grades on session channels.
- **Rast** (Das & Pfenning 2022) extends this with arithmetic refinements and temporal types for parallel complexity analysis.
- **QTT grades on channels**: A session channel at grade `n` means "this channel is used in `n` sessions." Grade 0 = erased (type-level only), grade 1 = linear (standard session), grade omega = replicated server.

For CALC, the connection is: RES_0054's graded context extension (Path 1: graded ILL) could be combined with session-typed loli continuations to get graded session types without full CLL.

### 8.3 RES_0055 (Model Checking via Linear Logic)

HCP's type system guarantees deadlock freedom structurally. In temporal logic terms, this is `AG (not deadlock)` -- on all paths, no deadlock is ever reached. This connects to RES_0055:

- **Deadlock freedom as a safety property**: `AG (not stuck_loli)` over CALC's execution tree.
- **Structural guarantee vs runtime check**: HCP proves deadlock freedom at type-checking time; CALC's model checker verifies it at exploration time. The approaches are complementary -- HCP prevents deadlocks by construction, CALC detects them by exploration.
- **Compositionality**: HCP's type system is compositional (type each process independently, compose via cut/mix). CALC's model checking is monolithic (explore the entire state space). HCP's approach scales better for large systems; CALC's approach gives stronger guarantees for small systems (exhaustive exploration finds ALL bugs, not just type errors).

### 8.4 RES_0057 (HVM and Interaction Nets)

HVM uses CLL proof nets. HCP uses CLL hypersequents. Both are classical. There is a triangle:

```
      HVM (interaction nets)
     /  computation  \
    /                  \
CLL proof nets  <-->  CLL hypersequents
    \                  /
     \  verification  /
      CALC (sequent calculus)
```

- **HVM = execution backend**: Reduces CLL proof nets to normal form. Optimal lambda reduction.
- **HCP = concurrency model**: Types concurrent processes via CLL hypersequents. Deadlock freedom.
- **CALC = verification engine**: Searches for proofs, explores all executions, checks properties.

A concrete scenario: CALC verifies that a concurrent program satisfies a specification (via exhaustive exploration). The proof term is a CLL proof. HVM executes the proof term optimally. HCP guarantees that the concurrent execution is deadlock-free.

The shared foundation -- CLL with exponentials -- means that translations between these representations are well-defined (proof nets <-> sequent calculus is a classical result; hypersequent proofs project to proof nets).

### 8.5 THY_0001 (Exhaustive Forward Chaining)

THY_0001 defines execution tree constructors: `leaf`, `step`, `fork`, `branch`, `cycle`, `bound`. A hypersequent interpretation:

- **branch(r_1, T_1, ..., r_n, T_n)**: Each `T_i` explores an independent rule application. If the `T_i` operate on disjoint resource subsets, this is an n-component hypersequent composed via mix.
- **fork(T_1, T_2)**: An additive choice (oplus). Both branches use the **same** resources (copied, not split). This is NOT mix -- it's additive branching within a single component.
- **step(r, theta, T')**: A single rule application within one component. This is a cut reduction step.

The distinction between `branch` (multiplicative, potentially independent) and `fork` (additive, necessarily the same resources) aligns with the hypersequent/sequent distinction: mix for the former, additive rules for the latter.

---

## 9. Directions for CALC

### Direction A: Add CLL as a Second Calculus

**What:** Define `cll.calc` and `cll.rules` alongside `ill.calc` and `ill.rules`. The prover layers (L1-L3) pick up the new connectives automatically.

**What changes:**
- `calculus/cll/cll.calc` -- par, bot, why-not, linear negation, one-sided sequent rules.
- `calculus/cll/cll.rules` -- CLL inference rules (tensor, par, oplus, with, bang, why-not, one, bot).
- `lib/kernel/sequent.js` -- Generalize to support one-sided sequents (list of formulas, no succedent/antecedent distinction) or two-sided sequents with multiple conclusions.
- `lib/prover/context.js` -- Handle multiple-conclusion context threading.

**What stays the same:** L1 verification, L2 rule application, L3 focusing (polarity/invertibility inferred from rules), L4 strategy. The forward engine stays ILL-specific.

**Effort:** MEDIUM. The prover is already calculus-generic; the main work is sequent representation.

**Value:** Enables modeling concurrent protocols, session-typed processes, and duality-based reasoning.

### Direction B: Implement Hypersequent Extension

**What:** Extend the sequent representation to hypersequents. Add H-MIX and H-CUT as structural rules.

**What changes:**
- `lib/kernel/sequent.js` -- Hypersequent = multiset of sequents.
- `lib/prover/rule-interpreter.js` -- Handle rules that operate across components (H-CUT) and compose components (H-MIX).
- `lib/prover/generic.js` -- `applicableRules` enumerates per-component and cross-component rules.
- `lib/prover/focused.js` -- Component-level focusing with macro-level component selection.

**What stays the same:** Content-addressed store, unification, substitution, AST.

**Effort:** HIGH. Hypersequent rules increase proof search complexity. Needs careful interaction with focusing.

**Value:** Enables parallel process typing, deadlock-freedom proofs, and graph-structured process topologies.

**Prerequisite:** Direction A (CLL calculus) should come first.

### Direction C: Session-Typed Forward Execution

**What:** Use session types to constrain and verify CALC's forward execution traces.

**What changes:**
- Define session type specifications as CLL formulas (or ILL with loli for the intuitionistic fragment).
- Add a **session checker** module that verifies execution traces against session types.
- Report violations as "protocol errors" with the divergence point.

**What stays the same:** The forward engine itself. This is a pure analysis layer on top of existing execution traces.

**Effort:** LOW-MEDIUM. No engine changes; new analysis module (~200 LOC).

**Value:** HIGH. Session-type violations in smart contracts (wrong message order, missing steps) are directly detectable.

**No prerequisite on Direction A/B.** Can work with ILL session types (loli-based, Caires-Pfenning style).

### Direction D: Session-Typed Loli Continuations

**What:** Formalize CALC's loli continuations as session-typed channels. A loli `A -o { B }` in state IS a session channel offering to consume A and produce B.

**What changes:**
- Annotate loli continuations with session types during forward execution.
- Track session progress: as lolis fire, the session type "advances."
- Detect stuck sessions (unfired lolis whose triggers are never produced) as session-type violations.

**What stays the same:** Forward engine core. This enriches the state representation.

**Effort:** MEDIUM. Requires integrating session type tracking into `match.js` and `forward.js`.

**Value:** Deadlock detection with logical explanations. Direct connection to Nomos-style contract verification (RES_0033).

### Direction E: Deadlock-Free-by-Construction Forward Rules

**What:** Use HCP's structural guarantee to ensure that sets of forward rules are deadlock-free by construction.

**How:** Given a set of forward rules, check whether they can be typed in HCP. If yes, the rules are deadlock-free. If not, report which rules create potential deadlocks.

**What changes:** New static analysis module that translates forward rules to HCP typing problems.

**Effort:** HIGH. Requires implementing HCP type checking.

**Value:** Strong guarantee. Rules that pass the check CANNOT deadlock, regardless of execution order.

### Priority Assessment

| Direction | Effort | Value | Prerequisites |
|---|---|---|---|
| **C: Session-typed execution** | LOW-MEDIUM | HIGH | None |
| **D: Session-typed lolis** | MEDIUM | HIGH | None (Direction C helps) |
| **A: CLL calculus** | MEDIUM | MEDIUM | None |
| **B: Hypersequents** | HIGH | MEDIUM | Direction A |
| **E: Deadlock-free rules** | HIGH | HIGH | Direction A + B |

Recommended order: **C, then D, then A**, with B and E as longer-term goals.

---

## 10. Open Questions

### Q1: Can Hypersequents Work with ILL?

HCP uses CLL. Could hypersequents be added to ILL directly? ILL lacks par and duality, so the mix rule's interaction with CLL duality would be absent. But the **structural** aspect of hypersequents (recording independence) could still apply: an ILL hypersequent `G1 | G2 | ... | Gn` would mean "these n sequents use disjoint resources." This would model CALC's independent execution branches without requiring CLL. The question is whether this restricted hypersequent framework has useful proof-theoretic properties (cut elimination, focusing).

### Q2: How Does Focusing Interact with Hypersequent Component Selection?

Focusing (Andreoli 1992) alternates inversion and focus phases. In a hypersequent, invertible rules apply within components (no cross-component interaction needed). But focus selection (choosing which positive formula to decompose) now has an additional dimension: which component? A **hypersequent focusing discipline** would first exhaust all invertible rules in all components (macro-inversion), then select a component and a focus target within it (macro-focus + micro-focus). Whether this preserves completeness is an open question.

### Q3: What Is the Complexity Cost of Hypersequent Proof Search?

Standard sequent calculus proof search for propositional MALL is PSPACE-complete. Hypersequent proof search has additional choices (component selection, mix introduction, cross-component cut). Does this increase complexity? For linear logic specifically, the mix rule is semantically valid, so the hypersequent extension is **conservative** (no new theorems). But the proof search space is larger because there are more ways to construct a proof.

### Q4: Can CALC's Forward Engine Detect Session Progress?

If loli continuations are session channels, can the forward engine track **session progress** -- how far along a session protocol each channel has advanced? This would enable:
- **Partial deadlock detection**: A session that hasn't progressed for N steps is "stalled."
- **Progress guarantees**: If every session channel makes progress on every path, the system is live.
- **Conformance checking**: The observed session progress matches the expected session type.

### Q5: What Is the Relationship Between HCP's Coherence and CALC's Confluence?

Carbone et al. (CONCUR 2016) generalized CLL duality to **coherence** for multiparty session types. CALC's forward engine may exhibit **confluence** (different rule orderings reach the same final state). Is there a formal relationship between coherence (compatibility of n session types) and confluence (independence of rule application order)? Both capture a notion of "these things don't interfere."

### Q6: How Do Priorities (PCP) Compare to Hypersequents (HCP)?

Dardha & Gay (FoSSaCS 2018) proposed Priority CP (PCP): assign numeric priorities to channel operations. Deadlock freedom follows if priorities decrease along dependencies (no cycles). Kokke et al. (ECOOP 2025) showed that HCP and PCP induce similar classes of deadlock-free processes. For CALC, priorities might be simpler to implement than full hypersequents -- annotate loli continuations with priorities, check for decreasing order.

---

## 11. Bibliography

### HCP and CP (Core)
- Kokke, W., Montesi, F. & Peressotti, M. (2019). "Better Late Than Never: A Fully Abstract Semantics for Classical Processes." Proc. ACM on Programming Languages 3(POPL), Article 24. [arXiv:1811.02209](https://arxiv.org/abs/1811.02209)
- Kokke, W., Montesi, F. & Peressotti, M. (2019). "Taking Linear Logic Apart." Joint International Workshop on Linearity & TLLA 2018. [arXiv:1904.06848](https://arxiv.org/abs/1904.06848)
- Wadler, P. (2014). "Propositions as Sessions." JFP 24(2-3):384-418. [PDF](https://homepages.inf.ed.ac.uk/wadler/papers/propositions-as-sessions/propositions-as-sessions.pdf)
- Wadler, P. (2012). "Propositions as Sessions." ICFP 2012. [ACM DL](https://dl.acm.org/doi/10.1145/2398856.2364568)

### Hypersequents
- Avron, A. (1991). "Hypersequents, Logical Consequence and Intermediate Logics for Concurrency." Annals of Mathematics and Artificial Intelligence 4(3-4):225-248. [Springer](https://link.springer.com/article/10.1007/BF01531058)
- Avron, A. (1987). "A Constructive Analysis of RM." Journal of Symbolic Logic 52(4):939-951.

### Session Types and Linear Logic
- Caires, L. & Pfenning, F. (2010). "Session Types as Intuitionistic Linear Propositions." CONCUR 2010, LNCS 6269, pp. 222-236. [Springer](https://link.springer.com/chapter/10.1007/978-3-642-15375-4_16)
- Caires, L., Pfenning, F. & Toninho, B. (2016). "Linear Logic Propositions as Session Types." MSCS 26(3):367-423. [PDF](https://www.cs.cmu.edu/~fp/papers/mscs13.pdf)
- Toninho, B. (2015). "A Logical Foundation for Session-based Concurrent Computation." PhD thesis, CMU-CS-15-109.

### Multiparty Session Types and Coherence
- Carbone, M., Lindley, S., Montesi, F., Schurmann, C. & Wadler, P. (2016). "Coherence Generalises Duality: A Logical Explanation of Multiparty Session Types." CONCUR 2016. [Dagstuhl](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2016.33)

### Priority-Based Deadlock Freedom
- Dardha, O. & Gay, S.J. (2018). "A New Linear Logic for Deadlock-Free Session-Typed Processes." FoSSaCS 2018, LNCS 10803, pp. 91-109. [Springer](https://link.springer.com/chapter/10.1007/978-3-319-89366-2_5)
- Kokke, W. & Dardha, O. (2021). "Prioritise the Best Variation." FORTE 2021. [arXiv:2103.14466](https://arxiv.org/abs/2103.14466)
- Kokke, W. & Dardha, O. (2025). "Contrasting Deadlock-Free Session Processes." ECOOP 2025. [Dagstuhl](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ECOOP.2025.17)
- Padovani, L. (2014). "Deadlock and Lock Freedom in the Linear Pi-Calculus." CSL-LICS 2014.

### GV and HGV
- Gay, S.J. & Vasconcelos, V.T. (2010). "Linear Type Theory for Asynchronous Session Types." JFP 20(1):19-50.
- Fowler, S., Kokke, W., Dardha, O., Lindley, S. & Morris, J.G. (2021). "Separating Sessions Smoothly." CONCUR 2021, LIPIcs 203, 36:1-36:18. [Dagstuhl](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.CONCUR.2021.36)
- Lindley, S. & Morris, J.G. (2015). "A Semantics for Propositions as Sessions." ESOP 2015. [PDF](https://homepages.inf.ed.ac.uk/slindley/papers/gv-semantics.pdf)

### Proofs as Processes (Foundational)
- Abramsky, S. (1994). "Proofs as Processes." TCS 135(1):5-9.
- Bellin, G. & Scott, P.J. (1994). "On the Pi-Calculus and Linear Logic." TCS 135(1):11-65. [ScienceDirect](https://www.sciencedirect.com/science/article/pii/0304397594001049)

### Nomos and SILL
- Das, A., Balzer, S., Hoffmann, J. & Pfenning, F. (2021). "Resource-Aware Session Types for Digital Contracts." CSF 2021.
- Das, A. & Pfenning, F. (2022). "Rast: A Language for Resource-Aware Session Types." LMCS 18(1).
- Balzer, S., Toninho, B. & Pfenning, F. (2019). "Manifest Deadlock-Freedom for Shared Session Types." ESOP 2019. [PDF](https://www.cs.cmu.edu/~balzers/publications/manifest_deadlock_freedom.pdf)

### DILL
- Barber, A. (1996). "Dual Intuitionistic Linear Logic." Technical Report ECS-LFCS-96-347, University of Edinburgh. [PDF](https://www.lfcs.inf.ed.ac.uk/reports/96/ECS-LFCS-96-347/ECS-LFCS-96-347.pdf)

### Linear Logic
- Girard, J.-Y. (1987). "Linear Logic." TCS 50(1):1-102.
- Andreoli, J.-M. (1992). "Logic Programming with Focusing Proofs in Linear Logic." JLC 2(3):297-347.

### Cross-References
- THY_0001 -- Exhaustive Forward Chaining in MALL with the Lax Monad
- RES_0026 -- Linear Logic Connectives: Par, Why Not, and Polarity
- RES_0033 -- Nomos: Session Types + Linear Types for Smart Contracts
- RES_0053 -- Bisimulation via Execution Trees
- RES_0054 -- Graded Resource Analysis for Linear Logic
- RES_0055 -- Symbolic Model Checking via Linear Logic
- RES_0056 -- Quantitative Type Theory: Sequent Calculus and Gap Analysis for CALC
- RES_0057 -- HVM and Interaction Nets
- THY_0008 -- Ownership Modalities as Session Types
- TODO_0017 -- Debt as Session Protocol
- TODO_0018 -- MPST-Based Authorization
