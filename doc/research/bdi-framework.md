# BDI Framework: Belief-Desire-Intention for CALC

The BDI (Belief-Desire-Intention) model is a foundational framework for rational agents. This document explores its formal foundations and, critically, how it connects to CALC's linear logic approach to resource-sensitive reasoning.

> **See also:** [[authorization-logic]] for says modality, [[ownership-design]] for ownership modalities, [[consensus-modalities-mpst]] for multi-party coordination, [[clf-celf-ceptre]] for forward-chaining agent semantics.

---

## Table of Contents

1. [Executive Summary](#executive-summary)
2. [BDI Foundations](#bdi-foundations)
3. [BDI Logic Formalizations](#bdi-logic-formalizations)
4. [The Linear Logic Connection](#the-linear-logic-connection)
5. [Resource-Sensitive Agency](#resource-sensitive-agency)
6. [BDI and CALC Synergies](#bdi-and-calc-synergies)
7. [Novel Research Directions](#novel-research-directions)
8. [Financial Agent Applications](#financial-agent-applications)
9. [Implementation Considerations](#implementation-considerations)
10. [Open Questions](#open-questions)
11. [References](#references)

---

## Executive Summary

**Core Insight:** BDI provides the "why" (agent reasoning) while CALC provides the "what" (resource transformations). Combining them yields agents that reason about resource-constrained actions.

| BDI Concept | CALC Analog | Connection |
|-------------|-------------|------------|
| Belief (B) | Persistent context (!A) | Knowledge that persists |
| Desire (D) | Goal formula | What agent wants to achieve |
| Intention (I) | Linear resource | Commitment consumed on execution |
| Commitment | Linearity | Used exactly once |
| Plan | Proof | Sequence of rule applications |
| Agent | Principal | Owner/authorizer of resources |

**Key Discovery:** Intentions are naturally *linear* — they're commitments that get consumed when executed. Beliefs are *exponential* — knowledge that can be used repeatedly. This maps directly to CALC's LNL (Linear/Non-Linear) structure.

---

## BDI Foundations

### Bratman's Philosophical Model

Michael Bratman's "Intention, Plans, and Practical Reason" (1987) provides the philosophical foundation:

**Three Mental Attitudes:**
1. **Beliefs** — Informational state: what the agent holds to be true about the world
2. **Desires** — Motivational state: what the agent would like to achieve
3. **Intentions** — Deliberative state: what the agent has committed to doing

**Why Intentions Matter:**

Intentions are not merely strong desires. They have distinctive functional roles:

1. **Conduct-controlling** — Intentions directly guide behavior
2. **Reasoning-constraining** — Future plans build on current intentions
3. **Persistence** — Intentions resist easy abandonment (commitment)

**The Commitment Thesis:**

The key difference between desire and intention is *commitment*:
- A desire is something you'd like (if convenient)
- An intention is something you're committed to pursuing

This commitment leads to:
1. Temporal persistence — stick with the plan
2. Constraint on future planning — don't adopt conflicting intentions
3. Resistance to reconsideration — don't constantly re-evaluate

### Commitment Strategies

Rao & Georgeff (1991) formalized three commitment strategies:

| Strategy | Description | Reconsideration |
|----------|-------------|-----------------|
| **Blind** | Never drop intentions | Only on success/impossibility |
| **Single-minded** | Drop if believed impossible | On belief change |
| **Open-minded** | Drop if no longer desired | On desire change |

**For CALC:** Financial contracts often require blind or single-minded commitment. An atomic swap, once initiated, should not be casually abandoned.

---

## BDI Logic Formalizations

### Rao & Georgeff's BDICTL

The foundational formal logic combines:
- **Multiple modal operators** for B, D, I
- **Branching-time temporal logic CTL*** for reasoning about possible futures

**Syntax:**
```
φ ::= p | ¬φ | φ ∧ ψ | Bel(φ) | Des(φ) | Int(φ) | Aφ | Eφ | ○φ | □φ | ◇φ
```

Where:
- `Bel(φ)` — agent believes φ
- `Des(φ)` — agent desires φ
- `Int(φ)` — agent intends φ
- `A`, `E` — for all / exists path (CTL)
- `○`, `□`, `◇` — next, always, eventually (temporal)

### Kripke Semantics

Worlds are organized as trees (possible futures), with accessibility relations:

```
B_i(w) = worlds compatible with agent i's beliefs at w
D_i(w) = worlds compatible with agent i's desires at w
I_i(w) = worlds compatible with agent i's intentions at w
```

**Key Properties (KD45 for Beliefs):**
- **D (Serial):** Agent doesn't believe contradictions
- **4 (Transitive):** Positive introspection (knows what it knows)
- **5 (Euclidean):** Negative introspection (knows what it doesn't know)

### Interplay Axioms

Rao & Georgeff's "asymmetry thesis" (from Bratman) yields:

```
Int(φ) → Des(φ)        -- Intentions are subset of desires
Int(φ) → Bel(◇φ)       -- Only intend achievable things
Int(φ) → ¬Int(¬φ)      -- Intentions are consistent
```

But NOT:
```
Des(φ) → Int(φ)        -- Not all desires become intentions
Bel(φ) → Int(φ)        -- Belief doesn't imply commitment
```

### AgentSpeak(L) and Jason

**AgentSpeak(L)** provides executable BDI semantics:

```agentspeak
// Beliefs
at(home).
have(money, 100).

// Goals
!buy(groceries).

// Plans
+!buy(X) : have(money, M) & M > 0
  <- go(store); purchase(X); go(home).
```

**Jason** is the practical implementation with operational semantics:
- Plans are triggered by events (goal adoption, belief change)
- Intentions are stacks of partially instantiated plans
- Execution cycle: perceive → deliberate → act

---

## The Linear Logic Connection

### The Key Insight: Intentions Are Linear

**Observation:** In classical BDI, intentions persist until executed or dropped. But from a resource perspective:

```
An intention to "transfer 10 tokens to Bob" is consumed upon execution.
You don't get to reuse the same intention infinitely.
```

This is exactly linear logic's resource semantics!

### Mapping BDI to Linear Types

| BDI | Linear Logic | Interpretation |
|-----|--------------|----------------|
| Belief | `!B` | Persistent, reusable knowledge |
| Desire | `D` (in context) | Motivational goal |
| Intention | `I` (linear) | One-shot commitment |
| Execute intention | `I ⊸ effect` | Consumes intention, produces effect |
| Adopt intention | `D ⊸ I` | Transform desire into commitment |

### Linear BDI Sequent

```
Beliefs ; Intentions ⊢ Goal
   !Γ   ;     Δ      ⊢  G

Where:
- Beliefs (!Γ) are in exponential context — use many times
- Intentions (Δ) are linear — use exactly once
- Goal (G) is what we're trying to prove/achieve
```

This is precisely CALC's LNL (Linear/Non-Linear) separation!

### Plans as Proofs

In linear logic planning:

```
A plan to transform resources A₁ ⊗ ... ⊗ Aₙ into goal G
is a proof of: A₁ ⊗ ... ⊗ Aₙ ⊢ G
```

The proof structure IS the plan. Each rule application IS an action.

**Example: Transfer Plan**
```
[Alice] coin(10) ⊗ Alice_intends_transfer(Bob, 5)
  ⊢ [Alice] coin(5) ⊗ [Bob] coin(5)

The intention is consumed; the resources are transformed.
```

---

## Resource-Sensitive Agency

### Porello & Troquard's Framework

**Key Paper:** "A Resource-Sensitive Logic of Agency" (ECAI 2014)

They combine:
- **Intuitionistic Linear Logic (ILL)** for resources
- **Non-normal modal operator** `E_i` for "agent i brings about"

**Core Idea: Bringing-It-About in ILL**

```
E_i(φ)     -- Agent i brings about φ (resource transformation)
E_i(φ) ⊸ φ  -- If agent brings about φ, then φ holds (T-axiom variant)
```

**Key Axiom:**
```
E_i(φ) ⊸ φ   -- Agency implies effect (consumes the action)
¬E_i(⊤)      -- Can't bring about tautologies (non-trivial agency)
```

**Sequent Calculus:**
```
    Γ ⊢ φ
───────────── (E_i-R)
  Γ ⊢ E_i(φ)

Γ, E_i(φ) ⊢ ψ    Δ ⊢ φ
───────────────────────── (E_i-L)
      Γ, Δ ⊢ ψ
```

### Porello & Endriss on Negotiation

**Key Paper:** "Modelling Multilateral Negotiation in Linear Logic" (ECAI 2010)

Multi-agent resource negotiation = distributed linear logic theorem proving:

- **Allocations** are multisets of goods owned by agents
- **Deals** are resource exchanges
- **Social welfare** is a provability question

```
Negotiation from allocation A to allocation B
= Proof of A ⊢ B in linear logic
```

**CALC Connection:** This is exactly our atomic swap semantics!

---

## BDI and CALC Synergies

### Synergy 1: Ownership as Agent Attribution

CALC's `[Alice] A` (Alice owns A) maps directly to agent-indexed mental states:

```
BDI:    Bel_Alice(p), Int_Alice(φ)
CALC:   [Alice] !Bel(p), [Alice] Int(φ)
```

The ownership modality attributes resources (including mental states) to specific agents.

### Synergy 2: Authorization as Affirmation

CALC's `Alice says φ` from authorization logic corresponds to BDI's agent perspective:

```
Alice says transfer(Bob, 10)  ≈  Int_Alice(transfer(Bob, 10))
```

Authorization is an externalized intention — making commitment public.

### Synergy 3: Multi-Party Coordination

CALC's work on MPST (Multi-Party Session Types) addresses multi-agent coordination:

```
MPST Global Type          ≈  Multi-agent protocol
Projection to local types ≈  Each agent's local plan
Coherence                 ≈  Agents can reach consensus
```

**Connection to BDI:** MPST provides the coordination mechanism; BDI provides the individual reasoning.

### Synergy 4: Forward Chaining as Agent Execution

CALC's Celf-style forward chaining is the agent execution model:

```
!Rule ⊗ Preconditions ⊸ Effects

When preconditions match, rule fires, producing effects.
This IS the BDI execution cycle: match plan → execute → update world.
```

### Synergy 5: Graded Modalities for Quantitative Beliefs

CALC's graded modalities `[]_r A` can express quantitative agent states:

```
[Alice] []_{0.8} Bel(price_will_rise)
-- Alice believes with 80% confidence that price will rise
```

This connects to probabilistic/graded BDI extensions.

---

## Novel Research Directions

### Direction 1: Linear BDI Logic

**Proposal:** A BDI logic where intentions are inherently linear.

```
Syntax:
  φ ::= ... | Bel(φ) | Des(φ) | Int(φ) | φ ⊗ ψ | φ ⊸ ψ | !φ

Typing:
  !Γ (beliefs) ; Δ (intentions) ⊢ G (goal)

Key Rules:
  !Γ ; Δ, Int(φ) ⊢ φ          -- Execute: consume intention, get effect
  !Γ, Bel(φ) ; Δ ⊢ ψ if φ ⊸ ψ  -- Reason: beliefs support inference
```

**Benefits:**
- Natural semantics for intention consumption
- No separate "commitment strategy" axioms — linearity handles it
- Cut elimination = execution correctness

### Direction 2: Pacioli-BDI Integration

**Proposal:** Agents with beliefs about Pacioli-group quantities.

From CALC's accounting connection:
```
[Alice] []_{(100, 0)} cash  -- Alice believes she has 100 cash, 0 debt
[Bob] []_{(0, 50)} cash     -- Bob believes he has 0 cash, 50 debt

Trade:
[Alice] Int(pay(Bob, 30)) ⊗ [Bob] Int(accept_payment)
⊸
[Alice] []_{(70, 0)} cash ⊗ [Bob] []_{(30, 50)} cash
```

**Insight:** Financial agents reason about both assets AND liabilities.

### Direction 3: Session-Typed Agent Protocols

**Proposal:** Use session types to specify multi-agent protocols, BDI for individual reasoning.

```
Global Protocol (MPST):
  AtomicSwap = Alice → Bob : offer(asset_a).
               Bob → Alice : { accept: ..., reject: ... }

Local Agent (BDI):
  +!participate(AtomicSwap) : have(asset_a)
    <- propose(asset_a); wait_response; handle_outcome.
```

**Benefits:**
- Protocol correctness from session types (deadlock freedom)
- Agent autonomy from BDI (flexible plan selection)

### Direction 4: Deliberation as Resource Consumption

**Proposal:** Model deliberation time as a consumable resource.

```
[Agent] []_t deliberation_budget ⊗ [Agent] Int(complex_plan)
⊸
[Agent] []_{t-cost} deliberation_budget ⊗ [Agent] refined_plan
```

**Application:** Real-time trading agents with bounded computation.

---

## Financial Agent Applications

### Trading Agents

BDI agents for financial markets:

```
Beliefs:
  price(AAPL, 150).
  trend(AAPL, bullish).
  !portfolio(AAPL, 100).

Desires:
  maximize_profit.

Intentions (linear!):
  Int(buy(AAPL, 10, limit: 148)).
  Int(sell(AAPL, 50, if_price: 160)).
```

**CALC Encoding:**
```
[Trader] !Bel(price(AAPL, 150)) ⊗
[Trader] !Bel(trend(AAPL, bullish)) ⊗
[Trader] []_{100} aapl_shares ⊗
[Trader] Int(buy(AAPL, 10))
```

### Multi-Sig Wallets as Multi-Agent Systems

A 2-of-3 multi-sig is three BDI agents that must coordinate:

```
[Alice] Int(approve(tx))
[Bob] Int(approve(tx))
[Carol] Int(reject(tx))

Consensus requires:
(Alice says approve) ⊗ (Bob says approve) ⊗ [MultiSig] funds
⊸ execute(tx)
```

### Smart Contract Agents

Contracts as autonomous BDI agents:

```
Contract Beliefs:
  !is_owner(Alice).
  !balance(1000).
  !locked_until(block_1000000).

Contract Intentions:
  Int(release(Alice)) : current_block > locked_until.
```

---

## Implementation Considerations

### Extending CALC for BDI

**Phase 1: Mental State Predicates**
```
// In .calc file
Bel : principal -> formula -> formula.
Des : principal -> formula -> formula.
Int : principal -> formula -> formula.
```

**Phase 2: Linear Intention Semantics**
```
// Intention execution rule
[P] Int(A) ⊸ [P] execute(A)

// Where execute triggers effects
execute(transfer(B, X)) ⊗ [P] X ⊢ [B] X
```

**Phase 3: AgentSpeak-like Plans**
```
// Plan as persistent implication
![P] (trigger(event) ⊗ context ⊸ [P] Int(action_sequence))
```

### Connection to Existing CALC Components

| Component | BDI Use |
|-----------|---------|
| `[P] A` ownership | Agent attribution |
| `P says A` authorization | Externalized intention |
| `[]_r A` graded | Belief confidence |
| `!A` exponential | Persistent beliefs |
| `A ⊗ B` tensor | Concurrent intentions |
| `A ⊸ B` lollipop | Plan step |
| Forward chaining | Agent execution cycle |

---

## Open Questions

### Q1: How Do Desires Fit?

Desires are less clearly linear or exponential:
- Persistent desires (exponential): "maximize profit"
- Achievable desires (linear?): "acquire 100 tokens"

**Hypothesis:** Desires are meta-level; intentions are object-level.

### Q2: Commitment Revision in Linear Setting

If intentions are linear (consumed on execution), how do we model:
- Dropping an intention before execution?
- Revising a partial plan?

**Possible Answer:** Weakening rule allows dropping. Revision = drop + adopt new.

### Q3: Multi-Agent Intention Sharing

Can agents share intentions? What does that mean linearly?

```
[Alice] Int(X) ⊗ [Bob] Int(X)  -- Both independently intend X
vs
[Alice ∧ Bob] Int(X)           -- Joint intention
```

### Q4: Temporal Aspects

BDI uses CTL* for temporal reasoning. CALC currently lacks temporal modalities.

**Options:**
- Add temporal operators (future work)
- Use stages (Ceptre-style) for temporal structure
- External time oracle

### Q5: Learning in Linear BDI

How do agents update beliefs? Standard BDI has belief revision.

**Linear version:**
```
!Bel(old) ⊸ !Bel(new)    -- Problematic: exponentials don't transform easily
```

May need explicit belief management outside pure linear fragment.

---

## References

### BDI Foundations

- [Bratman, "Intention, Plans, and Practical Reason" (1987)](https://philpapers.org/rec/BRAIPA) — Philosophical foundation
- [Rao & Georgeff, "BDI Agents: From Theory to Practice" (1995)](https://cdn.aaai.org/ICMAS/1995/ICMAS95-042.pdf) — Formal BDI logic
- [Meyer, Broersen, Herzig, "BDI Logics" (2015)](https://www.irit.fr/~Andreas.Herzig/P/HandbkEpi15_chap10.pdf) — Handbook chapter

### AgentSpeak and Jason

- [Bordini & Hübner, "BDI Agent Programming in AgentSpeak using Jason"](https://link.springer.com/chapter/10.1007/11750734_9)
- [Jason Language](https://jason-lang.github.io/) — Implementation

### Linear Logic and Agency

- [Porello & Troquard, "A Resource-Sensitive Logic of Agency" (ECAI 2014)](https://philpapers.org/rec/PORARL) — Linear logic + bringing-it-about
- [Porello & Endriss, "Modelling Multilateral Negotiation in Linear Logic" (ECAI 2010)](https://ebooks.iospress.nl/publication/5802) — Negotiation as proof
- [Porello & Endriss, "Modelling Combinatorial Auctions in Linear Logic" (KR 2010)](https://philarchive.org/rec/PORMCA)

### Linear Logic Planning

- [Kanovich, "Linear Logic as a Logic of Computations" (1995)](https://www.sciencedirect.com/science/article/pii/016800729400081R)
- [Martens, "Linear Logic Programming for Narrative Generation" (2013)](https://www.cs.cmu.edu/~cmartens/lpnmr13.pdf)

### STIT and Agency Logics

- [Belnap, Perloff, Xu, "Facing the Future" (2001)](https://link.springer.com/book/10.1007/978-94-010-0767-4) — STIT theory
- [Horty, "Agency and Deontic Logic" (2001)](https://oxford.universitypressscholarship.com/view/10.1093/0195134613.001.0001/acprof-9780195134612)

### Financial Agents

- [Conceptualizing BDI agents for financial markets (IEEE 2001)](https://ieeexplore.ieee.org/document/973018/)
- [Agent-Based Computational Economics](https://www.sciencedirect.com/handbook/handbook-of-computational-economics)

### CALC Cross-References

- [[authorization-logic]] — Says modality, principals
- [[ownership-design]] — Ownership modalities
- [[consensus-modalities-mpst]] — Multi-party coordination
- [[clf-celf-ceptre]] — Forward-chaining execution
- [[graded-resource-tracking]] — Quantitative modalities
- [[financial-primitives]] — Financial derivatives

---

*Created: 2026-02-10*
*Status: Initial research — connections to CALC identified, implementation TBD*
