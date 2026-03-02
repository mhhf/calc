---
title: "OTP Through the Lens of Linear Logic"
created: 2026-03-01
modified: 2026-03-01
summary: Deep analysis of Erlang/Elixir OTP architecture and its structural correspondence with linear logic, session types, and CALC's forward/backward engine.
tags: [linear-logic, session-types, concurrency, process-algebra, clf, forward-chaining, pi-calculus, Curry-Howard, architecture, BEAM]
category: "Related Paradigms"
---

# OTP Through the Lens of Linear Logic

## 1. OTP in One Paragraph

OTP (Open Telecom Platform) is Erlang's reification of concurrent system design into code. It provides **behaviours** — generic process patterns (GenServer, Supervisor, gen_statem) parameterized by user callbacks — atop the BEAM VM, which gives per-process heaps, preemptive scheduling via reduction counting, and copy-semantics message passing. The "let it crash" philosophy replaces defensive error handling with hierarchical **supervision trees** that restart failed processes from known-good states. The key insight: process = unit of failure = unit of state = unit of GC.

## 2. The Correspondence

Linear logic and OTP share a deep structural identity. This isn't metaphor — it's grounded in the Curry-Howard correspondence between linear logic and session types (Caires & Pfenning 2010, Wadler 2012).

### 2.1 Linear Facts = Messages

| Linear Logic | OTP |
|---|---|
| Linear fact in multiset | Message in process mailbox |
| Consumed exactly once by rule | Consumed exactly once by `receive` |
| `A ⊗ B` (produce both) | Send two messages |
| `A ⊸ B` (consume A, produce B) | Receive A, send B |
| `!A` (persistent, reusable) | ETS table entry (shared, non-consumed) |
| Multiset rewriting step | Process handles one message |

The forward engine's execution model (`forward.js`: match linear antecedents → consume → produce consequents) is isomorphic to a process receiving messages and sending replies. CALC's `State = { linear: FactSet, persistent: FactSet }` maps directly to `{ mailbox, ets }`.

### 2.2 State Threading = Linear Implication

GenServer's callback model enforces linearity mechanically:

```erlang
handle_call(Msg, _From, OldState) ->
    NewState = transform(OldState, Msg),
    {reply, ok, NewState}.
%% OldState consumed, NewState produced — exactly A ⊸ B
```

The old state is inaccessible after the callback returns. This is `State_old ⊸ State_new` — a linear implication where the antecedent is consumed. CALC's forward rules encode the same pattern: linear facts in the antecedent are consumed, consequent facts are produced.

### 2.3 ILL Connectives as Communication Primitives

Wadler's CP calculus (2012) gives the precise mapping:

| ILL Connective | Session Type | OTP Pattern |
|---|---|---|
| `A ⊗ B` (tensor) | Send A, continue as B | `gen_server:reply(A), continue(B)` |
| `A ⊸ B` (loli) | Receive A, continue as B | `receive A -> handle(A), B end` |
| `A & B` (with) | Offer choice {A, B} | `gen_statem` offering multiple state transitions |
| `A ⊕ B` (oplus) | Select one of {A, B} | Client choosing which `call` to make |
| `!A` (bang) | Reusable server | Registered named process (always available) |
| `1` (one) | Close session | Process termination (`normal` exit) |

This means CALC's existing connective set already models the full vocabulary of OTP-style communication.

### 2.4 Supervision Trees ↔ Exploration Trees

CALC's `symexec.explore()` produces DFS exploration trees. OTP supervision trees structure failure domains. Both are hierarchical with failure/backtracking propagation:

| Supervision Strategy | Exploration Analogue | Linear Logic Reading |
|---|---|---|
| `one_for_one` | Independent branches (backtrack one, others unaffected) | `A ⊗ B` — independent resources |
| `one_for_all` | Coupled obligations (if one fails, restart all) | `A & B` — must satisfy both |
| `rest_for_one` | Ordered dependencies (failure cascades right) | Sequential `⊸` chain |
| Restart intensity (max N in M sec) | Bound on retries before declaring `dead` | Bounded proof search depth |

The restart-intensity escalation (child fails → supervisor restarts → too many restarts → supervisor itself fails → grandparent restarts) mirrors CALC's backtracking: leaf fails → undo via Arena → parent tries next alternative → all alternatives exhausted → propagate failure up.

### 2.5 "Let It Crash" = Arena Checkpoint/Restore

Both systems handle failure through the same mechanism: speculative execution with rollback.

```
OTP:     init(State₀) → run → crash → supervisor restarts from State₀
CALC:    checkpoint(Arena) → explore branch → fail → restore(Arena)
```

Process isolation (separate heaps, no shared mutation) enables OTP's clean crash recovery. Arena isolation (separate undo logs for linear/persistent state) enables CALC's clean backtracking. The fundamental insight is identical: **isolation enables safe speculation**.

### 2.6 Bang Facts = ETS Tables

| `!A` (persistent fact) | ETS |
|---|---|
| Readable by any rule, never consumed | Readable by any process, persists |
| `state.persistent` FactSet | Named ETS table |
| `provePersistentGoals` queries them | `ets:lookup` queries them |
| Survive across rule firings | Survive across process restarts |

CALC's persistent proving (Level 1: state lookup, Level 2: backward prove via FFI/clauses) maps to ETS reads with optional computation.

## 3. The CLF Connection

The deepest theoretical link runs through CLF (Concurrent Logical Framework, Watkins et al. 2002). CLF extends the logical framework LF with linear types and a monad for concurrency, producing exactly the split that both CALC and OTP embody:

| CLF Concept | CALC | OTP |
|---|---|---|
| Monadic (synchronous) fragment | Forward engine — committed choice, no backtracking | GenServer — serial message processing |
| Backward (asynchronous) fragment | `prove.js` — goal-directed search | Application startup — dependency resolution |
| Definitional equality (independent steps commute) | Committed-choice confluence | Message ordering within a process is deterministic |
| Linear hypotheses | Linear facts in state | Messages in mailbox |
| Persistent hypotheses | Bang facts | ETS / application env |

Cervesato & Scedrov (2009) formalize this precisely: their language ω bridges state-based and process-based concurrency through multiset rewriting built from ILL connectives. CALC's forward engine IS a multiset rewriting system. OTP processes ARE concurrent multiset rewriters.

## 4. Formal Foundations

### 4.1 Propositions as Sessions

The lineage: Honda 1993 (binary session types) → Abramsky 1994 (proofs as processes) → Bellin & Scott 1994 (CLL ↔ π-calculus) → Caires & Pfenning 2010 (DILL = session-typed π) → Wadler 2012 (CP calculus, CLL = sessions).

The Caires-Pfenning result is the tightest: cut reduction steps in dual intuitionistic linear logic correspond 1:1 to communication steps in the session-typed π-calculus. Cut elimination = protocol completion. A well-typed session cannot deadlock — deadlock freedom is a theorem of the logic, not an engineering invariant.

### 4.2 Multiparty Extension

Honda, Yoshida & Carbone (POPL 2008) extend to n parties via global types projected to local types. The challenge: linear logic's duality works for 2 parties. Carbone et al. (CONCUR 2016) solve this by replacing duality with **coherence** — an n-ary compatibility notion. The cut rule generalizes to composing n processes.

### 4.3 Fault Tolerance

Two recent results address the gap between session types and real failure:

- **FTMPST** (Peters, Nestmann, Wagner, FORTE 2022): extends MPST with sender crash, receiver crash, and medium loss. Uses failure patterns to model failure detectors.
- **Crash-Stop MPST** (Barwell, Scalas, Yoshida, Zhou, CONCUR 2022): parametric safety covering the spectrum from fully reliable to fully unreliable sessions.

**Gap**: no type-theoretic treatment of supervision policies (one-for-one, rest-for-one, one-for-all) as first-class typed constructs.

### 4.4 Erlang + Session Types

Neykova & Yoshida (COORDINATION 2014) implement session actors — Erlang processes simultaneously participating in multiple sessions, with Scribble protocols for specification and runtime monitoring. Fowler (2015) monitors gen_server communication against MPST specifications. Both integrate with "let it crash" by treating protocol violation as a crash-worthy condition.

## 5. What This Means for CALC

### 5.1 CALC Can Model OTP Systems

CALC's forward engine already has the right primitives:

```
%% GenServer state machine as forward rules
%% State = linear fact, messages = linear facts, config = persistent

handle_add :  state S * msg (add X) -o { state (S + X) }
handle_get :  state S * msg get     -o { state S * reply S }
```

Supervision structure would be encoded as meta-level rules governing restart:

```
%% one_for_one: restart just the failed child
supervise : failed Child * child_spec Child Init -o { state Init * child_spec Child Init }
```

### 5.2 Protocol Verification

Since ILL connectives = session type constructors (§2.3), CALC's backward prover could verify protocol compliance: given a protocol spec (sequent) and an implementation (proof), proof search confirms they match. This is exactly Wadler's CP correspondence made executable.

### 5.3 Deadlock Freedom as Proof Search

A CALC proof that completes (all linear resources consumed, succedent established) corresponds to a protocol that terminates without deadlock. Failed proof search = potential deadlock. The structural memo optimization (§symexec) would detect equivalent protocol states — important for cyclic protocols.

### 5.4 gen_statem as Linear State Machine

```
%% State transitions consuming old state, producing new
%% Guards via persistent predicates
idle    * event start             -o { running }
running * event pause * !can_pause -o { paused  }
paused  * event resume            -o { running }
running * event stop              -o { done    }
```

The linear discipline guarantees: exactly one state at a time, no state duplication, every transition consumes the old state. CALC's constraint solver prunes impossible transitions (guard UNSAT → dead branch).

### 5.5 Open Problems

1. **Supervision typing**: encode restart strategies as logical connectives. `one_for_one` ≈ `⊗` (independent), `one_for_all` ≈ `&` (coupled). Can this be made precise?
2. **Hot code loading**: model as linear resource replacement — consume old code version, produce new. How does this interact with in-flight state?
3. **Distribution**: BEAM's location-transparent `Pid ! Msg` maps to linear logic's structural rules. Can we model network partition as failure of cut?
4. **Dynamic supervision** (simple_one_for_one): unbounded process creation maps to `!` — a persistent template producing linear instances. This is exactly bang elimination.

## 6. Key References

- Caires, L. & Pfenning, F. (2010). "Session Types as Intuitionistic Linear Propositions." CONCUR.
- Wadler, P. (2012). "Propositions as Sessions." ICFP.
- Watkins, K. et al. (2002). "A Concurrent Logical Framework." TYPES.
- Cervesato, I. & Scedrov, A. (2009). "Relating State-Based and Process-Based Concurrency through Linear Logic." Inf. & Comp.
- Honda, K., Yoshida, N. & Carbone, M. (2008). "Multiparty Asynchronous Session Types." POPL.
- Neykova, R. & Yoshida, N. (2014). "Session Actors." COORDINATION.
- Barwell, A. et al. (2022). "Crash-Stop MPST." CONCUR.
- Armstrong, J. (2003). "Making Reliable Distributed Systems in the Presence of Software Errors." PhD thesis.
- Simmons, R. (2012). "Substructural Logical Specifications." PhD thesis, CMU.
- Kobayashi, N. & Yonezawa, A. (1994). "Asynchronous Communication Model Based on Linear Logic." Formal Aspects of Computing.
