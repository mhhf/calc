---
title: "Debugging and Tracing in Logic Programming and Forward Execution Engines"
created: 2026-04-09
modified: 2026-04-09
summary: "Survey of debugging/tracing theory across LP systems (Byrd Box, spy points, Mercury/SWI trace), linear logic debuggers (Celf, Forum, Ceptre), zero-cost instrumentation patterns (V8, JVM JVMTI), and separation-of-concerns architectures for execution engine observability."
tags: [debugging, tracing, prolog, linear-logic, forward-chaining, hooks, instrumentation, engine, performance, clf, Celf, Ceptre]
category: "Implementation"
---

# Debugging and Tracing in Logic Programming and Forward Execution Engines

## 1. Byrd Box Model (Prolog Standard)

### 1.1 Origin and Ports

The **Byrd Box model** (Lawrence Byrd, 1980, "Understanding the Control Flow of Prolog Programs") is the canonical debugging model for Prolog-style backward chaining. Every goal is conceptualized as a box with four ports:

| Port | Meaning | When |
|---|---|---|
| **Call** | Entry — goal is first invoked | Before resolution begins |
| **Exit** | Success — goal succeeded, bindings established | After a successful clause body |
| **Fail** | Failure — goal failed (all clauses exhausted or body failed) | After all alternatives fail |
| **Redo** | Retry — backtracking into a previously-succeeded goal | Backtracking after a later goal fails |

The four-port model captures the full lifecycle of backward chaining. The typical sequence for a single successful invocation is `Call → Exit`; for a failing goal: `Call → Fail`; for a goal that succeeds once and then is retried: `Call → Exit → Redo → Exit` (or `→ Redo → Fail`).

**Reference:** Byrd, L. (1980). "Understanding the Control Flow of Prolog Programs." *Proceedings of the 1980 Logic Programming Workshop*. Edinburgh. (Also described in O'Keefe 1990 "The Craft of Prolog", Chapter 9.)

### 1.2 Step Counting vs Depth Tracking — the Byrd Convention

Byrd established a convention that is still followed in modern systems:

- **Invocation number** (`i`): A monotonically increasing counter across the entire trace. Identifies which Call event this is. Increments every time a new goal is invoked (a new Call port event). Also called "step" in modern implementations.
- **Depth** (`d`): The current stack depth — how many Call events are on the call stack at this point. Starts at 0 or 1 at the top level.

The standard trace output format in SWI-Prolog follows:
```
  [step,depth] Port: Goal
  [1,1] Call: member(X, [1,2,3])
  [2,2] Call: X = 1
  [2,2] Exit: X = 1
  [1,1] Exit: member(1, [1,2,3])
```

Both counters serve different purposes: **step/invocation** identifies a unique event globally (useful for setting "break at step N"), while **depth** shows the nesting level (useful for indenting output and reasoning about stack behavior).

**CALC relevance:** The `exec()` / `explore()` distinction in CALC directly follows this convention: `exec()` uses `{ step }` (monotonic counter across an execution run) while `explore()` uses `{ depth }` (DFS nesting level). This is deliberate: forward committed-choice execution does not backtrack, so a step counter is the natural measure. Exhaustive DFS exploration does nest, so depth is the natural measure.

### 1.3 Ports in SWI-Prolog

SWI-Prolog (van der Weide et al.) implements the four-port model with extensions:

- `trace/0`: Enter trace mode — all goals traced.
- `debug/0`: Enter debug mode — spy points only.
- `spy(Predicate)`: Set a spy point on a predicate. Triggers the debugger when `Predicate` is called/exited/failed.
- `nospy(Predicate)`: Remove spy point.
- `leash(+Ports)`: Which ports cause interaction. E.g., `leash(-all)` to run silently.
- `visible(+Ports)`: Which ports produce trace output.

SWI-Prolog also adds two extra ports beyond the four-port model:
- **Exception** port: Goal throws an exception.
- **Unify** port: Unification step (optional, very verbose).

**Reference:** SWI-Prolog manual: https://www.swi-prolog.org/pldoc/man?section=debugger

### 1.4 The "Creep/Leap/Skip" Interaction

In interactive trace mode, three commands control execution granularity:
- **Creep** (c, Enter): Single-step to next port event.
- **Leap** (l): Continue until the next spy point.
- **Skip** (s): Skip the rest of the current goal (complete it silently).

This suggests a layered model: the trace hook fires at every port, but the *interaction* filter decides whether to pause. This separation is architecturally significant — the trace **emitter** is always active, but the **consumer** decides granularity. CALC's `onStep` hook follows the same principle: zero-cost when `null`, observer-decides-granularity when provided.

## 2. Spy Points and Observation Directives

### 2.1 SWI-Prolog Spy Points

A **spy point** is a named predicate for which the debugger fires regardless of `trace/debug` mode. The concept originates with Prolog (Clocksin & Mellish 1981). Mechanism:

1. Predicates have a `spy` flag in their definition.
2. The interpreter checks this flag at Call, Exit, Fail, Redo.
3. If set, the debugger is invoked regardless of global trace mode.

SWI-Prolog spy points are permanent until explicitly removed, survive interpreter state. They can be conditional (via `spy/2` with a filter).

### 2.2 Mercury Debugging Infrastructure

Mercury (Somogyi et al., 1996 onward) has a distinct debugging model adapted for a purely declarative language with determinism declarations. Key systems:

**mdb** (Mercury debugger, Somogyi & Jeffery 1999): A port-based debugger adapted for Mercury's type system and determinism declarations. Mercury predicates are annotated with determinism modes (`det`, `semidet`, `nondet`, `multi`, `erroneous`, `failure`). The debugger understands that `det` predicates cannot have Redo/Fail ports.

Key innovation: **declarative debugging** (Shapiro 1982, refined for Mercury by Naish 1997). Instead of procedural trace inspection, declarative debugging asks the user "is this call correct?" and uses binary search over the execution tree to locate the bug. This is theoretically sound but requires user interaction.

**Reference:** Somogyi, Z., Henderson, F., & Conway, T. (1996). "The execution algorithm of Mercury, an efficient purely declarative logic programming language." *Journal of Logic Programming* 29(1-3), 17-64.

### 2.3 Logtalk Debugging (spy on objects)

Logtalk (Pinto & Moura) extends SWI-Prolog's debugging model with object-level spy points. A spy point can be set on a `(Object, Predicate)` pair, allowing selective debugging of specific object instances. This prefigures CALC's `filter` setting on `#trace` directives (filter by rule name).

### 2.4 Ceptre Trace Directives

Ceptre (Martens 2015) has execution directives that are the direct lineage of CALC's observation directives:

```ceptre
#trace _ main init.    % Random execution trace
#interactive combat.   % Interactive: human selects rule to fire
```

The `#trace` directive triggers a random forward execution from `init`, printing each rule that fires. The syntax `_ main init` means "any number of steps, in stage main, from initial context init". Ceptre's tracing is output-only (no hooks API), but the concept of file-embedded trace directives is directly inherited.

**Reference:** Martens, C. (2015). "Ceptre: A Language for Modeling Generative Interactive Systems." *Foundations of Digital Games*.

### 2.5 Celf Trace and Query Directives

Celf (Schack-Nielsen & Schürmann 2008) has:

```celf
#trace * {initial_state}.     % Forward trace to quiescence
#query * 1 1 10 A.             % Query: 10 attempts to prove A
#exec * {state}.               % Execute (synonym for trace)
```

The `*` parameter controls the "trace level" — whether intermediate states are printed. Celf's trace output shows each step as a rule name followed by the resulting state.

**Key insight:** Celf's trace model is "print everything" — it has no selective filtering. CALC improves on this with named directives (`#trace_name`) + `--only` filtering.

**Reference:** Schack-Nielsen, A. & Schürmann, C. (2008). "Celf — A Logical Framework for Deductive and Concurrent Systems." *IJCAR 2008*, LNCS 5195.

### 2.6 Forum / Linear Logic Programming Debugging

**Forum** (Miller 1994) is a linear logic programming language (subset of linear logic as a programming language). Forum does not have a dedicated debugging system in the literature — it was primarily a theoretical language.

**Lolli** (Hodas & Miller 1994) similarly has no dedicated trace infrastructure; it was implemented as a Prolog extension where Prolog's standard debugging applied.

**Linear Prolog systems** generally inherit Prolog's four-port model without adaptation for linearity. This is a gap: the four-port model does not have ports for resource consumption/production, which are the key observable events in a linear system.

## 3. Linear Logic Debugging — Specific Issues

### 3.1 The Resource Consumption Problem

Standard Prolog debugging only observes predicate invocations. Linear logic execution has an additional observable that matters for debugging: **which resources were consumed/produced on each step**. This is the key difference:

- Prolog trace: `[1,1] Call: foo(X)` — bindings visible, no resources
- Linear trace: `step 3: evm/add — consumed: [pc 5, gas 100, stack [1,2]]` — resources explicit

No existing LP debugging system (as of 2025) models this adequately. CALC's `onStep` hook (exposing `consumed`, `theta`, `slots`, `state`) is more information-rich than any standard LP debugger for resource-sensitive execution.

### 3.2 Resource Leak Detection

A common bug in linear logic programs is a "resource leak": facts produced that are never consumed, leaving the state non-empty at quiescence. This is analogous to memory leaks in imperative programs. Debugging tools for this:

- Celf's `#trace` prints the final state, making leaks visible.
- CALC's `#dump_state` groups by predicate, making it easy to see unexpected residual facts.

No theoretical paper addresses resource leak debugging specifically. This is an open research gap.

### 3.3 Existential Variable Debugging

When a rule produces existentially quantified facts (e.g., `∃x. storage x v`), tracing needs to show the witness chosen. CALC's `theta` snapshot in `onStep` carries the substitution, which includes these witnesses. This is richer than what Celf's trace shows.

### 3.4 Non-Determinism and Branching

In exhaustive exploration (`explore()`), the execution tree has branching points where multiple rules could fire. Standard debuggers have no model for this — they trace one execution path. CALC's `#debug` directive shows all leaves with their classification, which is closer to a model-checker inspection than a traditional debugger.

For linear logic specifically, the **bisimulation checking** literature (Sangiorgi & Walker, "The Pi-Calculus", 2001) is relevant — checking whether two execution trees have the same observable behavior, which can help verify that a program transformation preserved semantics.

## 4. Engine Hooks and Instrumentation Patterns

### 4.1 Zero-Cost Instrumentation

The canonical pattern for zero-cost optional instrumentation in high-performance engines is **null guard + branch prediction**:

```javascript
const onStep = opts.onStep || null;
// In hot loop:
if (onStep) onStep({ ... });
```

When `onStep` is `null`, V8 branch-predicts the `if` as never-taken after the first few iterations. The cost is effectively a single predicted branch (< 1 cycle). This is the same pattern used in CALC's `forward.run()` and `explore()`.

**Reference for V8 branch prediction:** Intel 64 Manual Vol. 3B, "Branch Prediction" (§17.4). V8 uses bimodal branch predictors for non-trivial hot loops. The null-guard pattern is standard practice in V8-targeting JavaScript engines.

### 4.2 JVMTI — JVM Tool Interface

The JVM's instrumentation model (JVMTI, JSR-163, 2004) is the most mature system for VM-level tracing. Key design decisions relevant to CALC:

**Capability model:** Agents must declare capabilities at startup (`AddCapabilities`). The JVM can optimize code more aggressively for disabled capabilities. E.g., if `can_generate_method_entry_events` is not requested, the JVM does not insert instrumentation hooks in method prologues.

**Event subscription:** Agents subscribe to specific event types (`MethodEntry`, `MethodExit`, `Exception`, `FieldModification`, etc.) via `SetEventNotificationMode`. Unsubscribed events have zero cost.

**Key insight:** Capability pre-declaration at startup is what enables zero-overhead for disabled capabilities. Runtime opt-in/opt-out still has overhead (checking a flag on each potential event site). JVMTI chooses the stronger guarantee: **no hook = no cost**, enforced at JIT compile time.

For CALC, this means: if the `onStep` hook is provided at `exec()` call time, there is no way to make it zero-cost for that run. The current null-check is the correct approach for call-level granularity. For even finer control, a "pre-declared" API (e.g., `calc.withHooks({onStep: fn}).exec(state)`) could allow the engine to JIT-specialize the hot loop — but this would require `new Function` or code generation.

**Reference:** JSR-163: "JavaTM Platform Profiler Architecture." Sun Microsystems, 2004. https://jcp.org/en/jsr/detail?id=163

### 4.3 V8 Profiler and --trace-ic

V8 exposes instrumentation through:
- `--prof`: Sampling profiler (tick-based, low overhead ~1-2%).
- `--trace-ic`: Log all inline cache state transitions (high overhead).
- `--trace-opt` / `--trace-deopt`: Optimization/deoptimization events.

The key design: `--trace-ic` is a **compile-time flag** — it is not settable per-call. When enabled, every IC site has instrumentation code. When disabled, that code is absent. V8 does not support per-IC runtime enable/disable without regenerating code.

This confirms that the strongest zero-cost guarantee requires **compile-time** selection of instrumentation, not runtime null-checks. Runtime null-checks are "almost zero cost" (1 predicted branch per hook site), not literally zero.

### 4.4 Mozilla SpiderMonkey Profiler

SpiderMonkey uses a similar pattern with the JIT-level "profiling mode": when profiling is active, the JIT emits extra code to push/pop to a virtual stack. When inactive, that code is not emitted. The transition from non-profiling to profiling mode requires discarding JIT code and re-jitting.

**Reference:** Ting, M. et al. "A Walk Through SpiderMonkey's Profiler." Mozilla Hacks Blog.

### 4.5 Lua/LuaJIT Debugging Hooks

Lua's debug hook API (`lua_sethook`) is particularly relevant as it has call/return/line granularity similar to Prolog's four ports:

```c
void lua_sethook(lua_State *L, lua_Hook f, int mask, int count);
// mask: LUA_MASKCALL | LUA_MASKRET | LUA_MASKLINE | LUA_MASKCOUNT
```

When no hook is set, the interpreter skips the hook check entirely (there is an `L->hookmask` integer that is checked — a single integer load and branch). This is effectively a single-instruction check per call/return site, which is the same strategy as CALC's `onStep || null`.

LuaJIT with tracing JIT: hooks force fallback to the interpreter (tracing is disabled when hooks are active). This is the tradeoff — instrumentation and full JIT optimization are mutually exclusive.

**Reference:** Ierusalimschy, R. (2006). "Programming in Lua." 2nd ed. Chapter 23 "The Debug Library."

### 4.6 GraalVM / Truffle Instrumentation Framework

GraalVM's Truffle framework (Wöß et al. 2014) has the most sophisticated approach: **partial evaluation with profile-guided specialization**. Instrumentation is implemented as AST nodes; when disabled, they are replaced with identity nodes that are eliminated by partial evaluation.

The key insight: in a PE-based system, the "cost of a no-op instrumentation node" is literally zero because PE eliminates it at compile time. This is theoretically optimal but requires the engine to be written in Truffle's style.

**Reference:** Wöß, A. et al. (2014). "An Object Storage Model for the Truffle Language Implementation Framework." *PPPJ 2014*.

## 5. Separation of Concerns in Debug Infrastructure

### 5.1 The "Observer Pattern" for Engine Hooks

The canonical software engineering pattern for engine observability is the **Observer/Event pattern** (GoF "Design Patterns", Gamma et al. 1994). The engine is the Subject; debuggers/profilers are Observers. The Subject has no knowledge of Observers — it only emits events.

CALC follows this: `onStep` and `onProveFail` are callbacks passed to `exec()`/`explore()`. The engine emits events but has no knowledge of what the observer does with them. The observer registry is simply the `opts` object.

### 5.2 The Aspect-Oriented Approach

Aspect-Oriented Programming (AOP, Kiczales et al. 1997) offers a more powerful separation: debug code is defined in "aspects" that are woven into the engine at specific "join points" (rule firings, match attempts, proof failures). The original Aspectj system demonstrates this.

For a symbolic execution engine, the relevant join points are:
- Rule match found (pre-application)
- Rule applied (post-mutation)
- Rule match failed
- Persistent goal proved / failed
- State cycle detected
- Exploration bound hit

CALC exposes only a subset: rule-applied (`onStep`) and persistent-goal-failed (`onProveFail`). Absent: rule-match-attempted, state-cycle, exploration-bound. These could be future hook additions.

**Reference:** Kiczales, G. et al. (1997). "Aspect-Oriented Programming." *ECOOP 1997*, LNCS 1241.

### 5.3 Separation in Logtalk

Logtalk's `logtalk_make/1` and its meta-predicates demonstrate a clean separation between the logical system and its instrumentation layer. Debugging predicates are implemented as meta-interpreters that wrap the standard interpreter:

```prolog
:- meta_predicate trace_call(0).
trace_call(Goal) :-
    debug_call_port(Goal),
    call(Goal),
    debug_exit_port(Goal).
```

This is a textbook separation: the debug layer (`trace_call`) wraps the base layer (`call`) without modifying it. The base interpreter has no knowledge of tracing.

CALC's architecture partially follows this: the hook callbacks are injected via `opts` without the engine having special debug logic. However, CALC's `onStep` fires **after** state mutation (post-apply), not before. A two-phase hook (`onBeforeStep` / `onAfterStep`) would give both pre- and post-mutation observations without engine modification.

### 5.4 Separating Logging from Computation in CHR

Constraint Handling Rules (CHR, Frühwirth 1998) has a specific debugging tool: **chr_show_store/1** which dumps the current constraint store without modifying execution. This mirrors CALC's `#dump_state` directive.

CHR systems (SWI-Prolog CHR library) also support rule tracing via:
```prolog
:- use_module(library(chr)).
:- chr_constraint foo/1.
:- chr_show_store(foo).
```

The store dump is declarative and non-invasive — it reads state without affecting it. CALC's `groupByPredicate()` in `directive-loader.js` implements the same abstraction.

**Reference:** Frühwirth, T. (1998). "Theory and practice of constraint handling rules." *Journal of Logic Programming* 37(1-3), 95-138.

### 5.5 The Probe Effect Problem

The **probe effect** (Heisenberg effect in debugging) occurs when the act of observation changes the computation. In LP engines:

1. **Allocation overhead**: Creating trace objects (`{ step, rule, consumed, theta }`) on every step allocates in the hot path. In CALC, `{ ...m.consumed }` and `m.theta.slice()` are snapshots that allocate only when `onStep` is non-null.

2. **GC pressure**: Frequent trace allocations increase GC pressure. In a long-running execution with thousands of steps, trace objects accumulate and trigger more frequent GC pauses.

3. **JIT deoptimization**: In V8/SpiderMonkey, if the trace callback has side effects (e.g., printing, maintaining a Set), it may cause the JIT to deoptimize the calling function.

**Mitigation strategies:**
- **Lazy materialization**: Pass a lazy view object instead of a snapshot. The observer materializes fields only if it accesses them. (Used in some JVM profilers.)
- **Ring buffer trace**: Pre-allocate a fixed-size ring buffer for trace entries, reusing slots. Avoids GC pressure for bounded traces.
- **Sampling**: Fire `onStep` only every N steps. Reduces allocation by N.

CALC uses the snapshot approach (`{ ...m.consumed }`, `m.theta.slice()`). For high-frequency tracing, a ring buffer could be considered.

## 6. Synthesis: Design Principles for CALC's Debug Framework

### 6.1 What Exists (well-founded)

CALC's current framework already follows best practices in several areas:

| Practice | Source | CALC Implementation |
|---|---|---|
| Step counter for committed-choice | Byrd 1980 (monotonic invocation number) | `{ step }` in `exec()` |
| Depth for DFS exploration | Byrd 1980 (depth counter) | `{ depth }` in `explore()` |
| Null-guard zero cost | Lua/JVMTI pattern | `const onStep = opts.onStep || null` |
| Snapshot consumed/theta | Probe effect mitigation | `{ ...m.consumed }`, `m.theta.slice()` |
| Named observation directives | Ceptre `#trace`, Celf `#trace` | `#trace_name`, `#dump_state_name`, etc. |
| File-embedded directives | Celf/Ceptre convention | `.ill` file directives |
| Failure reason in onProveFail | SWI-Prolog port model | `'cached_failure'|'exhausted'|'external_binding'` |

### 6.2 What is Novel in CALC (no direct precedent)

| Feature | CALC | Gap in prior work |
|---|---|---|
| Resource consumption in onStep (`consumed`) | First-class observable | No LP debugger exposes consumed resources |
| Named directives per state in file | `#trace_name initial_state .` | Celf/Ceptre have unnamed global trace |
| `onProveFail` with reason codes | Three-way failure reason | Prolog only has Fail port (no reason) |
| Combined forward/backward hooks (same API) | `exec`/`explore` with same `onStep` shape | No mixed-mode LP system has this |
| Per-leaf exploration classification (`classifyLeaf`) | Model-checker-style leaf categorization | Novel for LP debugging |

### 6.3 Research-Grade Gaps (potential future work)

1. **Pre-application hook**: Current `onStep` fires post-mutation. A pre-step hook would allow observers to record state before mutation (useful for "what changed" diffs without re-computing from scratch).

2. **Conditional breakpoints**: SWI-Prolog supports `spy/2` with conditions. CALC's `filterRule` in `#trace` settings is a primitive form, but no programmatic condition API exists.

3. **Declarative debugging for linear logic**: Shapiro's algorithmic debugging (1982) + Naish's Mercury adaptation (1997) could be adapted for linear resource programs. A "is this rule application correct?" oracle could localize bugs automatically.

4. **Execution tree visualization**: CALC builds an execution tree in `explore()`. Connecting this to a debugger UI (like the Prolog trace trees in Mercury's mdb) is not yet done.

5. **Proof certificate extraction for failed executions**: When `exec()` reaches quiescence on an unexpected state, providing a "why did I get here" explanation requires backward-chaining over the execution trace — a form of **blame assignment** similar to type error localization.

## 7. Key References

### Foundational
- Byrd, L. (1980). "Understanding the Control Flow of Prolog Programs." *Logic Programming Workshop 1980*, Edinburgh.
- Clocksin, W. & Mellish, C. (1981). "Programming in Prolog." Springer. (Chapter on the four-port model.)
- O'Keefe, R. (1990). "The Craft of Prolog." MIT Press. Chapter 9.

### Mercury Debugging
- Somogyi, Z., Henderson, F., Conway, T. (1996). "The execution algorithm of Mercury." *JLP* 29(1-3), 17-64.
- Jeffery, D., Somogyi, Z. (1999). "Declarative Debugging with Dynamic Slicing." *ICLP 1999*.

### Linear Logic Systems
- Schack-Nielsen, A. & Schürmann, C. (2008). "Celf — A Logical Framework for Deductive and Concurrent Systems." *IJCAR 2008*, LNCS 5195.
- Martens, C. (2015). "Ceptre: A Language for Modeling Generative Interactive Systems." *FDG 2015*.
- Hodas, J. & Miller, D. (1994). "Logic Programming in a Fragment of Intuitionistic Linear Logic." *Information and Computation* 110(2), 327-365. (Lolli)
- Miller, D. (1994). "A Multiple-Conclusion Meta-Logic." *LICS 1994*. (Forum)

### Instrumentation Engineering
- JSR-163 (2004). "JavaTM Platform Profiler Architecture." Sun Microsystems.
- Ierusalimschy, R. (2006). "Programming in Lua." 2nd ed. Chapter 23.
- Wöß, A. et al. (2014). "An Object Storage Model for the Truffle Language Implementation Framework." *PPPJ 2014*.
- Kiczales, G. et al. (1997). "Aspect-Oriented Programming." *ECOOP 1997*, LNCS 1241.

### CHR and Forward Chaining Debugging
- Frühwirth, T. (1998). "Theory and practice of constraint handling rules." *JLP* 37(1-3), 95-138.
- Schrijvers, T. & Frühwirth, T. (2005). "Optimal Union-Find in Constraint Handling Rules." *TPLP* 6(1-2).

### Declarative Debugging
- Shapiro, E.Y. (1982). "Algorithmic Program Debugging." MIT Press.
- Naish, L. (1997). "A Declarative Debugging Scheme." *Journal of Functional and Logic Programming*.
