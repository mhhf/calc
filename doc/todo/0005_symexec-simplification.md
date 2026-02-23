---
title: "Symbolic Execution: Constraint Propagation"
created: 2026-02-18
modified: 2026-02-23
summary: "Constraint propagation levels for eigenvariable path: equality resolution, FFI re-check, chain simplification, domain propagation, multi-mode resolution. Full theory, worked examples, implementation options, and architecture."
tags: [symexec, simplification, constraint-propagation, CLP, CHR, eigenvariable]
type: implementation
cluster: Symexec
status: planning
priority: 5
depends_on: [TODO_0004]
required_by: []
---

# Constraint Propagation

After [TODO_0004](0004_symexec-backward-foundation.md) (∃ + eigenvariables, **done**), constraints accumulate without simplification. This TODO adds propagation levels incrementally.

## Current State (post TODO_0004)

After TODO_0004, the forward engine handles symbolic values via eigenvariables:

```
evm/add fires:
  antecedent: pc(44) * code(44, 0x01) * stack(1, ?D) * stack(0, binlit(1)) * !inc(44, 45)
  ∃-resolution: plus(?D, binlit(1), C) — FFI fails (?D not ground)
                                        — backward fails (no clause matches)
                                        → C = evar(0) (fresh eigenvariable)
  consequent:  pc(45) * stack(0, evar(0)) * !plus(?D, binlit(1), evar(0))
```

The constraint `!plus(?D, binlit(1), evar(0))` persists in state. `evar(0)` flows through subsequent computation as an opaque placeholder. When `?D` later becomes ground (e.g., via ⊕ branching: `!eq(?D, 5)`), the constraint is **not** automatically re-checked.

**Problem:** Constraints accumulate indefinitely. After k arithmetic operations on symbolic values, state contains k persistent constraint facts. No simplification, no resolution, no pruning.

**Code paths involved:**
- `resolveExistentials` (match.js:370–398) — creates evars for unresolved ∃-slots
- `provePersistentGoals` (match.js:269–355) — three-level fallback (state → FFI → backward)
- `mutateState` (symexec.js:284–348) — adds persistent constraints to state
- `freshEvar` (fresh.js:14–18) — monotonic BigInt counter

---

## Theory: Why Constraint Propagation is Needed

### The Constraint Accumulation Problem

Consider a sequence of symbolic EVM operations:

```
Step 0: state has ?D (symbolic calldata)
Step 1: ADD  → evar(0), constraint !plus(?D, 1, evar(0))
Step 2: MUL  → evar(1), constraint !mul(evar(0), 2, evar(1))
Step 3: ADD  → evar(2), constraint !plus(evar(1), 7, evar(2))
Step 4: GT   → ⊕ branch on gt(evar(2), 100, ...)
```

At step 4, the ⊕ branching produces two children:
- Branch A: `!gt(evar(2), 100, (i e))` (true)
- Branch B: `!gt(evar(2), 100, e)` (false)

Both branches survive because `evar(2)` is symbolic. Later, if `?D` becomes ground via another branch:
```
Step 5 (in some parent branch): !eq(?D, 50)
```

Now the entire chain is ground-solvable:
- `?D = 50` → `plus(50, 1, C)` → `C = 51` → evar(0) should be 51
- `mul(51, 2, C)` → `C = 102` → evar(1) should be 102
- `plus(102, 7, C)` → `C = 109` → evar(2) should be 109
- `gt(109, 100, R)` → `R = 1` → Branch A survives, Branch B is infeasible

**Without propagation:** Both branches survive. State carries 4 unresolved constraints. Subsequent rules see `evar(2)` (opaque) instead of `109` (ground). More evars accumulate. The tree grows unnecessarily.

**With propagation:** The equality `evar(0) = 51` cascades through the chain, resolving all evars. Branch B is pruned. State is clean.

### Theoretical Framework

This is a well-studied problem with three parallel formulations:

#### CLP (Constraint Logic Programming)

Eigenvariable constraints map to CLP's **constraint store**. Each persistent fact `!plus(?D, 1, evar(0))` is a constraint in the store. Propagation is the process of deriving new constraints from existing ones until fixpoint.

**CLP(FD) model:** Each eigenvariable has an implicit domain (all possible 256-bit values). Constraints narrow domains. When a domain becomes a singleton, the evar auto-binds. When a domain becomes empty, the branch is infeasible.

- **Bounds propagation:** For `!plus(X, Y, Z)`: `Z.lo = X.lo + Y.lo`, `Z.hi = X.hi + Y.hi` (and symmetric). O(1) per constraint per wakeup. Sufficient for path feasibility detection.
- **Arc consistency (AC-3):** Queue of constraints to check. Domain change → re-enqueue affected constraints. O(ed^3) worst case, but domains are huge (2^256) so only bounds consistency is practical.

References: Jaffar & Maher 1994 (CLP survey), Triska 2012 (SWI-Prolog CLP(FD))

#### CHR (Constraint Handling Rules)

Constraint propagation rules are **CHR propagation/simpagation rules**. The equality resolution rule:

```chr
eq_bind @ !eq(evar(N), V) \ evar_constraint(evar(N), ...) <=> substitute(evar(N), V, ...).
```

This is simpagation: the equality is kept (persistent), the old constraint is replaced with a substituted version. CALC's forward rules already implement this pattern — the question is adding rules that specifically handle evar constraints.

**Confluence:** Propagation rules must be confluent (applying them in any order gives the same result). For equality resolution, this is trivially confluent — substitution commutes. For chain simplification (Level 2), confluence requires analysis.

References: Fruhwirth 2009, Duck et al. 2004 (refined operational semantics)

#### Attributed Variables (Holzbaur 1992)

In Prolog, attributed variables carry constraints. When unified (bound), a hook fires that propagates to dependent constraints. CALC's analog:

| Attributed Variable | CALC |
|---------------------|------|
| Variable with constraint list | `evar(N)` + persistent facts referencing it |
| `verify_attributes` on binding | Forward rule matching when evar resolves |
| Wakeup on unification | Re-check constraints whose inputs became ground |
| Attribute = interval domain | Persistent fact `domain(evar(N), lo, hi)` |

**Gap:** CALC lacks the **wakeup mechanism**. When `evar(N)` resolves, there's no automatic trigger to re-check dependent constraints. Each propagation level below addresses a piece of this gap.

### Relationship to Existing CALC Architecture

CALC's forward engine already has the architectural primitives for CLP-style constraint handling:

| CLP Primitive | CALC Equivalent | Status |
|---------------|-----------------|--------|
| Constraint store | `state.persistent` | Exists |
| Propagators | Forward rules | Exists |
| Guard evaluation | FFI + backward proving | Exists |
| Coroutining/freeze | Loli mechanism `!P -o {body}` | Exists |
| Incremental state | `mutateState` / `undoMutate` | Exists |
| Wakeup on binding | **Missing** — no trigger on evar resolution | TODO_0005 |
| Domain tracking | **Missing** — no interval bounds per evar | TODO_0005 |
| Substitution cascade | **Missing** — no evar→value replacement | TODO_0005 |

The **missing piece** is the propagation loop: detect evar resolution → substitute → re-check dependent constraints → repeat until fixpoint.

---

## Worked Example: Symbolic ADD Chain

Trace through a concrete scenario to understand what each level buys.

### Setup

```ill
% State after loading EVM bytecode
pc(0), code(0, 0x01), code(1, 0x01), code(2, 0x14),
stack(2, ?D), stack(1, binlit(3)), stack(0, binlit(5)),
sh(s(s(s(e)))),
!inc(0, 1), !inc(1, 2), !inc(2, 3)
```

`?D` is symbolic calldata (not a ground numeral).

### Step 1: ADD — `plus(?D, binlit(3), ?)`

```
evm/add matches: pc(0) * code(0,0x01) * stack(2,?D) * stack(1,binlit(3)) * !inc(0,1)
  ∃-resolution: plus(?D, binlit(3), C)
    FFI: binToInt(?D) → null (not ground) → mode_mismatch → skip
    backward: no clause matches ?D → fail
    → C = evar(0)
  new state: pc(1), stack(1, evar(0)), !plus(?D, binlit(3), evar(0)), ...
```

### Step 2: ADD — `plus(evar(0), binlit(5), ?)`

```
evm/add matches: pc(1) * code(1,0x01) * stack(1,evar(0)) * stack(0,binlit(5)) * !inc(1,2)
  ∃-resolution: plus(evar(0), binlit(5), C)
    FFI: binToInt(evar(0)) → null → mode_mismatch → skip
    → C = evar(1)
  new state: pc(2), stack(0, evar(1)), !plus(evar(0), binlit(5), evar(1)), ...
```

### Step 3: EQ — compare `evar(1)` with `binlit(8)`

```
evm/eq matches: pc(2) * code(2,0x14) * stack(0,evar(1)) * ... * !inc(2,3)
  ⊕ branch: (stack(0, binlit(0)) * !neq(evar(1), binlit(8)))
           + (stack(0, binlit(1)) * !eq(evar(1), binlit(8)))

  Branch A: !neq(evar(1), 8) — symbolic, both survive
  Branch B: !eq(evar(1), 8) — symbolic, both survive
```

### Without Propagation (current)

State at branch B:
```
{ !plus(?D, 3, evar(0)),
  !plus(evar(0), 5, evar(1)),
  !eq(evar(1), 8) }
```
Three unresolved constraints. `evar(1)` is opaque — no further information extraction. If downstream rules need the value of `evar(1)`, they can't use it.

### With Level 0 (Equality Resolution)

`!eq(evar(1), 8)` → substitute `evar(1) → binlit(8)` everywhere:
- `!plus(evar(0), 5, evar(1))` becomes `!plus(evar(0), 5, binlit(8))`
- `stack(0, evar(1))` becomes `stack(0, binlit(8))` — but wait, this was consumed. The substitution applies to remaining state.

The evar is resolved. But the chain is not yet fully solved.

### With Level 0 + Level 1 (FFI Re-check)

After substituting `evar(1) → 8`, check: is `!plus(evar(0), 5, 8)` now solvable?
- Mode: `- + +`. Default FFI mode is `+ + -` (or `+ + +` multiModal). But reverse mode: if we know output (8) and one input (5), can we deduce the other? `8 - 5 = 3` → `evar(0) = 3`.
- With multi-mode FFI: `evar(0) → 3`.

Now check: `!plus(?D, 3, 3)`:
- Mode: `- + +`. Reverse: `3 - 3 = 0` → `?D = binlit(0)`.

**Full chain resolved.** From `!eq(evar(1), 8)`, we derived `?D = 0`, `evar(0) = 3`, `evar(1) = 8`. All symbolic values grounded.

Branch A: `!neq(evar(1), 8)` plus the same chain. If `evar(1) = 8` (derived from the chain), then `neq(8, 8)` → false → **branch pruned**.

### With Level 3 (Domain Propagation)

Even without concrete equality, we can narrow domains:
- `!plus(?D, 3, evar(0))`: if `?D ∈ [0, 2^256-1]`, then `evar(0) ∈ [3, 2^256+2]` (mod 2^256)
- `!plus(evar(0), 5, evar(1))`: `evar(1) ∈ [8, 2^256+7]`
- `!neq(evar(1), 8)`: `evar(1) ∈ [0, 7] ∪ [9, 2^256-1]` — narrow domain excludes 8

This is less powerful than full resolution but catches infeasibility early.

---

## Implementation Architecture

### Option A: Post-Step Propagation Loop

After each `mutateState`, run a propagation loop on newly added persistent facts:

```
mutateState produces log of new persistent facts →
  for each new persistent fact F:
    if F is an equality !eq(evar(N), value):
      substitute evar(N) → value in all state facts (Level 0)
      re-check constraints whose inputs changed (Level 1)
      repeat until fixpoint
```

**Pros:** Clean separation — propagation is a post-step pass, forward engine untouched.
**Cons:** Must walk all facts to substitute. Need inverted index for efficiency.
**Complexity:** O(affected_facts) per propagation step. With inverted index: O(1) lookup + O(k) substitution for k dependent facts.

### Option B: Constraint Store as Separate Module

Dedicated constraint store alongside `state.persistent`:

```javascript
state.constraints = {
  byEvar: Map<evarHash, [constraintFact, ...]>,  // inverted index
  domains: Map<evarHash, { lo, hi }>,              // interval bounds
  pending: [],                                      // wakeup queue
}
```

**Pros:** Clean data structure, O(1) lookups, dedicated propagation logic.
**Cons:** Parallel data structure that must stay in sync with `state.persistent`. Undo complexity.

### Option C: Forward Rules as Propagators (Pure ILL)

Express propagation as forward rules in .ill files:

```ill
% Level 0: Equality resolution (meta-rule, not user-level)
prop/eq_resolve: !eq(X, V) * fact_with(X, ...) -o { fact_with(V, ...) }.

% Level 1: FFI re-check
prop/recheck: !plus(A, B, C) * !ground(A) * !ground(B) -o { !plus_resolved(A, B, C) }.
```

**Pros:** No engine changes — propagation is just more forward rules. Theoretically clean.
**Cons:** Can't express meta-level substitution (walking inside terms) as an object-level rule. The `fact_with(X, ...)` pattern would need to match any fact containing evar — requires higher-order matching or reflection.

### Recommended: Option A with Inverted Index

Option A is simplest and most maintainable. The inverted index makes it efficient. It's the CLP(FD) architecture adapted to CALC:

```
Forward step → mutateState → new persistent facts
  ↓
propagateConstraints(state, newFacts):
  queue = newFacts
  while queue not empty:
    fact = dequeue()
    if isEqualityBinding(fact):      // Level 0
      evar, value = extractBinding(fact)
      affected = evarIndex[evar]
      for each constraint in affected:
        substitute evar → value in constraint
        if constraint now ground:
          result = tryFFIDirect(constraint)   // Level 1
          if result.success:
            add result bindings to queue (cascade)
          elif result === false:
            return INFEASIBLE               // prune branch
  return OK
```

**Data structures:**

```javascript
// Inverted index: evar hash → Set of persistent fact hashes containing it
state.evarIndex = new Map();  // populated in mutateState when adding persistent facts

// Add to mutateState:
for (const evar of extractEvars(factHash)) {
  if (!state.evarIndex.has(evar)) state.evarIndex.set(evar, new Set());
  state.evarIndex.get(evar).add(factHash);
}
```

**Undo:** The inverted index is monotonically growing within a branch (evars only accumulate). On `undoMutate`, entries added in the current step are removed. Track additions in the undo log.

---

## Propagation Levels (Incremental, Each Independent)

### TODO_0005.Level_0 — Equality Resolution (~50 LOC)

**Trigger:** A persistent fact `!eq(evar(N), value)` appears in state (from ⊕ branching path conditions).

**Action:** Substitute `evar(N) → value` in all persistent facts referencing `evar(N)`:

1. Look up `evarIndex[evar(N)]` → set of fact hashes
2. For each fact, rebuild with `evar(N)` replaced by `value`
3. Remove old fact from state, add new fact
4. Update `evarIndex` (remove evar(N) entries, add new entries if evar refs remain)
5. If the new fact is itself an equality binding, cascade (add to queue)

**Worked step-by-step:**

```
State: { !plus(?D, 3, evar(0)), !plus(evar(0), 5, evar(1)), !eq(evar(1), 8) }

Step 1: Process !eq(evar(1), 8)
  evarIndex[evar(1)] = { plus(evar(0), 5, evar(1)) }
  Substitute: plus(evar(0), 5, evar(1)) → plus(evar(0), 5, 8)
  State: { !plus(?D, 3, evar(0)), !plus(evar(0), 5, 8) }
  Queue: [plus(evar(0), 5, 8)]  (changed, may cascade)

Step 2: plus(evar(0), 5, 8) — not an equality, no cascade at Level 0
  Stop.
```

**Result:** One evar resolved. Remaining: `!plus(?D, 3, evar(0))`, `!plus(evar(0), 5, 8)`.

**Implementation:**

```javascript
function substituteEvar(state, evarHash, value) {
  const affected = state.evarIndex.get(evarHash);
  if (!affected) return [];
  const changed = [];
  for (const factHash of affected) {
    if (!state.persistent[factHash]) continue;
    const newFact = rebuildWithSubstitution(factHash, evarHash, value);
    if (newFact !== factHash) {
      delete state.persistent[factHash];
      state.persistent[newFact] = true;
      changed.push(newFact);
      // Update evarIndex for the new fact
      updateEvarIndex(state, factHash, newFact);
    }
  }
  state.evarIndex.delete(evarHash);
  return changed;
}

function rebuildWithSubstitution(hash, target, replacement) {
  if (hash === target) return replacement;
  const tag = Store.tag(hash);
  if (!tag) return hash;
  const arity = Store.arity(hash);
  let changed = false;
  const children = [];
  for (let i = 0; i < arity; i++) {
    const child = Store.child(hash, i);
    const newChild = rebuildWithSubstitution(child, target, replacement);
    children.push(newChild);
    if (newChild !== child) changed = true;
  }
  return changed ? Store.put(tag, children) : hash;
}
```

**Complexity:** O(k * d) where k = number of affected facts, d = average term depth. With content-addressed Store, `rebuildWithSubstitution` is memoized (same subterm → same rebuild).

**Undo:** Track `[oldFactHash, newFactHash]` pairs. On undo: restore old fact, remove new fact, restore evarIndex entries.

**Testing:** Unit test with the worked example above. Integration test: EVM ADD chain → EQ branch → verify evar resolved.

### TODO_0005.Level_1 — FFI Re-check (~30 LOC)

**Trigger:** After Level 0 substitution, a constraint's inputs are now all ground.

**Action:** Re-prove via FFI. If FFI succeeds, the output evar resolves → cascade.

**Extending the worked example:**

```
After Level 0: { !plus(?D, 3, evar(0)), !plus(evar(0), 5, 8) }

Level 1: Check !plus(evar(0), 5, 8)
  Mode analysis: - + + (all "input" modes except first)
  Standard FFI mode is + + - (compute output from inputs).
  Reverse mode: output=8, input2=5 → input1 = 8-5 = 3
  → evar(0) = 3

  Cascade to Level 0: substitute evar(0) → 3
  !plus(?D, 3, evar(0)) → !plus(?D, 3, 3)

Level 1 re-check: !plus(?D, 3, 3)
  Mode: - + + → reverse: ?D = 3-3 = 0
  But ?D is a freevar, not an evar. Do we bind it?
  Answer: Only bind evars. ?D is a program-level variable.
  → No cascade. Constraint remains.
```

**Multi-mode FFI:** Currently, FFI modes are fixed (`+ + -` for plus). To support reverse mode, extend the FFI:

```javascript
// Option 1: Explicit reverse-mode functions
const defaultMeta = {
  plus: {
    ffi: 'arithmetic.plus',
    modes: [
      { pattern: '+ + -', fn: 'arithmetic.plus' },        // C = A + B
      { pattern: '- + +', fn: 'arithmetic.plusReverse1' },  // A = C - B
      { pattern: '+ - +', fn: 'arithmetic.plusReverse2' },  // B = C - A
    ]
  },
  // ...
};

// Option 2: Single function with groundness analysis
function plusMultiMode(args) {
  const [a, b, c] = args;
  const aGround = isGround(a), bGround = isGround(b), cGround = isGround(c);
  if (aGround && bGround) return { success: true, theta: [[2, compute(a + b)]] };
  if (aGround && cGround) return { success: true, theta: [[1, compute(c - a)]] };
  if (bGround && cGround) return { success: true, theta: [[0, compute(c - b)]] };
  return null; // mode mismatch
}
```

Option 2 is simpler. ~15 LOC per FFI function. Only `plus`, `sub`, `mul` (with division for reverse) need multi-mode.

**Implementation:**

```javascript
function recheckConstraint(state, factHash, calc) {
  const goal = factHash;  // persistent fact IS the goal
  const result = tryFFIDirect(goal);  // already handles mode checking
  if (result && result.success) {
    // Extract evar bindings from result
    for (const [varHash, value] of result.theta) {
      if (Store.tag(varHash) === 'evar') {
        const changed = substituteEvar(state, varHash, value);
        // cascade: re-check changed constraints
        for (const c of changed) recheckConstraint(state, c, calc);
      }
    }
  }
  return result;
}
```

**Note:** `tryFFIDirect` currently returns bindings as `[[hashOfVar, value], ...]`. For multi-mode, it needs to be able to return bindings for input positions too. This requires extending the FFI return format.

**Complexity:** O(1) per FFI call. Cascade is bounded by constraint chain length (typically short — EVM arithmetic chains are ~5-10 deep).

**Testing:** Unit test: `!plus(evar(0), 5, 8)` → evar(0) resolves to 3 via reverse-mode FFI.

### TODO_0005.Level_2 — Chain Simplification (~100 LOC)

**Trigger:** Constraint chains where intermediate evars can be eliminated.

**Pattern:** `!plus(X, 3, evar(0)), !plus(evar(0), 5, evar(1))` → `!plus(X, 8, evar(1))`

This is **transitive constraint resolution**: if `evar(0) = X + 3` and `evar(1) = evar(0) + 5`, then `evar(1) = X + 8`. The intermediate `evar(0)` can be eliminated.

**When useful:** Long arithmetic chains on the same symbolic value. EVM gas computation often produces chains like:
```
!plus(2, GAS, evar(0))      % gas deduction for opcode
!plus(3, evar(0), evar(1))  % next gas deduction
!plus(2, evar(1), evar(2))  % next gas deduction
```

Chain simplification merges: `!plus(7, GAS, evar(2))`. Intermediate evars eliminated.

**Algorithm:**

```
For each constraint C with an evar in an "output" position:
  Look up evarIndex for that evar
  If exactly one other constraint has that evar in an "input" position:
    And both constraints use the same predicate (e.g., plus):
    Merge: combine constants, eliminate intermediate evar
```

**Confluence analysis:** `plus(X, a, Y), plus(Y, b, Z)` → `plus(X, a+b, Z)` is confluent iff:
- No other constraint references Y (the intermediate evar)
- The merge operation is associative (plus is associative)
- The merged constant `a+b` is computed correctly (use FFI)

For `plus`: trivially confluent (addition is associative). For `mul`: `mul(X, a, Y), mul(Y, b, Z)` → `mul(X, a*b, Z)` — also confluent. For mixed `plus`/`mul`: NOT simplifiable without distribution (which breaks termination — see [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) §3.3 "Dangerous rules").

**Implementation sketch:**

```javascript
function simplifyChain(state, evarHash) {
  const consumers = state.evarIndex.get(evarHash);
  if (!consumers || consumers.size !== 1) return false;  // branching — can't merge
  const consumer = [...consumers][0];
  const producer = findProducer(state, evarHash);  // constraint where evar is output
  if (!producer) return false;

  const pPred = getPredicateHead(producer);
  const cPred = getPredicateHead(consumer);
  if (pPred !== cPred) return false;  // different predicates — can't merge

  // Extract: producer = pred(X, a, evar), consumer = pred(evar, b, Y)
  // Merge: pred(X, a+b, Y)
  const merged = mergeConstants(producer, consumer, evarHash);
  if (!merged) return false;

  // Remove old constraints, add merged
  delete state.persistent[producer];
  delete state.persistent[consumer];
  state.persistent[merged] = true;
  // Update evarIndex
  state.evarIndex.delete(evarHash);
  updateEvarIndex(state, producer, merged);
  updateEvarIndex(state, consumer, merged);
  return true;
}
```

**Testing:** Unit test: chain of 3 plus constraints → simplified to 1. Integration: EVM gas chain.

### TODO_0005.Level_3 — Domain Propagation (~200 LOC)

**Trigger:** Any constraint involving evars, even when inputs aren't ground.

**Action:** Track interval bounds per evar. Narrow on each constraint addition. Prune when domain empty.

**Data structure:**

```javascript
// Per-evar domain: [lo, hi] inclusive (BigInt)
state.domains = new Map();  // evarHash → { lo: BigInt, hi: BigInt }

// Initialize: domain(evar(N)) = [0n, (1n << 256n) - 1n]  (uint256)
```

**Propagation rules for arithmetic:**

```
!plus(A, B, C):
  C.lo = max(C.lo, A.lo + B.lo)
  C.hi = min(C.hi, A.hi + B.hi)
  A.lo = max(A.lo, C.lo - B.hi)
  A.hi = min(A.hi, C.hi - B.lo)
  (symmetric for B)

!neq(A, V) where V is ground:
  if A.lo == V == A.hi: INFEASIBLE (domain empty after removing V)
  if A.lo == V: A.lo = V + 1
  if A.hi == V: A.hi = V - 1

!eq(A, V) where V is ground:
  A.lo = V, A.hi = V (singleton domain)
  → triggers Level 0 (equality resolution)

!gt(A, B, R):
  if R = 1 (true branch): A.lo = max(A.lo, B.hi + 1)
  if R = 0 (false branch): A.hi = min(A.hi, B.lo)
```

**Modular arithmetic caveat:** EVM operates mod 2^256. `plus(X, Y, Z)` is really `(X + Y) mod 2^256`. Overflow means `Z` can be smaller than either input. Bounds propagation must account for wrapping. Practical simplification: treat values < 2^128 as non-wrapping (most gas/stack values). Flag constraints that might wrap.

**Infeasibility detection:**

```javascript
function narrowDomain(state, evarHash, lo, hi) {
  const d = state.domains.get(evarHash) || { lo: 0n, hi: MAX_UINT256 };
  d.lo = lo > d.lo ? lo : d.lo;
  d.hi = hi < d.hi ? hi : d.hi;
  if (d.lo > d.hi) return INFEASIBLE;  // empty domain → prune branch
  state.domains.set(evarHash, d);
  if (d.lo === d.hi) {
    // Singleton → bind evar to value, trigger Level 0
    substituteEvar(state, evarHash, Store.put('binlit', [d.lo]));
  }
  return OK;
}
```

**Undo:** Store previous `{ lo, hi }` in undo log. Restore on backtrack.

**Testing:** Unit: `!plus(evar(0), 5, evar(1))` with `evar(1).hi = 10` → `evar(0).hi = 5`. Integration: path condition pruning on EVM branching.

### TODO_0005.Level_4 — Multi-Mode Resolution (~200 LOC)

**Trigger:** A constraint has enough ground arguments to compute the remaining ones, but not in the standard FFI mode.

**Action:** Constraint rewriting for non-standard modes:

```
!plus(A, B, C) ∧ ground(A, C) ⟹ B = C - A
!mul(A, B, C) ∧ ground(A, C) ∧ A ≠ 0 ⟹ B = C / A  (if divisible)
!sub(A, B, C) ∧ ground(B, C) ⟹ A = B + C
```

This is the multi-mode FFI from Level 1, but formalized as constraint rewriting rules. Can be implemented either:
- **In the FFI layer** (extend each FFI function with reverse modes) — ~15 LOC per function
- **As ILL forward rules** (higher-order, needs meta-level variable inspection)
- **As dedicated constraint rewriter** (pattern match on constraint + groundness) — cleanest

**Recommended: FFI layer extension.** Each FFI function gets a `resolveMode(args)` that inspects groundness and returns which mode to use:

```javascript
function plusResolve(args) {
  const [a, b, c] = args;
  const ag = isGround(a), bg = isGround(b), cg = isGround(c);
  if (ag && bg && !cg) return { mode: '+ + -', compute: () => a + b };
  if (ag && !bg && cg) return { mode: '+ - +', compute: () => c - a };
  if (!ag && bg && cg) return { mode: '- + +', compute: () => c - b };
  if (ag && bg && cg) return { mode: '+ + +', verify: () => a + b === c };
  return null;  // insufficient groundness
}
```

**Danger: division for mul reverse.** `mul(A, B, C)` with known A and C: `B = C / A`. But `C / A` may not be an integer. Only valid if `C mod A === 0`. Must check.

**Testing:** Unit: `!plus(evar(0), 5, 13)` → evar(0) = 8. `!mul(3, evar(0), 12)` → evar(0) = 4. `!mul(3, evar(0), 13)` → no resolution (not divisible).

---

## Inverted Index Design

The inverted index is the key data structure enabling efficient propagation. It maps each evar to the set of persistent facts that reference it.

### Structure

```javascript
state.evarIndex = new Map();
// Map<evarHash: number, Set<factHash: number>>
```

### Population

In `mutateState`, when adding a persistent fact:

```javascript
function extractEvars(hash) {
  const evars = [];
  const stack = [hash];
  while (stack.length > 0) {
    const h = stack.pop();
    const tag = Store.tag(h);
    if (tag === 'evar') { evars.push(h); continue; }
    if (!tag) continue;
    for (let i = 0; i < Store.arity(h); i++) stack.push(Store.child(h, i));
  }
  return evars;
}

// In mutateState, after adding persistent fact h:
for (const evar of extractEvars(h)) {
  if (!state.evarIndex.has(evar)) state.evarIndex.set(evar, new Set());
  state.evarIndex.get(evar).add(h);
}
```

### Undo

Track index additions in the undo log:

```javascript
// In mutateState undo log: extend with TYPE=2 for evarIndex entries
log.push(2, evarHash, factHash);  // signals: remove factHash from evarIndex[evarHash]

// In undoMutate:
if (type === 2) {
  const set = state.evarIndex.get(hash);
  if (set) { set.delete(oldValue); if (set.size === 0) state.evarIndex.delete(hash); }
}
```

### Complexity

- Population: O(d) per fact (d = term depth, typically 3-5)
- Lookup: O(1) (Map + Set)
- Substitution cascade: O(k * d) where k = affected facts
- Memory: O(n) where n = number of evar-containing persistent facts

---

## Alternative Approaches Considered

### Option: Expression Constructors (Skolem Path)

Instead of opaque evars, use expression terms: `plus_expr(X, Y)` for "X + Y, not yet computed."

**Pros:**
- Self-describing (carries operation + arguments)
- Content-addressed (identical inputs → same hash)
- Pattern-matchable (normalizers can inspect structure)
- No inverted index needed (info is in the term itself)

**Cons:**
- Growth: O(depth) per chain — `plus_expr(plus_expr(plus_expr(?D, 3), 5), 7)` after 3 ADDs
- Needs equational completion (catch-all clauses, confluence proof — [RES_0043](../research/0043_equational-completion.md))
- Needs AC-normalization for deduplication ([RES_0016](../research/0016_expression-simplification.md) §3)
- "Dirty theory" — catch-all axiom makes fallback ordering an implementation detail
- Harder to export to SMT (must flatten expression trees)

**Decision:** [TODO_0002](0002_symexec-expression-decision.md) chose eigenvariables. Expression constructors backlogged in [TODO_0003](0003_symexec-expression-foundation.md).

**Possible hybrid:** Use eigenvariables (flat constraints, SMT-ready) but add expression-term simplification as an optional normalization layer. The constraint `!plus(evar(0), 5, evar(1))` could be **rendered** as `evar(1) = evar(0) + 5` for human consumption, while remaining flat for the engine.

### Option: Loli-as-Freeze (CLP Coroutining)

Instead of creating evars when FFI fails, emit a loli continuation: `!plus(A, B, C) -o { body(C) }`. Resume when A becomes ground.

**Already implemented** in CALC's loli mechanism. The question is whether to **auto-emit** lolis on FFI mode mismatch (~20 LOC change) vs. explicitly design rules with ∃.

**Problem:** Loli-freeze blocks sequential flow. After ADD with symbolic input, there's no `pc` fact → execution stalls. Eigenvariables keep execution flowing (evar(0) is a value, even if opaque).

**Composition:** Loli-freeze works for **boolean guards** (⊕ branching explores both, one guard eventually satisfies). Eigenvariables work for **value-producing** operations (ADD, MUL). Both mechanisms compose: use ∃ for arithmetic, loli for triggers.

### Option: E-Graph Layer

Wrap the constraint store in an e-graph. Equalities like `evar(0) = 3` merge e-classes. Congruence closure propagates: if `f(evar(0))` was in state, `f(3)` is automatically equivalent.

**Pros:** Handles congruence automatically. Content-addressed Store is already half an e-graph.
**Cons:** 500-800 LOC. E-graphs are monotonic, ILL consumes facts — need scoped/colored variant (another ~300 LOC). Overkill for Level 0-1.

**Verdict:** Consider for Level 3+ if simpler approaches prove insufficient. See [RES_0016](../research/0016_expression-simplification.md) §1 (e-graph survey).

### Option: SMT Backend

Accumulate constraints, export to Z3/CVC5, check satisfiability.

**Pros:** Complete decision procedure. Handles arbitrary boolean combinations.
**Cons:** External dependency (WASM build of Z3 is ~5MB). Latency (even simple queries take ~1ms). CALC's architecture is designed for sub-millisecond per-step performance. SMT makes sense as a **final validation** tool (check if leaf states are feasible), not per-step.

**Verdict:** Out of scope for constraint propagation. Consider for a separate "SMT export" feature (TODO for later).

---

## Implementation Plan

### Phase 1: Foundation (~80 LOC)

1. **Inverted index** in `state.evarIndex` — populated in `mutateState`, undone in `undoMutate`
2. **`rebuildWithSubstitution(hash, target, replacement)`** utility in `lib/kernel/substitute.js`
3. **`extractEvars(hash)`** utility (walk term, collect evar children)
4. Tests: inverted index population/undo, substitution correctness

### Phase 2: Level 0 — Equality Resolution (~50 LOC)

1. **`propagateEqualities(state, newPersistentFacts)`** — detect `!eq(evar, value)`, substitute, cascade
2. Hook into `mutateState` return path (or wrap in a `mutateAndPropagate`)
3. Tests: worked example (ADD chain → EQ → resolution). Branch pruning test.

### Phase 3: Level 1 — FFI Re-check (~30 LOC)

1. **After Level 0 substitution:** check if constraint is now ground → re-prove via FFI
2. If FFI succeeds → new evar binding → cascade back to Level 0
3. Tests: `!plus(evar(0), 5, 8)` → evar(0) = 3

### Phase 4: Level 4 — Multi-Mode FFI (~80 LOC)

1. Extend `plus`, `mul`, `sub` FFI functions with reverse modes
2. Mode selection based on groundness analysis in `tryFFIDirect`
3. Tests: reverse-mode resolution for each arithmetic operation

### Phase 5 (optional): Level 2 — Chain Simplification (~100 LOC)

1. Detect same-predicate chains through intermediate evars
2. Merge constants, eliminate intermediate evars
3. Confluence analysis (plus chains: trivially confluent)
4. Tests: gas chain simplification

### Phase 6 (optional): Level 3 — Domain Propagation (~200 LOC)

1. `state.domains` map with interval bounds per evar
2. Propagation rules for plus, mul, gt, neq, eq
3. Infeasibility detection (empty domain → prune)
4. Modular arithmetic handling for uint256
5. Tests: interval narrowing, infeasibility pruning

### Estimated Total

| Level | LOC | Dependencies | Value |
|-------|-----|-------------|-------|
| Foundation (index) | ~80 | None | Enables all levels |
| Level 0 (equality) | ~50 | Foundation | High — resolves evars from ⊕ branching |
| Level 1 (FFI re-check) | ~30 | Level 0 | High — cascades through arithmetic chains |
| Level 4 (multi-mode) | ~80 | Level 1 | Medium — enables reverse-mode solving |
| Level 2 (chain merge) | ~100 | Foundation | Medium — reduces constraint count |
| Level 3 (domains) | ~200 | Foundation | Medium — enables path pruning |
| **Total** | **~540** | | |

Foundation + Level 0 + Level 1 is the **minimum useful** package (~160 LOC). Levels 2-4 are independent and can be added later.

---

## Interaction with Symexec DFS

### Propagation in the Mutation/Undo Framework

The symexec DFS uses in-place mutation with undo logs. Propagation must integrate with this:

```
explore(state, depth):
  matches = findAllMatches(state)
  for each match:
    undo = mutateState(state, match)          // produces new facts
    propUndo = propagateConstraints(state)     // Level 0-4
    if propUndo === INFEASIBLE:
      undoPropagate(state, propUndo)
      undoMutate(state, undo)
      continue  // skip this child — branch pruned
    child = explore(state, depth + 1)
    undoPropagate(state, propUndo)
    undoMutate(state, undo)
    children.push(child)
```

Propagation happens **after** mutateState but **before** exploring children. Its changes are undone alongside the mutation when backtracking.

### Impact on State Hash / Cycle Detection

Propagation changes state (substitutes evars, adds/removes persistent facts). The state hash must reflect these changes. Options:
1. **Recompute hash after propagation** — correct but O(n) per step
2. **Incremental hash update** — track additions/removals, XOR-combine — O(delta) per step
3. **Hash includes constraints** — already the case (persistent facts are part of hashState)

Option 3 is already implemented. Propagation changes persistent facts via the same mechanism as mutateState. hashState already includes all persistent facts. No additional work needed.

### Impact on Loli Matching

After evar resolution, loli guards may become provable. Example:
```
State has: !neq(evar(0), 0) -o { pc(NPC) }
After propagation: evar(0) = 5
Guard !neq(5, 0) is now FFI-provable → loli fires
```

This happens naturally — after propagation changes state, the next `findAllMatches` call will match the loli. No special handling needed.

---

## Cross-References

- [TODO_0004](0004_symexec-backward-foundation.md) — ∃ connective + eigenvariables (done, prerequisite)
- [TODO_0002](0002_symexec-expression-decision.md) — decision: eigenvariables over Skolem
- [TODO_0003](0003_symexec-expression-foundation.md) — Skolem path (backlogged)
- [THY_0009](../theory/0009_symbolic-values-in-forward-chaining.md) — three problems decomposition
- [THY_0004](../theory/0004_symbolic-branching.md) — ⊕ branching theory
- [RES_0049](../research/0049_constraint-propagation-systems.md) — CLP/CHR/attributed variables survey
- [RES_0016](../research/0016_expression-simplification.md) — expression simplification techniques
- [RES_0039](../research/0039_symbolic-arithmetic-design-space.md) — tool comparison (hevm, K, Tamarin, Rosette)
- [RES_0043](../research/0043_equational-completion.md) — equational completion (Skolem path)
- [RES_0021](../research/0021_fresh-variable-generation.md) — fresh variable mechanisms
- [RES_0007](../research/0007_chr-linear-logic.md) — CHR ↔ ILL mapping

## Key Code Paths

- `resolveExistentials` — match.js:370–398 (creates evars)
- `provePersistentGoals` — match.js:269–355 (three-level fallback)
- `mutateState` / `undoMutate` — symexec.js:284–368 (state mutation)
- `freshEvar` — fresh.js:14–18 (monotonic counter)
- `tryFFIDirect` — match.js:207–247 (FFI dispatch)
- FFI metadata — ffi/index.js:72–86 (mode declarations)
- `explore` — symexec.js:387+ (DFS with mutation/undo)
