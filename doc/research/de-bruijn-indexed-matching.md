# De Bruijn Indexed Pattern Matching

Compile-time slot assignment for metavariables in forward chaining rules. Replaces linear theta scan with O(1) indexed lookup.

**Cross-references:** Stage 6 in [[forward-optimization-roadmap]], [[term-storage-models]], [[prover-optimization]]

---

## The Problem

CALC's forward chaining hot path uses a flat interleaved substitution `theta = [v0, t0, v1, t1, ...]`. Both `match()` (unify.js:398-401) and `applyFlat()` (substitute.js:111-113) scan theta linearly to find a variable's binding:

```javascript
// match() — binding check (unify.js:398-401)
for (let ti = 0; ti < theta.length; ti += 2) {
  if (theta[ti] === p) { existingVal = theta[ti + 1]; break; }
}

// applyFlat() — substitution lookup (substitute.js:111-113)
for (let i = 0; i < theta.length; i += 2) {
  if (theta[i] === hash) return theta[i + 1];
}
```

For a rule with K metavars matched against N patterns, this is O(K) per lookup, O(K*N) per rule application. For `evm/add` (K=6, 7 match operations, ~50 applyFlat calls per run), this totals ~350 linear scans per symexec run.

The fix is classical: assign each metavar a compile-time slot index, and theta becomes a fixed-size indexed array.

---

## Theoretical Foundations

### De Bruijn Indices (1972)

De Bruijn's key insight for lambda calculus: replace named variables with positional indices relative to their binder. `λx. λy. x` becomes `λ. λ. 2` — variable `2` means "bound by the binder 2 levels up."

This eliminates alpha-equivalence (renaming) issues and makes variable lookup positional. In lambda calculus, the index tells you how many binders to skip; in our setting, the index tells you which theta slot to read.

**Our adaptation:** We don't have lambda binders — we have rule-scoped metavariables. Each metavar `_X` in a forward rule gets a fixed slot number `s`, and theta becomes `Array(maxSlot)` with `theta[s]` holding the binding. The slot assignment is computed once at `compileRule()` time from the pattern structure.

This is sometimes called a **"named de Bruijn"** scheme: variable names are kept for debugging/display, but all runtime operations use positional indices.

### Warren Abstract Machine (WAM)

The WAM (Warren, 1983; Ait-Kaci, 1991) is the standard compilation target for Prolog. Its variable handling is directly analogous to our indexed theta.

**Register allocation.** The WAM compiler analyzes a clause head and assigns each variable to a register. Variables are classified as:

- **Temporary** (X-registers): only needed within the current goal. Stored in argument registers `X1, X2, ...`
- **Permanent** (Y-registers): needed across multiple goals. Stored in environment slots `Y1, Y2, ...`

The WAM's `allocate N` instruction reserves N environment slots — exactly analogous to `theta = new Array(metavarCount)`.

**First-occurrence vs subsequent-occurrence.** The WAM distinguishes:

- `get_variable(Xn, Ai)` — first occurrence of variable Xn in argument position Ai. Copies Ai into Xn. (Analogous to: `theta[slots[_X]] = value` — bind.)
- `get_value(Xn, Ai)` — subsequent occurrence. Unifies Xn with Ai. (Analogous to: `theta[slots[_X]] === value` — consistency check.)

This distinction is made at **compile time** by tracking which variables have been seen. In CALC's `match()`, the current code discovers first-vs-subsequent at **runtime** (linear scan: "is `_X` already in theta?"). With indexed slots, the distinction becomes O(1): `theta[slot] === undefined` → first occurrence (bind), else → subsequent (check).

**CALC vs WAM differences:**

| Aspect | WAM | CALC |
|--------|-----|------|
| Variables | Clause-scoped, backtrackable | Rule-scoped, no backtracking |
| Theta lifetime | Until choice point/cut | Until tryMatch returns |
| Occurs check | Optional (sound but slow) | Not needed (one-directional matching) |
| Binding | Two-way unification | One-way: pattern → ground term |
| Reset | Trail-based undo on backtrack | Truncate or fill(undefined) |

The one-way matching in CALC is strictly simpler than WAM's full unification. A WAM variable can be bound and then later unified against a conflicting value (requiring occurs check). In CALC, `match()` only matches patterns against ground terms — a metavar is either unbound (`theta[slot] === undefined`) or bound to a ground value (no recursive check needed).

### Explicit Substitution Calculi

Abadi, Cardelli, Curien & Levy (1991) introduced the λσ-calculus, making substitution a first-class operation. The key rule:

```
1[a · σ] = a     — variable 1 looks up position 1, gets first element
```

This is O(1) lookup by position. Contrast with named substitution `x[x := a] = a` which requires name comparison (or association list scan).

Our indexed theta is an explicit substitution environment in this sense. `theta[slot]` is exactly `slot[θ]` — positional lookup into a substitution. The difference: λσ uses de Bruijn indices (relative to binders), we use compile-time slot assignments (relative to rule scope).

**Shift operations.** In λσ, substitutions under a binder require "shifting" (incrementing free variable indices). CALC doesn't need shifts — all metavars are rule-scoped (no nested binders). This makes our indexed theta strictly simpler than λσ environments.

### Flat Environments in Functional Compilers

OCaml, Haskell (GHC), and SML compilers all use flat array environments for closures:

- **OCaml:** Closures are `(code_pointer, env)` where `env` is a flat array of values. Variable access is `env[n]` — O(1).
- **GHC STG:** Closures carry free variables in flat layout. Pattern match variables are allocated to stack slots.
- **SML/NJ:** CPS-based compilation assigns each variable a register or stack slot at compile time.

All of these compile named variables to positional indices. The same transformation applies to CALC's metavars.

---

## Application to CALC

### Concrete Trace: `evm/add`

```
evm/add:
  pc PC *                    -- linear[0]: pc(_PC)
  code PC (i (e)) *          -- linear[1]: code(_PC, i(e))
  !inc PC PC' *              -- persistent[0]: inc(_PC, _PC')
  sh (s (s SH)) *            -- linear[2]: sh(s(s(_SH)))
  stack (s SH) A *           -- linear[3]: stack(s(_SH), _A)
  stack SH B *               -- linear[4]: stack(_SH, _B)
  !plus A B C                -- persistent[1]: plus(_A, _B, _C)
  -o {
    code PC (i (e)) *        -- consequent: code(_PC, i(e))
    pc PC' *                 -- consequent: pc(_PC')
    sh (s SH) *              -- consequent: sh(s(_SH))
    stack SH C               -- consequent: stack(_SH, _C)
  }.
```

**Metavars (6 distinct):** `_PC, _PC', _SH, _A, _B, _C`

**Compile-time slot assignment** (in `compileRule()`):

```javascript
// collectMetavars() walks all patterns → { _PC, _PC', _SH, _A, _B, _C }
// Assign sequential indices:
metavarSlots = { [hash_PC]: 0, [hash_PC']: 1, [hash_SH]: 2,
                 [hash_A]: 3, [hash_B]: 4, [hash_C]: 5 }
metavarCount = 6
```

**Current flow (flat theta, linear scan):**

| Step | Operation | Theta state | Scan length |
|------|-----------|-------------|-------------|
| 1 | `match(pc(_PC), pc(42))` | `[_PC, 42]` | 0 (new binding) |
| 2 | `match(code(_PC, i(e)), code(42, ie))` | `[_PC, 42]` | **1** (check _PC) |
| 3 | FFI `inc(42) → 43` | `[_PC, 42, _PC', 43]` | — |
| 4 | `match(sh(s(s(_SH))), sh(ss5))` | `[.., _SH, 5]` | 0 (new binding) |
| 5 | `match(stack(s(_SH), _A), stack(s5, 100))` | `[.., _SH, 5, _A, 100]` | **2** (check _SH) |
| 6 | `match(stack(_SH, _B), stack(5, 200))` | `[.., _B, 200]` | **3** (check _SH) |
| 7 | FFI `plus(100, 200) → 300` | `[.., _C, 300]` | — |

Total: 6 scans of increasing length (1+2+3 = 6 comparisons for checks alone). Per tryMatch call.

Then `applyFlat` for each consequent pattern scans all 6 bindings (12 entries) per variable lookup. For 4 consequent patterns with ~2 vars each: 8 lookups × 6 avg comparisons = ~48 comparisons.

**With indexed theta (O(1) lookup):**

| Step | Operation | Code |
|------|-----------|------|
| 1 | bind _PC | `theta[0] = 42` |
| 2 | check _PC | `theta[0] === 42` ✓ (O(1)) |
| 3 | bind _PC' | `theta[1] = 43` |
| 4 | bind _SH | `theta[2] = 5` |
| 5 | check _SH, bind _A | `theta[2] === 5` ✓, `theta[3] = 100` |
| 6 | check _SH, bind _B | `theta[2] === 5` ✓, `theta[4] = 200` |
| 7 | bind _C | `theta[5] = 300` |

Every operation is O(1). No scanning.

For `applyFlat`: each variable lookup is `theta[slots[hash]]` — O(1). Total: 8 lookups × 1 = 8 operations (vs ~48 comparisons).

### Where the Changes Go

**1. `compileRule()` in forward.js (line 281-352)**

Add slot assignment using existing `collectMetavars()` from rule-analysis.js:

```javascript
// After existing analysis...
const allMetavars = new Set();
for (const p of linearPats) collectMetavars(p, allMetavars);
for (const p of persistentPats) collectMetavars(p, allMetavars);
for (const p of conseqLinear) collectMetavars(p, allMetavars);
for (const p of conseqPersistent) collectMetavars(p, allMetavars);

const metavarSlots = {};
let slotIdx = 0;
for (const mv of allMetavars) {
  metavarSlots[mv] = slotIdx++;
}
compiled.metavarSlots = metavarSlots;
compiled.metavarCount = slotIdx;
```

**2. `tryMatch()` in forward.js (line 569-763)**

Replace `theta = []` with `theta = new Array(rule.metavarCount)`:

```javascript
// Line 571: const theta = [];
// Becomes: const theta = new Array(rule.metavarCount);
```

Pass `rule.metavarSlots` to `match()` calls. FFI/backward results convert:

```javascript
// FFI result conversion (line 717-718):
// theta.push(ft[fi][0], ft[fi][1]);
// Becomes:
theta[rule.metavarSlots[ft[fi][0]]] = ft[fi][1];
```

The deferral binding check (line 617-629) becomes:

```javascript
// theta[rule.metavarSlots[v]] !== undefined
```

**3. `match()` in unify.js (line 382-470)**

Add optional `slots` parameter. When provided:

```javascript
// Binding (line 403): theta.push(p, t);
// Becomes: theta[slots[p]] = t;

// Binding check (line 398-401): linear scan
// Becomes: const existingVal = theta[slots[p]];
// if (existingVal !== undefined && existingVal !== t) return null;
```

Cold-path callers (without `slots`) continue using flat format.

**4. `applyFlat()` in substitute.js (line 106-151)**

Add optional `slots` parameter. When provided:

```javascript
// Lookup (line 111-113): linear scan
// Becomes: const idx = slots[hash];
// if (idx !== undefined && theta[idx] !== undefined) return theta[idx];
```

**5. `subApply()` in forward.js (line 42-48)**

Thread `slots` through to `applyFlat`:

```javascript
function subApply(hash, theta, slots) {
  return _subApplyFlat(hash, theta, slots);
}
```

### Deferral Safety

The deferral mechanism in `tryMatch` (line 610-630) changes pattern matching order. Pattern A might be deferred, causing pattern B to match first. With the current flat theta, bindings are appended in match order — the position of `_PC`'s binding depends on which pattern matched first.

With indexed theta, deferral is irrelevant: `_PC` always goes to `theta[0]` regardless of match order. This is the key safety property — **slot assignments are a compile-time invariant, immune to runtime reordering.**

### Reset Semantics

When `tryMatch` fails (line 660, 695): `theta.length = savedLen` truncates the flat theta.

With indexed theta, truncation doesn't work — slots are non-contiguous. Options:

1. **Allocate per tryMatch:** `new Array(count)` for count=6-8 is ~20ns. Simple, no state management.
2. **Fill on failure:** `for (let i = 0; i < count; i++) theta[i] = undefined`. For count=6-8, this is ~5ns.
3. **Generation counter:** Store `[value, generation]` pairs, increment generation on reset. O(1) reset but doubles memory and complicates lookup.

Option 1 is simplest and fast enough. V8 optimizes small `new Array(N)` allocations.

**But wait:** tryMatch doesn't just reset on rule failure — it also resets on individual pattern failure within a rule (line 660: `theta.length = savedLen` after a failed match). With indexed theta, we need to track which slots were written since the save point and undo them.

Solution: maintain a small "undo stack" of slot indices written since the last save point:

```javascript
const undoStack = [];
// In match(): when binding theta[slot] = t, also undoStack.push(slot)
// On failure: while (undoStack.length > savedUndoLen) theta[undoStack.pop()] = undefined
```

This is O(bindings-since-save) which is typically 1-3.

---

## Performance Analysis

### Current Scale (44 rules, 6-8 metavars)

**match() savings:** ~350 linear scans/run → 350 indexed lookups. Average scan length ~3 → save ~700 comparisons. At ~2ns per comparison: ~1.4µs saved.

**applyFlat() savings:** ~50 calls × ~3 variable lookups × ~4 avg scan length = ~600 comparisons → 150 indexed lookups. Save ~450 comparisons: ~0.9µs.

**Total:** ~2.3µs/run. At 0.95ms median: ~0.24% improvement. Marginal.

**But:** The real value is in enabling Stage 7 (delta optimization + compiled substitution), which saves ~140 match calls and ~140 applyFlat calls per run. Stage 7 cannot work without indexed slots because delta bypass needs to write specific metavar bindings by slot, not by position in a scan list.

### At Scale (400 rules, 20 metavars)

Linear scan of 20 entries is ~5x slower than scan of 4. With 400 rules and proportionally more match calls: indexed lookup saves ~10-20µs/run. More significant.

### At Scale (1000 rules, 100K facts)

Dominant cost shifts to rule selection and fact indexing (Stage 9 territory). Theta scan becomes negligible compared to candidate filtering. Indexed theta still helps per-rule, but the bottleneck is elsewhere.

### Memory

`new Array(N)` for N ≤ 20: 64-160 bytes. One per tryMatch call. Negligible.

`metavarSlots` object per compiled rule: ~6-20 entries × ~16 bytes = ~96-320 bytes. 44 rules: ~14KB total. Negligible.

---

## Relationship to Other Optimizations

### Stage 7 (Delta Optimization) — Enabled By This

Delta bypass extracts metavar bindings directly from facts:

```javascript
// Delta pattern: pc(_PC) → pc(_PC')
// Instead of match(pattern, fact, theta):
theta[slots[_PC]] = Store.child(fact, 0);  // O(1) extract + bind
```

This requires knowing `_PC`'s slot index at compile time. Without indexed theta, delta bypass must either (a) scan flat theta to find `_PC`'s position, or (b) always append to the end (breaking position assumptions).

Compiled substitution for consequents also requires indexed theta:

```javascript
// Instead of applyFlat(pc_pattern, theta):
Store.put('pc', [theta[slots[_PC']]]);  // O(1) lookup + construct
```

### Stage 4 (Allocation Reduction) — Compatible

The flat worklist (`_Gp[]`/`_Gt[]`) and arity-specialized `applyFlat` are orthogonal to theta format. Indexed theta replaces the flat interleaved theta but keeps all other Stage 4 optimizations.

### Stage 5 (Theta Format Unification) — Superseded

If all paths use indexed theta, the flat-vs-paired format distinction disappears. Cold paths would use `theta[slot]` too. The slot format IS the unified format. Stage 5 becomes unnecessary.

### Stage 9 (Discrimination Trees) — Independent

Discrimination trees select which rules to try. Indexed theta affects what happens after a rule is selected (the match/substitute step). No interaction.

---

## Complications

### 1. API Backward Compatibility

`match()` currently returns `theta` (the flat array). Callers outside forward.js (tests, backward prover, sequent prover) pass no `slots` parameter and expect flat format.

**Solution:** `slots` is optional. Without it, `match()` uses the current flat format. The indexed path is opt-in, activated only from `tryMatch()`.

### 2. applyFlat Format Divergence

With indexed theta, `applyFlat(hash, theta, slots)` reads `theta[slots[hash]]`. Without slots, it scans linearly. Two code paths in one function.

**Solution:** Separate functions: `applyFlat` (linear scan, cold path) and `applyIndexed` (slot lookup, hot path). Clear names, no branching overhead.

### 3. FFI/Backward Prover Results

FFI returns `[[v, t], ...]` (paired format). Backward prover returns `[[v, t], ...]`. Both must be converted to indexed format:

```javascript
for (const [v, t] of ffiResult.theta) {
  theta[slots[v]] = t;
}
```

This is already the current conversion pattern (just with flat push instead of slot write). No additional complexity.

### 4. Slot Collision Risk

If a metavar hash appears in `slots` but the runtime term has a **different** freevar at the same hash, slot lookup returns a wrong index. Can this happen?

**No.** Content-addressing guarantees: same name → same hash. Different name → different hash. `slots` maps metavar hashes to indices. A runtime term's freevar has the same hash iff it has the same name. No collision is possible.

### 5. Undefined vs Missing

In JavaScript, `theta[slots[hash]]` where `slots[hash]` is `undefined` evaluates to `theta[undefined]` which is `undefined`. This is harmless — it means "not bound," same as the linear scan returning no match.

If `hash` is not a metavar at all (e.g., a predicate constructor), `slots[hash]` is `undefined`, and the lookup returns `undefined` → "not bound" → fall through to structural decomposition. Correct behavior.

---

## Implementation Checklist

1. Add `metavarSlots` and `metavarCount` to `compileRule()` output
2. Add `matchIndexed()` — indexed version of `match()` (or extend with optional `slots`)
3. Add `applyIndexed()` — indexed version of `applyFlat()`
4. Update `tryMatch()` to use indexed theta + undo stack
5. Update `subApply()` to thread slots
6. Update `applyMatch()` to use indexed theta for consequent substitution
7. Cross-check test: run every symexec with both flat and indexed, assert identical trees
8. Benchmark: 20-run median comparison

**Estimated effort:** ~150 LOC added, ~30 removed. Medium complexity due to undo stack.

---

## Research Directions

### Compile-Time First/Subsequent Distinction

The WAM compiles first-occurrence vs subsequent-occurrence into **different instructions** (`get_variable` vs `get_value`). We could do the same: at compile time, analyze each pattern to determine which metavars are first-seen and which are checks. Then in `matchIndexed()`, skip the "is it already bound?" check for first-occurrence vars.

This saves one comparison per first-occurrence bind. For `evm/add`: 6 first-occurrence binds out of ~10 metavar accesses. Marginal but clean.

**Research needed:** How does this interact with deferral? If pattern order changes at runtime (deferral), a "first-occurrence" in the static order might actually be a "subsequent" at runtime. Solution: use the WAM approach — first/subsequent is per-pattern, not per-rule. Each pattern independently knows whether `_PC` has been seen in prior patterns.

### Compiled Match Functions

Beyond indexed slots, each rule's match could be compiled to a specialized function:

```javascript
// evm/add compiled match:
function matchEvmAdd(facts, theta) {
  const pcFact = findByPred('pc', facts);
  if (!pcFact) return null;
  theta[0] = Store.child(pcFact, 0);  // _PC = first child
  const codeFact = findByIndex('code', theta[0], facts);
  if (!codeFact) return null;
  // ... etc
}
```

This eliminates the generic `match()` loop entirely. Related to Stage 9 (compiled pattern matching / Maranget). Would give maximum performance but requires a code generation step.

**See:** [[compiled-pattern-matching]] (planned research document)

### Typed Slot Arrays

If metavar slots had type information (e.g., "slot 0 is always a Store index, slot 1 is always a BigInt"), the theta array could be split into typed arrays for better V8 optimization. Currently all slots hold Store indices (uint32-range numbers), so a single array suffices.

**Zig relevance:** In Zig, typed slots → `[6]?u32` (fixed-size array of optional u32). All slots are u32 (Store indices). Stack-allocated, zero GC. The slot map → `comptime` lookup table.

---

## References

- Ait-Kaci, H. (1991). *Warren's Abstract Machine: A Tutorial Reconstruction.* MIT Press. — WAM register allocation, get_variable/get_value instruction semantics.
- Abadi, M., Cardelli, L., Curien, P.-L. & Levy, J.-J. (1991). *Explicit substitutions.* J. Functional Programming 1(4). — The λσ-calculus, positional substitution lookup.
- de Bruijn, N.G. (1972). *Lambda calculus notation with nameless dummies.* Indagationes Mathematicae 34. — Original de Bruijn indices.
- Appel, A.W. (1992). *Compiling with Continuations.* Cambridge University Press. — CPS-based closure representation, flat environments.
- Leroy, X. (1990). *The ZINC experiment.* INRIA Technical Report 117. — Flat closure representation in ML compilers.
- Peyton Jones, S. (1992). *Implementing lazy functional languages on stock hardware: the STG machine.* J. Functional Programming 2(2). — STG closure layout, variable access by position.
- Warren, D.H.D. (1983). *An abstract Prolog instruction set.* SRI Technical Note 309. — Original WAM specification.
