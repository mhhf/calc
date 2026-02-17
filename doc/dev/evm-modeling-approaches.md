# EVM State Modeling in ILL: Design Space Exploration

## Problem

The current `evm.ill` models EVM bytecode execution as forward-chaining rules in ILL. Each opcode is a rule that consumes/produces linear facts representing the machine state. The long-term goal is to scale this to verify real-world smart contracts (target: k-dss/MakerDAO MCD, which takes K framework ~1 week via SMT).

We need to choose a state representation that:
1. Enables fast proof search (rule matching, state mutation)
2. Handles symbolic values (variables, unknowns) cleanly
3. Scales to large contracts (174+ instructions, 37+ state variables)
4. Supports simplification/lemma rules for symbolic arithmetic
5. Produces readable/traceable proof trees

## Current Approach: Separated Predicates

Every piece of EVM state is a separate linear fact tensored together:

```
pc PC * code PC 0x01 * sh (s (s SH)) * stack (s SH) A * stack SH B *
gas G * storage K V * memory Addr Size Val * sender S * ...
```

Computation is pushed to persistent backward-chaining predicates with FFI:

```
evm/add:
  pc PC * code PC 0x01 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) A * stack SH B *
  !plus A B C
  -o { code PC 0x01 * pc PC' * sh (s SH) * stack SH C }.
```

### Strengths

- **O(1) rule selection.** Fingerprint layer: `pc` value → `code` lookup → opcode → rule. This is the key optimization (12.7x speedup).
- **Independent facts.** Strategy stack indexes by predicate head. Each fact is independently addressable for matching.
- **Efficient mutation.** Mutation+undo on individual facts: change only what's needed, restore on backtrack. O(delta) per step.
- **Preservation optimization.** `rule-analysis.js` detects patterns identical on both sides of `-o` (e.g., `code PC 0x01`) and skips consume/produce. Already eliminates most overhead from code facts.
- **Natural ILL semantics.** Each linear fact is a resource consumed/produced. Persistent facts (`!inc`, `!plus`) are reusable.
- **Proven performance.** 181ms → ~1ms for 63-node multisig symexec tree (181x total speedup).

### Weaknesses

- **Fact count.** Multisig has 174 `code` facts + stack + gas + pc + sh + storage + memory + ... = 200+ facts in state. Preservation optimization handles code, but the predicate index still iterates over them.
- **Stack height tracking.** Separate `sh SH` fact + `stack SH V` pairs with successor-based indexing `(s (s SH))`. Verbose, error-prone, hard to read.
- **Symbolic accumulation.** Long programs accumulate symbolic expressions in separate stack facts. To trace the final result, you must reconstruct which `stack N V` facts exist and at what height. Not readable.
- **Commutativity cost.** Tensor is commutative. With 200+ facts, matching must search through them (mitigated by predicate indexing, but still linear in facts-per-predicate).

### Performance Bottleneck

Backward proving (FFI arithmetic) is 83.6% of symexec time. State representation affects the other 16.4%. So at current scale (44 rules, 63 nodes), state representation is secondary. But for k-dss scale (13 contracts, 100+ behaviours, 37+ state variables), state size and symbolic reasoning dominate.

## The Core Problem: Symbolic Arithmetic

The state representation debate (Approaches A-D below) is secondary. The gating capability for k-dss is: **the current engine cannot execute past symbolic arithmetic.**

### What Happens Today

When a forward rule has `!plus A B C` and A is symbolic:

1. `tryFFIDirect()` — FFI fails (`binToInt(freevar)` → null). Returns null (non-definitive for multi-modal).
2. State lookup — no `plus` facts in `state.persistent`. Fails.
3. Backward proving — clause heads (`plus(e,Y,Y)`, `plus(i(X),...)`) don't unify with symbolic freevars. Fails.
4. Rule is **skipped**. Engine tries next candidate.

Multisig works because all arithmetic has concrete arguments (PC, opcodes, gas are ground). Symbolic values (Sender, Member01) only appear in eq/neq comparisons, which branch via additive choice (`&`).

For k-dss: `Urn_ink + dink`, `Art * rate`, `(ink + dink) * spot` — all symbolic. The engine gets stuck after the first arithmetic opcode.

### The Design Question (Reframed)

Not "how to arrange state facts" but: **when FFI fails on symbolic values, what should the result be, and where/when is it simplified?**

### The ILL-Native Solution: Catch-All Clauses

Add backward-chaining catch-all clauses that produce symbolic expression terms:

```
plus_sym:  plus X Y (plus_expr X Y).
mul_sym:   mul X Y (mul_expr X Y).
minus_sym: minus X Y (minus_expr X Y).
```

When FFI fails, the three-fallback chain reaches backward proving, finds `plus_sym`, binds `C = plus_expr(X, Y)`. **Zero engine changes needed** — the existing fallback mechanism handles it automatically.

The term `plus_expr(X, 3)` enters the state as a stack value. Subsequent operations produce deeper nesting: `plus_expr(plus_expr(X, 3), 5)`, etc.

**This unlocks symbolic execution with zero engine changes.** The question becomes: where and when to SIMPLIFY accumulating expressions.

### Where Normalization Should Happen

Previous draft proposed Store.put-time normalization. **This is wrong:**

- Store.put can't normalize: it would corrupt rule patterns (`plus(_A, _B, _C)` with metavars)
- Content-addressing dedup would break (hash/content mismatch)
- Ground arithmetic is already handled by FFI (zero work needed)

The correct hook: **post-substitution** in `applyIndexed`/`subCompiled` (substitute.js, 6 call sites). When substitution produces a new term, check if it's simplifiable before returning.

### Normalization Confluence

Analysis confirms the core rules are safe (confluent + terminating via polynomial interpretation):

- **Safe:** identity (`plus(0,X)→X`), annihilation (`mul(0,X)→0`), ground eval, self-cancel (`minus(X,X)→0`), simple cancel (`plus(minus(X,Y),Y)→X`)
- **Dangerous — never add to normalizer:** distribution (`mul(X,plus(Y,Z))→...`) breaks termination
- **Deep cancellation:** use flatten-then-cancel, not structural rewrite rules
- **Tools:** CSI, AProVE can verify confluence automatically given `.trs` rules

### Three Simplification Strategies

All assume catch-all clauses produce symbolic terms. They differ in WHERE simplification happens:

**Strategy S1: Engine-level normalization (hevm path)**

Post-substitution normalizer in substitute.js. Handles ground folding, identity, cancellation. Fast, deterministic, O(1) per produced term. But hardcoded in JS — adding new simplification rules requires engine changes.

**Strategy S2: ILL simplification rules (K path)**

Simplification as forward rules in .ill:
```
% Ground folding — stack fact contains plus_expr where both args are ground
simplify_plus: stack SH (plus_expr A B) * !plus A B C -o { stack SH C }.
% Identity
simplify_plus_zero: stack SH (plus_expr X 0) -o { stack SH X }.
```

Declarative, extensible from .ill. But limited to fact-level matching (can't reach arbitrary depth), and adds extra forward steps per simplification.

**Strategy S3: Hybrid (engine normalization + ILL lemma rules)**

Engine normalizes ground + identity + cancellation (fast, always correct). ILL rules handle domain-specific lemmas (keccak injectivity, signed/unsigned, storage patterns). Most powerful but two places to maintain simplification logic.

### How Other Tools Handle This

| Tool | Symbolic result | Simplification | When |
|------|----------------|----------------|------|
| hevm | `Add(Var x, Lit 3)` ADT | Smart constructors (eager) | At construction |
| halmos | Z3 `BitVec` expr | Delegated to Z3 | At query |
| K/KEVM | Stuck `+Int` application | `[function]` + `[simplification]` rules | Eagerly to fixpoint |
| Tamarin | Ground term mod E | AC-normalization + variants | At matching |
| Rosette | Hash-consed term | Eager partial eval + merge | At construction |

K's bottleneck is **lemma engineering** — proofs get stuck on terms that are logically simplifiable but have no matching rule. Users must understand internal simplification state to write effective lemmas. Our catch-all approach avoids "stuck" — expressions always reduce to SOME symbolic term.

See `doc/research/symbolic-arithmetic-design-space.md` for detailed comparison.

## The O(n) Argument: Nested vs Separate

A common objection to nested state (Approach A/B) is that memory/storage access becomes O(n). But this deserves careful analysis:

**Separate facts:** `memory 0 32 V0 * memory 32 32 V1 * ...` — accessing `memory 43 ...` scans all memory facts. With predicate indexing (`byPred['memory'] → [h0, h1, ...]`), it's O(k) where k = number of memory facts. With a secondary index keyed by address, it's O(1).

**Nested map:** A list-of-pairs `map(pair(0, V0), pair(32, V1), ...)` gives O(k) access by scanning the list. But an `arrlit` node with O(1) child access changes this: `Store.child(arrlit, index)` is a direct typed array read.

The truth: **both representations can achieve O(1) with appropriate indexing.** Separate facts use hash-map secondary indexes. Nested terms use `arrlit` with direct child access. The cost isn't fundamentally different — it's about which indexing structure is easier to build and maintain.

For **code** (dense, 0-indexed, immutable): `arrlit` is ideal. `Store.child(codeArrlit, pc)` gives the opcode at O(1) cost.

For **storage** (sparse, 256-bit keys, mutable): separate facts with hash-map index are better. An `arrlit` for 2^256 possible keys is obviously impossible.

For **memory** (sparse but denser than storage, mutable): separate facts are pragmatic. `arrlit` would need to handle gaps.

## Path-Based Fingerprinting for Nested Terms

The current fingerprint layer achieves O(1) rule selection via:
```
state.linear → find 'pc' fact → PC value → stateIndex._byKey[PC] → code fact → opcode → rule
```

This requires `pc` and `code` as separate facts. For a nested representation like `vm(PC, Gas, Stack)`, we need a generalized version.

### The Idea: Multi-Level Path Access

Instead of separate `pc` and `code` facts, use **child-index paths** into nested terms:

```
// vm(PC, Gas, Stack) is a Store node. Code is arrlit.
path [0]           → PC value           (Store.child(vmHash, 0))
path [3]           → Code arrlit        (Store.child(vmHash, 3) — if code is child 3)
path [3, PC_value] → opcode at PC       (Store.child(codeArrlit, pcValue))
```

Each step is `Store.child(hash, index)` — a direct typed array read. Three array reads vs the current two hash-map lookups. Array reads are 2-5x faster than hash-map lookups.

### Can This Make Nested Competitive?

**For code access:** Yes. If code is stored as an `arrlit` child of the `vm` term (or as a separate persistent arrlit — both work), path-based access gives O(1) opcode lookup. The fingerprint layer would:
1. `Store.child(vmHash, 0)` → PC (BigInt extraction from binlit)
2. `Store.child(codeArrlit, Number(pcValue))` → opcode
3. Opcode → rule lookup in index

This is potentially FASTER than the current approach because it avoids hash-map lookups entirely.

**For the strategy stack:** The fingerprint layer's `findFingerprintValue()` currently chases `pointer predicate → secondary index → discriminator → ground value`. With path-based access, this becomes `child extraction → child extraction → child extraction` — simpler and cheaper.

### Overhead Analysis

**Building:** Pre-compute which paths matter for each rule at compile time (same as current `detectFingerprintConfig`). E.g., "ADD rule: PC is at path [0] of the vm fact."

**Runtime per step:**
- Current: mutate 3-5 separate facts in `state.linear`, update stateIndex. O(delta) mutations + hash-map ops.
- Nested: `Store.put('vm', [newPC, newGas, newStack, ...])` creates one new node, replace one entry in `state.linear`. O(arity) array write + one hash-map op.

For arity ~5 (PC, Gas, Stack, a few more), this is comparable. The nested approach does one allocation per step (`Store.put`) while the current approach does 3-5 counter mutations.

**Branching/undo:** With nested, the `vm` fact is one hash. Snapshotting = copying one number. Undo = restoring one number. Cheaper than undoing 3-5 separate fact mutations.

### Relationship to Stage 8

The optimization roadmap's Stage 8 ("Path-Based Nested Access — O(K*D) vs O(N)") is exactly this idea applied to pattern matching. For a compound term `vm(PC, Gas, Stack)`, a rule that only needs PC can navigate to path [0] directly, skipping the full term traversal.

With path-based fingerprinting, Stage 8 becomes a prerequisite rather than an optimization — it's how the engine knows WHERE in the nested term to look.

### When Code Changes (SELFDESTRUCT, CREATE)

Code-as-arrlit inside the `vm` term handles SELFDESTRUCT naturally: the `vm` term is rebuilt without the code child (or with an empty arrlit). Since `vm` is linear, it's consumed and reproduced each step anyway.

Alternatively, code can stay as separate persistent facts `!code PC V` and only be "deleted" via a special rule that transitions to a "destructed" state. SELFDESTRUCT was deprecated (EIP-6049) and code-deletion removed in Cancun (EIP-6780), so this is primarily for pre-Cancun completeness.

## Approach A: Bundled EVM State (Single Linear Fact)

Bundle ALL state (including memory/storage) into one term:

```
evm(PC, Gas, cons(A, cons(B, nil)), MemoryMap, StorageMap, ...)
```

### Analysis

**Pros:**
- Single linear fact → no commutativity search
- Stack is a list term → no height tracking
- Cheaper branching (one hash to copy/restore)

**Cons:**
- Memory/storage as nested maps: can't use sparse hash-map indexing. Even with `arrlit`, storage keys are 256-bit (no flat array possible).
- Full rebuild each step even when only PC changes (but with content-addressing, unchanged children share the same hash).
- All map-state operations (SLOAD, SSTORE, MLOAD, MSTORE) must walk/rebuild the map structure.

**With path-based fingerprinting:** Code access IS O(1) if code is an arrlit child. But storage/memory access remains problematic for sparse keys.

**Verdict:** The storage/memory problem is the real blocker, not fingerprinting. Keep storage/memory as separate facts.

## Approach B: Hybrid (Bundled Execution + Separate Maps)

Separate mutable state into two categories:
1. **Execution state** (changes every step): PC, gas, stack → one linear fact
2. **Map state** (changes selectively): storage, memory → individual facts
3. **Immutable state** (never changes): code → persistent facts or arrlit

```
vm(PC, Gas, cons(A, cons(B, nil))) *  % one linear fact
!code PC 0x01 *                       % persistent (or arrlit-based)
storage Key Val *                     % linear, one per slot
memory Addr Size Val *                % linear, one per cell
!plus A B C                           % persistent backward
```

Rules:

```
evm/add:
  vm(PC, Gas, cons(A, cons(B, Stack))) *
  !code PC 0x01 *
  !inc PC PC' *
  !plus A B C
  -o {
    vm(PC', Gas', cons(C, Stack))
  }.

evm/sstore:
  vm(PC, Gas, cons(Key, cons(Val, Stack))) *
  !code PC 0x55 * !inc PC PC' *
  storage Key _
  -o {
    vm(PC', Gas', Stack) *
    storage Key Val
  }.
```

### Analysis

**Pros:**
- **Fingerprint layer survives.** PC is `Store.child(vmHash, 0)`. Code lookup via path or persistent facts. Opcode → rule via index. O(1) with array accesses.
- Stack as list → no `sh` tracking. Readable.
- Storage/memory stay as individual facts → O(1) access via hash-map indexing.
- Fewer linear facts overall: 1 `vm` + storage + memory vs N `stack` + `sh` + `pc` + `gas` + storage + memory.
- Stack changes are one term rebuild (not N separate fact mutations).
- Branching is cheaper: snapshot/undo one `vm` hash instead of 3-5 fact counters.

**Cons:**
- Deep pattern matching for stack-intensive operations (DUP16 = depth 16).
- `vm` term must be destructured and rebuilt each step (one `Store.put`, O(arity)).
- Can't independently skip matching on `Gas` when only `PC` and stack change (whole term is matched).

**Verdict:** Most promising. Preserves key optimization (fingerprint via paths), improves readability (stack as list), reduces fact count. Recommended for prototyping.

## Approach C: Nested Functional (Everything Inside)

All computation happens inside terms, no external predicates:

```
evm(PC, Gas, cons(plus(A, B), Stack), Mem, Stor, ...)
  -o { evm(PC', Gas', cons(C, Stack), Mem, Stor, ...) }
```

Where `plus(A, B)` is a function constructor that must be simplified.

### The Deep Simplification Problem

The fundamental challenge with nested computation: `cons(plus(A, plus(2, 3)), Rest)`. The simplification `plus(2, 3) → 5` is at depth 2, inside a `cons` inside the stack. An ILL forward rule can only match at the top level of facts — it can't fire "inside" a term.

**C1 (built-in normalizer) and C2 (simplification as forward rules) can't handle this** without rules for every possible nesting depth.

**C3 (normalization phase) is the right approach.** The implementation is **post-substitution normalization** in `applyIndexed`/`subCompiled` (substitute.js). NOT in Store.put (see "Where Normalization Should Happen" above).

When substitution produces a new term via `Store.put('plus_expr', [hash_of_3, hash_of_5])`, the normalizer wrapping the call detects both children are ground binlits, computes 3+5=8, and returns `Store.put('binlit', [8n])` instead.

Since terms are built **bottom-up** (children before parents), inner expressions are normalized before outer ones. `plus_expr(X, plus_expr(2, 3))` first normalizes `plus_expr(2, 3) → 5`, then constructs `plus_expr(X, 5)`.

Substitution triggers normalization automatically: when `applyIndexed` grounds a variable, the resulting term passes through the normalizer.

### Normalization Rules Beyond Ground Arithmetic

For symbolic identities:
```javascript
// In a hypothetical Store.put normalizer:
if (tag === 'plus') {
  if (children[1] === ZERO_HASH) return children[0];  // X + 0 = X
  if (children[0] === ZERO_HASH) return children[1];  // 0 + X = X
  if (isGround(children[0]) && isGround(children[1])) return ffiPlus(...);
}
```

For deeper algebraic rules like `plus(minus(X, Y), Y) → X`:
```javascript
if (tag === 'plus' && Store.tag(children[0]) === 'minus') {
  if (Store.child(children[0], 1) === children[1]) {
    return Store.child(children[0], 0);  // minus(X, Y) + Y = X
  }
}
```

### Soundness

Store.put-time normalization is sound if each rewrite rule is a valid equality. Replacing a term with an equal term preserves logical validity. This is standard in proof assistants (Coq's `Compute`, Lean's `reduce`, K's `[function]` rules, hevm's smart constructors).

Specific concerns:
- **Confluence.** Normalization rules must be confluent (order-independent). Standard arithmetic identities are confluent. Custom rules need verification.
- **Termination.** Normalization must terminate. No rule should expand terms. Arithmetic simplification always reduces or preserves term size.
- **Completeness.** We don't need completeness (normalize everything). Just normalize what we can. Unsimplified terms are valid — they represent symbolic expressions.

### Declarative vs Hardcoded

The normalizer is hardcoded (per-calculus custom code), not declarative ILL rules. This is a trade-off:
- K framework: `[function]` rules are declarative but eagerly applied by the engine
- hevm: smart constructors are hardcoded in Haskell
- Our approach: normalizer rules in Store.put, configurable per-calculus

For declarative normalization, we'd need a way to register normalization rules that fire at construction time. This is possible but adds complexity.

**Verdict:** Store.put-time normalization solves the deep nesting problem cleanly. Bottom-up construction = automatic deep normalization. Sound given confluent rules. This is needed regardless of which approach (A/B/C/D) we choose.

## Approach D: Stack-as-List Only (Minimal Change)

Keep everything else the same, but replace `stack SH V` + `sh SH` with a single stack list:

```
pc PC * code PC 0x01 *
stack (cons A (cons B Rest)) *
gas G * storage K V * ...
```

### Analysis

The smallest change from current. Eliminates `sh` tracking and multiple `stack` facts, but keeps everything else as separate facts.

**Pros:**
- Minimal disruption to existing infrastructure
- Fingerprint layer works unchanged
- Stack readable as single term
- Fewer facts (1 `stack` instead of N `stack` + 1 `sh`)

**Cons:**
- Deep matching for DUP/SWAP (same as Approach B)
- Still has many separate facts (pc, gas, etc.)

**Verdict:** Good stepping stone toward Approach B.

## How Other Frameworks Model State

### K Framework / KEVM

- **State:** Structured nested cells `<k>`, `<pc>`, `<wordStack>`, etc.
- **Rules:** Pattern-match on relevant cells only (rest stays implicit via `...`).
- **Simplification:** `[function]` annotation = eager evaluation. Lemmas as rewrite rules.
- **Arithmetic:** Symbolic terms + Z3 (MBQI disabled due to performance). 256-bit range tracking.
- **Performance:** 1 week for k-dss. Bottleneck: SMT quantifier reasoning on failure proofs.

K's cell hierarchy reflects its rewriting semantics — you can rewrite sub-configurations independently (the `...` notation means "rest unchanged"). In ILL, the whole linear fact is consumed/produced, so K-style cells add nesting cost without this benefit.

### hevm

- **State:** Haskell GADT `VM t`. Stack is a list.
- **Simplification:** Smart constructors eagerly simplify: `add (Lit 2) (Lit 3) → Lit 5`. Same principle as our proposed Store.put normalization.
- **Symbolic:** `Expr EWord` ADT with symbolic operations preserved as terms.
- **Storage:** Pattern-matches Solidity storage layouts into per-mapping SMT arrays.

### Celf/CLF

- **State:** Flat multiset of linear facts (like CALC's current approach).
- **Duality:** Backward chaining outside monad, forward chaining inside monad `{ ... }`.
- CALC is already more optimized than Celf. Our architecture mirrors CLF's monadic duality.

### Move Prover

- Linear types at the language level make conservation laws automatic. ILL gives us this at the rule level.

### Tamarin Prover

- Multiset of facts (linear + persistent). Closest to CALC's approach. Constraint-solving based matching. Variant pruning for scalability.

## ILL vs SMT: Where Do We Need What?

### What K Uses SMT For

K framework uses both rewriting (declarative rules) and SMT (Z3). The rewriting engine handles:
- Concrete execution (no SMT needed)
- Pattern matching on configuration cells
- Simplification via lemma rules
- Case splitting on symbolic conditions

K NEEDS SMT for:
1. **Path condition feasibility:** "Is this branch reachable given accumulated constraints?"
2. **Arithmetic properties:** "Does this overflow? Are these values equal under constraints?"
3. **Storage slot non-aliasing:** "Are keccak(key1) and keccak(key2) different slots?"
4. **Failure proof exhaustion:** "Show there are NO inputs that reach this state."

### Minimal SMT-Hard Example

From k-dss, the simplest non-trivial proof is `rely-diff` (Vat contract):

```act
behaviour rely-diff of Vat
interface rely(address usr)

for all
    May : uint256

storage
    wards[CALLER_ID] |-> May
    wards[usr]       |-> _ => 1

iff
    May == 1
    VCallValue == 0

if
    CALLER_ID =/= usr
```

This proves: "If `wards[msg.sender] == 1` and `sender ≠ usr`, then after executing `rely(usr)`, `wards[usr]` becomes 1 and `wards[sender]` is unchanged."

**Why SMT is needed:** Storage slot for `wards[sender]` is at `keccak(0 ++ sender)`. Storage slot for `wards[usr]` is at `keccak(0 ++ usr)`. K must prove these don't alias:

```
sender ≠ usr  →  keccak(0 ++ sender) ≠ keccak(0 ++ usr)
```

K can't derive this by rewriting — keccak has no algebraic structure. SMT treats keccak as an uninterpreted function with an injectivity axiom.

#### Minimal Bytecode for This Challenge

Stripped to essentials — a contract that writes to one storage slot and reads another, where slots are keccak-addressed:

```
% Setup: key1 at memory[0:32], key2 at memory[32:64]
% Assumption: key1 ≠ key2

% Compute slot1 = sha3(key1), load old value
PUSH1 32          % size
PUSH1 0           % offset
SHA3              % slot1 = keccak(memory[0:32])
DUP1
SLOAD             % old_val1 = storage[slot1]
SWAP1

% Write new value to slot1
PUSH1 0x42        % new_value
SWAP1
SSTORE            % storage[slot1] = 0x42

% Compute slot2 = sha3(key2), read value
PUSH1 32          % size
PUSH1 32          % offset
SHA3              % slot2 = keccak(memory[32:64])
SLOAD             % val2 = storage[slot2]

% Property: val2 is unchanged (because slot1 ≠ slot2)
```

#### ILL Model

```
% After SSTORE: state has storage slot1 0x42
% SLOAD for slot2 matches: storage slot2 V

% The match succeeds IF slot1 ≠ slot2 (different storage facts)
% or produces V = 0x42 IF slot1 = slot2 (same fact)

% ILL needs to prove: sha3(key1) ≠ sha3(key2) given key1 ≠ key2
% This requires a lemma:
sha3_injective: neq (sha3 X) (sha3 Y)
  <- neq X Y.
```

With this one lemma, ILL can derive `!neq slot1 slot2`, which means the `storage slot2 V` fact is independent of `storage slot1 0x42`. The SLOAD matches the original `storage slot2 original_value`.

**Key observation:** For THIS case, ILL handles it with one backward-chaining lemma. No SMT needed. The keccak injectivity becomes a simple proof-search step.

#### Where ILL Gets Harder

The k-dss `Vat.frob` proof has 37+ symbolic variables and needs:
- `Urn_ink + dink` must fit in uint256 (overflow check)
- `(Urn_art + dart) * Ilk_rate <= (Urn_ink + dink) * Ilk_spot` (collateralization ratio)
- Multiple signed/unsigned conversions
- Non-linear arithmetic: `A * B < C` where all symbolic

These require constraint reasoning that simple lemma rules can't easily express. The fundamental question: **can accumulated path conditions in ILL substitute for SMT constraint solving?**

#### Path Conditions in ILL

When a JUMPI branches on `X < 5`:
- True branch: `!gt 5 X 0 (i e)` added as persistent fact (X < 5)
- False branch: `!neq condition 0` or equivalent

These path conditions accumulate as persistent facts. Later lemma rules can check for them:

```
% If we know X < 5 and need to prove X < 10:
lt_transitive: gt 10 X 0 (i e)
  <- gt 5 X 0 (i e).   % X < 5 implies X < 10
```

For simple orderings, this works. For non-linear constraints (`A * B < C`), we'd need either:
- Extensive lemma libraries (k-dss has 143)
- A constraint solver integration (partial SMT)
- Accept incompleteness (some proofs won't go through without manual lemmas)

**Open question:** How far can lemma rules + FFI take us before we need SMT? The multisig example (63-node tree) works entirely without SMT. k-dss-level (37 variables, non-linear arithmetic) likely needs either SMT or very clever lemma design.

## Simplification Strategy

### Level 1: Eager Ground Simplification (FFI)

Already working. `!plus 3 5 C` → C = 8 via BigInt FFI.

### Level 2: Identity/Annihilation Lemmas

Simple symbolic rules as backward-chaining clauses:

```
plus_zero_l: plus e X X.           % 0 + X = X
plus_zero_r: plus X e X.           % X + 0 = X
mul_one_l:   mul (i e) X X.        % 1 * X = X
mul_zero_l:  mul e X e.            % 0 * X = 0
```

Plus Store.put-time normalization for nested terms (handles arbitrary depth).

### Level 3: Constraint-Aware Algebraic Simplification

This is the critical level for scaling beyond multisig. K-dss has 143 lemmas at this level. Three sub-approaches, analyzed in depth:

#### 3a: Constraint Predicates

Model range constraints as persistent facts in the state:

```
% Accumulated from execution + path conditions:
!rangeUInt256 X.
!rangeUInt256 Y.

% Simplification rule that checks constraints:
chop_add_safe: chop_add X Y Z
  <- plus X Y Z
  <- rangeUInt256 Z.     % Z fits in 256 bits → no wrap
```

**Pros:**
- Constraints live in the state naturally (already how JUMPI path conditions work)
- Backward proving searches the persistent state for matching constraints
- No term representation changes
- Constraints accumulate automatically through execution

**Cons:**
- Need to PRODUCE constraint facts at the right time (when do we know `rangeUInt256 X`?)
- Backward proving for constraint checks adds to the 83.6% bottleneck
- Constraint explosion: many facts of the form `!rangeUInt256 Xi` accumulate

**When constraints are available:** EVM operations naturally produce range information. CALLDATALOAD produces a 256-bit value (always in range). ADD with overflow check establishes the result is in range. A specialized `produce_constraint` mechanism could emit these.

#### 3b: Guard Predicates

Simplification rules with explicit guard checks as backward-chaining premises:

```
% Simplify plus(minus(X, Y), Y) → X when subtraction is valid
plus_minus_cancel: plus (minus X Y) Y X
  <- leq Y X.           % guard: Y <= X (subtraction was valid)

% Simplify chop(X + Y) → X + Y when no overflow
chop_add_no_overflow: chop_add X Y Z
  <- plus X Y Z
  <- lt Z (pow256).      % guard: Z < 2^256

% k-dss style: signed/unsigned conversion
unsigned_add: plus X (unsigned Y) Z
  <- plus X Y Z
  <- rangeSInt256 Y
  <- rangeUInt256 X
  <- rangeUInt256 Z.
```

**Pros:**
- Guards are explicit backward-chaining goals
- Can use FFI for ground guard checks (`leq 3 5` → true)
- Declarative: the lemma states what it needs

**Cons:**
- Symbolic guards (`leq Y X` where both symbolic) need their own lemmas or constraint facts
- Chaining guards is possible but may create deep backward-proving trees
- Need to handle guard failure gracefully (simplification just doesn't apply)

#### 3c: Typed/Annotated Terms

Attach range/type info directly to term values:

```
% Terms carry their type
typed: bin -> range -> bin.
u256: range.
s256: range.
addr: range.

% Operations on typed values propagate types
typed_plus: plus (typed X u256) (typed Y u256) (typed Z u256)
  <- plus X Y Z
  <- lt Z (pow256).

% Untyped values can be typed when range is established
assign_type: typed X u256 <- rangeCheck X.
```

**Pros:**
- Range info travels with the value — no separate constraint facts
- Pattern matching on `typed X u256` is efficient (one tag check)
- Self-documenting: you can see which values are range-checked

**Cons:**
- Changes term representation globally — every rule must handle typed values
- Extra wrapping/unwrapping overhead (every value becomes `typed(X, range)`)
- Rigid: adding new type info requires new range constructors
- Breaks existing FFI (needs to understand typed terms)

#### Recommendation

**3b (guard predicates) combined with 3a (constraint predicates)** is the most natural fit:

- Path conditions from JUMPI branches produce constraint facts (3a)
- Simplification lemmas check for these constraints via backward proving (3b)
- No term representation changes (unlike 3c)
- Guards can fall back to FFI for ground cases
- Lemma rules are declarative and extensible

### Level 3 Multi-Layer Simplification

K-dss's dirty lemmas show the real complexity. Consider gas computation accumulation:

```k
% k-dss dirty_lemmas.k.md, lines 117-132:
rule X -Int (A1 +Int (A2 +Int (A3 +Int ... (A17 +Int (X +Int AS))...)))
  => 0 -Int (A1 +Int (A2 +Int (A3 +Int ... (A17 +Int AS)...)))
```

This is a cancellation lemma for 17+ nested additions where X appears at both ends. In ILL, we'd need:

```
% General cancellation: X - (... + X + ...) → -(... + ...)
% Can't write a fixed-depth rule. Need recursive approach:

% Option 1: Recursive lemma chain
cancel_in_sum: minus X (plus A (plus B Rest)) (neg (plus A Rest'))
  <- cancel_in_sum X (plus B Rest) Rest'.

cancel_base: minus X (plus X Rest) (neg Rest).
```

This works but requires the backward prover to search through the nested additions recursively — O(depth) backward-proving steps.

**Alternative: Store.put normalization handles this at construction time.** When building `minus(X, plus(A1, plus(A2, ...plus(X, AS)...)))`, the normalizer detects X on both sides and cancels. This is O(depth) at construction time, amortized across the computation.

For k-dss's 17-deep nesting, the normalizer would need to walk 17 levels. Still O(n) but happens once at construction, not repeatedly during proof search.

### Level 4: Storage Pattern Decomposition

K-dss and hevm both decompose Solidity storage patterns:
- `keccak(key ++ slot_id)` → per-mapping array
- `keccak(slot_id) + offset` → per-array element

In ILL:

```
% Injectivity lemma (used in rely-diff example above)
sha3_injective: neq (sha3 X) (sha3 Y) <- neq X Y.

% Keccak of distinct base slots are distinct
sha3_distinct_bases: neq (sha3 (concat X S1)) (sha3 (concat Y S2))
  <- neq S1 S2.

% Storage offset distinctness
slot_offset: neq (plus (sha3 X) N1) (plus (sha3 X) N2)
  <- neq N1 N2.
```

## Import Graph

Currently `evm.ill` and `bin.ill` are loaded via JS (`mde.load([bin.ill, evm.ill, multisig.ill])`). This is dirty — dependencies should be declared in .ill files so we can swap EVM implementations by changing one import.

**Fix:** Add `#import` directives:

```
% bin.ill — no imports (leaf)
% evm.ill — add at top:
#import(../prelude/types.ill)
#import(bin.ill)

% multisig.ill — add:
#import(evm.ill)
#import(multisig_code.ill)  % already there
```

Then `mde.load('multisig.ill')` resolves the full graph. `resolveImports()` already handles recursive resolution — just needs dedup (skip already-imported paths, ~3 lines).

With this, `evm2.ill` can `#import(bin.ill)` and `multisig2.ill` can `#import(evm2.ill)` — different implementations benchmarkable without touching JS.

## Symbolic Value Representation: Full Possibility Space

Two orthogonal axes determine the symbolic execution approach:
1. **Value representation** — what does C become when `!plus A B C` can't be computed?
2. **Simplification strategy** — where/when are symbolic expressions reduced?

The three simplification strategies (S1-S3 above) address axis 2. This section explores axis 1 exhaustively.

### R1: Catch-All Skolem Terms

When `!plus A B C` fails, a backward-chaining catch-all clause produces a **structured term**:

```
plus_sym: plus X Y (plus_expr X Y).
```

C becomes `plus_expr(A, B)` — a concrete Store node carrying the operation name and inputs. Subsequent operations nest: `plus_expr(plus_expr(A, B), 5)`.

**How it works:** The existing three-fallback chain (FFI → state lookup → backward proving) reaches `plus_sym`, which always unifies. Zero engine changes.

**Properties:**
- Auto-unique: `plus_expr(A, B)` has a deterministic hash from inputs (content-addressed)
- Self-describing: the term carries its provenance (operation + arguments)
- Pattern-matchable: normalizer can inspect structure (`plus_expr(X, 0) → X`)
- Nested growth: O(depth) per chain of symbolic operations, but content-addressed sharing limits actual storage

**Analogues:** hevm's `Add(Var x, Lit 3)`, K's stuck `+Int` applications, Rosette's hash-consed terms.

### R2: Loli Continuations with Eigenvariables

Instead of producing a Skolem term, **assume** `!plus A B C` and continue with C as a fresh variable:

```
evm/add:
  pc PC * code PC 0x01 * sh (s (s SH)) * stack (s SH) A * stack SH B
  -o {
    code PC 0x01 *
    (!plus A B C -o { pc PC' * sh (s SH) * stack SH C })
  }.
```

The engine's `expandItem` already handles `!P -o { body }` by:
1. Producing the body as linear facts (execution continues)
2. Adding `!P` as a persistent fact (constraint assumed)

So `!plus A B C` with C free becomes a **flat constraint** in `state.persistent`, and C flows into the state as a variable.

**The naming problem:** `applyIndexed` with an unbound metavar slot returns the original freevar hash unchanged. Since freevars are content-addressed, `Store.put('freevar', ['_C'])` always returns the same hash. If the rule fires twice (two ADD steps), both produce the same C hash — two constraints `plus(3, 2, C)` and `plus(5, 7, C)` share C. This is unsound.

**Mitigation: Step-indexed eigenvariables.** Generate fresh variables with a monotonic counter:

```javascript
// In forward.js, ~10 LOC:
let evarCounter = 0;
function freshEvar() {
  return Store.put('evar', [Store.put('binlit', [BigInt(evarCounter++)])]);
}

// When substituting consequent with unbound metavar slot:
if (theta[slot] === undefined) {
  theta[slot] = freshEvar();
}
```

Each `evar(N)` is globally unique. Constraints become: `plus(3, 2, evar(0))`, `plus(5, 7, evar(1))` — distinct.

**Why de Bruijn doesn't directly apply:** De Bruijn indices encode distance-to-binder in syntactically scoped structures. Our constraints live in a flat state (multiset), not a binding tree. The closest analogue is **locally nameless**: de Bruijn within a single rule (which we already do — metavar slots ARE de Bruijn-like), globally unique names across rules (eigenvariables with step counter). So we already use the right internal representation; the missing piece is global fresh generation across rule applications.

**Properties:**
- Flat constraints: `plus(A, B, evar(0))`, `plus(evar(0), E, evar(1))` — no nesting
- Constraint interaction: when `evar(0)` resolves (e.g., on a concrete branch), propagate the value to all constraints and state facts referencing it
- SMT-friendly: flat constraints map directly to `(assert (= (+ a b) c))` assertions
- Backward resolution: if A becomes ground later, `!plus A B evar(0)` can be re-checked and resolved via FFI
- Needs engine change: ~10 LOC for fresh generation, plus constraint propagation machinery

**Scaling advantage:** When a symbolic value becomes concrete (through path branching or constraint propagation), evar-based constraints can be **resolved** — FFI recomputes the result, and the evar is replaced everywhere. With Skolem terms, `plus_expr(A, B)` is a fixed hash even after A becomes concrete; re-evaluation requires either a normalizer pass or explicit resolution rules.

**Scaling disadvantage:** Less sharing than Skolem (each evar is unique even for equivalent operations). More Store nodes (evar + constraint per operation vs one Skolem term). Constraint propagation requires an evar→facts index.

**Analogues:** Constraint Logic Programming (CLP), Tamarin's constraint solving, existential introduction in sequent calculus.

### R3: CPS Decomposition

Split each EVM rule into consume → compute → produce, with explicit concrete/symbolic alternatives:

```
evm/add/consume:
  pc PC * code PC 0x01 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) A * stack SH B
  -o { add_cont PC' A B SH }.

add_cont/concrete:
  add_cont PC' A B SH * !plus A B C
  -o { pc PC' * sh (s SH) * stack SH C }.

add_cont/symbolic:
  add_cont PC' A B SH
  -o { pc PC' * sh (s SH) * stack SH (plus_expr A B) }.
```

The concrete version has `!plus A B C` as antecedent — fires when FFI succeeds. The symbolic version is the fallback — fires when the continuation fact has no arithmetic match.

**Properties:**
- Explicit control over concrete vs symbolic paths — no catch-all ordering concerns
- Strategy stack prefers `add_cont/concrete` (more antecedents = more specific)
- Two forward steps per opcode (consume + produce) — doubles step count
- Rule count roughly doubles (2 per opcode)
- Each cont fact is unique to one opcode → strategy stack handles naturally

**Advantage:** No catch-all clauses needed. The fallback is a separate rule, not a backward clause. Ordering is handled by the engine's natural specificity preference.

**Disadvantage:** 2x rule count, 2x forward steps. Intermediate `add_cont` facts pollute the state. More verbose .ill files.

### R4: Skolem Terms + Constraint Side-Channel

Use Skolem terms for execution continuity (state flows through `plus_expr(A, B)` as values) AND emit flat constraints as persistent facts for external reasoning:

```
plus_sym: plus X Y (plus_expr X Y).

% Forward rule: after catch-all fires, also record the constraint
emit_constraint:
  stack SH (plus_expr A B)
  -o {
    stack SH (plus_expr A B) *        % preserve the value
    !arith_constraint (plus A B (plus_expr A B))  % record constraint
  }.
```

Or more elegantly, modify catch-all to emit both:

```
plus_sym_tracked: plus X Y (plus_expr X Y)
  <- emit_persistent (arith_eq plus X Y (plus_expr X Y)).
```

**Properties:**
- Best of both: Skolem terms for pattern-matching normalization, flat constraints for SMT export
- More storage (both representations)
- Constraint emission can be toggled (only needed for SMT integration)
- Same engine as R1 (no fresh variable generation needed)

**Advantage:** Future-proof. When we add SMT integration, constraints are already available. Meanwhile, Skolem terms work for normalization.

**Disadvantage:** Redundant information storage. Complexity of keeping both representations in sync.

### R5: Deferred Thunks (Lazy Evaluation)

When `!plus A B C` fails, produce a "thunk" that resolves when its arguments become ground:

```
plus_sym: plus X Y (thunk plus X Y).

% Resolution rule: when both args are ground, evaluate
resolve_thunk_plus:
  stack SH (thunk plus A B) * !is_ground A * !is_ground B * !plus A B C
  -o { stack SH C }.
```

The thunk is like a Skolem term but with explicit evaluation semantics. The resolution rule fires as a forward simplification when preconditions are met.

**Properties:**
- Lazy: defers computation until arguments are available
- Handles mixed concrete/symbolic: if A is concrete now but B becomes concrete through branching, the thunk resolves then
- Requires `!is_ground` predicate (checkable via tag inspection, no Store traversal for binlit/atom)
- Same Store representation as Skolem terms (thunk IS a Skolem term with different naming)
- Resolution rules are forward simplification rules (approach S2)

**Advantage:** Natural for symbolic execution with branching — thunks resolve on concrete branches automatically.

**Disadvantage:** Essentially R1 + S2 combined under a different name. `is_ground` check adds overhead.

### Representation Comparison

| | R1 Skolem | R2 Loli/Evar | R3 CPS | R4 Skolem+Constraint | R5 Thunks |
|---|---|---|---|---|---|
| C becomes | `plus_expr(A,B)` | `evar(N)` | `plus_expr(A,B)` | `plus_expr(A,B)` | `thunk(plus,A,B)` |
| Constraint stored | Implicit in term | Explicit persistent fact | Implicit | Both | Implicit |
| Engine changes | 0 LOC | ~10 LOC (fresh gen) | 0 LOC | 0 LOC | 0 LOC |
| .ill changes | ~10 lines | Rule rewrite (all opcodes) | ~2x rules | ~20 lines | ~15 lines |
| Auto-unique | Yes (content-addressed) | Needs fresh gen | Yes | Yes | Yes |
| Pattern-matchable | Yes | No (opaque evar) | Yes | Yes | Yes |
| Simplifiable | Normalizer | Constraint propagation | Normalizer | Both | Normalizer + resolution |
| Nesting | Deep | Flat | Deep | Deep + flat | Deep |
| SMT export | Flatten terms | Direct | Flatten terms | Direct | Flatten terms |
| Backward resolution | Needs normalizer pass | Natural (re-check constraint) | Needs normalizer pass | Natural | Via resolution rules |
| Sharing (memory) | High (content-addressed) | Low (each evar unique) | High | Medium | High |
| Forward steps | 0 extra | 0 extra | 2x | 1 extra (emit) | 0-1 extra |

### When Each Approach Wins

**R1 (Skolem)** wins when: most symbolic expressions stay symbolic end-to-end (no resolution needed), normalizer handles all useful simplifications, no SMT integration planned. Simplest, fastest, most battle-tested (hevm, K).

**R2 (Loli/Evar)** wins when: symbolic values frequently become concrete through branching (evar resolution propagates automatically), SMT integration is planned (flat constraints export directly), constraint interaction is important (combining path conditions with arithmetic constraints).

**R3 (CPS)** wins when: explicit control over concrete vs symbolic paths is critical, the programmer wants to see exactly which path was taken, debugging/tracing is a priority. Highest readability cost.

**R4 (Skolem+Constraint)** wins when: both normalization AND SMT export are needed (k-dss likely). Future-proof at the cost of some redundancy.

**R5 (Thunks)** wins when: mixed concrete/symbolic with frequent late resolution. Essentially R1 with explicit resolution semantics.

## Revised Top Approaches

Two axes: **value representation** (R1-R5 above) × **simplification strategy** (S1-S3 above). Not all combinations make sense. Here are the most promising:

### Approach 1: Skolem + Engine Normalization (R1 × S1 — hevm path)

**Symbolic handling:** Catch-all clauses produce Skolem terms. Post-substitution normalizer in substitute.js simplifies at construction time.

**What's in .ill:**
```
% Constructors for symbolic expressions
plus_expr:  bin -> bin -> bin.
mul_expr:   bin -> bin -> bin.
minus_expr: bin -> bin -> bin.

% Catch-alls (reached only when FFI fails)
plus_sym:  plus X Y (plus_expr X Y).
mul_sym:   mul X Y (mul_expr X Y).
minus_sym: minus X Y (minus_expr X Y).

% Domain lemmas as backward clauses
sha3_injective: neq (sha3 X) (sha3 Y) <- neq X Y.
```

**What's in JS:** ~100 LOC normalizer in substitute.js (ground folding, identity, cancellation).

**Pros:** Fast (O(1) per term), deterministic, bottom-up handles depth, zero structural engine changes, FFI fast path preserved. Most familiar from K/hevm.
**Cons:** Simplification rules hardcoded in JS. Backward resolution requires normalizer re-walk. No direct SMT export.

### Approach 2: Skolem + ILL Simplification Rules (R1 × S2 — K path)

**Symbolic handling:** Same Skolem terms. Simplification as forward rules in .ill — fully declarative.

**What's in .ill:**
```
% Same constructors + catch-alls as Approach 1

% Simplification forward rules (fire between opcode steps)
simplify_plus_ground:
  stack SH (plus_expr A B) * !plus A B C
  -o { stack SH C }.

simplify_plus_zero_l:
  stack SH (plus_expr 0 X) -o { stack SH X }.

simplify_plus_zero_r:
  stack SH (plus_expr X 0) -o { stack SH X }.

simplify_plus_cancel:
  stack SH (plus_expr (minus_expr X Y) Y)
  -o { stack SH X }.

% Domain lemmas (same as Approach 1)
sha3_injective: neq (sha3 X) (sha3 Y) <- neq X Y.
```

**What's in JS:** Minimal — possibly priority mechanism (~20 LOC).

**Pros:** Fully declarative — new simplifications = new .ill rules, no JS changes. Extensible. Most readable/auditable.
**Cons:** Only matches at fact level (depth 1-2). Extra forward steps per simplification. Rule set grows.

### Approach 3: Loli Eigenvariables + Constraint Propagation (R2 × S-constraint)

**Symbolic handling:** Loli continuations with step-indexed eigenvariables. Constraints accumulate as persistent facts. Resolution via constraint propagation.

**What's in .ill:**
```
% EVM rules rewritten with loli pattern for symbolic arithmetic:
evm/add:
  pc PC * code PC 0x01 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) A * stack SH B
  -o {
    code PC 0x01 *
    (!plus A B C -o { pc PC' * sh (s SH) * stack SH C })
  }.

% Domain lemmas (same)
sha3_injective: neq (sha3 X) (sha3 Y) <- neq X Y.
```

**What's in JS:** ~10 LOC fresh evar generation. Constraint propagation engine (~80 LOC): when an evar is resolved (value becomes concrete), substitute through all state facts and re-check constraints.

**Pros:** Flat constraints (no nesting), natural backward resolution (evars resolve when args become concrete), direct SMT export, clean separation of state and arithmetic obligations. Most amenable to external solver integration.
**Cons:** Every opcode rule needs rewriting (loli pattern). Constraint propagation engine is non-trivial. Less content-addressed sharing. Evar-based values are opaque to pattern matching (can't normalize `evar(42) + 0`).

### Approach 4: Hybrid Skolem + Engine Normalization + ILL Lemmas (R1 × S3 — K+hevm path)

**Symbolic handling:** Engine normalizes common patterns (ground, identity, cancellation). ILL rules handle domain-specific lemmas.

**What's in .ill:**
```
% Same constructors + catch-alls

% Domain-specific lemmas ONLY (not basic arithmetic)
sha3_injective: neq (sha3 X) (sha3 Y) <- neq X Y.
sha3_distinct_bases: neq (sha3 (concat X S1)) (sha3 (concat Y S2)) <- neq S1 S2.

% Constraint-aware simplifications via guard predicates
chop_add_safe: chop_add X Y Z <- plus X Y Z <- rangeUInt256 Z.
```

**What's in JS:** ~100 LOC normalizer + constraint production (~50 LOC).

**Pros:** Most powerful. Engine handles fast common cases, .ill handles domain logic. Matches K/KEVM architecture.
**Cons:** Two simplification locations. Harder to debug.

### Approach 5: CPS Decomposition + Skolem Fallback (R3 × S1)

**Symbolic handling:** Each opcode split into consume/compute/produce with explicit concrete vs symbolic alternatives.

**What's in .ill:**
```
evm/add/consume:
  pc PC * code PC 0x01 * !inc PC PC' *
  sh (s (s SH)) * stack (s SH) A * stack SH B
  -o { add_cont PC' A B SH }.

add_cont/concrete:
  add_cont PC' A B SH * !plus A B C
  -o { pc PC' * sh (s SH) * stack SH C }.

add_cont/symbolic:
  add_cont PC' A B SH
  -o { pc PC' * sh (s SH) * stack SH (plus_expr A B) }.
```

**What's in JS:** ~100 LOC normalizer (same as Approach 1).

**Pros:** Most explicit control. No catch-all ordering concerns. Each path is a visible rule. Best for debugging/tracing.
**Cons:** 2x rule count, 2x forward steps. More verbose. Intermediate continuation facts.

### Master Comparison

| | Ap1 (R1×S1) | Ap2 (R1×S2) | Ap3 (R2) | Ap4 (R1×S3) | Ap5 (R3×S1) |
|---|---|---|---|---|---|
| Value repr | Skolem nested | Skolem nested | Flat evar | Skolem nested | Skolem nested |
| Simplification | JS engine | .ill rules | Constraint prop | Both | JS engine |
| JS LOC | ~100 | ~20 | ~90 | ~150 | ~100 |
| .ill changes | ~30 lines | ~80 lines | Full rewrite | ~60 lines | ~2x rules |
| Extensibility | JS | .ill only | JS | .ill for domain | .ill |
| Depth handling | Unlimited | Depth 1-2 | N/A (flat) | Unlimited + 1-2 | Unlimited |
| Forward steps/op | 1 | 1 + N simpl | 1 | 1 | 2 |
| SMT readiness | Low | Low | High | Medium | Low |
| Backward resolution | Normalizer pass | Simpl rules | Natural | Normalizer + rules | Normalizer pass |
| Readability | Medium | High | Medium | Medium | Highest |
| k-dss readiness | Medium | Medium | Medium-High | High | Medium |

### Recommended Implementation Order

1. **Shared foundation** (all approaches): Catch-all clause constructors (`plus_expr`, etc.) in .ill. Import graph (done). Stack-as-list rewrite. ~1 hour.

2. **Approach 1** (Skolem + engine normalizer) — implement `evm-skolem.ill` + normalizer. Benchmark: symbolic multisig, expression growth.

3. **Approach 2** (Skolem + ILL rules) — implement `evm-simpl.ill`. Same benchmark. Compare forward step count and expression sizes vs Approach 1.

4. **Approach 3** (Loli eigenvariables) — implement `evm-loli.ill` + fresh evar generation. Same benchmark. Compare constraint count and resolution rates.

5. **Evaluate:** Which representation produces smaller/simpler states? Which has fewer forward steps? Which handles branching better? These three cover the fundamental design space — Approaches 4 and 5 are combinations/refinements.

Key benchmark questions:
- **1 vs 2:** Engine vs rule-level simplification — which is faster?
- **1 vs 3:** Nested Skolem vs flat constraints — which scales better with branching?
- **2 vs 3:** Declarative Skolem rules vs loli constraints — which is more readable/maintainable?

## Theory-Informed Simplification Techniques

The 5 approaches above were derived from EVM-specific tools (hevm, K). Proof theory and term rewriting literature reveals additional techniques. Full survey: `doc/research/expression-simplification.md`.

### T1: AC-Normalization at Construction Time (Maude philosophy)

**Highest-impact single technique.** Declare `plus`/`mul` as associative-commutative. At `Store.put` time:
1. Flatten nested applications: `plus(plus(a,b), c)` → `ac_plus([a, b, c])`
2. Sort children by hash (canonical order)
3. Fold constants: `ac_plus([3, x, 5])` → `ac_plus([8, x])`
4. Identity elimination: `ac_plus([0, x])` → `x`

Content-addressing then gives AC equivalence for free: `plus(a,plus(b,c))` and `plus(c,plus(a,b))` hash identically. Every downstream operation — matching, indexing, state dedup — benefits with zero per-step cost.

**Orthogonal to R1-R5**: works with any value representation. Applies to Skolem terms (`plus_expr`) too.

**LOC:** ~300 (flatten/sort in Store, constant folding, identity rules).

### T2: E-Graphs / Colored E-Graphs

Store is half an e-graph (content-addressed hashcons). The missing half: union-find equivalence classes. A full e-graph would represent all equivalent forms of a symbolic expression simultaneously. **Extraction** picks the simplest form via cost function.

**Colored e-graphs** (Singher & Shacham 2023) add context-sensitive equalities: each JUMPI branch gets a "color." Equalities from that branch are visible only in that color. Maps perfectly to symexec's tree exploration.

**Tension with ILL:** E-graphs are monotonic (only add equalities). Linear logic consumes facts. Need scoped e-graph that can fork/rollback at branch points.

**LOC:** ~800 for basic e-graph + rebuild. ~300 for colored extension.

### T3: CHR Compilation for Forward Engine

CHR simpagation IS ILL forward rules. Decades of compilation research applies directly:
- **Join ordering:** Match most selective antecedent first. For `A * B * !plus A B C -o D`, if there are 5 `A` facts but 100 `B` facts, match `A` first. Currently: left-to-right.
- **Guard scheduling:** Move cheap FFI guards (neq: O(1) BigInt compare) before expensive pattern matches. Currently: guards evaluated at pattern match position.
- **Occurrence indexing:** Each constraint occurrence in a rule head compiled to a lookup.

**LOC:** ~150 (join ordering in rule-analysis.js, guard reordering).

### T4: Bottom-Up Simplifier (Isabelle simp architecture)

Run a post-step normalization pass on every newly produced term:
1. Traverse bottom-up (simplify subterms first)
2. Try simplification rules at each node (indexed by disc tree)
3. **Simprocs** = FFI functions (already exist)
4. **Congruence rules** = propagate known equalities into subterms

Missing piece from Isabelle: congruence rules. If `!eq A 5` is in persistent state, `plus(A, 3)` should simplify to `8`. Currently the engine doesn't propagate equalities into subterms.

**LOC:** ~300 (bottom-up traverser, congruence propagation). Connects to existing disc-tree + FFI.

### T5: Interval Tracking + Path Feasibility

Maintain `[lo, hi]` bounds per symbolic variable, updated on every arithmetic/comparison fact:
- `lt(gas, 100)` → `gas ∈ [0, 99]`
- `gt(gas, 50)` → `gas ∈ [51, 2^256-1]`
- Intersection: `gas ∈ [51, 99]`
- Empty intersection → prune path (infeasible)

Lightweight alternative to full SMT. Catches simple contradictions fast. Inspired by abstract interpretation (Cousot & Cousot) interval domain.

**LOC:** ~200 (interval store, update on arithmetic facts, infeasibility check).

### Theory Techniques vs Existing Approaches (Cross-Cutting)

| Theory Technique | Compatible With | Primary Benefit |
|---|---|---|
| T1 AC-Normalization | All approaches (R1-R5, S1-S3) | AC equivalence → syntactic identity, free dedup |
| T2 E-Graphs | R1 Skolem best fit | Multiple equivalent forms tracked simultaneously |
| T3 CHR Compilation | Forward engine (all) | Faster rule matching (join ordering, guard scheduling) |
| T4 Bottom-Up Simplifier | R1 Skolem + S1 Engine | Deep subterm simplification, congruence propagation |
| T5 Interval Tracking | All approaches | Path pruning, contradiction detection |

### Revised Top 5 Approaches (Theory-Integrated)

Incorporating theory techniques, the recommended approaches become:

**1. Skolem + AC-Canonical Engine Normalization (R1 × S1 × T1,T4)**
- Catch-all clauses produce Skolem terms
- AC-normalization at Store.put time (T1) for canonical forms
- Bottom-up simplifier (T4) for deep rewrites
- JS: ~400 LOC. .ill: ~30 lines.
- **Why #1:** Highest impact/effort ratio. T1 alone handles most common simplifications for free.

**2. Skolem + ILL Simplification Rules + AC-Canonical (R1 × S2 × T1)**
- Same Skolem terms, but simplification rules in .ill (declarative)
- AC-normalization at construction time (T1) handles commutativity/associativity
- .ill rules handle domain-specific lemmas (sha3 injectivity, etc.)
- JS: ~300 LOC (AC-norm). .ill: ~80 lines.
- **Why #2:** Most extensible. New simplifications = new .ill rules.

**3. Loli Eigenvariables + Constraint Propagation + Intervals (R2 × T5)**
- Flat constraints with step-indexed eigenvariables
- Interval tracking (T5) for path feasibility pruning
- CLP-style attributed variables for constraint propagation
- JS: ~300 LOC. .ill: full rewrite.
- **Why #3:** Most SMT-ready. Flat constraints export directly.

**4. Hybrid Skolem + E-Graph Layer (R1 × S3 × T1,T2)**
- Skolem terms for state flow, e-graph for equivalence tracking
- AC-normalization (T1) as base layer
- Colored e-graph (T2) for branch-sensitive simplification
- JS: ~1100 LOC. .ill: ~60 lines.
- **Why #4:** Most powerful at scale. But highest implementation cost.

**5. Skolem + AC-Canonical + CHR Join Optimization (R1 × S1 × T1,T3)**
- Same as Approach 1, but with CHR-style rule matching optimization
- Join ordering (T3) reorders antecedent matching by selectivity
- Guard scheduling (T3) moves cheap FFI checks first
- JS: ~550 LOC. .ill: ~30 lines.
- **Why #5:** Performance-focused. Best when rule count grows (100+ symbolic rules).

### Recommended Implementation Order (Revised)

1. **Foundation (all approaches):** Catch-all constructors in .ill, import graph, stack-as-list. ~1 hour.

2. **T1: AC-Canonical Store.put.** Implement for `plus`/`mul`. Immediate benefit for all approaches. ~1 day.

3. **Approach 1 (Skolem + T1 + T4).** Implement engine normalizer + AC-canonical forms. Benchmark symbolic multisig. ~2 days.

4. **Approach 2 (Skolem + T1 + ILL rules).** Same benchmark with declarative rules instead of engine normalizer. Compare step counts. ~1 day.

5. **Approach 3 (Loli + T5).** Implement eigenvariable generation + interval tracking. Same benchmark. Compare constraint growth vs expression growth. ~2 days.

6. **Evaluate:** Which approach produces smaller states? Which has fewer steps? Which handles branching (JUMPI) better?

7. **Scale-up (if needed):** Add T2 (e-graphs) and/or T3 (CHR join ordering) to the winning approach.

## Open Questions

1. **How far without SMT?** Keccak slot independence works with one lemma. k-dss's `frob` (37 variables, non-linear arithmetic) likely needs either extensive lemma libraries or SMT. Find boundary experimentally.

2. **Lemma discovery.** k-dss's 143 lemmas were hand-written over months. Can we detect "stuck" symbolic terms and suggest needed lemmas?

3. **Expression growth rate.** Without normalization, how fast do symbolic expressions grow? With normalization, do they stay bounded? Need empirical data from symbolic multisig.

4. **Simplification rule priority.** In Approach 2, do simplification rules compete with opcode rules for matching? Does the strategy stack handle this naturally, or do we need explicit priority?

5. **Catch-all clause ordering.** The catch-all `plus_sym` must only fire when FFI fails. The three-fallback chain ensures this today. Will it still work if we add more backward clauses for `plus`?

6. **Gas modeling.** K-dss tracks gas. hevm/halmos skip it for symbolic mode. Could be a compile-time flag.

7. **Evar propagation cost.** For Approach 3, when an evar resolves, how expensive is propagation through all state facts? Need an evar→facts index. What's the amortized cost at 10K+ steps?

8. **Skolem vs evar for branching.** Symexec creates branches via additive choice (`&`). With Skolem terms, each branch has the same `plus_expr(A, B)` hash (shared). With evars, each branch has independent `evar(N)`. Does sharing help or hurt?

9. **Constraint interaction.** Can flat evar constraints (Approach 3) enable cross-constraint reasoning that Skolem terms can't? E.g., `plus(A, B, evar0)` + `lt(A, 5)` → `lt(evar0, B+5)` — can the engine derive this without SMT?

10. **CPS overhead.** In Approach 5, the intermediate continuation facts (`add_cont`) must be indexed by the strategy stack. How many continuation types are needed? Does this fragment the index?

11. **AC-normalization interaction with matching.** If Store.put normalizes `plus(a,b)` to `ac_plus([a,b])`, do existing forward rule patterns still match? Need either: (a) rewrite rule patterns to use `ac_plus`, or (b) AC-aware matching in `tryMatch`. Option (a) is simpler.

12. **E-graph monotonicity vs linear consumption.** How does a scoped e-graph interact with `mutateState()`/`undoMutate()`? Need e-graph undo operations aligned with the existing undo log architecture.

13. **Horner form for multi-variable polynomials.** k-dss's `frob` has 37 variables. Horner form is canonical per-variable but the variable ordering matters. How to choose the ordering? Lexicographic by variable name (deterministic) vs frequency-based (adaptive)?

## References

- Cervesato, Hodas, Pfenning (2000) — *Efficient Resource Management for Linear Logic Proof Search*
- Martens (2015) — *Programming Interactive Worlds with Linear Logic* (Ceptre)
- Simmons & Pfenning (2008) — *Linear Logical Algorithms*
- Andreoli (1992) — *Logic Programming with Focusing Proofs in Linear Logic*
- k-dss (MakerDAO) — `~/src/k-dss/` — formal verification via K framework
- KEVM — `~/src/evm/repos/` — K framework EVM semantics
- hevm — `~/src/evm/repos/` — Haskell symbolic EVM
- Move Language — *A Language With Programmable Resources*
- Tamarin Prover — multiset rewriting for security protocol verification
- Jaffar & Maher (1994) — *Constraint Logic Programming: A Survey* (CLP framework for flat constraints)
- Locally nameless representation — de Bruijn within binders, global names across (Charguéraud 2012)
- Symbolic arithmetic design space — `doc/research/symbolic-arithmetic-design-space.md`
- Expression simplification survey — `doc/research/expression-simplification.md`
- Willsey et al. (2021) — *egg: Fast and Extensible Equality Saturation*
- Singher & Shacham (2023) — *Colored E-Graph: Equality Reasoning with Conditions*
- Eker (2003) — *Associative-Commutative Rewriting on Large Terms* (Maude)
- Frühwirth (2009) — *Constraint Handling Rules*
- Nipkow, Paulson & Wenzel — *Isabelle/HOL* (simp tactic architecture)
- Cousot & Cousot (1977) — *Abstract Interpretation: A Unified Lattice Model*
- Nelson & Oppen (1979) — *Simplification by Cooperating Decision Procedures*
