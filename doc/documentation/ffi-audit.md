---
title: FFI Audit — representation clusters, clause backup, linearity
tags:
  - ffi
  - architecture
  - representation
  - soundness
  - optimization
  - engine
---

# FFI Audit

Complete inventory of FFI predicates under `lib/engine/ill/ffi/`, classified by
representation cluster, clause-backup status, groundness mode, and linearity
classification. Input audit for TODO_0223 (Layer C — representation framework).
Status as of commit 2136d74.

## 1. Summary numbers

| Count | Item |
|---:|---|
| **56** | predicates declared in `defaultMeta` (`index.js:120–177`) |
| **53** | FFI implementations registered (`registry.size`) |
| **2** | metadata-only entries (`trie_get`, `trie_set` — compiled-clause dispatch, FFI removed) |
| **1** | aliased implementation (`not` and `not256` both dispatch to `arithmetic.bitwiseNot`) |
| **9** | representation clusters (see §3) |
| **8** | predicates with **no defining clauses** anywhere in the calculus |
| **2** | predicates with **only a zero-case clause** (`sdiv256/zero`, `smod256/zero`) |
| **0** | FFI predicates that consume linear resources (all are persistent / term-level) |
| **4** | target native representations currently produced by FFI code (`BigInt`, `Uint32Array`, `Uint8Array` / `Buffer`, JS `string`) |

## 2. Current FFI architecture (one glance)

```
lib/engine/ill/ffi/
├── index.js          # registry + defaultMeta (mode + multiModal flags)
├── mode.js           # parseMode("+ + -") + checkMode — groundness dispatch
├── convert.js        # φ / φ⁻¹: binToInt, intToBin, strToHash, hashToStr, isGround
├── arith-core.js     # pure BigInt core — shared by FFI + residual-resolver
├── arithmetic.js     # 43 arith/comparison/EVM-int primitives (1056 LOC)
├── array.js          # arr_get/set/alen/read_bytes/notMember + arrToTrie (312 LOC)
├── memory.js         # mem_read/expand/no_overlap/sha3_compute (206 LOC)
└── calldata.js       # cd_read over sconcat chain (37 LOC)
```

Complementary representation machinery outside `ffi/`:

- **`lib/kernel/eq-theory.js`** — 102 LOC: per-tag rewrite API. Built-in: strlit ↔ cons/atom.
- **`lib/engine/ill/binlit-theory.js`** — 139 LOC: binlit ↔ `i/o/e` rewrite + canonicalize.
- **`lib/engine/ill/bytecode-normalize.js`** — 234 LOC: one-shot `code PC V` → arrlit → trie state transform at load.
- **`lib/engine/ill/residual-resolver.js`** — shares `arith-core.js` with FFI; compiles ground residual goals at rule-specialisation time.

These are hand-coded Hoare abstraction functions with the same `φ / φ⁻¹ + native op`
shape as the FFI predicates — they are the non-registry half of today's manual
representation layer.

## 3. Predicate inventory by representation cluster

Groundness modes are abbreviated; `+` = ground input, `-` = computed output.
Clause column: `full` = complete inductive definition, `partial` = only special
case(s), `none` = not defined.

### 3.1 pure-binlit arithmetic (natural numbers, unbounded)

| Pred | Mode | Clause | Domain / notes |
|---|---|---|---|
| plus | `+ + +` multi | full (`bin.ill`) | multi-modal: `+-+` used by sub |
| inc | `+ -` | full | successor |
| mul | `+ + -` | full | |
| sub | `+ + -` | full | saturating at 0 |
| div | `+ + -` | full (via divmod) | fails on zero |
| mod | `+ + -` | full (via divmod) | fails on zero |
| checked_sub | `+ + -` | full | fails when `A < B` — EVM-gas critical |
| trim | `+ -` | full | canonical form — FFI is identity on binlit |

Cluster size: 8. Canonical Peano → BigInt target. All clauses in `calculus/ill/programs/bin.ill`.

### 3.2 pure-binlit comparison / equality

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| lt | `+ +` | full (via `gt`) | |
| le | `+ +` | full | |
| eq | `+ +` | full | reflexive + unification |
| neq | `+ +` | full (8 case clauses) | |
| gt | `+ + + -` | full (9 case clauses) | with carry — enables lexicographic |
| eq_bool | `+ + -` | full (3 clauses) | deterministic variant returning `0/1` |

Cluster size: 6. Boolean outcomes produced either as success/failure or as `0/1` binlit.

### 3.3 bit-level binlit (general, unbounded)

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| and | `+ + -` | full | overloaded with bool in `types.ill` |
| or | `+ + -` | full | overloaded with bool in `types.ill` |
| not | `+ -` | full | overloaded with bool in `types.ill`; FFI is 256-bit |
| xor | `+ + -` | full | |
| shr | `+ + -` | full | |
| shl | `+ + -` | full | |

Cluster size: 6. FFI masks to 256 bits; clauses are pure-logical (unbounded).
**Asymmetry flag**: FFI and clauses agree only when inputs fit in 256 bits —
`not` is the starkest case: clause `not e e` vs FFI `~0 = 2^256 - 1`. Needs an
explicit domain guard in the Layer-C registration.

### 3.4 EVM 256-bit modular arithmetic

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| to256 | `+ -` | full | `X mod 2^256` |
| not256 | `+ -` | full | aliases `bitwiseNot` |
| sub256 | `+ + -` | full | wrapping subtraction |
| div256 | `+ + -` | full | zero-safe — division by 0 returns 0 |
| mod256 | `+ + -` | full | zero-safe |
| exp256 | `+ + -` | full (`exp256/clause`) | clause is evaluator, not inductive |
| slt | `+ + -` | full (3 clauses: sign-sign cases) | signed-less-than (two's complement) |
| byte256 | `+ + -` | full (2 clauses: OOB + ok) | EVM BYTE opcode |
| sar256 | `+ + -` | full (4 clauses) | arithmetic right shift |
| addmod256 | `+ + + -` | full (zero + nz) | |
| mulmod256 | `+ + + -` | full (zero + nz) | |
| **sdiv256** | `+ + -` | **partial — only `sdiv256/zero`** | clause gap for nonzero signed div |
| **smod256** | `+ + -` | **partial — only `smod256/zero`** | clause gap for nonzero signed mod |
| **signextend256** | `+ + -` | **none** (declared only, `evm.ill:192`) | used by rules at `evm.ill:634` — no clause proof possible |
| **byte_size256** | `+ -` | **none** (declared only, `bin.ill:106`) | used by `evm.ill:549` — no clause proof possible |
| byte_replace | `+ + + -` | full (`byte_replace/def`) | uses ILL primitives |

Cluster size: 16. **4 with clause gaps**. All produce `X mod 2^256` values.

### 3.5 EVM gas policy

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| sstore_gas | `+ + -` multi | full (3 clauses) | Yellow-Paper SSTORE gas; clause + FFI both return 5000 on symbolic (conservative default) |

Cluster size: 1. Multi-modal because it returns a default for symbolic inputs.

### 3.6 opcode classifiers

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| is_push | `+ -` | full (`is_push/def`) | via `between` + `plus` — indirect |
| is_dup | `+ -` | full (`is_dup/def`) | same style |
| is_swap | `+ -` | full (`is_swap/def`) | same style |

Cluster size: 3. Clauses exist but go via `between` (which itself may have no
concrete definition; worth a follow-up check). Acceptable for audit purposes.

### 3.7 fixed-point reals

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| **fixed_mul** | `+ + + -` | **none** (only `fixedK_mul A B C :- fixed_mul K A B C` aliases in `types.ill:71-72`) | semantics is genuinely different arithmetic |
| **fixed_div** | `+ + + -` | **none** (only aliases at `types.ill:74-75`) | |

Cluster size: 2. **Novel CALC-specific gap**: these primitives embed a
scale factor (powers of 10) not expressible in pure Peano arithmetic without
Ackermann-scale blowup. Candidate for Layer C Phase-2 metatheoretic soundness
(bijection + homomorphism) rather than Phase-1 clause-equivalence property test.

### 3.8 string primitives (fully extralogical)

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| **string_concat** | `+ + -` | **none anywhere** | FFI-only primitive |
| **string_length** | `+ -` | **none anywhere** | FFI-only primitive |

Cluster size: 2. **Zero clause coverage**. No reachable clause-fallback path —
a FFI failure cannot fall through to logic. The strlit theory (`eq-theory.js`)
bridges strlit ↔ cons/charlit, which would in principle permit recursive clause
definitions of `concat` / `length`, but none exist. Layer-C candidate for
"extralogical primitive" classification: the registration must explicitly flag
"no clause equivalent exists — property-test is the only soundness witness".

### 3.9 array (arrlit + bit-indexed trie)

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| arr_get | `+ + -` | full (`arr.ill:28-31`) | arrlit O(1), trie O(log N) |
| arr_set | `+ + + -` multi | full (`arr.ill:40-44`) | functional update |
| alen | `+ -` | full (2 clauses) | only defined for arrlit/acons, not trie |
| read_bytes | `+ + + -` | full (2 clauses) | |
| notMember | `+ +` | full (2 clauses) | |
| trie_get | `+ + -` | full (3 clauses) | **FFI removed** — compiled-clause dispatch only |
| trie_set | `+ + + -` | full (3 clauses) | **FFI removed** — compiled-clause dispatch only |

Cluster size: 7. **`trie_get`/`trie_set` already migrated**: the defaultMeta
entries at `index.js:165-166` keep mode info only; Tier-2 compiled-clause
dispatch is the execution path. This is the existing template for a clean
FFI → representation-registry migration.

### 3.10 write-log memory

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| mem_read | `+ + -` multi | full (3 clauses: hit/miss/zero) | McCarthy's axioms |
| mem_expand | `+ + + - -` | full (3 clauses) | high-water mark + gas |
| no_overlap | `+ + + +` | full (2 clauses, symmetric) | |
| sha3_compute | `+ + + -` | full (`sha3_compute/eval`) | clause is trivial — produces symbolic `sha3 Bytes` constructor; FFI computes the concrete keccak256 |

Cluster size: 4. `sha3_compute` is the only primitive where **FFI and clause
compute different kinds of value**: clause returns a symbolic constructor,
FFI returns a concrete 256-bit digest. Soundness gate: a solver/decision
procedure check that symbolic `sha3 Bytes` is interpreted as
`keccak256(Bytes)` — not a trivial property test.

### 3.11 calldata

| Pred | Mode | Clause | Notes |
|---|---|---|---|
| cd_read | `+ + -` multi | full (`cd_read/hit|skip|cross|partial|nil`) | sconcat chain traversal |

Cluster size: 1. FFI has a documented leading-zero limitation
(`calldata.js:5-15`) — symbolic fallback via sconcat form is canonical.

## 4. Clause-backup status summary

| Status | Count | Predicates |
|---|---:|---|
| Full clause coverage | 46 | most arith, compare, bit, arr, mem, calldata |
| Partial (zero case only) | 2 | `sdiv256`, `smod256` |
| Declared only (no defining clauses) | 2 | `signextend256`, `byte_size256` |
| Alias only (no defining clauses) | 2 | `fixed_mul`, `fixed_div` |
| No calculus presence at all | 2 | `string_concat`, `string_length` |
| FFI removed, clause-only | 2 | `trie_get`, `trie_set` |

**Hard soundness gaps** (FFI off → wrong or stuck): 8 predicates — §3.4 (4), §3.7 (2), §3.8 (2).

### FFI principle verification

`CLAUDE.md` states: *"Every FFI predicate MUST have backward clause definitions.
FFI off → clause resolution takes over."* The audit shows the principle is
**violated for 8 of 56 predicates**. `test:noffi` passes because its
adversarial workload (TODO_0069) doesn't exercise these specific predicates,
not because the clauses exist. Two fix paths:

- **Author the missing clauses.** Viable for `signextend256` and `byte_size256`
  (inductive on byte position / bit shift); labor-intensive but mechanical.
- **Classify as extralogical in Layer C.** Explicit `soundness.kind =
  'metatheoretic'` flag with a mathematical specification (keccak256 for
  `sha3_compute`, 10^k scaling for `fixed_*`, JS string ops for `string_*`)
  rather than clause-equivalence property testing.

Layer-C registration must surface this classification; it is currently implicit.

## 5. Target native representations

| Native | Used by | Bridge functions |
|---|---|---|
| `BigInt` | §3.1–§3.6 (48 preds) | `binToInt` / `intToBin` (`convert.js:17-43`) |
| `Uint32Array` (hashes) | §3.9 arrlit path (5 preds) | `Store.getArrayElements` / `Store.putArray` |
| Term-tree walk over `tn` | §3.9 trie path + bytecode-normalize | `trieNav` / `_trieInsert` / `_trieSet` (`array.js:35-46`, `bytecode-normalize.js`) |
| `Uint8Array` + `Buffer` | §3.10 `sha3_compute` | local byte assembly + `keccak256` |
| JS `string` | §3.8 | `strToHash` / `hashToStr` (`convert.js:51-63`) |

Four native types total. None of them are currently registered through a
uniform mechanism — every FFI predicate owns its own bridge boilerplate.
The Hoare-abstraction shape:

```js
if (!isGround(a) || !isGround(b)) return { success: false, reason: 'mode_mismatch' };
const aInt = binToInt(a), bInt = binToInt(b);       // φ
if (aInt === null || bInt === null) return { success: false, reason: 'conversion_failed' };
const cInt = nativeOp(aInt, bInt);                  // native f_abs
return { success: true, theta: [[c, intToBin(cInt)]] };   // φ⁻¹
```

…appears **≈50 times verbatim** across `arithmetic.js`. Layer-C generalization
collapses this to a single dispatch table; the 50 modules become ~50 rows in a
registry table.

## 6. Linearity classification

Query: does any FFI predicate consume or produce **linear** resources (as
opposed to operating on terms)?

All callers within forward rules prefix FFI predicates with `!`
(persistent), e.g. `!arr_get BC PC OP`, `!plus A B C`, `!to256 C C'`. The FFI
groundness check operates on term hashes, not on the linear fact multiset.

**Result: uniform `linearity: 'persistent-only'`** — no FFI predicate touches
the linear store. This simplifies Layer C Phase 1: all current predicates fit
the "term-under-fact" case from `cc_layer_c.md:60-62`. The novel linearity-check
infrastructure (`ops preserve multiset of bridged facts`) is still required by
Layer C's charter, but **has zero current customers** — it is a
forward-looking gate for future registrations that refine linear data
(e.g. an in-place array mutation predicate).

## 7. Non-obvious observations

1. **`arith-core.js` is proto-registry.** A 70-line pure-BigInt dispatch table
   (`computeArith(pred, args)`) already abstracts arithmetic from the FFI/
   residual-resolver split. Layer C's `ops` map is its structural generalization
   over all four native types.

2. **`binlit-theory.js` is proto-registration.** 139 LOC implement exactly the
   Layer-C shape for one predicate cluster (binlit ↔ i/o/e). The `canRewrite`,
   `rewrite`, and `canonicalize` entry points correspond to Layer C's
   `target.tag` selection and `canonicalize` slot. The existing API is almost
   isomorphic to the Layer-C data model — confirms the extension is
   evolutionary, not invasive.

3. **Overloaded predicates.** `and`, `or`, `not` are defined in both
   `types.ill` (booleans: 4/2/2 clauses) and `bin.ill` (binlit: via `i/o`
   recursion). The FFI always dispatches to binlit semantics. Layer C
   registration must disambiguate by argument shape — concrete domain
   guard needed.

4. **`sha3_compute` is specification-level different from its clause.** Clause
   returns symbolic `sha3 Bytes`; FFI returns concrete keccak256. This is not
   a Hoare-equivalence refinement — it is a *decision procedure* replacing an
   uninterpreted symbol. Layer-C `soundness.kind = 'metatheoretic'` with a
   witness "the FFI implements the chosen interpretation of `sha3`" is honest;
   anything else is hand-waving.

5. **`sstore_gas` returns a *conservative default* for symbolic inputs.**
   Unlike most FFIs which fail on non-ground args, `sstore_gas` returns 5000
   (Gsreset). Layer-C must express "partial isomorphism with a default
   branch" — another shape not yet in the registry design.

6. **`multiModal: true` flag is load-bearing.** `plus`, `arr_set`, `mem_read`,
   `cd_read`, `sstore_gas` declare multi-modal. The Layer-C design currently
   has a single `mode` per op; it must become `modes: Mode[]` to preserve
   existing multi-mode dispatch (or the surrounding pipeline must normalize
   multi-modal into per-mode ops at registration time).

7. **`FFI principle violation under `test:noffi`.** The 8 predicates without
   clause backup will fail silently if `test:noffi` grows to cover them. The
   audit adds a concrete regression target: extend `tools/fuzz-ffi.js` to flag
   FFI→clause divergence on `sstore_gas`, `signextend256`, `byte_size256`,
   `fixed_mul`, `fixed_div`, `string_concat`, `string_length`, `sha3_compute`.

8. **`bytecode-normalize.js` is representation-change-at-load.** 234 LOC of
   EVM-specific state transforms (`code PC V` → `bytecode(arrlit)` →
   `bytecode(trie)`) implemented entirely outside eq-theory. Layer C's
   representation model should accommodate *state-level* representation
   changes (not just term-level), or this logic stays out-of-registry.

9. **`residual-resolver.js` is the third FFI client.** `arith-core.js` is
   shared between FFI and `residual-resolver.js` (compile-time grounding).
   A Layer-C registration must expose its native op for *both* runtime
   dispatch and compile-time residualization. Easy if the native op is a
   pure function; harder for `mem_read` / `sha3_compute` which touch the
   Store.

## 8. Recommendations for Layer C API

Driven by concrete findings above:

- **`modes: Mode[]` not `mode: Mode`** — preserve `multiModal` support (§7.6).
- **`domain` must express numeric bounds**, not just groundness — the
  `not` / `not256` asymmetry (§3.3) shows that "ground + fits in 2^256" is a
  frequently-needed domain.
- **`soundness.kind` must include `'symbolic-interpretation'`** beyond
  Phase 1/2/3 — `sha3_compute` and the fixed-point primitives don't fit any
  of the declared three phases cleanly.
- **`fallbackMode: 'default-value' | 'fail' | 'clause'`** — `sstore_gas`
  returns a conservative default (§7.5); today's FFI flag this ad-hoc.
- **Dual-surface registration** — runtime FFI call and compile-time
  residualization are the same function (§7.9). Registration API must expose
  a single `impl` that both paths can consume.

## 9. Migration-order implication

Order implied by the audit (cheapest-first, soundness-preserving):

1. **Binlit arithmetic (§3.1–§3.2, 14 preds).** Full clause coverage;
   single native type (BigInt); single bridge (`convert.js`). Property-test
   soundness trivial. **Template for Phase 1.**
2. **Bit-level (§3.3, 6 preds).** Same native type. Needs domain-bound
   declaration.
3. **EVM 256-arith (§3.4, 16 preds).** Needs explicit modular-domain
   declaration; flags the 4 clause gaps.
4. **arrlit/trie array (§3.9, 5 preds + 2 trie migrated).** Different native
   (Uint32Array); migration pattern already validated by trie_get/trie_set.
5. **Write-log memory (§3.10, 4 preds).** Includes `sha3_compute` —
   requires the `'symbolic-interpretation'` soundness kind.
6. **Calldata (§3.11, 1 pred).** Similar to write-log but simpler.
7. **Opcode classifiers (§3.6, 3 preds).** Trivial.
8. **Gas policy / multi-modal defaults (§3.5 + `sstore_gas`).** Exercises the
   `fallbackMode` field.
9. **Fixed-point + strings (§3.7–§3.8, 4 preds).** Extralogical — deferred to
   after §1-§8 because they change soundness-witness taxonomy rather than test
   only the API shape.

Step 1 alone (plus) is the end-to-end template called out in TODO_0223
checklist; the audit confirms it is the cheapest first step.

## 10. What this audit does NOT cover

- **Performance delta per predicate.** Needed to justify keeping FFI on each
  specific predicate post-registration. Out of scope for an inventory audit;
  in scope for the migration checkpoint.
- **`test:noffi` workload coverage map.** Which of the 56 predicates are
  exercised by adversarial workloads? Answers the "can we turn FFI off?"
  question at the predicate level. Separate follow-up.
- **Zig / LLVM downstream mapping.** Each cluster's target type informs the
  Zig port but requires Zig-specific typing (u256, arena allocation, etc.)
  not surfaced here.
- **Inter-predicate closure.** E.g., `between` used by `is_push/is_dup/is_swap`
  clauses — is it in turn primitive or derived? A closure audit would trace
  each clause back to base constructors; not required for Layer C design.
