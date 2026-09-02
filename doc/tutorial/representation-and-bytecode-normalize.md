---
title: Representations, Optimizations, and the bytecode-normalize Question
tags:
  - tutorial
  - representation
  - ffi
  - architecture
  - foreground-background
  - hoare-refinement
---

# Representations, Optimizations, and the bytecode-normalize Question

A from-scratch walkthrough for someone who has never opened the codebase. We
build the picture in layers, then come back to the actual decision: where (if
anywhere) does `bytecode-normalize.js` belong in the upcoming representation
registry?

---

## 1. What CALC is

CALC is a **sequent-calculus toolbox**. Think of it as a methodological
framework: a thing that lets you *build* logical calculi, not a single fixed
calculus. The CALC core knows about sequents, rules, derivations, and proof
search in the abstract — it does not commit to any specific logic.

You add a logic on top by writing small declaration files:

- a **`.family` file** — declares the structural family via rules
- a **`.calc` file** — declares the connectives and types of your logic
- a **`.rules` file** — declares the inference rules in sequent notation

CALC reads those declarations and gives you a working prover, parser,
explorer, and execution engine for your logic. Different logics → different
calculi → all built on the same toolbox.

```
┌─────────────────────────────────────────────────────┐
│ user programs   (e.g. a Multisig contract)          │
├─────────────────────────────────────────────────────┤
│ EVM, binary numbers, memory, ...  (programs)        │  ← .ill files in calculus/ill/programs/
├─────────────────────────────────────────────────────┤
│ ILL — one specific calculus       (a logic)         │  ← .calc + .rules + .family
├─────────────────────────────────────────────────────┤
│ CALC core — sequent calculus toolbox  (framework)   │  ← lib/kernel/, lib/calculus/, ...
└─────────────────────────────────────────────────────┘
```

Important: every layer above the core is *optional* and *replaceable*. ILL is
just the calculus we currently build on the toolbox. Another team could build
classical logic, modal logic, or anything else on the same CALC core.

## 2. ILL: one calculus on top of CALC

**Intuitionistic Linear Logic (ILL)** is implemented as a calculus on top of
CALC. It introduces:

- **Linear connectives** like `*` (tensor), `-o` (linear implication)
- A distinction between **linear** facts (used up when consumed) and
  **persistent** facts (reusable knowledge, written `!A`)
- An **LNL family** ("Linear-Non-Linear") that organises the two contexts

So when ILL programs talk about "a state", they mean *a multiset of linear
facts plus a set of persistent ones*. That's an ILL convention. Other
calculi on CALC would have different state notions, or none at all.

## 3. EVM and binary numbers: programs in ILL

Above ILL, we write **programs** (`.ill` files in `calculus/ill/programs/`).
The Ethereum Virtual Machine is one such program. Binary numbers are another.

For example, `calculus/ill/programs/bin.ill` defines:

```
bin: type.
e: bin.
i: bin -> bin.    % "double-plus-one"
o: bin -> bin.    % "double"
plus: (a:bin) -> (b:bin) -> (c:bin) -> type.
plus/z: plus e B B.
plus/o: plus (o A) B C <- ...
plus/i: plus (i A) B C <- ...
```

This is an inductive specification: `plus` is a relation on three
binary-number terms, with three clauses telling the prover how to derive a
proof of it.

**Crucial point**: `bin`, `plus`, `mul`, `lt`, etc. are **not part of ILL**.
They are defined in an ILL program. ILL doesn't know what a number is; it
just knows about linear connectives. The numbers and their arithmetic live
strictly at the **EVM/programs layer**.

## 4. Foreground and background

This is the conceptual frame on which everything else hangs.

The **foreground** is the logical truth. Anything in the foreground is
justified by the rules of the calculus and the clauses of the program.
Foreground reasoning is reducible to "I have these rules, I applied them, the
proof checks." Nothing outside the rule system is allowed.

The **background** is optimization. The engine is allowed to do *anything*
behind the scenes — replace a slow recursion with a fast JS function, store a
list as a tree, hash terms for O(1) equality — *as long as the result agrees
with the foreground*. The foreground is the spec; the background is the
implementation.

A program author should be able to think only about the foreground. The
background is invisible if it works correctly. If it doesn't, that's a bug in
the optimization, not in the spec.

## 5. The Hoare 1972 idea: the contract a background must satisfy

C. A. R. Hoare gave the rule for swapping representations soundly. You have
two functions:

- **φ**: optimized (concrete) → logical (abstract). "Decode."
- **φ⁻¹**: logical → optimized. "Encode."

…and the obligation, for every operation `f` you want to optimize:

```
φ(f_optimized(c))  =  f_logical(φ(c))
```

In words: "compute optimally, then decode" gives the same answer as "decode,
then compute logically". This is **soundness of data refinement**.

This is exactly what FFI does in CALC. FFI is the **background**; clauses are
the **foreground**.

Concrete example. The foreground says (in `bin.ill`):

```
plus/z: plus e B B.
plus/o: plus (o A) B C <- ...
```

The background says (in `calculus/ill/lib/ffi/arithmetic.js`):

```js
function plus([a, b, c]) {
  return { theta: [[c, intToBin(binToInt(a) + binToInt(b))]] };
}
```

The Hoare obligation: for every binary numeral `a`, `b`, structural `plus(a,
b, c)` succeeds with the same `c` as `binToInt(a) + binToInt(b)` then encoded
back. **It does**, by induction on the bit structure. So FFI `plus` is a
sound background for foreground `plus`.

If you turn FFI off (`useFFI: false`), the engine falls back to the
foreground. The answer is the same; only the speed changes. That property —
"FFI off and FFI on give equal results" — is the entire reason fuzz-ffi.js
exists.

## 6. Today: three Hoare-style registries (the user's question, confirmed)

You asked: "currently the binary-number arithmetic in FFI is done in three
different places — eq-theory.js, ffi/index.js, arith-core.js. All do the same
thing and will be unified in TODO_0223?"

**Yes — this is correct.** All three implement Hoare-style data refinement
for the same domain (EVM-layer binary arithmetic). They differ only in *when*
they hit:

| File | What it swaps | When it runs |
|---|---|---|
| `lib/kernel/eq-theory.js` | one term ↔ another (`binlit(5n)` ↔ `i(o(i(e)))`) | at unification time, every step |
| `calculus/ill/lib/ffi/index.js` | a predicate goal → a JS function (`plus`, `mul`, ...) | at goal-proving time, every step |
| `calculus/ill/lib/ffi/arith-core.js` | shared BigInt core used by FFI + residual resolver | runtime + compile-time |

They share φ/φ⁻¹ logic (in `convert.js`), but each registers itself
separately, with its own API. Adding a new representation means touching all
three. **TODO_0223 (Layer C)** is the project to turn them into a single
registration: declare the representation once, all three subsystems use it.

One note on layering. The path `calculus/ill/lib/ffi/` is slightly misleading.
Conceptually the FFI for binary arithmetic optimises EVM/program-layer
predicates (`plus`, `mul`, etc. defined in `bin.ill`), not ILL primitives. So
the FFI is **EVM-layer optimization** even though the directory is named
`ill/ffi/`. This is a path/naming issue; the architectural placement is right.
> can we rework this layering/path? first do a universal api, then introducing files NEXT to their ill definitions - e.g. bin.ill.ffi.js (alternatively bin.ffi.js) which lives next to bin.ill and is the ffi definition for predicates defined in bin.ill. Similarly distribute all ffi definitions (or layered optimizations) for that matter NEXT to their definitions. e.g. taking them out of lib/engine and putting them back into calculus/ill where they belong - as the author of calculus/ill is responsible to write those optimizations (ffi and others) while writing the calculus itself. the role of the engine should just be to 1. provide an api to write those and 2. aggregate and orchestrate all of them.

## 7. What `bytecode-normalize.js` actually does — step by step

Now we can finally get to the bytecode-normalize file.

### Step 0 — what the data looks like at the start

When you load an Ethereum contract into CALC, you start from a hex string
like:

```
0x608060405260043610610033...
```

`tools/bytecode-to-ill.js` turns that into a CALC fact. There are **two** output formats:

**Default (modern):** one single fact holding a hex literal. Look at
`calculus/ill/programs/multisig_nocall_solc_code.ill` — line 4 is literally:

```
bytecode 0x608060405260043610610033... *
```

That's *one linear fact*. The hex literal becomes a single term; the hex
itself is recognised by the parser and stored as an `arrlit` (a JS-native
`Uint32Array` of byte hashes). After loading: linear context contains the one
fact `bytecode(arrlit(...))`, and that's it for the bytecode.

**Legacy:** `--legacy` mode emits one tiny fact per byte:

```
code 0   0x60 *
code 1   0x80 *
code 2   0x60 *
... (~1024 lines)
```

This is the historical format — kept only for backward compatibility with old
test files.

> we don't need legacy stuff. lets remove that in favor of simpler, more minimal code so we don't need to maintain different implementations and reduce complexity.

### Step 1 — `codeToArrlit` (legacy compat shim)

If the program arrived in the legacy multi-fact form, this function:

1. Walks the linear context, collecting every `code PC V` fact.
2. Builds a single `Uint32Array` indexed by PC, with `V` at each slot.
3. Removes all the old `code PC V` linear facts.
4. Adds one new `bytecode(arrlit)` linear fact.

Many linear facts in → one linear fact out. **This is the only state-shaped
step in the whole file**, and it exists only to handle the legacy format. Any
modern program already arrives as a single `bytecode 0x...` fact.

### Step 2 — `bytesToSemantic` (term-level normalization)

After step 1, the linear context has one fact: `bytecode(arrlit(byte0, byte1,
..., byteN))`. Each slot is a single byte (0..255).

But EVM has multi-byte instructions: `PUSH3 0xAA 0xBB 0xCC` is *one*
instruction occupying *four* slots — opcode `0x62` (= PUSH3) followed by
three immediate bytes. After execution `PUSH3` pushes the value `0xAABBCC`
onto the stack, not three separate values.

`bytesToSemantic` walks the array and rewrites it: at PUSH positions, it
absorbs the next n bytes into one combined value. So:

```
before: [ 0x62, 0xAA, 0xBB, 0xCC, 0x01, ... ]   (byte-level)
after:  [ 0x62, 0xAABBCC, 0,  0,  0x01, ... ]   (semantic-level)
```

Same length, same opcode positions, but PUSH immediates are now single
combined values. The slots in between are zeroed out (they're never read in
correct execution; PC always advances past them).

Crucially: this is a **term-level** transformation. The number of facts in
the state doesn't change. One `bytecode(arrlit)` fact in → one
`bytecode(arrlit)` fact out, with the inner term rewritten.

### Step 3 — `bytecodeToTrie` (term-level, on demand)

After step 2 we have `bytecode(arrlit(...))`. The arrlit is a JS-native
array — fast for FFI lookups (`arr_get` returns in O(1)) but **opaque to the
foreground**. Inductive ILL clauses cannot pattern-match on a Uint32Array;
they only understand constructors like `tn(left, right)` or `atom(x)`.

So if you turn FFI off (`useFFI: false`), the engine cannot look up bytes by
PC anymore — there are no clauses for `arr_get` over a JS-native array, only
for `arr_get` over a logical structure.

`bytecodeToTrie` solves this by converting `arrlit` → `trie` (a balanced
radix tree built from constructors `tn` and `atom`). Same data, different
shape; now inductive `arr_get` clauses can recurse into it.

This conversion is **lazy**: it only happens when the engine enters noFFI
mode. The default fast path keeps the arrlit and uses FFI lookup.

This is the classic foreground/background pattern:

| Path | Representation | When it runs |
|---|---|---|
| Foreground (logic, noFFI) | `trie` (built from constructors) | when proving without FFI; clause resolution recurses |
| Background (optimization, FFI) | `arrlit` (Uint32Array) | default fast path; FFI handler is O(1) |

### Why a trie and not just an array? (your question)

The user asked: "isn't an array O(1) lookup, vs O(log n) for a tree? Why
build a tree?"

**The trie is not for performance — it's for foreground compatibility.**

In FFI mode (default), we *do* use the array (the arrlit). FFI `arr_get` is
O(1) over the Uint32Array. That's the fastest path and it's the one that
runs in production.

The trie exists for the *foreground* path. When FFI is off, the engine has
to use only the rules of the logic — and the rules of the logic don't know
about JS-native arrays. They only know about ILL terms built from declared
constructors. So we project the array into a constructor tree
(`tn(left, right)` plus `atom(byte)` leaves) that inductive clauses can walk.
That walk is O(log n), yes — but it's the *only* legal foreground path. We
need it to exist for anyone who wants to prove a property without trusting
FFI, and for adversarial soundness tests (`test:noffi`).

So your intuition was right: in the actual hot path we use the array. The
tree is the logical mirror of the array, used only when the prover is
forbidden from looking at JS-native data.

## 8. Term vs state vs cardinality — the real distinction

Now we can give a precise vocabulary.

A **term-level** refinement preserves the *structure* of the linear/persistent
context. It rewrites the data inside one fact. The number of facts is
unchanged. Examples:

- `binlit(5n)` ↔ `i(o(i(e)))` — same fact, different term inside.
- `arrlit` ↔ `trie` — same fact `bytecode(...)`, different inner term.
- byte-level arrlit ↔ semantic-level arrlit — same fact, different inner
  term.

A **state-level** refinement *changes the cardinality* of the context. It
takes N facts and produces M ≠ N. Example:

- 1024 `code PC V` linear facts → 1 `bytecode(arrlit)` linear fact.

That's the only true state-level refinement currently in the codebase.

Notice that *after* the state-level step, all subsequent processing is
term-level, because the data is then living inside one fact. So
bytecode-normalize.js is really one state-level shim (legacy)
followed by two term-level normalizations (current).

You also asked: "isn't the code already an array-like term, so shouldn't it
be a term?" **You are correct for modern programs.** The `bytecode 0x...`
single-fact form *is* a term, the moment it's parsed. The state-level step
only fires on legacy input. In the modern pipeline, bytecode-normalize.js is
essentially a sequence of term-level transformations on one `bytecode(...)`
fact.

## 9. The actual decision: scope of bytecode-normalize.js in Layer C

We can now state the decision crisply.

The file does three things:

1. `codeToArrlit` — **state-level**, **legacy compatibility shim**. Cardinality
   change: many `code PC V` → one `bytecode(arrlit)`. Only fires on `--legacy`
   inputs.
2. `bytesToSemantic` — **term-level**. Inner-term rewrite of one fact.
   Byte-level array → semantic-level array.
3. `bytecodeToTrie` — **term-level**. Inner-term rewrite of one fact. arrlit
   → trie. Only fires when entering noFFI mode.

(2) and (3) fit term-level Layer C with no fuss. They are exactly the same
shape as `binlit ↔ structural`: a registered representation, a φ/φ⁻¹ on
inner terms, an obligation that lookups agree.

(1) is the only piece that doesn't fit. It is genuinely cardinality-changing
and runs at load-time. **But it is also legacy** — the modern input pipeline
never produces multi-fact code; the `--legacy` flag is for old test files
only.

This reframes the whole decision tree.

### Option A — In-registry, term-level only

Migrate (2) and (3) into Layer C as ordinary term-level registrations. Leave
(1) as a one-off legacy compat function in the loader, documented as such,
explicitly out of registry scope. If the legacy format is ever retired,
delete (1) entirely; no Layer C change needed.

This is the cleanest answer **given what the file actually does today**.
Layer C stays term-level, simple, single-purpose. The state-shaped code
becomes a legacy footnote, not an architectural axis.

### Option B — In-registry with a state-level peer

Extend Layer C to have a "state-level / cardinality-changing" registration
shape, so that even `codeToArrlit` becomes a registration. Generalises Layer
C to handle the state axis as a first-class peer.

The cost: every reader of the registry now has to understand the state axis
even though there's exactly one customer (a legacy compat shim that may go
away). The benefit only materialises if a second state-level transform shows
up later. We do not currently have one in sight.

### Option C — Spin out a sibling todo for state-level

Open a separate todo "State-level representation refinement" for any future
cardinality-changing transforms. Defer until a real second customer appears.
For now, treat (1) as an exclusion (same as Option A's plan for it).

The difference from A is mostly intent: C says "we acknowledge this is a gap
and reserve a place to fix it later"; A says "the legacy form is going away
anyway, no need to design for it." If the legacy multi-fact format genuinely
is being retired, A is honest. If we expect to introduce more state-level
transforms (e.g. memory consolidation, calldata normalization), C is honest.

### Quality criterion the user introduced

> Ideally generated from the logic entirely, without us needing to write
> native code, because [the framework] recognises [the representation as]
> being close to native structures.

This is a **TODO_0184 (Layer A — recognition)** concern, not a Layer C
concern. Layer C is the registry; Layer A is the synthesizer that *fills*
the registry by analysing clauses and recognising patterns.

For (2) — `bytesToSemantic` — Layer A could in principle recognise the EVM
semantics from PUSH-opcode rules in `evm.ill` and synthesize the
normalization, but this is far from trivial. For now it is hand-coded.

For (3) — `bytecodeToTrie` — Layer A could plausibly recognise the
arrlit↔trie equivalence as a generic array-indexing optimization. A
worthwhile target for Layer A's first cluster (`arr_get`, `arr_set`, ...).

Either way, Layer C is the registry that Layer A populates. The two
collaborate: A generates entries, C dispatches them. Hand-written entries
sit alongside synthesized ones.

## 10. Recommendation

**Option A**, with the following concrete actions in TODO_0223 and
ffi-audit.md:

1. Document the foreground/background distinction explicitly in the
   architecture doc. (It is the conceptual anchor of Layer C — without it,
   "what FFI is for" is fuzzy.)
2. State that Layer C is **term-level, run-time-or-compile-time**. State-level
   transforms (cardinality changes) are out of scope for Layer C.
3. Note `codeToArrlit` as a **legacy compat function** in the loader, with
   the intent that it disappears when the multi-fact code format is retired.
4. Plan to migrate `bytesToSemantic` and `bytecodeToTrie` into Layer C as
   term-level registrations during the array-cluster migration phase
   (§3.9 of the audit).

If a second state-level transform appears later (memory normalization,
calldata consolidation, etc.), promote to Option C and open a sibling todo
for state-level refinement at that moment. Until then, the YAGNI answer is
"term-level only, with one legacy shim outside the registry."

The reason this differs from my earlier recommendation: I had not realised
that the modern input format is already a single `bytecode(arrlit)` term and
that `codeToArrlit` is a legacy shim. With that fact, the bulk of
bytecode-normalize.js is term-level work that fits Layer C natively, and the
state-level worry collapses to a deprecation question.

---

## Appendix — concept index

- **CALC core** — `lib/kernel/`, `lib/calculus/`, `lib/parser/`, `lib/prover/`,
  `lib/engine/` (the generic parts). Sequent calculus toolbox. Doesn't know
  about ILL.
- **Family** — declares the structural framework of a calculus (e.g.
  `lnl.family` for ILL's linear/persistent split). Family files live next to
  `.calc` files.
- **Calculus** — `.calc` (connectives, types) + `.rules` (inference rules).
  ILL is one calculus.
- **Program** — `.ill` files in `calculus/ill/programs/`. EVM is a program.
  `bin.ill` is a program. User contracts (Multisig) are programs.
- **Foreground** — anything justified by the rules. Pure logic. The spec.
- **Background** — optimizations. Must satisfy a Hoare obligation against
  the foreground. The implementation.
- **Hoare refinement (1972)** — the discipline for swapping representations
  soundly: φ, φ⁻¹, and a homomorphism law. Every FFI predicate is one of
  these.
- **FFI** — the registered background optimizations for EVM-layer predicates
  (binary arithmetic, memory, opcodes, ...). Lives in `calculus/ill/lib/ffi/`,
  even though conceptually it belongs to the EVM layer.
- **Term-level refinement** — preserves the cardinality of the linear /
  persistent context; rewrites the data inside one fact.
- **State-level refinement** — changes the cardinality; many facts → one,
  or vice versa. Currently exactly one instance: `codeToArrlit` (legacy).
- **Layer C (TODO_0223)** — the unified registry of term-level Hoare
  refinements. Will subsume eq-theory.js + ffi/index.js + arith-core.js.
- **Layer A (TODO_0184)** — the synthesizer that *recognises* representations
  in clauses and fills Layer C automatically. Aspirational; not implemented.
