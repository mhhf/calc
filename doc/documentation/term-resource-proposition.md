# Terms, Resources, and Propositions in CALC

Design principle for choosing representation in ILL.

## Three categories

| Category | ILL encoding | What it is | Example |
|---|---|---|---|
| **Term** | constructor (`→ bin`) | An object — what something IS | `write(0x00, 0xFF, M)`, `sha3(bytes)`, `5` |
| **Resource** | linear fact (`→ type`, no `!`) | Something you POSSESS, exactly once | `storage KEY VAL`, `gas N`, `mem M` |
| **Proposition** | persistent fact (`→ type`, `!`) | Something you KNOW, always available | `!plus 3 4 7`, `!gt X Y 0 1` |

**Terms** are inert — they don't compute, they just exist. They're nouns.
**Resources** have multiplicity — consumed and produced by forward rules.
**Propositions** have truth values — proved by backward chaining (FFI + clauses).

## Relationships

```
backward predicate: Term → Proposition
    "derives knowledge FROM structure"
    mem_read(write(0x00,V,M), 0x00) = V

forward rule: Resource × Proposition → Resource
    "transforms possessions using knowledge"
    mem M * stack [V,A|R] * !mem_expand ... → mem write(A,V,M) * stack R

constructor: Term × Term → Term
    "builds objects from objects"
    write(addr, val, old_mem) → new memory term
```

## Decision principle

> **Terms encode what something IS.**
> **Propositions encode what you KNOW about it.**
> **Resources encode what you POSSESS.**

The test: *"Can I write down WHAT this object IS?"*

- Memory after MSTORE 0x00 0xFF: "It IS `write(0x00, 0xFF, M)`." → Term.
- Calldata for transfer(addr,uint256): "It IS `sconcat(4, sel, sconcat(32, ?To, sconcat(32, ?Amount, ε)))`." → Term.
- ?To is less than 2^160: "I KNOW that." → Proposition: `!lt ?To MAX 0 1`.

## When to use each

| Situation | Encoding | Reason |
|---|---|---|
| Define an object at construction time | Term (constructor) | You know what it IS |
| Value must compose with other values (stack, memory arg, constructor arg) | Term (constructor) | Must be a single `bin` value |
| Learn/derive facts about existing objects | Proposition (persistent) | Knowledge, not identity |
| Possess something that changes via consume/produce | Resource (linear fact) | Multiplicity matters |

## Applications

| Domain | Encoding | Justification |
|---|---|---|
| Memory state | Term in resource: `mem write(addr,val,M)` | Can define what memory IS after each MSTORE |
| Storage entries | Resources: `storage K V` | Per-key possession, per-key mutation |
| Calldata structure | Term in proposition: `!calldata sconcat(...)` | Can define what calldata IS at init |
| Comparison result | Term: `eq_expr(X,Y)` | Must live on stack |
| Hash | Term: `sha3(bytes)` | Must live on stack/in storage keys |
| Arithmetic | Proposition: `!plus A B C` | Derived knowledge about terms |
| Constraints | Proposition: `!lt ?X 100 0 1` | Learned about metavar |

## Metadata about terms

Content addressing forces the placement: a term IS its hash, so anything
stored inside a term changes its identity (two programs differing only in a
comment would be different hashes — breaking O(1) equality, canonical forms,
and the eq-theory bridge; same argument as THY_0020's extrinsic-sorts result).
Three lawful places for metadata, chosen by one test — *does it change what
you can DO with the term, is it something you KNOW, or is it for humans only?*

| Metadata kind | Place | Mechanism |
|---|---|---|
| Affects typing/execution (grade, stamp, sort, principal) | In the type | `bang(g,A)`, `monad(g,A)`, `A@t`, refinement sorts (TODO_0157) |
| Knowledge about the term (version, author, implements-spec) | Persistent proposition over the hash | `!version T V`, `!impl Spec V T` |
| Inert, human-facing (comment, doc, name) | Sidecar keyed by hash, outside the logic | Unison/Lean-docstring model (needs stable identity, TODO_0271) |

Corollaries: the hash is the intrinsic version of an implementation; human
version names are propositions or sidecar entries, never term fields. Metadata
beside a *linear* resource must be persistent (`A ⊗ !M`), baked into the
constructor, or a stamp — never a loose linear sibling fact (desyncs on
consumption). Linear resource instances have no identity in the multiset; to
attach metadata per-instance, widen the constructor, use a fresh-name handle
(`∃x` + facts about `x`), or a stamp.

## Backward predicates derive knowledge FROM terms

`mem_read` takes the write-chain TERM and derives what value is at an address:
```
mem_read/hit:  mem_read (write Addr V Rest) Addr V.
mem_read/miss: mem_read (write W V Rest) R Result <- neq R W <- ... <- mem_read Rest R Result.
mem_read/zero: mem_read empty_mem R 0.
```

This is what backward chaining does best — structural pattern matching on constructor terms. The three-tier cascade (FFI → state lookup → clause resolution) optimizes this.

Same pattern for any navigable term: `cd_read` navigates `sconcat(...)`, `arr_get` navigates arrlit/trie, `notMember` navigates cons-lists.
