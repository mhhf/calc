---
title: "The Content-Addressed Store as a SNAX Concretization: A Split Verdict"
created: 2026-09-08
modified: 2026-09-08
summary: "TODO_0309 P4 worked the conjecture 'calc's content-addressed store is a legal non-standard SNAX concretization with (a·p)★ = hash of the subterm at path p' against SNAX's actual concretization laws (DeYoung–Pfenning MFPS 2022): L1 local calculability of projected addresses and L2 projection-distinctness (aπ₁·p₁ ≠ aπ₂·p₂). Verdict: PARTIALLY FALSIFIED, with a precise repair. L2 fails syntactically (equal subtrees alias to one hash) but its purpose survives as L2′ — colliding addresses carry equal storables, and write conflicts are IMPOSSIBLE by construction since the address determines the content (hash-consing legality, stated against SNAX's laws). The deeper, temporal failure is unrepairable: a content address cannot name an ALLOCATED-BUT-UNWRITTEN cell — the parent's address is a function of its children's values, so cell(a,□) for composite a has no store representation and SNAX's futures protocol (allocate, project, write components concurrently, block on reads) cannot be concretized. What survives is a split: calc realizes SNAX by FACTORING addresses from values — machine.sax's symbolic destination terms (d, p1 d, p2 d) are a legal SNAX address algebra (the free term algebra: L1 trivial, L2 by constructor injectivity), the store concretizes STORABLES, and !cell d V is the graph pairing them. The original conjecture conflated the two roles; the factored form is the theorem."
tags: [sax, destination-passing, content-addressed-store, data-layout, snax, multiset-rewriting, engine-metatheory]
category: "Engine metatheory"
unique_contribution: "Three results not in the MFPS 2022 paper or prior CALC docs: (1) the falsification analysis — hash-consing violates SNAX's L2 projection-distinctness exactly on equal subtrees, but satisfies the weakened L2′ (aliases carry equal storables) under which the one-writer discipline is not merely preserved but VACUOUSLY enforced: in a content-addressed store a write conflict is unrepresentable because the address is a function of the written value — the store is 'write-once' in a stronger sense than SNAX demands; (2) the temporal no-go — content addressing inverts SNAX's address-flow direction (SNAX: addresses flow top-down at allocation, components written later by independent processes; store: addresses flow bottom-up from written values), so the futures fragment (cell(a,□), read-blocking) has NO concretization into content addresses, and this is a structural impossibility, not an implementation gap; (3) the factorization theorem — the destination TERM algebra (projections as free constructors) is a legal SNAX address algebra satisfying L1+L2 on the nose, and calc's machine.sax realizes SNAX precisely as (free symbolic addresses) × (content-addressed storables) linked by the write-once cell predicate — identifying WHERE in the system each SNAX law lands, and explaining post-hoc why the sax-native machine had to introduce destination terms rather than use store hashes as destinations."
references:
  - "DeYoung–Pfenning, Data Layout from a Type-Theoretic Perspective (MFPS 2022, ENTICS; extended: arXiv:2212.06321) — §3.2: 'SNAX requires only that aπ₁ and aπ₂ are calculable from a : A₁ × A₂ and that aπ₁·p₁ ≠ aπ₂·p₂ for all projections p₁ and p₂'; the sample concretization (a·π₂)★ = a★ + |A₁|; the ↓A pointer type; well-formedness a ⋡ b ('two writers') and the SNIP⁺ no-allocation rule"
  - "TODO_0309 P4 (this deliverable; falsification declared acceptable in the plan); P1 (machine.sax — the factored realization this doc explains); TODO_0261 avenue E (subsumed)"
  - "THY_0036 (the confluence certificate's write-once discipline is the operational shadow of the factored form: symbolic destinations keyed, content values in cells)"
  - "doc/documentation/content-addressed-store.md (the store's actual contract: put idempotence, O(1) equality)"
  - "tests/engine/store-snax.test.js (the executable pins: L2 aliasing exhibit, conflict impossibility, free-algebra distinctness)"
  - "Hash-consing folklore (Ershov 1958; Filliâtre–Conchon 2006): sharing immutable values is sound — here made precise as which SNAX law it violates and which weakening restores it"
---

# The Content-Addressed Store as a SNAX Concretization: A Split Verdict

## 1. The conjecture and the actual laws

The conjecture (TODO_0261 avenue E → 0309 P4): the content-addressed
store is a legal non-standard SNAX concretization with

    (a·p)★  =  the hash of the subterm at path p under a.

SNAX (MFPS 2022) is deliberately agnostic about concretizations — the
paper's sample `(a·π₂)★ = a★ + |A₁|` is "not the only possible" one —
but it is NOT lawless. The stated requirements:

- **L1 (calculability).** `aπ₁` and `aπ₂` are calculable from
  `a : A₁ × A₂`.
- **L2 (projection-distinctness).** `aπ₁·p₁ ≠ aπ₂·p₂` for ALL
  projections p₁, p₂ — the component subtrees occupy disjoint address
  sets.

Behind L2 stands the one-writer discipline: typing presupposes `a ⋡ b`
for readable b ("or there would incorrectly be two writers to address
a"), and the operational semantics allocates `cell(a, □)` — an
address that EXISTS before it is written, so `read` can block on it
(the futures protocol; SNIP⁺ pointedly does NOT allocate, because an
eligible address names a location inside an existing block).

## 2. L2 falsified — and the weakening that survives

Take `a : A × A` holding the pair ⟨v, v⟩ with equal components. Under
the conjectured map, `(a·π₁)★ = (a·π₂)★ = hash(v)`: **aliasing, in
direct violation of L2**, and not in a corner case — structure sharing
on equal subtrees is the store's entire point (one hash per value,
O(1) equality).

But look at what L2 is FOR. Its purpose is that no two processes write
one address. In the store, the address IS a function of the written
content: `hash(v)` can only ever be "written" with v. Two writers of
the same address necessarily write the same storable, and `Store.put`
is idempotent — the second write is not merely harmless, it is
LITERALLY THE SAME EVENT. So the store satisfies:

- **L2′.** Colliding projected addresses carry equal storables, and
  write conflicts are unrepresentable.

Under L2′ the one-writer discipline is enforced VACUOUSLY — a stronger
guarantee than SNAX asks for, obtained by giving up address/value
separation. This is the folklore hash-consing legality argument, here
made precise as: which SNAX law breaks (L2), on which inputs (equal
subtrees), and which weakening restores soundness for the read-only
fragment (L2′ suffices for every SAX read rule — reads never conflict
and never mutate).

## 3. The temporal no-go: content addresses cannot name futures

The deeper failure is directional and unrepairable. In SNAX, addresses
flow TOP-DOWN: `cut` allocates a block, `×A` gives the writer
`aπ₁ : A₁, aπ₂ : A₂` — the component addresses exist and are handed
to INDEPENDENT processes BEFORE anything is written; readers block on
`cell(a, □)`. In the store, addresses flow BOTTOM-UP: a composite's
hash is computed FROM its children's hashes. Consequences:

- `cell(a, □)` has no store representation for composite a — the
  address of an unwritten pair does not exist yet.
- The concurrent protocol (allocate, fork writers, block reads) cannot
  be concretized: there is nothing to hand the component writers.
- Only BOTTOM-UP evaluation orders — equivalently, final
  configurations and value construction — are concretizable.

This is a structural impossibility, not an implementation gap: any
address scheme where the address is a function of the value cannot
name the value's future. (It is the same extensionality that made L2
fail — one cause, two symptoms.)

## 4. The factorization theorem: what calc actually does

machine.sax already embodies the repair, and the analysis explains
why it HAD to. The machine's destinations are SYMBOLIC TERMS —
`d`, `p1 D`, `p2 D` — with projections as free constructors, and the
write-once cell predicate `!cell D V` pairs a destination with a
content-addressed value. Check the laws against the TERM algebra:

- **L1**: `p1 D` is calculable from D — it is a constructor
  application, locally calculable in the strictest sense (no
  dereference, no type info needed).
- **L2**: `p1 D · p⃗ ≠ p2 D · p⃗′` — free-algebra constructor
  injectivity; distinctness holds ON THE NOSE, for all extensions.
- `hole D` REALIZES `cell(a, □)` (the machine's fact playing the
  paper's allocated-unwritten role under the factorization map):
  symbolic addresses exist before their values — the futures protocol
  concretizes, reads block (in the committed engine: rules wait for
  the cell fact).

So the correct statement is a factorization:

> **calc realizes SNAX as (free symbolic address algebra) ×
> (content-addressed storable universe), linked by `!cell`.** The
> destination terms carry L1+L2 and the temporal protocol; the store
> carries storables with L2′-sharing; neither component alone is a
> legal concretization of the whole theory — the conjecture conflated
> the two roles.

The confluence certificate (THY_0036) is the operational shadow of the
same split: its discipline keys LINEAR facts by destination terms
(the address side) while single-writer cells hold values (the storable
side) — the D2/D4 conditions are statements about the address algebra,
never about hashes.

## 5. What survives of the original conjecture

Restricted to FINAL configurations (all cells written), the map
`(D)★ = hash(value at D)` is a well-defined homomorphism from the
destination graph to the store, and it is exactly the store's sharing
quotient: distinct destinations with equal values collapse. In that
restricted sense the store is a concretization "of values" — with
maximal indirection (every child link is a pointer; SNAX's ↓A
placed everywhere) and maximal sharing (beyond anything SNAX's
per-block address arithmetic can express). Adjacency-dependent
reasoning is lost, but adjacency was never a SNAX law — only the
sample concretization used it.

## 6. Executable pins

tests/engine/store-snax.test.js: (i) the L2 aliasing exhibit — a pair
of equal subterms has hash-equal projected children; (ii) conflict
impossibility — put is idempotent, address determines content;
(iii) free-algebra distinctness — `p1 d ≠ p2 d` and all their
extensions as terms; (iv) bottom-up determinism — a composite's hash
is a function of its children's hashes (same children ⇒ same parent).
