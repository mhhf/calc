# The Numeric Tower: Dual Representation and the Mode Contract

How numbers live in CALC/till, and exactly which query modes are decided by
which face. Source of truth for rule authors writing arithmetic premises.

## Dual representation

Every numeral has two faces, kept isomorphic by equational theories
(`lib/kernel/eq-theory.js` cross-tag matching, O(1) dispatch):

| kind | literal (canonical storage) | structural (clause-facing) | theory |
|---|---|---|---|
| natural | `binlit n` | `i`/`o`/`e` chains (LSB-first) | `binlit-theory.js` |
| rational | `ratlit n d` | `rat N D` (N, D bins) | `ratlit-theory.js` |

- **Literals are canonical**: `putRat` normalizes (gcd-reduced, den 1 →
  `binlit`), so content-addressed equality is O(1) and FFI results are
  hash-equal to canonicalized clause derivations.
- **Structural forms are the clause view**: clause heads pattern-match
  constructors (`plus (i M) (i N) (o R)`, `plus (rat A B) V R`). Cross-tag
  matching lets a literal goal argument match a structural head lazily
  (peel one constructor per step) — both directions, both kinds. Mixed
  bin/frac goals work (`plus 3 1/2 R` → `7/2`): bins embed as n/1.
- The v1 value range is **ℚ≥0**: `ratlitTheory.rewrite` refuses negative
  numerators, `rat(N, D)` ranges over bins, and the FFI decoders reject
  negatives (signed STORAGE exists — D14 — but signed semantics wait for
  debt/dual grades).

## One predicate per operation across the tower

`plus/mul/lt/le/eq/neq/eq_bool` are single predicates (TODO_0011 §3
collapse): bin.ill's clauses are the bin instance, rat.ill's `/q` clauses
the instance at the bound, dispatched by matching. The FFI face mirrors this
via `num.*` handlers (`ill/ffi/index.js`): bin fast path first, rational
fallback second — coherent on the overlap by the collapse law. `qsub` and
`qdiv` stay split names (checked vs. saturating monus, field vs. Euclidean —
the coherence law forbids sharing).

## The mode contract (TODO_0273)

"Forward" = all inputs ground, output free. "Solve" = one addend free,
result ground (the residual `H = c ⊖ known`, the fence check built in:
negative ⇒ fail).

| query | clause face | FFI face |
|---|---|---|
| `plus a b R` forward (ℕ, ℚ, mixed) | complete | complete (`num.plus`) |
| `plus H b c` / `plus a H c` solve (ℕ, ℚ) | **sound only** — carry cases can hit the depth bound (`plus/s4` orders `plus M N Q` before `inc Q R`, two free vars in the recursive subgoal) | **complete** — success ⟺ c ≥ known, H = c − known (`qplus` solve modes; bin args coerce n/1, den-1 results re-canonicalize to binlit) |
| `qsub a b R` (ℕ, ℚ) | complete | complete (checked: fails on negative) |
| comparisons (ℕ, ℚ, mixed) | complete | complete |

Per the FFI principle, the clause face is the semantics and is everywhere
SOUND; the FFI face is the terminating decision procedure. The solve-mode
search incompleteness of the clause face is a moding property of the bin
carry clause, not a semantic gap — the proofs exist, SLD may not find them
under a depth bound. The grade algebra's residual `⊖`
(`calculus/till/calculus-config.js`) is the O(1) third face; all three are
fuzzed for agreement in `tools/fuzz-till.js` (definedness and value,
including must-fail negatives).

## Where grades meet the tower

Forward .till rules do arithmetic in-logic: `after (Q + D)` lowers to a
persistent `!plus Q D Q$0` goal (`convert.js:desugarTimed`) — forward mode,
complete on both faces. Backward sequent rules state THEORY PREMISES
(TODO_0273): `monad_l` carries `<- !qsub F E H` — the partial residual `⊖`
as a derivability statement, discharged by the engine backchainer with the
FFI face as O(1) fast path (out-of-fence ⇒ underivable ⇒ rule
inapplicable; see `doc/theory/0022_fenced-grade-algebras.md`). The grade
algebra's `residual` remains only as the timed scheduler's runtime
bookkeeping face. Rule authors write `qsub` (forward mode, complete
everywhere), not solve-mode `plus`.
