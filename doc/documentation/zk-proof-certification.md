# ZK Proof Certification

CALC proofs can be verified in zero knowledge using STARK proofs. The ZK subsystem takes a proof term (from the backward prover or forward engine) and produces a cryptographic proof that the term is valid — without revealing the proof itself.

## What It Is

Two verification models:
- **Tree path**: a STARK proof that `checkTerm(proofTerm, sequent)` succeeds — full ILL derivation verification.
- **Flat path**: a STARK proof that a forward execution trace conserves resources and uses valid rules — no proof term, just resource accounting.

Both produce a ~200KB STARK proof verifiable in milliseconds. The prover (JS) generates a witness trace, the verifier (Rust) checks it via polynomial constraints over BabyBear (31-bit prime field).

## When It's Useful

- **On-chain verification**: post a STARK proof (or Groth16 wrap, ~260 bytes) that a computation followed declared rules
- **Trustless certification**: a third party can verify a proof without trusting the prover software
- **EVM symbolic execution**: the 279-step `multisig_nocall_solc` benchmark produces a verifiable certificate that the execution trace is valid

## Architecture

Two verification paths coexist, selected by a `format` field in the witness JSON:

```
                  ┌─── Tree path ──────────────────────────┐
                  │  ILL proof term → 13 chips, 7 buses    │
Proof term ──→ JS witness ──→ JSON ──→ Rust STARK prover ──→ proof
                  │  Flat certificate → 5–7 chips, 5 buses │
                  └─── Flat path ──────────────────────────┘
```

**Tree path**: verifies full ILL derivation trees. Handles backward proofs, forward proofs, mixed. 13 chips across 7 buses verify obligation threading, formula decomposition, linear resource tracking, rule membership, and substitution correctness.

**Flat path**: verifies forward execution traces only. Each step records consumed/produced facts + rule identity. 5–7 chips across 5 buses verify resource conservation, rule membership, formula structure (tensor spine), and substitution correctness for loli matches. 10x fewer rows, 32x smaller witness.

### Technology Stack

| Component | Choice | Why |
|---|---|---|
| STARK toolkit | Plonky3 (v0.4.1) | Most active, BabyBear native |
| Multi-chip framework | OpenVM stark-backend (v1.3.0, audited) | LogUp buses, per-chip AIR |
| Field | BabyBear (31-bit, quartic ext ~2^124) | Standard for Plonky3 |
| Language | Rust (verifier), JS (witness) | Rust for constraints, JS for existing prover |

## Two Certificate Paths

### Tree-Based (ILL Proof Terms)

Produced by the backward prover, forward engine (via `buildGuidedTerm`), or manual prover. Each proof term node maps to one chip row in DFS pre-order.

**Buses** (7):

| Bus | Type | Tuple | Role |
|---|---|---|---|
| OBLIG_BUS | PermutationCheck | (nonce, type, lax) | Obligation produce/consume |
| CONTEXT_BUS | PermutationCheck | (hash) | Linear resource tracking |
| FORMULA_BUS | Lookup | (hash, tag, child0, child1) | Formula decomposition |
| DISCARD_BUS | Lookup | (nonce) | zero_l discard permits |
| GAMMA_BUS | Lookup | (hash) | Persistent zone membership |
| SUBST_TREE_BUS | PermutationCheck | (subst_id, old_hash, new_hash) | Per-node tree matching |
| FREEVAR_BUS | Lookup | (subst_id, freevar_hash, ground_value) | Freevar consistency |

**Chips** (13 for ILL): InitChip, DupChip, ZeroLChip, DiscardChip, SubstChip (width 15), FreevarRomAir, FormulaRomAir, GammaRomAir, + generic RuleChip instances (one per rule family: tensor_r, loli_l, with_r, oplus_r1, etc.)

**Soundness**: LogUp bus balance enforces multiset equality — every obligation produced is consumed exactly once, every linear resource introduced is consumed exactly once. False positive probability ≤ n/|F_ext| where F_ext ~2^124.

### Flat (Rewriting Certificates)

Produced by the forward engine via `buildRewriteTrace`. Each forward step (rule application) maps to one row. Forward-only — does not apply to backward proofs.

**Buses** (5): CONTEXT_BUS + GAMMA_BUS + FORMULA_BUS + SUBST_TREE_BUS + FREEVAR_BUS.

**Chips** (5–7):

| Chip | Main width | Preprocessed | Role |
|---|---|---|---|
| FlatInitChip | 1 (dummy) | 2 | Send initial linear context to CONTEXT_BUS |
| FlatStepChip | 54 | — | Receive consumed, send produced, verify rule structure + substitution |
| FlatFinalChip | 2 | — | Receive remaining context from CONTEXT_BUS |
| FormulaRomAir | 1 | 5 | Formula decomposition supply for FORMULA_BUS |
| GammaRomAir | 1 | 2 | Persistent clause supply for GAMMA_BUS |
| SubstChip | 15 | — | Per-node loli body substitution verification (SUBST_TREE_BUS) |
| FreevarRomAir | 1 | 3 | Freevar→ground binding supply for FREEVAR_BUS |

FlatStepChip row layout (width 54): `[active, is_loli, ground_loli, consumed_0..5, consumed_active_0..5, produced_0..5, produced_active_0..5, ant_hash, ant_i1..4, cons_hash, cons_i1..4, monad_hash, compiled, ground_ant, ground_cons, subst_id, body_leaf_0..5, body_diff_0..5]`

For compiled rules (`is_loli=0`): ant_hash/cons_hash are right-associated tensor trees matching consumed/produced slots. FORMULA_BUS lookups verify the tensor spine decomposition. GAMMA_BUS verifies rule membership.

For loli matches (`is_loli=1`): ant_hash/cons_hash come from the original loli's Store decomposition (may contain metavariables). Antecedent verification via ground_ant + SUBST_TREE_BUS demand to SubstChip. Body verification via per-leaf SUBST_TREE_BUS demands gated by body_diff columns. Anti-suppression constraint: `(1 - body_diff[i]) * (body_leaf[i] - p[i]) = 0` ensures body_diff can only be 0 when body_leaf equals produced.

The `compiled` column stores `active * (1 - is_loli)` as a trace value to keep max constraint degree at 4 (requiring `log_blowup=2`). Without it, spine boundary constraints would be degree 5 (requiring `log_blowup=3`, doubling LDE memory).

**Inter-derivability**: flat certificates and ILL proof terms are inter-derivable for the forward fragment. `buildGuidedTerm` converts flat→ILL. `buildRewriteTrace` converts ILL→flat (trivially, by extracting consumed/produced per step). See TODO_0084 for the soundness proof.

## Calculus-Agnostic Design

The Rust verifier contains zero ILL-specific code. Everything is derived from the calculus definition at witness generation time:

1. **Tags**: `deriveZkTags(calculus)` assigns integer IDs to connectives from `.calc` definitions
2. **Rule specs**: `deriveZkRuleSpecs(calculus, tags)` maps `.rules` descriptors to `RuleSpec` structs
3. **Witness JSON**: carries `tags` and `rule_specs` — the Rust bridge reads them at runtime

The same compiled Rust binary verifies proofs from any calculus defined in CALC.

## File Structure

### JS (witness generation)

```
lib/zk/
├── witness.js              # Tree-based: generateWitness(term, sequent, opts)
│                           #   deriveZkTags(calculus), deriveZkRuleSpecs(calculus, tags)
└── flat-witness.js         # Flat: generateFlatWitness(trace, sequent, opts)

lib/prover/
├── rewrite-trace.js        # buildRewriteTrace(trace), checkRewriteTrace(delta0, trace)
├── guided-term.js          # buildGuidedTerm(trace, rfTerm) — forward trace → ILL proof term
└── check-term.js           # checkTerm(term, sequent) — proof term type-checker
```

### Rust (STARK verifier)

```
zk/proof-checker/
├── Cargo.toml
├── src/
│   ├── lib.rs              # Re-exports
│   ├── bridge.rs           # JSON → trace matrices → STARK prover
│   │                       #   prove_json() dispatches by format field
│   │                       #   prove_witness() — tree path
│   │                       #   prove_flat_witness() — flat path
│   ├── buses.rs            # 7 bus definitions (OBLIG, CONTEXT, FORMULA, DISCARD, GAMMA, SUBST_TREE, FREEVAR)
│   ├── rule/
│   │   └── mod.rs          # RuleSpec, ColumnLayout, generic RuleChip AIR impl
│   └── chips/
│       ├── init.rs         # InitChip (tree, main 1 + prep 5)
│       ├── dup.rs          # DupChip (additive context copy, width 2)
│       ├── zero_l.rs       # ZeroLChip (ex falso, width 6)
│       ├── discard.rs      # DiscardChip (discard permits, width 3)
│       ├── subst.rs        # SubstChip (freevar bridge, width 15)
│       ├── formula_rom.rs  # FormulaRomAir (formula decomposition, main 1 + prep 5)
│       ├── gamma_rom.rs    # GammaRomAir (persistent clause supply, main 1 + prep 2)
│       ├── freevar_rom.rs  # FreevarRomAir (freevar consistency, main 1 + prep 3)
│       ├── flat_init.rs    # FlatInitChip (flat, main 1 + prep 2)
│       ├── flat_step.rs    # FlatStepChip (flat, width 54)
│       └── flat_final.rs   # FlatFinalChip (flat, width 2)
└── tests/
    ├── common/mod.rs       # Test helpers
    ├── p1f_e2e.rs          # 16 e2e tests (JS fixtures → STARK)
    ├── p2_*.rs             # Generic RuleChip tests (per-rule family)
    └── s1-s5_*.rs          # Infrastructure spike tests
```

### Test fixtures

```
zk/proof-checker/tests/fixtures/
├── identity.json           # A ⊢ A
├── tensor_r.json           # A, B ⊢ A ⊗ B
├── tensor_swap.json        # A ⊗ B ⊢ B ⊗ A
├── loli_r.json             # ⊢ A ⊸ A
├── loli_l.json             # P, P ⊸ Q ⊢ Q
├── with_r.json             # A ⊢ A & A
├── with_l1.json            # A & B ⊢ A
├── oplus_r1.json           # A ⊢ A ⊕ B
├── one_r.json              # ⊢ I
├── one_l.json              # I, A ⊢ A
├── zero_l.json             # 0 ⊢ C
├── bang_dereliction.json   # !A ⊢ A
├── copy.json               # ; A ⊢ A
├── nested_loli_tensor.json # (A⊗B)⊸C, A, B ⊢ C
├── solc_forward.json       # 279-step EVM (tree, 858KB)
└── solc_flat.json          # 279-step EVM (flat, 27KB)
```

## Usage

### Generate a tree-based witness (JS)

```javascript
const { generateWitness, deriveZkTags, deriveZkRuleSpecs } = require('./lib/zk/witness');

const tags = deriveZkTags(calculus);
const ruleSpecs = deriveZkRuleSpecs(calculus, tags);
const witness = generateWitness(proofTerm, sequent, { tags, ruleSpecs });
// witness = { tags, rule_specs, chips, formula_rom, gamma_rom }
```

### Generate a flat witness (JS)

```javascript
const { buildRewriteTrace, checkRewriteTrace } = require('./lib/prover/rewrite-trace');
const { generateFlatWitness } = require('./lib/zk/flat-witness');

const trace = buildRewriteTrace(forwardTrace);
const check = checkRewriteTrace(initialContext, trace);
assert(check.valid);

const witness = generateFlatWitness(trace, sequent, { calculus });
// witness = { format: 'flat', chips: { flat_init, flat_step, flat_final },
//             formula_rom, gamma_rom, tags, constants }
```

### Verify in Rust

```rust
use proof_checker::bridge::prove_json;

let json = std::fs::read_to_string("witness.json").unwrap();
prove_json(&json).expect("STARK verification");
// prove_json dispatches to tree or flat path based on format field
```

### Run tests

```bash
# JS witness tests
npm test -- --grep "zk"

# Rust STARK tests (all 63)
cd zk && cargo test --release

# Just e2e (JS fixtures → STARK)
cd zk && cargo test --release --test p1f_e2e
```

## Benchmarks (279-step EVM symbolic execution)

| Metric | Tree path | Flat path |
|---|---|---|
| Total trace rows | 6,267 | 596 |
| Witness size | 858 KB | 27 KB |
| Chips | 13 | 5 |
| Buses | 5 | 3 |
| STARK proving (release) | 2.56s | 2.81s |
| Rust tests | 63 pass | included above |

Proving time is comparable because STARK fixed overhead (FRI, Poseidon) dominates at these trace sizes. The flat path's advantage is witness compactness and architectural simplicity.

### Scaling budget

Single STARK proof budget: ~4M rows per chip before needing degree tiers or continuations.

| Path | Rows for solc_symbolic | Headroom to 4M |
|---|---|---|
| Tree | 6,267 | ~640x |
| Flat | 596 | ~14,000x |

## Key Data Structures

### RuleSpec (Rust + JSON)

Describes one inference rule's bus interactions declaratively:

```rust
pub struct RuleSpec {
    pub name: String,
    pub tag: Option<u32>,           // connective tag for FORMULA_BUS
    pub arity: u8,                  // children of principal formula
    pub oblig_receive: bool,        // receive from OBLIG_BUS?
    pub premises: Vec<PremiseSpec>, // obligations to produce
    pub ctx_receive: bool,          // receive principal from CONTEXT_BUS?
    pub ctx_sends: Vec<CtxSend>,    // send to CONTEXT_BUS
    pub formula_lookup: bool,       // look up in FORMULA_BUS?
    pub gamma_lookup: bool,         // look up in GAMMA_BUS?
    pub is_identity: bool,          // hash serves both OBLIG and CONTEXT
}
```

The generic `RuleChip` reads this spec and emits polynomial constraints. Column layout is computed automatically — no manual index bookkeeping. Adding a rule = adding a `RuleSpec` value. Adding a calculus = deriving specs from `.rules` descriptors.

### WitnessJson (Rust)

```rust
pub struct WitnessJson {
    pub tags: HashMap<String, u32>,           // connective → tag integer
    pub rule_specs: HashMap<String, RuleSpec>, // rule → chip spec
    pub chips: HashMap<String, Vec<Vec<u32>>>, // chip name → rows
    pub formula_rom: Vec<Vec<u32>>,
    pub gamma_rom: Vec<Vec<u32>>,
}
```

### FlatWitnessJson (Rust)

```rust
pub struct FlatWitnessJson {
    pub format: String,                        // "flat"
    pub chips: HashMap<String, Vec<Vec<u32>>>, // flat_init, flat_step, flat_final
    pub formula_rom: Vec<Vec<u32>>,            // formula decomposition entries
    pub gamma_rom: Vec<Vec<u32>>,              // persistent clause entries
    pub tags: HashMap<String, u32>,            // connective → tag integer
    pub constants: HashMap<String, u32>,       // e.g. { one_hash: ... }
}
```

## Future Extensions

**Degree tiers**: compile the circuit at multiple degrees (2^10, 2^14, 2^18, 2^22). Auto-select the smallest that fits. Same constraints, different padding. Reduces proving time for small proofs.

**Public input binding (3b.2)**: formula ROM, gamma ROM, init sequent, and flat init context are preprocessed columns committed at keygen via Poseidon2. The next step is exposing a public input hash binding the proof to a specific sequent.

**Binary serialization**: replace JSON witness bridge with bincode for faster JS→Rust transfer.

**On-chain verification**: STARK → Groth16 wrap via gnark → Solidity verifier (~270k gas). Same production pipeline as SP1.

**Multimodalities**: flat certificates extend — add zone tag per fact, one CONTEXT_BUS per zone.

**muMALL (fixed points)**: certificate structure unchanged — μ-unfolding happens at match time, not in the rewriting structure.

**Dependent types**: resource accounting is orthogonal to type dependency. FlatStepChip gets wider (type witnesses), but the one-row-per-step structure is the same.

## References

- TODO_0084: full design document with soundness proofs, phase history, and architectural insights
- TODO_0086: zone-agnostic bus architecture (generalizing structural buses beyond ILL's two-zone shape)
- Plonky3: github.com/Plonky3/Plonky3
- OpenVM stark-backend: github.com/openvm-org/stark-backend
- ZKSMT (Luick et al., USENIX Security 2024): IVC for SMT proof checking
