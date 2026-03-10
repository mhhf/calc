# OpenVM Stark Backend: Custom AIR Chips with Plonky3

Source: github.com/openvm-org/stark-backend (v1.3.0, MIT/Apache-2.0)

## 1. Crate Names and Versions

Workspace version: **1.3.0**. All Plonky3 dependencies pinned to **=0.4.1**.

### Cargo.toml dependencies

```toml
[dependencies]
# Core proving backend
openvm-stark-backend = { git = "https://github.com/openvm-org/stark-backend", tag = "v1.3.0" }
# Testing/engine helpers (optional)
openvm-stark-sdk = { git = "https://github.com/openvm-org/stark-backend", tag = "v1.3.0" }

# Plonky3 (pinned, all at =0.4.1)
p3-air = "=0.4.1"
p3-field = "=0.4.1"
p3-matrix = "=0.4.1"
p3-baby-bear = "=0.4.1"
p3-poseidon2 = "=0.4.1"
p3-fri = "=0.4.1"
```

**Note:** These crates are not on crates.io as standalone releases — they are workspace path crates published only from the git repo. Depend via git or by vendoring. The openvm-stark-backend crate re-exports all p3-* crates, so you can reference them as `openvm_stark_backend::p3_air`, etc.

---

## 2. Trait Hierarchy

```
BaseAir<F>
  └─ BaseAirWithPublicValues<F>    num_public_values()
  └─ PartitionedBaseAir<F>        cached_main_widths(), common_main_width()

Air<AB: AirBuilder>
  └─ eval(&self, builder: &mut AB)

Rap<AB: PermutationAirBuilder>    (wraps Air via blanket impl when AB: InteractionBuilder)
  └─ eval(&self, builder: &mut AB)

AnyRap<SC>: Arc<dyn AnyRap<SC>> == AirRef<SC>   (dynamic dispatch for keygen)
```

`Rap` is **not** a supertrait of `Air` — the blanket impl in `interaction/rap.rs` auto-wraps any `Air<AB>` where `AB: InteractionBuilder` into a `Rap<AB>`.

---

## 3. Implementing a Custom AIR Chip

### 3.1 Columns

```rust
use std::mem::size_of;
use std::borrow::Borrow;
use openvm_stark_backend::p3_field::Field;

pub const NUM_MY_COLS: usize = 3;

#[repr(C)]
pub struct MyCols<F> {
    pub a: F,
    pub b: F,
    pub c: F,   // constrained to a + b
}

impl<F> Borrow<MyCols<F>> for [F] {
    fn borrow(&self) -> &MyCols<F> {
        debug_assert_eq!(self.len(), NUM_MY_COLS);
        let (prefix, shorts, suffix) = unsafe { self.align_to::<MyCols<F>>() };
        debug_assert!(prefix.is_empty() && suffix.is_empty() && shorts.len() == 1);
        &shorts[0]
    }
}
```

### 3.2 AIR struct — BaseAir + Air

```rust
use openvm_stark_backend::{
    p3_air::{Air, AirBuilder, BaseAir},
    p3_matrix::Matrix,
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
};

pub struct MyAir;

impl<F> BaseAir<F> for MyAir {
    fn width(&self) -> usize { NUM_MY_COLS }
    // preprocessed_trace() returns None by default — override for preprocessed columns
}

impl<F> BaseAirWithPublicValues<F> for MyAir {
    fn num_public_values(&self) -> usize { 1 }
}

impl<F> PartitionedBaseAir<F> for MyAir {}  // default: no cached_mains partitions

impl<AB: AirBuilder> Air<AB> for MyAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local: &MyCols<AB::Var> = main.row_slice(0).unwrap().borrow();
        let next:  &MyCols<AB::Var> = main.row_slice(1).unwrap().borrow();

        // Transition constraint: a' = b, b' = c, c' = b + c
        builder.when_transition().assert_eq(next.a, local.b);
        builder.when_transition().assert_eq(next.b, local.c);
        builder.when_transition().assert_eq(next.c, local.b + local.c);

        // First row: match public value
        let pv = builder.public_values();
        builder.when_first_row().assert_eq(local.a, pv[0]);
    }
}
```

### 3.3 Chip struct

```rust
use std::sync::Arc;
use openvm_stark_backend::{
    config::{StarkGenericConfig, Val},
    p3_field::PrimeField32,
    p3_matrix::dense::RowMajorMatrix,
    prover::{cpu::CpuBackend, types::AirProvingContext},
    AirRef, Chip, ChipUsageGetter,
};

pub struct MyChip { pub n: usize }

impl MyChip {
    pub fn air<SC: StarkGenericConfig>(&self) -> AirRef<SC> {
        Arc::new(MyAir)
    }
}

impl<SC: StarkGenericConfig> Chip<(), CpuBackend<SC>> for MyChip
where Val<SC>: PrimeField32
{
    fn generate_proving_ctx(&self, _: ()) -> AirProvingContext<CpuBackend<SC>> {
        let trace = generate_trace::<Val<SC>>(self.n);
        let first_val = trace.get(0, 0).unwrap();
        AirProvingContext::simple(Arc::new(trace), vec![first_val])
    }
}

impl ChipUsageGetter for MyChip {
    fn air_name(&self) -> String { "MyAir".to_string() }
    fn current_trace_height(&self) -> usize { self.n }
    fn trace_width(&self) -> usize { NUM_MY_COLS }
}
```

`AirProvingContext::simple(trace, pis)` — single common_main, no cached_mains.
`AirProvingContext::simple_no_pis(trace)` — no public values.

---

## 4. Bus Interactions (LogUp)

### 4.1 Key types

```rust
use openvm_stark_backend::interaction::{
    BusIndex,
    InteractionBuilder,   // trait — extends AirBuilder with push_interaction
    LookupBus,            // subset lookup: table ↔ query
    PermutationCheckBus,  // multiset equality: send ↔ receive
};
```

`BusIndex = u16`. A bus is just a `u16` constant shared between chips that communicate.

### 4.2 PermutationCheckBus — send/receive

```rust
const MY_BUS: PermutationCheckBus = PermutationCheckBus::new(0);

impl<AB: InteractionBuilder> Air<AB> for SenderAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let value = local[0];
        let count = local[1];          // must be boolean-constrained separately
        MY_BUS.send(builder, [value], count);
    }
}

impl<AB: InteractionBuilder> Air<AB> for ReceiverAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let value = local[0];
        let enabled = local[1];
        MY_BUS.receive(builder, [value], enabled);
    }
}
```

`send` adds an interaction with positive count; `receive` adds with negative count. The LogUp protocol enforces that the signed sum over all rows on all chips is zero for each bus.

### 4.3 LookupBus — range/table lookups

```rust
const RANGE_BUS: LookupBus = LookupBus::new(1);

// Table chip: add key with how many times it will be looked up
RANGE_BUS.add_key_with_lookups(builder, [value], num_lookups_expr);

// Query chip: assert value is in the table
RANGE_BUS.lookup_key(builder, [query_value], enabled);
```

### 4.4 push_interaction directly

```rust
// count > 0 → send; count < 0 → receive; count = 0 → disabled
builder.push_interaction(
    bus_index,
    [field0, field1],   // message fields
    count_expr,         // signed multiplicity
    count_weight,       // u32, for trace height constraint (0 = no constraint)
);
```

---

## 5. Multi-Stage (RAP) Witnesses

The system uses a **two-phase RAP** structure — no explicit `stage-0`/`stage-1` user API; it is handled automatically:

| Phase | What happens |
|-------|-------------|
| **Stage 0 (main)** | User provides `common_main` + `cached_mains` trace. Committed with PCS. |
| **Stage 1 (permutation)** | Backend auto-generates LogUp columns after sampling challenges. Width = `num_interaction_chunks + 1`. |

The stage-1 trace layout (from `fri_log_up.rs`):
```
| perm_1 | perm_2 | ... | perm_s | phi |
```
- `perm_i`: partial LogUp sum for interaction chunk `i`
- `phi`: running sum across all chunks (must equal 0 at last row — exposed value)

Users never generate stage-1 traces manually — `generate_proving_ctx` only fills stage-0.

### Cached (partitioned) mains

When a chip has a read-only table committed at key-gen time:

```rust
impl<F> PartitionedBaseAir<F> for MyAir {
    fn cached_main_widths(&self) -> Vec<usize> { vec![TABLE_WIDTH] }
    fn common_main_width(&self) -> usize { QUERY_WIDTH }
}

impl<AB: InteractionBuilder + PartitionedAirBuilder> Air<AB> for MyAir {
    fn eval(&self, builder: &mut AB) {
        let query_row = builder.common_main().row_slice(0).unwrap();
        let table_row = builder.cached_mains()[0].row_slice(0).unwrap();
        // use both
    }
}
```

In `generate_proving_ctx`, build a `CommittedTraceData` by committing the cached trace:
```rust
let (commit, data) = device.commit(&[Arc::clone(&cached_trace)]);
AirProvingContext {
    cached_mains: vec![CommittedTraceData { commitment: commit, data, trace: cached_trace }],
    common_main: Some(Arc::new(query_trace)),
    public_values: vec![],
}
```

---

## 6. Preprocessed Columns

Preprocessed columns are committed during key generation (not per-proof). Override in `BaseAir`:

```rust
impl<F: Clone> BaseAir<F> for MyAir {
    fn width(&self) -> usize { MAIN_WIDTH }
    fn preprocessed_trace(&self) -> Option<RowMajorMatrix<F>> {
        // Return fixed table; committed once during keygen
        Some(RowMajorMatrix::new(my_fixed_data, PREP_WIDTH))
    }
}
```

Access in constraints via `builder.preprocessed()`:
```rust
impl<AB: AirBuilder> Air<AB> for MyAir {
    fn eval(&self, builder: &mut AB) {
        let prep = builder.preprocessed();
        let prep_local = prep.row_slice(0).unwrap();
        let fixed_value = prep_local[0];
        // constrain against main
    }
}
```

`preprocessed_trace` returns `None` by default. If non-`None`, `compute_prep_data_for_air` commits it and stores commitments in both proving and verifying keys.

---

## 7. Prove/Verify Pipeline

### 7.1 Quick path (testing)

```rust
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::BabyBearPoseidon2Engine,
    engine::StarkFriEngine,
};
use openvm_stark_backend::p3_field::AbstractField;
use openvm_stark_backend::p3_matrix::dense::RowMajorMatrix;

// Build traces
let trace = generate_trace::<BabyBear>(n);
let pis = vec![BabyBear::from_canonical_u32(42)];

// Single chip, no partitioned mains
BabyBearPoseidon2Engine::run_simple_test_fast(
    vec![Arc::new(MyAir)],
    vec![trace],
    vec![pis],
).expect("proof failed");
```

### 7.2 Full keygen + prove + verify

```rust
use openvm_stark_sdk::{
    config::baby_bear_poseidon2::{BabyBearPoseidon2Engine, default_engine},
    engine::StarkFriEngine,
};
use openvm_stark_backend::{
    engine::StarkEngine,
    keygen::MultiStarkKeygenBuilder,
    prover::types::{AirProvingContext, ProvingContext},
    AirRef,
};

// 1. Build engine
let engine = default_engine();   // BabyBear + Poseidon2, standard_fast FRI params

// 2. Key generation
let mut keygen_builder = engine.keygen_builder();
let air_id_0 = keygen_builder.add_air(Arc::new(ChipA_Air) as AirRef<_>);
let air_id_1 = keygen_builder.add_air(Arc::new(ChipB_Air) as AirRef<_>);
let pk = keygen_builder.generate_pk();
let vk = pk.get_vk();

// 3. Generate traces (one per chip)
let ctx_a = chip_a.generate_proving_ctx(());
let ctx_b = chip_b.generate_proving_ctx(());

// 4. Assemble ProvingContext
let proving_ctx = ProvingContext {
    per_air: vec![(air_id_0, ctx_a), (air_id_1, ctx_b)],
};

// 5. Prove
let proof = engine.prove(&pk.to_device(engine.device()), proving_ctx);

// 6. Verify
engine.verify(&vk, &proof).expect("verification failed");
```

### 7.3 `any_rap_arc_vec!` macro

For `run_simple_test_fast` and similar helpers:
```rust
use openvm_stark_sdk::any_rap_arc_vec;
let airs = any_rap_arc_vec![ChipA_Air, ChipB_Air];
```
This macro wraps each air in `Arc::new(...)` and collects into `Vec<AirRef<SC>>`.

---

## 8. Multi-Chip Proving (Linked via Bus)

Multiple chips linked via `PermutationCheckBus` or `LookupBus`:

```rust
const EXECUTION_BUS: PermutationCheckBus = PermutationCheckBus::new(0);
const MEMORY_BUS:    LookupBus           = LookupBus::new(1);

// CPU chip: sends (pc, opcode) on execution bus, queries memory bus
// Memory chip: receives on execution bus, provides table on memory bus

let mut kb = engine.keygen_builder();
let cpu_id  = kb.add_air(Arc::new(CpuAir)    as AirRef<_>);
let mem_id  = kb.add_air(Arc::new(MemoryAir) as AirRef<_>);
let pk = kb.generate_pk();

let proving_ctx = ProvingContext {
    per_air: vec![
        (cpu_id,  cpu_chip.generate_proving_ctx(execution_record)),
        (mem_id,  mem_chip.generate_proving_ctx(execution_record)),
    ],
};
let proof = engine.prove(&pk.to_device(engine.device()), proving_ctx);
engine.verify(&pk.get_vk(), &proof).unwrap();
```

The LogUp constraint enforces that for each bus, the sum of all `count * message` contributions across all chips and all rows is zero. The prover generates stage-1 permutation columns automatically for each chip that participates in any interaction.

---

## 9. Key Types Quick Reference

| Type | Location | Purpose |
|------|----------|---------|
| `AirRef<SC>` | `rap` | `Arc<dyn AnyRap<SC>>` — main keygen interface |
| `Chip<R, PB>` | `chip` | trait: `generate_proving_ctx(record: R) -> AirProvingContext<PB>` |
| `ChipUsageGetter` | `chip` | metrics: name, height, width |
| `AirProvingContext<PB>` | `prover::types` | cached_mains + common_main + public_values |
| `CommittedTraceData<PB>` | `prover::types` | commitment + trace + pcs_data |
| `ProvingContext<PB>` | `prover::types` | `Vec<(air_id, AirProvingContext)>` |
| `MultiStarkKeygenBuilder` | `keygen` | registers AIRs, produces PK |
| `MultiStarkProvingKey` | `keygen` | contains per-AIR VKs + preprocessed commitments |
| `BusIndex` | `interaction` | `u16` bus identifier |
| `PermutationCheckBus` | `interaction` | multiset equality between chips |
| `LookupBus` | `interaction` | subset lookup (query ⊆ table) |
| `InteractionBuilder` | `interaction` | extends `AirBuilder` with `push_interaction` |
| `PartitionedAirBuilder` | `air_builders` | extends builder with `cached_mains()` / `common_main()` |
| `BabyBearPoseidon2Engine` | `stark-sdk` | ready-to-use engine for testing |
| `StarkFriEngine` | `stark-sdk` | trait with `run_simple_test_fast` etc. |
| `StarkEngine` | `engine` | trait with `prove`, `verify`, `keygen_builder` |

---

## 10. Minimal Complete Example

A chip that constrains `a[i+1] = a[i] + 1` and sends every value on a bus:

```rust
use std::sync::Arc;
use openvm_stark_backend::{
    p3_air::{Air, AirBuilder, BaseAir},
    p3_field::{PrimeField32, PrimeCharacteristicRing},
    p3_matrix::{dense::RowMajorMatrix, Matrix},
    interaction::{InteractionBuilder, PermutationCheckBus},
    rap::{BaseAirWithPublicValues, PartitionedBaseAir},
    config::{StarkGenericConfig, Val},
    prover::{cpu::CpuBackend, types::AirProvingContext},
    AirRef, Chip, ChipUsageGetter,
};

const COUNTER_BUS: PermutationCheckBus = PermutationCheckBus::new(0);

pub struct CounterAir { pub n: usize }

impl<F> BaseAir<F> for CounterAir {
    fn width(&self) -> usize { 1 }
}
impl<F> BaseAirWithPublicValues<F> for CounterAir {}
impl<F> PartitionedBaseAir<F> for CounterAir {}

impl<AB: InteractionBuilder> Air<AB> for CounterAir {
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0).unwrap();
        let next  = main.row_slice(1).unwrap();
        let val = local[0];
        let val_next = next[0];

        // Arithmetic constraint
        builder.when_transition().assert_eq(val_next, val + AB::Expr::ONE);

        // Send every value on the bus (enabled=1 always)
        COUNTER_BUS.send(builder, [val], AB::Expr::ONE);
    }
}

pub struct CounterChip { pub n: usize }

impl CounterChip {
    pub fn air<SC: StarkGenericConfig>(&self) -> AirRef<SC> {
        Arc::new(CounterAir { n: self.n })
    }
}

impl<SC: StarkGenericConfig> Chip<(), CpuBackend<SC>> for CounterChip
where Val<SC>: PrimeField32
{
    fn generate_proving_ctx(&self, _: ()) -> AirProvingContext<CpuBackend<SC>> {
        let h = self.n.next_power_of_two();
        let vals: Vec<Val<SC>> = (0..h)
            .map(|i| Val::<SC>::from_canonical_usize(i))
            .collect();
        let trace = RowMajorMatrix::new(vals, 1);
        AirProvingContext::simple_no_pis(Arc::new(trace))
    }
}

impl ChipUsageGetter for CounterChip {
    fn air_name(&self) -> String { "CounterAir".to_string() }
    fn current_trace_height(&self) -> usize { self.n }
    fn trace_width(&self) -> usize { 1 }
}
```
