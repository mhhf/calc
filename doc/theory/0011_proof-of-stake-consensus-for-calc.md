---
title: "Proof-of-Stake Consensus for CALC: Proofs as Transactions"
created: 2026-02-24
modified: 2026-02-24
summary: "Adapting Ethereum's PoS consensus to a multi-party proof verification network where linear logic proofs serve as transactions, the L1 kernel replaces re-execution, and linear resource semantics eliminate double-spending by construction."
tags: [consensus, proof-of-stake, linear-logic, blockchain, verification, proof-market]
category: "Ownership"
unique_contribution: "A concrete architecture mapping Ethereum's Gasper consensus onto CALC's proof system, showing that (1) linear logic's resource semantics solve double-spending at the type level rather than the consensus level, (2) proof verification replaces transaction re-execution yielding O(proof_size) validator cost, and (3) the asymmetry between proof search and proof verification naturally produces a three-role proof market (users, provers, validators) absent from traditional blockchains."
references: [RES_0059]
---

# Proof-of-Stake Consensus for CALC

## 1. The Core Insight

Blockchains solve two problems: **resource safety** (no double-spending) and **ordering** (which state transition comes first). Traditional blockchains solve both at the consensus layer — validators re-execute transactions to verify state transitions and agree on ordering.

CALC's linear logic already solves resource safety at the **type level**. A linear resource must be consumed exactly once — not by convention or consensus, but by logical necessity. A proof that consumes a resource twice is not a valid proof. Period.

This means consensus in CALC only needs to solve **ordering**: when two valid proofs compete for the same linear resource, which one wins? Everything else — correctness, resource safety, computation validity — is guaranteed by the proof itself.

## 2. The Mapping

### Ethereum → CALC Dictionary

| Ethereum | CALC | Notes |
|---|---|---|
| Transaction | Proof submission | Both are state transitions |
| EVM execution | Proof search (L3/L4) | The "hard work" |
| Transaction verification | Proof verification (L1 kernel) | The "cheap check" |
| Account balance | Linear resource | Consumed on use |
| Contract code | Persistent rule (under !) | Reusable |
| Smart contract call | Forward rule application | Trigger condition → result |
| Block | Proof batch | Ordered collection |
| State (world trie) | Content-addressed store | Hash-indexed |
| Gas | — | Not needed (see §4) |
| ETH | Stake token + bounty token | Dual role |

### What Stays the Same

- Slot/epoch time structure
- Casper FFG finality (justification → finalization)
- LMD-GHOST fork choice
- RANDAO proposer selection
- Validator lifecycle (deposit → active → exit)
- Slashing for equivocation (double vote, surround vote)
- Committee-based attestation
- Gossipsub networking

### What Changes Fundamentally

1. **No re-execution**: Validators verify proofs, not re-run computations
2. **No gas**: Proof verification cost is bounded by proof size
3. **Three roles**: Users, provers, and validators (not just users and validators)
4. **Resource safety is structural**: Linear types, not consensus, prevent double-spending
5. **Deterministic verification**: A proof is valid or not — no edge cases, no out-of-gas

## 3. State Model

### Ethereum State

```
WorldState = Map<Address, Account>
Account    = { nonce, balance, storageRoot, codeHash }
```

### CALC State

```
CALCState = {
  linear:      Set<Hash>        // consumable resources (≈ UTXO set)
  persistent:  Set<Hash>        // reusable knowledge (under !)
  rules:       Set<Rule>        // forward/backward rules (≈ contract code)
  stateRoot:   Hash             // Merkle root of the above
}
```

The content-addressed store provides natural Merkle properties: the state root is a hash over the resource sets, and any state transition can be verified by checking the proof + the Merkle witness.

**Linear pool** = the resources available for consumption. Each resource is a content-addressed formula hash. Consuming a resource removes it from the pool. Producing a resource adds it.

**Persistent pool** = facts under `!` (bang). These survive consumption and are available to all future proofs. Deploying a new persistent fact is like deploying a smart contract.

**Rules** = the forward and backward rules that define valid state transitions. The ILL calculus rules are present from genesis. Users can deploy new rules (= new "smart contracts").

## 4. Why No Gas?

Ethereum needs gas because EVM execution is Turing-complete — a transaction could loop forever. Gas bounds computation and creates a fee market.

CALC doesn't need gas because:

1. **Proof verification is bounded**: `verifyTree(proof)` is O(|proof|). The proof tree itself bounds the work.
2. **No halting problem**: Proof verification always terminates. It walks the tree and checks each step.
3. **Prover bears cost**: The expensive work (proof search) happens off-chain. Only the cheap verification happens on-chain.
4. **No state rent**: Content-addressed formulas are small and deduplicated.

The fee model is simpler: submitters pay a flat fee proportional to proof size (bytes), not computation steps. This eliminates gas auctions, EIP-1559 complexity, and MEV from gas games.

## 5. Transaction Types

### 5.1 Proof Submission

The primary transaction. A prover submits a complete proof tree.

```
ProofSubmission {
  sequent:     Sequent          // what was proved
  proofTree:   ProofTree        // the proof itself
  consumed:    List<Hash>       // linear resources consumed (antecedents)
  produced:    List<Hash>       // new resources produced (succedent)
  fee:         uint64           // fee to proposer
  submitter:   PubKey
  signature:   Sig
}
```

**Verification** (by any validator):
1. Check `consumed` ⊆ current linear pool
2. Run `verifyTree(proofTree)` — the L1 kernel
3. Check proof's antecedents match `consumed` and conclusion matches `produced`
4. If valid: remove `consumed` from pool, add `produced` to pool

This is the key asymmetry: the submitter may have spent hours finding the proof (L3/L4 search), but any validator can verify it in milliseconds (L1 kernel).

### 5.2 Rule Deployment

Deploy new forward/backward rules — the equivalent of deploying a smart contract.

```
RuleDeployment {
  rule:        Rule             // the rule definition
  persistent:  bool             // under ! or one-time
  fee:         uint64
  deployer:    PubKey
  signature:   Sig
}
```

A deployed rule becomes available for anyone to use in future proof submissions. Forward rules fire automatically when their conditions are met (like Ethereum events/triggers). Backward rules are available for proof search.

### 5.3 Goal Posting (Bounty)

A user posts a sequent they want proved, with a bounty for the first valid proof.

```
GoalPosting {
  sequent:     Sequent          // what needs to be proved
  bounty:      uint64           // reward for first valid proof
  deadline:    Slot             // expiration
  resources:   List<Hash>       // linear resources offered as antecedents
  poster:      PubKey
  signature:   Sig
}
```

This creates a **proof market**: users post goals, provers compete to find proofs, validators verify the winning proof. The bounty incentivizes proof search.

### 5.4 Resource Minting

Creating new linear resources from axioms or persistent knowledge.

```
ResourceMint {
  proof:       ProofTree        // proof from axioms/persistent that produces the resource
  produced:    List<Hash>       // new resources
  fee:         uint64
  minter:      PubKey
  signature:   Sig
}
```

## 6. Block Structure

```
CALCBlock {
  slot:            uint64
  epoch:           uint64
  proposer_index:  ValidatorIndex
  parent_root:     Hash
  state_root:      Hash               // Merkle root after applying all txns
  body: {
    proof_submissions:   List<ProofSubmission>
    rule_deployments:    List<RuleDeployment>
    goal_postings:       List<GoalPosting>
    resource_mints:      List<ResourceMint>
    attestations:        List<Attestation>
    slashings:           List<SlashingEvidence>
    validator_exits:     List<ValidatorExit>
    randao_reveal:       BLSSignature
  }
}
```

### Block Production

The proposer (selected by RANDAO):
1. Collects pending proof submissions from the gossip network
2. **Orders** them, resolving resource conflicts (two proofs consuming the same linear resource → pick one)
3. Verifies each proof sequentially against the running state
4. Builds the block and broadcasts it

### Resource Conflict Resolution

The only ordering problem: two valid proofs `P1` and `P2` both want to consume linear resource `R`. The proposer must pick one. Strategies:

1. **Fee priority**: Higher fee wins (simple, like Ethereum)
2. **Proof efficiency**: Smaller proof tree wins (incentivizes elegant proofs)
3. **First seen**: Temporal ordering from gossip network
4. **Goal priority**: Proofs satisfying posted goals get priority

The losing proof is returned to the mempool. If its consumed resources are still available, it can be included in a future block.

## 7. Consensus

### Time Structure

Same as Ethereum:
- **Slot**: 12 seconds, one block opportunity
- **Epoch**: 32 slots = 6.4 minutes
- **Checkpoint**: First slot of each epoch

### Attestation

Validators attest to blocks. Each attestation contains:

```
CALCAttestation {
  slot:              uint64
  committee_index:   uint64
  block_root:        Hash          // LMD-GHOST vote
  source:            Checkpoint    // FFG source
  target:            Checkpoint    // FFG target
  proof_valid:       bool          // all proofs in block verified ✓
}
```

The `proof_valid` flag is the CALC-specific addition. Since proof verification is deterministic, honest validators always agree on this. A validator who sets `proof_valid = true` for a block containing invalid proofs is **slashable** (and the invalid proof is the evidence).

### Finality

Directly from Casper FFG:
1. Checkpoint justified when 2/3 of stake attests source → target link
2. Checkpoint finalized when next checkpoint is also justified

Once finalized: consumed linear resources are permanently gone, produced resources are permanent, deployed rules are permanent. No reversion possible without destroying 1/3 of total stake.

### Fork Choice

LMD-GHOST from highest justified checkpoint, with proposer boosting. Identical to Ethereum — the proof content doesn't affect fork choice, only the block/attestation structure.

## 8. Slashing

### Slashable Offenses

| Offense | Evidence | Penalty |
|---|---|---|
| FFG double vote | Two attestations, same target epoch, different data | Correlation-scaled (same as Ethereum) |
| Surround vote | Two attestations where one source/target spans the other | Correlation-scaled |
| Invalid proof attestation | Block with invalid proof + validator's `proof_valid=true` attestation | Full stake (deterministic fraud) |
| Double block proposal | Two different blocks for the same slot | Correlation-scaled |

**Invalid proof attestation** is unique to CALC and has a **full stake penalty** because it is deterministic fraud — there is no ambiguity about whether a proof is valid. The L1 kernel is the arbiter, and its output is reproducible by anyone. This is unlike Ethereum where execution edge cases can cause honest disagreement.

### Why Slashing is Cleaner

In Ethereum, there are edge cases around gas, state access, and execution semantics that can cause honest validators to disagree. In CALC, proof verification is:
- **Deterministic**: Same input → same output, always
- **Total**: Always terminates with valid/invalid
- **Reproducible**: Any node can re-verify

This means any disagreement about proof validity is provably dishonest, making slashing simpler and more aggressive.

## 9. The Three-Role Proof Market

Traditional blockchains have two roles: **users** (submit transactions) and **validators** (verify and order transactions). CALC introduces a third: **provers**.

```
User                    Prover                   Validator
  |                       |                         |
  |-- post goal+bounty -->|                         |
  |                       |-- search for proof      |
  |                       |   (L3/L4, expensive)    |
  |                       |                         |
  |                       |-- submit proof -------->|
  |                       |                         |-- verify (L1, cheap)
  |                       |                         |-- attest
  |                       |                         |-- include in block
  |<-- result + receipt --|<-- reward --------------|
```

### Role Economics

| Role | Work | Cost | Revenue |
|---|---|---|---|
| **User** | Post goals | Bounty + fee | Gets proven result |
| **Prover** | Find proofs | CPU time for search | Bounties + submission fees |
| **Validator** | Verify proofs, maintain consensus | Staked capital + verification CPU | Attestation rewards + proposer rewards |

### Why Three Roles?

The asymmetry between proof search and proof verification creates a natural division:
- **Proof search** is expensive and requires specialized knowledge/compute (like mining in PoW)
- **Proof verification** is cheap and mechanical (like validating in PoS)
- **Goal posting** requires domain knowledge but no compute

This means provers can specialize: some might be experts in arithmetic proofs, others in resource allocation proofs, etc. The proof market matches demand (goals) with supply (provers) through bounties.

### Prover Competition

Multiple provers can race to solve the same goal. The first valid proof submitted (and included in a block) wins the bounty. This is competitive but **not wasteful** like PoW mining — the prover is doing useful mathematical work.

Provers who lose the race can still submit proofs for other goals. Their failed attempt isn't wasted energy — they may have found intermediate lemmas useful for future proofs.

## 10. Smart Contracts as Logical Rules

### Ethereum Smart Contracts

In Ethereum, a smart contract is EVM bytecode stored at an address. Calling it executes the bytecode against the current state. The contract is opaque — its behavior is defined by the code.

### CALC "Smart Contracts"

In CALC, a "smart contract" is a set of deployed rules. The behavior is defined by the logical structure of the rules, which is transparent and verifiable.

**Example: Token Transfer**

```
-- Rule: transfer
-- Consumes: owns(sender, token, amount)  [linear]
-- Requires: authorized(sender, tx)       [persistent, proved]
-- Produces: owns(receiver, token, amount) [linear]

owns(S, T, A), authorized(S, TX) ⊸ owns(R, T, A)
```

This rule is a loli (⊸): it consumes the linear resource `owns(S, T, A)`, requires proving `authorized(S, TX)` from persistent knowledge, and produces `owns(R, T, A)`.

**A proof submission that uses this rule IS the transfer**. The proof tree demonstrates:
1. The sender owns the tokens (linear resource exists)
2. The sender authorized the transfer (persistent proof)
3. The tokens are transferred (new linear resource created)

No re-execution needed — the proof IS the evidence of correct execution.

**Example: Escrow**

```
-- Deposit: lock funds in escrow
owns(S, T, A), escrow_terms(S, R, T, A, conditions) ⊸ escrowed(S, R, T, A, conditions)

-- Release: fulfill conditions, release funds
escrowed(S, R, T, A, conditions), fulfilled(conditions) ⊸ owns(R, T, A)

-- Refund: conditions expire, return funds
escrowed(S, R, T, A, conditions), expired(conditions) ⊸ owns(S, T, A)
```

Three rules that together form an escrow contract. The linear resource `escrowed(...)` can only be consumed once — either by release or refund, never both. Linear logic enforces this without any mutex or reentrancy guard.

### Composability via Cut

Proofs compose via the cut rule. If proof P1 produces resource A and proof P2 consumes resource A, they can be combined into a single proof P1;P2 (cut on A). This is the logical version of atomic transaction composition.

Cut elimination guarantees that composed proofs can be normalized — the composition is always well-defined.

## 11. Linear Logic Advantages Over Traditional Blockchains

### Double-Spending is a Type Error

In Ethereum, double-spending is prevented by nonce tracking and consensus. A malicious transaction that tries to spend twice is rejected by validators during re-execution.

In CALC, double-spending is a **type error in the proof**. A proof that consumes a linear resource twice is not a valid proof — it fails `verifyTree()` at the L1 kernel level. This is not a consensus decision; it's a logical fact.

This means:
- No need for nonce tracking
- No need for transaction ordering to prevent double-spends
- Ordering only matters for **resource contention** (two valid proofs wanting the same resource)

### Reentrancy is Impossible

Ethereum's biggest vulnerability class (DAO hack, etc.) is reentrancy — a contract calling back into itself during execution. In CALC:
- Linear resources are consumed when used. A rule that consumes resource R cannot see R again.
- There is no "execution context" that can be re-entered. Each proof step is a pure logical derivation.
- Composition via cut is well-defined and normalizing.

### State Bloat is Bounded

Every formula in the content-addressed store is:
- Structurally shared (identical subformulas share the same hash)
- Immutable (content-addressed)
- Small (formulas are tree-structured, not arbitrary bytecode)

Linear resources are consumed and removed from state. Only persistent facts (under !) accumulate indefinitely — and these are deduplicated by content addressing.

## 12. Puzzle Pieces: What We Need to Build

### Existing (already in CALC)

| Component | CALC Module | Role in Consensus |
|---|---|---|
| Proof verification | `lib/kernel/` (L1) | Transaction validation |
| Proof search | `lib/prover/focused.js` (L3) | Prover's off-chain work |
| Forward execution | `lib/engine/forward.js` | Rule firing, state transitions |
| Content-addressed store | `lib/kernel/store.js` | State representation |
| Symbolic execution | `lib/engine/symexec.js` | Exploring proof spaces |
| Rule compilation | `lib/engine/compile.js` | "Smart contract" deployment |

### New Infrastructure Needed

| Component | Description | Ethereum Analog |
|---|---|---|
| **Networking (P2P)** | Gossipsub for proofs, attestations, goals | libP2P / DevP2P |
| **Validator registry** | Stake deposits, activation queue, exits | Beacon chain validator set |
| **Committee selection** | RANDAO-based shuffling of verifiers | Beacon chain committees |
| **Block production** | Ordering proofs, resolving conflicts | Execution client |
| **State Merkle tree** | Merkle root over linear/persistent pools | World state trie |
| **Finality gadget** | Casper FFG for proof checkpoints | Beacon chain Casper |
| **Fork choice** | LMD-GHOST for block selection | Beacon chain fork choice |
| **Proof mempool** | Pending proof submissions + goal postings | Transaction mempool |
| **Bounty mechanism** | Goal posting, escrow, payout | — (novel) |
| **Slashing monitor** | Detect invalid attestations, equivocation | Slasher client |

### Development Phases

**Phase 1: Local Multi-Party Verification**
- Multiple nodes sharing a proof store
- Simple round-robin block production
- No staking, no finality (just ordered agreement)
- Validates the core idea: proofs as transactions work

**Phase 2: Staked Consensus**
- Validator registry with stake deposits
- Committee-based attestation
- Casper FFG finality
- Slashing for invalid attestations and equivocation

**Phase 3: Proof Market**
- Goal posting with bounties
- Prover competition
- Fee market for proof inclusion
- Prover specialization

**Phase 4: Production Hardening**
- Sync protocols (checkpoint sync)
- Light clients (verify proofs without full state)
- Rule auditing and formal verification of rules
- Governance for rule upgrades

## 13. Open Questions

1. **Stake denomination**: What is staked? A native token? Proof-of-work (proofs themselves as stake)? Reputation?

2. **Proof size limits**: Should blocks have a maximum total proof size? This is the analog of gas limits but simpler — just byte limits.

3. **Rule governance**: Who can deploy new rules? Should rule deployment require a governance vote? Can malicious rules be removed?

4. **Cross-calculus interop**: If different communities use different calculi (not just ILL), can they interoperate? This is like cross-chain bridges but for different logics.

5. **Privacy**: Proofs are transparent — anyone can see what resources were consumed and produced. Do we need zero-knowledge proofs for privacy? (ZK proofs of linear logic proofs — meta!)

6. **Incentive alignment for provers**: How do we prevent proof withholding (a prover finds a proof but waits to submit until profitable)? MEV-like concerns.

7. **Rule equivalence**: Two rules might be logically equivalent but syntactically different. Should the system detect and deduplicate?

8. **Persistent fact accumulation**: Linear resources are consumed, but persistent facts grow monotonically. Is this sustainable? Do we need garbage collection for unused persistent facts?

## 14. Comparison with Related Work

| System | Computation Model | Verification Cost | Resource Safety |
|---|---|---|---|
| **Ethereum** | EVM re-execution | O(gas) — re-execute everything | Consensus (nonces, balances) |
| **ZK-Rollups** | ZK proof verification | O(1) per proof, O(n) to generate | ZK proof |
| **Optimistic Rollups** | Fraud proof (challenge) | O(1) amortized, O(n) on challenge | Challenge period |
| **CALC-chain** | Proof tree verification | O(proof_size) — walk the tree | Linear types (structural) |

CALC-chain sits between ZK-rollups and optimistic rollups:
- Like ZK-rollups: the proof IS the certificate of correct execution
- Like optimistic rollups: verification is cheap relative to generation
- Unlike both: resource safety comes from the logic, not the proof system

## References

- RES_0059: Ethereum Proof of Stake Consensus Mechanism
- Girard, J.-Y. (1987). Linear Logic. *Theoretical Computer Science*.
- Andreoli, J.-M. (1992). Logic Programming with Focusing Proofs in Linear Logic. *JLC*.
- Buterin, V. et al. (2020). Combining GHOST and Casper. *arXiv:2003.03052*.
