# Strategy Layers for Forward Rule Indexing

The strategy stack partitions forward rules across indexing layers for efficient candidate lookup during symbolic execution. Each layer claims rules it can index well; unclaimed rules fall through to the next.

## Layer Stack (ordered)

```
fingerprintLayer  →  O(1) per step, for rules with ground discriminator
discTreeLayer     →  O(depth) per fact, general-purpose trie over patterns
predicateLayer    →  O(R) linear scan (safety net, rarely activates)
```

`detectStrategy(rules)` auto-builds this stack. The fingerprint layer is added only when a dominant discriminating predicate is detected from rule structure. The disc-tree layer claims all remaining rules.

## How the Discrimination Tree Works

Each rule's first linear trigger pattern is flattened to a **preorder tag sequence**:

```
code(_PC, push1)  →  [code, WILDCARD, atom]
stack(_V, _S)     →  [stack, WILDCARD, WILDCARD]
```

These sequences form paths in a trie. At query time, a ground fact is flattened the same way, and the trie is walked following both concrete tag matches and wildcard branches (which skip entire subtrees using arity-based size computation).

## Writing a Custom Strategy Layer

A layer has two methods:

```javascript
{
  claims(rule) → boolean,   // "can I index this rule?"
  build(rules) → {          // build index from claimed rules
    getCandidateRules(state, stateIndex) → rule[]
  }
}
```

### Fingerprint Auto-Detection

`detectFingerprintConfig()` auto-detects discriminator structure from compiled rules. Three patterns are recognized:

**Standard (arity >= 2):** A binary+ predicate has one ground child and one variable child across most rules. A separate pointer predicate (unary, sharing a variable with the key position) links the current position to the lookup key.

```ill
% code(PC, OPCODE) is the discriminator, pc(PC) is the pointer
code(_PC, my_opcode) * pc(_PC) * ... -o { ... }
```

**Self-pointer (arity 1):** A unary predicate has a ground value — e.g., `pc(0x0)`. The predicate IS its own pointer (`keyPos === groundPos`). No separate pointer predicate needed. This pattern arises from compile-time specialization, where `arr_get` cut elimination produces per-PC rules with ground program counters.

```ill
% After specialization: pc(0x0) is both discriminator and pointer
pc 0x0 * gas GAS * ... -o { pc 0x2 * ... }.
pc 0x2 * gas GAS * ... -o { pc 0x5 * ... }.
```

**Virtual (persistent goal):** When no linear discriminator exists, `compileRule` scans persistent antecedents for `!arr_get B PC GROUND` patterns and builds a virtual discriminator from the ground value and associated linear pointer/array predicates.

**Discriminator preference:** When multiple candidates exist, the compiler prefers non-arrlit ground values (binlit/atom) over arrlit. Arrlit values are often shared across all rules (e.g., `bytecode(arrlit)`) giving zero discrimination, while binlit values (e.g., `pc(0x5)`) vary per rule.

### Example: Domain-Specific Layer

For programs where the auto-detected layers aren't enough:

```javascript
function makeMyLayer(config) {
  return {
    claims: (rule) => rule.triggerPreds.includes(config.pred),
    build: (rules) => {
      const index = {};
      for (const rule of rules) {
        const key = extractKey(rule);  // your domain logic
        if (!index[key]) index[key] = [];
        index[key].push(rule);
      }
      return {
        getCandidateRules(state, stateIndex) {
          const key = computeKey(state);  // your domain logic
          return index[key] || [];
        }
      };
    }
  };
}
```

Then register it before the disc-tree:
```javascript
const layers = [];
layers.push(makeMyLayer({ pred: 'myPred' }));
layers.push(makeDiscTreeLayer());
const stack = buildStrategyStack(rules, layers);
```

## Performance Characteristics

| Layer | Lookup | Build | Best For |
|-------|--------|-------|----------|
| fingerprint | O(1) | O(R) | Programs with ground discriminator (EVM, instruction sets) |
| disc-tree | O(D * F_rel) | O(R * P) | General programs, 50-1000 rules |
| predicate | O(R) | O(R) | Fallback for edge cases |

Where: R = rules, D = pattern depth, F_rel = facts from relevant predicates, P = pattern size.

The disc-tree only scans facts from predicates that appear in its indexed rules, so it's efficient even when the state has many unrelated facts.
