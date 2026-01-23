# Manual Proof View Implementation

Interactive proof assistant for constructing proofs in the sequent calculus.

## Overview

The Manual Proof tab provides **two proof views**:

1. **Classical View** - Traditional sequent calculus with ⊢ notation, proof tree growing upward
2. **Structured View** - Lamport-style hierarchical proofs with numbered steps (for longer/complex proofs)

Both views support:
- Enter a sequent (goal to prove)
- See applicable rules, apply them interactively
- Undo rule applications
- Auto-complete using the existing proof search
- Visual proof completion status

---

## Research Summary

### Sequent Calculus Proof Assistants

Based on analysis of [Logitext](http://logitext.mit.edu/main), [Calculus Toolbox](https://goodlyrottenapple.github.io/calculus-toolbox/doc/scala-ui.html), [Proof Tree Builder](https://joomy.korkutblech.com/papers/ptb.pdf):

**Common UI Patterns:**
- Click on sequent → show applicable rules
- Select rule → premises appear above conclusion
- Proof tree grows upward (bottom-up display)
- Leaves with no premises (axioms) = proven
- Color coding: green=proven, red/blue=unproven

### Lamport's Structured Proofs

Based on [How to Write a 21st Century Proof](https://lamport.azurewebsites.net/pubs/proof.pdf) and [TLA+ Proof System](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Other_proof_constructs.html):

**Key Concepts:**
- Hierarchical structure replaces linear prose
- Numbered levels: `<1>`, `<2>`, `<3>` for nesting depth
- Numbered steps within levels: `<1>1`, `<1>2`, `<2>1`
- Keywords: ASSUME/PROVE, SUFFICES, CASE, BY, QED
- References between steps: `BY <1>1, <2>3`
- Collapsible levels for managing complexity

**Visual Format:**
```
THEOREM Foo
<1>1. ASSUME P PROVE Q
  <2>1. R BY <1>1
  <2>2. S BY <2>1, DEF T
  <2>3. QED BY <2>2
<1>2. QED BY <1>1
```

**Benefits:**
- Scales to complex proofs
- Each step has explicit justification
- Can skip details by reading only high-level steps
- Easy to identify which parts need revision

---

## Design Decisions

### Rule Display: Hybrid Approach (Recommended)

When showing applicable rules, display **both** the abstract rule and concrete preview:

```
┌─────────────────────────────────────────────────────────┐
│ Tensor_L                                                │
│                                                         │
│ Abstract:     Γ, A, B ⊢ C                              │
│              ─────────────                              │
│               Γ, A ⊗ B ⊢ C                             │
│                                                         │
│ Preview:  Applying to current sequent would create:     │
│           P, Q, R ⊢ S                                   │
│                                                         │
│                                    [Apply]  [Cancel]    │
└─────────────────────────────────────────────────────────┘
```

**Rationale:**
- Abstract form teaches the rule pattern (educational)
- Preview shows concrete effect (practical decision-making)
- Users think "what do I need to prove next?" - preview answers this

### Undo Support

Maintain a history stack:

```typescript
const [history, setHistory] = createSignal<PT[]>([]);
const [historyIndex, setHistoryIndex] = createSignal(0);

function undo() {
  if (historyIndex() > 0) {
    setHistoryIndex(i => i - 1);
    setProofTree(history()[historyIndex() - 1]);
  }
}

function redo() {
  if (historyIndex() < history().length - 1) {
    setHistoryIndex(i => i + 1);
    setProofTree(history()[historyIndex() + 1]);
  }
}
```

### Auto-Complete

"Finish Automatically" button calls existing `Proofstate.auto()`:

```typescript
function autoComplete(nodeId: string) {
  const pt = getNodeAtPath(proofTree(), nodeId);
  const result = Proofstate.auto(pt, {
    positive: atoms,
    negative: [],
    mode: 'proof',
    rules, bwd, getRule
  });

  if (result.success) {
    // Replace node with completed subtree
    const newTree = setNodeAtPath(proofTree(), nodeId, pt);
    pushHistory(newTree);
  }
}
```

---

## Two Views Architecture

### View 1: Classical Proof Tree

Traditional bottom-up tree with inference lines:

```
        ─────────────  ─────────────
         A ⊢ A         B ⊢ B
        ══════════════════════════════ (⊗R)
              A, B ⊢ A ⊗ B
```

**Implementation:**
- Recursive component with `flex-direction: column-reverse`
- Horizontal inference lines (double for conclusion)
- Rule name on the right
- Click any unproven sequent to select it

**Best for:**
- Short proofs (< 10 steps)
- Learning sequent calculus
- Visualizing proof structure

### View 2: Structured Proof (Lamport-style)

Hierarchical numbered steps:

```
GOAL: A, B ⊢ A ⊗ B

<1>1. SUFFICES A ⊢ A ∧ B ⊢ B
      BY Tensor_R
  <2>1. A ⊢ A
        BY Id
  <2>2. B ⊢ B
        BY Id
  <2>3. QED
<1>2. QED BY <1>1
```

**Implementation:**
- List-based rendering with indentation
- Collapsible/expandable levels
- Step references shown explicitly
- "Proof sketch" mode hides sub-proofs

**Best for:**
- Long/complex proofs
- Documentation and export
- Step-by-step explanation

### View Toggle

Users can switch between views. **Both views are fully interactive** - same underlying PT data structure, different visualizations, both allowing rule application by clicking on unproven steps.

```tsx
const [viewMode, setViewMode] = createSignal<'tree' | 'structured'>('tree');

// Same underlying PT data structure, different rendering
// Both views support clicking to select nodes and apply rules
<Show when={viewMode() === 'tree'}>
  <ClassicalProofTree
    pt={proofTree()}
    onNodeSelect={setSelectedPath}
  />
</Show>
<Show when={viewMode() === 'structured'}>
  <StructuredProofView
    pt={proofTree()}
    onNodeSelect={setSelectedPath}  // Same interaction!
  />
</Show>
```

The Structured View is intended to become the primary/default prover for complex proofs, so full interactivity is essential.

---

## Existing Infrastructure

### Data Structures

**PT (Proof Tree)** - `lib/pt.js`:
```typescript
class PT {
  premisses: PT[];       // Child proof trees (subgoals)
  conclusion: Sequent;   // The sequent at this node
  type: string;          // Rule name or "???" if unproven
  proven: boolean;       // Whether this subtree is complete
  delta_in: object;      // Resources available
  delta_out: object;     // Resources consumed
}
```

**Sequent** - `lib/sequent.js`:
```typescript
class Sequent {
  linear_ctx: Record<string, {num: number, val: Node}>;
  persistent_ctx: Record<string, Node>;
  succedent: Node;
  focus?: Node;
  focusPosition?: 'L' | 'R';
}
```

### Rule Application

**Proofstate.apply()** - `lib/proofstate.js:321`:
- Takes PT, rule name, position (id), and rule
- Computes MGU between rule conclusion and current sequent
- Creates new PT nodes for each premise
- Sets `pt.type` to rule name

**Proofstate.auto()** - `lib/proofstate.js:69`:
- Automatic proof search with focusing
- Returns `{success, theta, delta_out, debug}`
- Can be called on any subtree

**Ruleset.init()** - `lib/ruleset.js`:
- Returns `{rules, bwd, getRule}`
- `rules`: all rules as `Record<string, Sequent[]>`
- `getRule(name)`: returns rule with fresh variables

---

## Implementation Plan

### File Structure

```
src/ui/
├── pages/
│   └── ManualProof.tsx              # Main page with view toggle
├── components/
│   └── proof/
│       ├── ClassicalProofTree.tsx   # View 1: Bottom-up tree
│       ├── StructuredProofView.tsx  # View 2: Lamport-style
│       ├── ProofNode.tsx            # Single sequent node
│       ├── InferenceLine.tsx        # Horizontal rule line
│       ├── RuleSelector.tsx         # Rule picker panel
│       ├── ProofControls.tsx        # Undo/Redo/Auto buttons
│       └── StepReference.tsx        # <n>m step numbering
└── lib/
    └── proofLogic.ts                # Browser-compatible proof logic
```

### Phase 1: Core Infrastructure

```typescript
// src/ui/lib/proofLogic.ts

// Browser-compatible rule initialization (no fs)
export function initBrowserRuleset(): Ruleset;

// Find applicable rules for a sequent
export function getApplicableRules(seq: Sequent, rules: Rules): ApplicableRule[];

// Apply a rule, return new PT
export function applyRule(pt: PT, ruleName: string, position: string): PT;

// Check if proof is complete
export function isProofComplete(pt: PT): boolean;

// Convert PT to structured proof text
export function ptToStructuredProof(pt: PT): StructuredStep[];

// Path-based tree manipulation
export function getNodeAtPath(pt: PT, path: number[]): PT | null;
export function setNodeAtPath(root: PT, path: number[], node: PT): PT;
```

### Phase 2: Classical Tree View

```tsx
// src/ui/components/proof/ClassicalProofTree.tsx

interface ClassicalProofTreeProps {
  pt: PT;
  selectedPath: number[] | null;
  onNodeSelect: (path: number[]) => void;
}

function ClassicalProofTree(props: ClassicalProofTreeProps) {
  return (
    <div class="flex flex-col-reverse items-center">
      {/* Premises above */}
      <Show when={props.pt.premisses.length > 0}>
        <div class="flex gap-8 mb-2">
          <For each={props.pt.premisses}>
            {(p, i) => (
              <ClassicalProofTree
                pt={p}
                selectedPath={/* derive child path */}
                onNodeSelect={props.onNodeSelect}
              />
            )}
          </For>
        </div>
        <InferenceLine ruleName={props.pt.type} />
      </Show>

      {/* Conclusion at bottom */}
      <ProofNode
        sequent={props.pt.conclusion}
        isLeaf={props.pt.premisses.length === 0}
        isProven={props.pt.proven}
        isSelected={/* check path */}
        onClick={() => props.onNodeSelect(currentPath)}
      />
    </div>
  );
}
```

### Phase 3: Structured View

```tsx
// src/ui/components/proof/StructuredProofView.tsx

interface StructuredStep {
  level: number;      // 1, 2, 3...
  step: number;       // 1, 2, 3... within level
  assertion: string;  // The sequent or claim
  justification: string;  // "BY Tensor_L" or "SUFFICES"
  isQED: boolean;
  children: StructuredStep[];
  collapsed: boolean;
}

function StructuredProofView(props: { pt: PT }) {
  const steps = createMemo(() => ptToStructuredProof(props.pt));

  return (
    <div class="font-mono text-sm space-y-1">
      <div class="font-bold">GOAL: {props.pt.conclusion.toString()}</div>
      <For each={steps()}>
        {(step) => <StepRow step={step} />}
      </For>
    </div>
  );
}

function StepRow(props: { step: StructuredStep }) {
  const indent = () => props.step.level * 24; // px

  return (
    <div style={{ "padding-left": `${indent()}px` }}>
      <span class="text-blue-600">{`<${props.step.level}>${props.step.step}.`}</span>
      <span class="ml-2">{props.step.assertion}</span>
      <span class="text-gray-500 ml-2">{props.step.justification}</span>

      <Show when={!props.step.collapsed}>
        <For each={props.step.children}>
          {(child) => <StepRow step={child} />}
        </For>
      </Show>
    </div>
  );
}
```

### Phase 4: Rule Selector

```tsx
// src/ui/components/proof/RuleSelector.tsx

interface RuleSelectorProps {
  sequent: Sequent;
  applicableRules: ApplicableRule[];
  onApply: (ruleName: string) => void;
  onCancel: () => void;
}

function RuleSelector(props: RuleSelectorProps) {
  return (
    <div class="fixed inset-0 bg-black/50 flex items-center justify-center">
      <div class="bg-white dark:bg-gray-800 rounded-lg p-4 max-w-2xl max-h-[80vh] overflow-auto">
        <h3 class="text-lg font-bold mb-4">Select Rule to Apply</h3>

        <For each={props.applicableRules}>
          {(rule) => (
            <div class="border rounded p-3 mb-2 hover:bg-gray-50">
              {/* Rule name */}
              <div class="font-mono font-bold text-blue-600">{rule.name}</div>

              {/* Abstract rule (fraction notation) */}
              <div class="my-2">
                <SequentRule
                  name=""
                  ruleStrings={rule.ruleStrings}
                  simplified={true}
                />
              </div>

              {/* Preview of result */}
              <div class="text-sm text-gray-600 mt-2">
                <div class="font-medium">Would create premises:</div>
                <For each={rule.premises}>
                  {(p) => <div class="ml-4">• {p.toString()}</div>}
                </For>
              </div>

              <button
                onClick={() => props.onApply(rule.name)}
                class="mt-2 px-4 py-1 bg-blue-600 text-white rounded"
              >
                Apply
              </button>
            </div>
          )}
        </For>

        <button onClick={props.onCancel} class="mt-4 text-gray-500">
          Cancel
        </button>
      </div>
    </div>
  );
}
```

### Phase 5: Main Page

```tsx
// src/ui/pages/ManualProof.tsx

export default function ManualProof() {
  // State
  const [input, setInput] = createSignal('');
  const [proofTree, setProofTree] = createSignal<PT | null>(null);
  const [selectedPath, setSelectedPath] = createSignal<number[] | null>(null);
  const [viewMode, setViewMode] = createSignal<'tree' | 'structured'>('tree');
  const [history, setHistory] = createSignal<PT[]>([]);
  const [historyIndex, setHistoryIndex] = createSignal(-1);

  // Computed
  const isComplete = createMemo(() =>
    proofTree() ? isProofComplete(proofTree()!) : false
  );
  const applicableRules = createMemo(() => {
    if (!selectedPath() || !proofTree()) return [];
    const node = getNodeAtPath(proofTree()!, selectedPath()!);
    return node ? getApplicableRules(node.conclusion, rules) : [];
  });

  // Actions
  function startProof() { /* parse input, create initial PT */ }
  function handleApplyRule(ruleName: string) { /* apply, push history */ }
  function handleUndo() { /* pop history */ }
  function handleRedo() { /* forward in history */ }
  function handleAutoComplete() { /* call Proofstate.auto */ }

  return (
    <div class="max-w-6xl mx-auto p-6">
      {/* Header */}
      <h2>Manual Proof</h2>

      {/* Input + Examples */}
      <FormulaInput ... />
      <ExampleButtons ... />
      <button onClick={startProof}>Start Proof</button>

      {/* View Toggle */}
      <div class="flex gap-2 my-4">
        <button onClick={() => setViewMode('tree')}>Tree View</button>
        <button onClick={() => setViewMode('structured')}>Structured View</button>
      </div>

      {/* Controls */}
      <ProofControls
        onUndo={handleUndo}
        onRedo={handleRedo}
        onAuto={handleAutoComplete}
        canUndo={historyIndex() > 0}
        canRedo={historyIndex() < history().length - 1}
      />

      {/* Proof Display */}
      <Show when={proofTree()}>
        <Show when={viewMode() === 'tree'}>
          <ClassicalProofTree
            pt={proofTree()!}
            selectedPath={selectedPath()}
            onNodeSelect={setSelectedPath}
          />
        </Show>
        <Show when={viewMode() === 'structured'}>
          <StructuredProofView pt={proofTree()!} />
        </Show>
      </Show>

      {/* Completion Status */}
      <Show when={isComplete()}>
        <div class="bg-green-100 text-green-800 p-4 rounded">
          ✓ Proof Complete!
        </div>
      </Show>

      {/* Rule Selector Modal */}
      <Show when={selectedPath() && applicableRules().length > 0}>
        <RuleSelector
          sequent={getNodeAtPath(proofTree()!, selectedPath()!).conclusion}
          applicableRules={applicableRules()}
          onApply={handleApplyRule}
          onCancel={() => setSelectedPath(null)}
        />
      </Show>
    </div>
  );
}
```

---

## Implementation Order

### Milestone 1: Basic Interactive Prover (Classical View)
- [ ] Create ManualProof.tsx page skeleton
- [ ] Add to navigation (4th tab: "Prove")
- [ ] Sequent input with example buttons
- [ ] proofLogic.ts - browser-compatible initialization
- [ ] ProofNode component
- [ ] ClassicalProofTree recursive component
- [ ] RuleSelector with hybrid display
- [ ] Apply rule functionality
- [ ] Proof completion detection

### Milestone 2: Undo/Redo + Auto
- [ ] History stack implementation
- [ ] Undo/Redo buttons
- [ ] Auto-complete button (calls Proofstate.auto)
- [ ] Keyboard shortcuts (Ctrl+Z, Ctrl+Y)

### Milestone 3: Structured View
- [ ] ptToStructuredProof conversion function
- [ ] StructuredProofView component
- [ ] Step numbering (<n>m format)
- [ ] Collapsible levels
- [ ] View toggle switch

### Milestone 4: Polish
- [ ] Better error messages
- [ ] Proof export (LaTeX, ASCII)
- [ ] Save/load proofs (localStorage)
- [ ] Mobile responsive layout

---

## Example Sequents

```typescript
const examples = [
  { label: 'Identity', formula: '-- : P |- -- : P' },
  { label: 'Modus Ponens', formula: '-- : P, -- : P -o Q |- -- : Q' },
  { label: 'Tensor Identity', formula: '-- : P * Q |- -- : P * Q' },
  { label: 'Tensor Comm.', formula: '-- : P * Q |- -- : Q * P' },
  { label: 'With Elim', formula: '-- : A & B |- -- : A' },
  { label: 'Distribution', formula: '-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)' },
  { label: 'Currying', formula: '-- : (A * B) -o C |- -- : A -o (B -o C)' },
];
```

---

## References

### Sequent Calculus UIs
- [Calculus Toolbox Scala UI](https://goodlyrottenapple.github.io/calculus-toolbox/doc/scala-ui.html)
- [Logitext Tutorial](http://logitext.mit.edu/tutorial)
- [Proof Tree Builder Paper](https://joomy.korkutblech.com/papers/ptb.pdf)

### Lamport's Structured Proofs
- [How to Write a 21st Century Proof](https://lamport.azurewebsites.net/pubs/proof.pdf)
- [The Morning Paper summary](https://blog.acolyer.org/2015/01/12/how-to-write-a-21st-century-proof/)
- [TLA+ Proof System Tutorial](https://proofs.tlapl.us/doc/web/content/Documentation/Tutorial/Other_proof_constructs.html)
- [TLAPS Beginner's Experience](https://sriramsami.com/tlaps/)
