import { createSignal, createMemo, Show, onMount, onCleanup } from 'solid-js';
import ErrorBoundary from '../components/common/ErrorBoundary';
import FormulaInput from '../components/math/FormulaInput';
import KaTeX from '../components/math/KaTeX';
import ClassicalProofTree from '../components/proof/ClassicalProofTree';
import StructuredProofView from '../components/proof/StructuredProofView';
import JsonProofView from '../components/proof/JsonProofView';
import AsciiProofTree from '../components/proof/AsciiProofTree';
import RuleSelector from '../components/proof/RuleSelector';
import ProofControls from '../components/proof/ProofControls';
import ContextSplitDialog from '../components/proof/ContextSplitDialog';
import RuleDetailDialog from '../components/proof/RuleDetailDialog';
import {
  parseSequent,
  createProofTree,
  isProofComplete,
  countNodes,
  getNodeAtPath,
  setNodeAtPath,
  cloneProofTree,
  getApplicableRules,
  applyRule,
  applyRuleWithSplit,
  applyFocusAction,
  applyBlurAction,
  autoProve,
  collapseFocusSteps,
  sequentToLatex,
  ptToStructuredProof,
  serializeProofTree,
  initBrowserRuleset,
  getContextEntries,
  getLinearContext,
  type ProofTreeNode,
  type ApplicableRule,
  type ContextEntry,
  getRuleApplicationDetails,
  type RuleApplicationDetails,
} from '../lib/proofLogicV2';

type ViewMode = 'tree' | 'structured' | 'ascii' | 'json';
type ProofMode = 'unfocused' | 'focused';

export default function ManualProof() {
  // Initialize ruleset on mount
  onMount(() => {
    initBrowserRuleset();
  });

  // Input state
  const [input, setInput] = createSignal('');
  const [error, setError] = createSignal<string | null>(null);

  // Proof state
  const [proofTree, setProofTree] = createSignal<ProofTreeNode | null>(null);
  const [selectedPath, setSelectedPath] = createSignal<number[] | null>(null);
  const [viewMode, setViewMode] = createSignal<ViewMode>('tree');
  const [proofMode, setProofMode] = createSignal<ProofMode>('unfocused');

  // History for undo/redo
  const [history, setHistory] = createSignal<ProofTreeNode[]>([]);
  const [historyIndex, setHistoryIndex] = createSignal(-1);

  // Context split dialog state
  const [splitDialogRule, setSplitDialogRule] = createSignal<ApplicableRule | null>(null);
  const [splitDialogPosition, setSplitDialogPosition] = createSignal<string | null>(null);
  // Also save the path at the time the dialog was opened
  const [splitDialogPath, setSplitDialogPath] = createSignal<number[] | null>(null);

  // Rule detail dialog state
  const [ruleDetailDialogData, setRuleDetailDialogData] = createSignal<RuleApplicationDetails | null>(null);

  // Computed values
  const isComplete = createMemo(() =>
    proofTree() ? isProofComplete(proofTree()!) : false
  );

  const nodeCounts = createMemo(() =>
    proofTree() ? countNodes(proofTree()!) : { proven: 0, unproven: 0 }
  );

  const selectedNode = createMemo(() => {
    const pt = proofTree();
    const path = selectedPath();
    if (!pt || !path) return null;
    return getNodeAtPath(pt, path);
  });

  // Node at the saved split dialog path (for when dialog is open)
  const splitDialogNode = createMemo(() => {
    const pt = proofTree();
    const path = splitDialogPath();
    if (!pt || !path) return null;
    return getNodeAtPath(pt, path);
  });

  // Get focus state from proof tree node (if any)
  const focusState = createMemo(() => {
    const node = selectedNode();
    if (!node) return null;
    // Focus info is stored in delta_in by applyRule for Focus actions
    const focusPosition = node.delta_in?.focusPosition;
    const focusId = node.delta_in?.focusId;
    if (!focusPosition) return null;
    return {
      position: focusPosition,
      id: focusId,
    };
  });

  const applicableRules = createMemo((): ApplicableRule[] => {
    const node = selectedNode();
    if (!node) return [];
    try {
      // SUCKLESS: Pass the node directly - it extracts focus from delta_in
      // No need to manually pass focusState
      return getApplicableRules(node, {
        mode: proofMode(),
      });
    } catch (e) {
      console.error('Error getting applicable rules:', e);
      return [];
    }
  });

  const structuredProof = createMemo(() => {
    const pt = proofTree();
    if (!pt) return null;
    return ptToStructuredProof(pt);
  });

  const serializedProof = createMemo(() => {
    const pt = proofTree();
    if (!pt) return null;
    return serializeProofTree(pt, proofMode());
  });

  // Push to history
  function pushHistory(pt: ProofTreeNode) {
    const idx = historyIndex();
    // Remove any future history if we're not at the end
    const newHistory = history().slice(0, idx + 1);
    newHistory.push(cloneProofTree(pt));
    setHistory(newHistory);
    setHistoryIndex(newHistory.length - 1);
  }

  // Start a new proof
  function startProof() {
    const inputStr = input().trim();
    if (!inputStr) {
      setError('Please enter a sequent');
      return;
    }

    try {
      const seq = parseSequent(inputStr);
      const pt = createProofTree(seq);
      setProofTree(pt);
      setSelectedPath(null);
      setError(null);
      setHistory([cloneProofTree(pt)]);
      setHistoryIndex(0);
    } catch (e: any) {
      setError(e.message || 'Failed to parse sequent');
      setProofTree(null);
    }
  }

  // Apply a rule
  function handleApplyRule(ruleName: string, position: string) {
    const pt = proofTree();
    const path = selectedPath();
    if (!pt || !path) return;

    const node = getNodeAtPath(pt, path);
    if (!node) return;

    // Find the rule in applicable rules to check if it's a splitting rule
    const rules = applicableRules();
    const rule = rules.find(r => r.name === ruleName && r.position === position);

    // Check if this is a context-splitting rule with resources to distribute
    if (rule?.splitContext) {
      const entries = getContextEntries(node.conclusion, undefined, rule._apiAction);
      if (entries.length > 0) {
        setSplitDialogRule(rule);
        setSplitDialogPosition(position);
        setSplitDialogPath(path);
        return;
      }
    }

    applyRuleDirectly(ruleName, position);
  }

  // Apply rule without showing split dialog (uses selectedPath)
  function applyRuleDirectly(ruleName: string, position: string) {
    const path = selectedPath();
    if (!path) return;
    applyRuleAtPath(ruleName, position, path);
  }

  // Apply rule at a specific path (can be used with saved path)
  function applyRuleAtPath(ruleName: string, position: string, path: number[]) {
    const pt = proofTree();
    if (!pt) return;

    const node = getNodeAtPath(pt, path);
    if (!node) return;

    // Verify position exists for left rules (v2 uses index-based positions)
    if (position !== 'R') {
      const idx = parseInt(position, 10);
      const linear = getLinearContext(node.conclusion);
      if (isNaN(idx) || idx < 0 || idx >= linear.length) {
        console.error('applyRuleAtPath: position not found:', position);
        console.error('Available indices:', linear.length);
        setError('The selected formula is no longer available. Please try again.');
        return;
      }
    }

    try {
      let newNode: ProofTreeNode | null = null;

      // Handle focus mode special actions
      if (proofMode() === 'focused') {
        if (ruleName === 'Focus' || ruleName === 'Focus_L' || ruleName === 'Focus_R') {
          // Focus action - handled by applyRule which stores focus info in delta_in
          newNode = applyRule(node, ruleName, position);
        } else if (ruleName === 'Blur') {
          // Blur action - clear focus state
          newNode = applyBlurAction(node);
        } else if (ruleName === 'Id+' || ruleName === 'Id-') {
          // Identity with explicit polarity
          newNode = applyRule(node, 'Id', position);
          if (newNode) {
            newNode.type = ruleName; // Show Id+ or Id- instead of Id
          }
        } else {
          // Regular rule in focused mode
          newNode = applyRule(node, ruleName, position);
        }
      } else {
        // Unfocused mode - direct rule application
        newNode = applyRule(node, ruleName, position);
      }

      if (newNode) {
        const newTree = setNodeAtPath(pt, path, newNode);
        setProofTree(newTree);
        pushHistory(newTree);
        setSelectedPath(null);  // Close modal, user clicks on next node to continue
      } else {
        setError('Failed to apply rule');
      }
    } catch (e: any) {
      console.error('Error applying rule:', e);
      setError(e.message || 'Failed to apply rule');
    }
  }

  // Apply rule with custom context split
  function handleApplyWithSplit(splits: { premise1: string[]; premise2: string[] }) {
    const pt = proofTree();
    const rule = splitDialogRule();
    const position = splitDialogPosition();
    // Use the saved path from when the dialog was opened
    const path = splitDialogPath();

    if (!pt || !path || !rule || !position) return;

    const node = getNodeAtPath(pt, path);
    if (!node) return;

    // Verify the position still exists in this node's linear context (v2 uses indices)
    if (position !== 'R') {
      const idx = parseInt(position, 10);
      const linear = getLinearContext(node.conclusion);
      if (isNaN(idx) || idx < 0 || idx >= linear.length) {
        console.error('Position no longer valid in node:', position);
        console.error('Available indices:', linear.length);
        setError('The selected formula is no longer available. Please try again.');
        setSplitDialogRule(null);
        setSplitDialogPosition(null);
        setSplitDialogPath(null);
        return;
      }
    }

    try {
      const newNode = applyRuleWithSplit(node, rule.name, position, splits, rule._apiAction);

      if (newNode) {
        const newTree = setNodeAtPath(pt, path, newNode);
        setProofTree(newTree);
        pushHistory(newTree);
        setSelectedPath(null);
      } else {
        setError('Failed to apply rule with split');
      }
    } catch (e: any) {
      console.error('Error applying rule with split:', e);
      setError(e.message || 'Failed to apply rule with split');
    }

    // Close dialog
    setSplitDialogRule(null);
    setSplitDialogPosition(null);
    setSplitDialogPath(null);
  }

  // Auto-split: apply the rule and let the prover figure out the distribution
  function handleAutoSplit() {
    const rule = splitDialogRule();
    const position = splitDialogPosition();
    const savedPath = splitDialogPath();

    if (!rule || !position || !savedPath) return;

    // Close dialog first
    setSplitDialogRule(null);
    setSplitDialogPosition(null);
    setSplitDialogPath(null);

    // Apply using the saved path
    applyRuleAtPath(rule.name, position, savedPath);
  }

  // Close split dialog
  function handleCancelSplit() {
    setSplitDialogRule(null);
    setSplitDialogPosition(null);
    setSplitDialogPath(null);
  }

  // Handle rule label click - show details dialog
  function handleRuleClick(node: ProofTreeNode) {
    const details = getRuleApplicationDetails(node);
    setRuleDetailDialogData(details);
  }

  // Handle rule click from structured view (uses path to find node)
  function handleStructuredRuleClick(step: { path: number[] }) {
    const pt = proofTree();
    if (!pt) return;
    const node = getNodeAtPath(pt, step.path);
    if (node) {
      handleRuleClick(node);
    }
  }

  // Auto-complete selected node or entire tree
  async function handleAutoComplete() {
    const pt = proofTree();
    const path = selectedPath();

    // If a node is selected, auto-prove that subtree
    const targetPt = path && pt ? getNodeAtPath(pt, path) : pt;
    if (!targetPt) return;

    try {
      // In unfocused mode, hide focus steps from the result
      const hideFocusSteps = proofMode() === 'unfocused';
      const result = await autoProve(targetPt, { hideFocusSteps });

      if (result.success) {
        if (path && pt) {
          const newTree = setNodeAtPath(pt, path, result.pt);
          setProofTree(newTree);
          pushHistory(newTree);
        } else {
          setProofTree(result.pt);
          pushHistory(result.pt);
        }
        setSelectedPath(null);
        setError(null);
      } else {
        setError('Auto-complete could not find a proof');
      }
    } catch (e: any) {
      console.error('Auto-complete error:', e);
      setError(e.message || 'Auto-complete failed');
    }
  }

  // Undo
  function handleUndo() {
    const idx = historyIndex();
    if (idx > 0) {
      setHistoryIndex(idx - 1);
      setProofTree(cloneProofTree(history()[idx - 1]));
      setSelectedPath(null);
    }
  }

  // Redo
  function handleRedo() {
    const idx = historyIndex();
    const hist = history();
    if (idx < hist.length - 1) {
      setHistoryIndex(idx + 1);
      setProofTree(cloneProofTree(hist[idx + 1]));
      setSelectedPath(null);
    }
  }

  // Reset proof
  function handleReset() {
    const hist = history();
    if (hist.length > 0) {
      setProofTree(cloneProofTree(hist[0]));
      setHistory([cloneProofTree(hist[0])]);
      setHistoryIndex(0);
      setSelectedPath(null);
    }
  }

  // Keyboard shortcuts
  function handleKeyDown(e: KeyboardEvent) {
    if ((e.ctrlKey || e.metaKey) && e.key === 'z') {
      e.preventDefault();
      if (e.shiftKey) {
        handleRedo();
      } else {
        handleUndo();
      }
    }
    if ((e.ctrlKey || e.metaKey) && e.key === 'y') {
      e.preventDefault();
      handleRedo();
    }
    if (e.key === 'Escape') {
      setSelectedPath(null);
    }
  }

  onMount(() => {
    if (typeof document !== 'undefined') {
      document.addEventListener('keydown', handleKeyDown);
    }
  });

  onCleanup(() => {
    if (typeof document !== 'undefined') {
      document.removeEventListener('keydown', handleKeyDown);
    }
  });

  // Example sequents
  const examples = [
    { label: 'Identity', formula: '-- : P |- -- : P' },
    { label: 'Modus Ponens', formula: '-- : P, -- : P -o Q |- -- : Q' },
    { label: 'Tensor Identity', formula: '-- : P * Q |- -- : P * Q' },
    { label: 'Tensor Comm.', formula: '-- : P * Q |- -- : Q * P' },
    { label: 'With Elim', formula: '-- : A & B |- -- : A' },
    { label: 'Distribution', formula: '-- : P -o (R & Q) |- -- : (P -o Q) & (P -o R)' },
  ];

  return (
    <ErrorBoundary>
      <div class="max-w-6xl mx-auto p-6 space-y-6 text-gray-900 dark:text-gray-100">
        {/* Header */}
        <div>
          <h2 class="text-2xl font-bold text-gray-900 dark:text-white mb-2">
            Interactive Proof
          </h2>
          <p class="text-gray-600 dark:text-gray-400">
            Construct proofs step-by-step. Click on an unproven sequent to see applicable rules.
          </p>
        </div>

        {/* Input section */}
        <div class="bg-white dark:bg-gray-800 rounded-lg p-4 shadow-sm border border-gray-200 dark:border-gray-700 text-gray-900 dark:text-gray-100">
          <FormulaInput
            value={input()}
            onInput={setInput}
            error={error()}
            placeholder="Enter a sequent (e.g., -- : P, -- : P -o Q |- -- : Q)"
          />

          {/* Example buttons */}
          <div class="flex flex-wrap gap-2 mt-3">
            <span class="text-sm text-gray-500 dark:text-gray-400">Examples:</span>
            {examples.map((ex) => (
              <button
                onClick={() => setInput(ex.formula)}
                class="px-2 py-1 text-xs bg-gray-100 dark:bg-gray-700 text-gray-700 dark:text-gray-300 rounded hover:bg-gray-200 dark:hover:bg-gray-600 transition-colors"
                title={ex.label}
              >
                {ex.label}
              </button>
            ))}
          </div>

          {/* Start button */}
          <div class="mt-4 flex gap-2">
            <button
              onClick={startProof}
              class="px-4 py-2 bg-blue-600 text-white rounded-lg hover:bg-blue-700 transition-colors font-medium"
            >
              Start Proof
            </button>
            <Show when={proofTree() && !isComplete()}>
              <button
                onClick={handleAutoComplete}
                class="px-4 py-2 bg-green-600 text-white rounded-lg hover:bg-green-700 transition-colors font-medium flex items-center gap-2"
              >
                <svg class="w-4 h-4" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M13 10V3L4 14h7v7l9-11h-7z" />
                </svg>
                Auto-complete All
              </button>
            </Show>
          </div>
        </div>

        {/* Proof area */}
        <Show when={proofTree()}>
          {/* Controls */}
          <ProofControls
            onUndo={handleUndo}
            onRedo={handleRedo}
            onReset={handleReset}
            canUndo={historyIndex() > 0}
            canRedo={historyIndex() < history().length - 1}
            provenCount={nodeCounts().proven}
            unprovenCount={nodeCounts().unproven}
            isComplete={isComplete()}
          />

          {/* Mode and View toggles */}
          <div class="flex items-center gap-6 flex-wrap">
            {/* Proof mode toggle */}
            <div class="flex items-center gap-2">
              <span class="text-sm text-gray-500 dark:text-gray-400">Mode:</span>
              <div class="flex rounded-lg overflow-hidden border border-gray-200 dark:border-gray-700">
                <button
                  onClick={() => setProofMode('unfocused')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-purple-600 text-white': proofMode() === 'unfocused',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': proofMode() !== 'unfocused',
                  }}
                  title="Direct rule application without focusing (for learning the calculus)"
                >
                  Unfocused
                </button>
                <button
                  onClick={() => setProofMode('focused')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-purple-600 text-white': proofMode() === 'focused',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': proofMode() !== 'focused',
                  }}
                  title="Show focusing steps in proof search (for learning proof search)"
                >
                  Focused
                </button>
              </div>
            </div>

            {/* View toggle */}
            <div class="flex items-center gap-2">
              <span class="text-sm text-gray-500 dark:text-gray-400">View:</span>
              <div class="flex rounded-lg overflow-hidden border border-gray-200 dark:border-gray-700">
                <button
                  onClick={() => setViewMode('tree')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-blue-600 text-white': viewMode() === 'tree',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': viewMode() !== 'tree',
                  }}
                >
                  Tree
                </button>
                <button
                  onClick={() => setViewMode('structured')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-blue-600 text-white': viewMode() === 'structured',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': viewMode() !== 'structured',
                  }}
                >
                  Structured
                </button>
                <button
                  onClick={() => setViewMode('ascii')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-blue-600 text-white': viewMode() === 'ascii',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': viewMode() !== 'ascii',
                  }}
                  title="View proof as ASCII text"
                >
                  ASCII
                </button>
                <button
                  onClick={() => setViewMode('json')}
                  class="px-3 py-1.5 text-sm font-medium transition-colors"
                  classList={{
                    'bg-blue-600 text-white': viewMode() === 'json',
                    'bg-white dark:bg-gray-800 text-gray-700 dark:text-gray-300 hover:bg-gray-100 dark:hover:bg-gray-700': viewMode() !== 'json',
                  }}
                  title="View proof as JSON (for export/debugging)"
                >
                  JSON
                </button>
              </div>
            </div>
          </div>

          {/* Proof display */}
          <div class="bg-white dark:bg-gray-800 rounded-lg p-6 shadow-sm border border-gray-200 dark:border-gray-700 overflow-x-auto text-gray-900 dark:text-gray-100">
            <Show when={viewMode() === 'tree'}>
              <div class="flex justify-center min-w-fit">
                <ClassicalProofTree
                  pt={proofTree()!}
                  selectedPath={selectedPath()}
                  onNodeSelect={setSelectedPath}
                  onRuleClick={handleRuleClick}
                />
              </div>
            </Show>
            <Show when={viewMode() === 'structured' && structuredProof()}>
              <StructuredProofView
                rootStep={structuredProof()!}
                selectedPath={selectedPath()}
                onNodeSelect={setSelectedPath}
                onRuleClick={handleStructuredRuleClick}
              />
            </Show>
            <Show when={viewMode() === 'ascii' && serializedProof()}>
              <AsciiProofTree proof={serializedProof()!} />
            </Show>
            <Show when={viewMode() === 'json' && serializedProof()}>
              <JsonProofView proof={serializedProof()!} />
            </Show>
          </div>

          {/* Completion message */}
          <Show when={isComplete()}>
            <div class="bg-green-50 dark:bg-green-900/20 border border-green-200 dark:border-green-800 rounded-lg p-4 text-center">
              <div class="flex items-center justify-center gap-2 text-green-700 dark:text-green-400">
                <svg class="w-6 h-6" fill="none" viewBox="0 0 24 24" stroke="currentColor">
                  <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M9 12l2 2 4-4m6 2a9 9 0 11-18 0 9 9 0 0118 0z" />
                </svg>
                <span class="text-lg font-semibold">Proof Complete!</span>
              </div>
              <p class="text-green-600 dark:text-green-500 text-sm mt-1">
                All branches have been closed.
              </p>
            </div>
          </Show>
        </Show>

        {/* Empty state */}
        <Show when={!proofTree() && !error()}>
          <div class="text-center py-12 text-gray-500 dark:text-gray-400">
            <svg class="w-16 h-16 mx-auto mb-4 opacity-50" fill="none" viewBox="0 0 24 24" stroke="currentColor">
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="1.5" d="M9 5H7a2 2 0 00-2 2v12a2 2 0 002 2h10a2 2 0 002-2V7a2 2 0 00-2-2h-2M9 5a2 2 0 002 2h2a2 2 0 002-2M9 5a2 2 0 012-2h2a2 2 0 012 2" />
            </svg>
            <p>Enter a sequent above and click "Start Proof" to begin.</p>
          </div>
        </Show>

        {/* Rule selector modal */}
        <Show when={selectedPath() && selectedNode() && !splitDialogRule()}>
          <RuleSelector
            sequentLatex={sequentToLatex(selectedNode()!.conclusion)}
            applicableRules={applicableRules()}
            onApply={handleApplyRule}
            onCancel={() => setSelectedPath(null)}
            onAutoComplete={handleAutoComplete}
          />
        </Show>

        {/* Context split dialog */}
        <Show when={splitDialogRule() && splitDialogNode()}>
          <ContextSplitDialog
            rule={splitDialogRule()!}
            contextEntries={getContextEntries(
              splitDialogNode()!.conclusion,
              undefined,  // Don't manually exclude - API already computed correct entries
              splitDialogRule()!._apiAction  // Use API's pre-computed contextEntries
            )}
            currentSequent={splitDialogNode()!.conclusion}
            position={splitDialogPosition()!}
            onApply={handleApplyWithSplit}
            onCancel={handleCancelSplit}
            onAutoSplit={handleAutoSplit}
          />
        </Show>

        {/* Rule detail dialog */}
        <RuleDetailDialog
          details={ruleDetailDialogData()}
          onClose={() => setRuleDetailDialogData(null)}
        />
      </div>
    </ErrorBoundary>
  );
}
