/**
 * EmbedProve — an embeddable proof exercise for book chapters.
 *
 * Markdown usage:
 *   ```{prove}
 *   goal: P, P -o Q |- Q
 *   rules: id, loli_l          (optional — restrict the palette)
 *   mode: unfocused            (optional — unfocused | focused)
 *   hint: Use the implication. (optional)
 *   id: ch2-modus-ponens       (optional — records exercise progress)
 *   title: Modus ponens        (optional)
 *   ```
 *
 * Same proof machinery as the /prove page (proofLogic + ManualProofAPI),
 * scoped to one goal sequent with success detection.
 */
import { createSignal, createMemo, createEffect, Show, onMount } from 'solid-js';
import ErrorBoundary from '../common/ErrorBoundary';
import ClassicalProofTree from '../proof/ClassicalProofTree';
import RuleSelector from '../proof/RuleSelector';
import ContextSplitDialog from '../proof/ContextSplitDialog';
import RuleDetailDialog from '../proof/RuleDetailDialog';
import { markExercise, isExerciseDone } from '../../state/progress';
import { parseSpecBody, type WidgetProps } from '../../lib/hydrateWidgets';
import {
  parseSequent,
  createProofTree,
  isProofComplete,
  getNodeAtPath,
  setNodeAtPath,
  cloneProofTree,
  getApplicableRules,
  applyRule,
  applyRuleWithSplit,
  autoProve,
  sequentToLatex,
  initBrowserRuleset,
  getContextEntries,
  getLinearContext,
  getRuleApplicationDetails,
  type ProofTreeNode,
  type ApplicableRule,
  type RuleApplicationDetails,
} from '../../lib/proofLogic';

const SPEC_KEYS = ['goal', 'rules', 'mode', 'hint', 'id', 'title'];

export default function EmbedProve(props: WidgetProps) {
  const spec = parseSpecBody(props.body, SPEC_KEYS);
  const goal = (spec.goal || '').trim();
  const allowedRules = spec.rules
    ? new Set(spec.rules.split(',').map(s => s.trim()).filter(Boolean))
    : null;
  const mode = spec.mode === 'focused' ? 'focused' : 'unfocused';
  const exerciseId = spec.id?.trim();

  const [proofTree, setProofTree] = createSignal<ProofTreeNode | null>(null);
  const [selectedPath, setSelectedPath] = createSignal<number[] | null>(null);
  const [history, setHistory] = createSignal<ProofTreeNode[]>([]);
  const [historyIndex, setHistoryIndex] = createSignal(-1);
  const [error, setError] = createSignal<string | null>(null);
  const [showHint, setShowHint] = createSignal(false);
  const [splitDialogRule, setSplitDialogRule] = createSignal<ApplicableRule | null>(null);
  const [splitDialogPosition, setSplitDialogPosition] = createSignal<string | null>(null);
  const [splitDialogPath, setSplitDialogPath] = createSignal<number[] | null>(null);
  const [ruleDetail, setRuleDetail] = createSignal<RuleApplicationDetails | null>(null);

  function start() {
    try {
      initBrowserRuleset();
      const seq = parseSequent(goal);
      const pt = createProofTree(seq);
      setProofTree(pt);
      setHistory([cloneProofTree(pt)]);
      setHistoryIndex(0);
      setSelectedPath(null);
      setError(null);
    } catch (e: any) {
      setError(e.message || 'Failed to parse goal sequent');
    }
  }

  onMount(start);

  const isComplete = createMemo(() => (proofTree() ? isProofComplete(proofTree()!) : false));

  // Record exercise progress once the proof closes.
  createEffect(() => {
    if (isComplete() && exerciseId) markExercise(props.slug, exerciseId);
  });

  const selectedNode = createMemo(() => {
    const pt = proofTree();
    const path = selectedPath();
    if (!pt || !path) return null;
    return getNodeAtPath(pt, path);
  });

  const splitDialogNode = createMemo(() => {
    const pt = proofTree();
    const path = splitDialogPath();
    if (!pt || !path) return null;
    return getNodeAtPath(pt, path);
  });

  const applicableRules = createMemo((): ApplicableRule[] => {
    const node = selectedNode();
    if (!node) return [];
    try {
      let rules = getApplicableRules(node, { mode });
      if (allowedRules) {
        rules = rules.filter(r => allowedRules.has(r.name) || r.category === 'Focus');
      }
      return rules;
    } catch (e) {
      console.error('EmbedProve: applicable rules failed', e);
      return [];
    }
  });

  function pushHistory(pt: ProofTreeNode) {
    const idx = historyIndex();
    const next = history().slice(0, idx + 1);
    next.push(cloneProofTree(pt));
    setHistory(next);
    setHistoryIndex(next.length - 1);
  }

  function applyRuleAtPath(ruleName: string, position: string, path: number[]) {
    const pt = proofTree();
    if (!pt) return;
    const node = getNodeAtPath(pt, path);
    if (!node) return;
    if (position !== 'R') {
      const idx = parseInt(position, 10);
      const linear = getLinearContext(node.conclusion);
      if (isNaN(idx) || idx < 0 || idx >= linear.length) {
        setError('The selected formula is no longer available. Try again.');
        return;
      }
    }
    try {
      const rule = applicableRules().find(r => r.name === ruleName && r.position === position);
      const newNode = applyRule(node, ruleName, position, rule?._apiAction);
      if (newNode) {
        const newTree = setNodeAtPath(pt, path, newNode);
        setProofTree(newTree);
        pushHistory(newTree);
        setSelectedPath(null);
        setError(null);
      } else {
        setError('Failed to apply rule');
      }
    } catch (e: any) {
      setError(e.message || 'Failed to apply rule');
    }
  }

  function handleApplyRule(ruleName: string, position: string) {
    const pt = proofTree();
    const path = selectedPath();
    if (!pt || !path) return;
    const node = getNodeAtPath(pt, path);
    if (!node) return;
    const rule = applicableRules().find(r => r.name === ruleName && r.position === position);
    if (rule?.splitContext) {
      const entries = getContextEntries(node.conclusion, undefined, rule._apiAction);
      if (entries.length > 0) {
        setSplitDialogRule(rule);
        setSplitDialogPosition(position);
        setSplitDialogPath(path);
        return;
      }
    }
    applyRuleAtPath(ruleName, position, path);
  }

  function closeSplitDialog() {
    setSplitDialogRule(null);
    setSplitDialogPosition(null);
    setSplitDialogPath(null);
  }

  function handleApplyWithSplit(splits: { premise1: string[]; premise2: string[] }) {
    const pt = proofTree();
    const rule = splitDialogRule();
    const position = splitDialogPosition();
    const path = splitDialogPath();
    if (!pt || !path || !rule || !position) return;
    const node = getNodeAtPath(pt, path);
    if (!node) { closeSplitDialog(); return; }
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
      setError(e.message || 'Failed to apply rule with split');
    }
    closeSplitDialog();
  }

  function handleAutoSplit() {
    const rule = splitDialogRule();
    const position = splitDialogPosition();
    const path = splitDialogPath();
    closeSplitDialog();
    if (rule && position && path) applyRuleAtPath(rule.name, position, path);
  }

  async function handleAutoComplete() {
    const pt = proofTree();
    const path = selectedPath();
    const target = path && pt ? getNodeAtPath(pt, path) : pt;
    if (!target) return;
    try {
      const result = await autoProve(target, { hideFocusSteps: mode === 'unfocused' });
      if (result.success) {
        const newTree = path && pt ? setNodeAtPath(pt, path, result.pt) : result.pt;
        setProofTree(newTree);
        pushHistory(newTree);
        setSelectedPath(null);
        setError(null);
      } else {
        setError('No proof found from here — this branch may be unprovable.');
      }
    } catch (e: any) {
      setError(e.message || 'Auto-complete failed');
    }
  }

  function handleUndo() {
    const idx = historyIndex();
    if (idx > 0) {
      setHistoryIndex(idx - 1);
      setProofTree(cloneProofTree(history()[idx - 1]));
      setSelectedPath(null);
    }
  }

  function handleReset() {
    const hist = history();
    if (hist.length > 0) {
      setProofTree(cloneProofTree(hist[0]));
      setHistory([cloneProofTree(hist[0])]);
      setHistoryIndex(0);
      setSelectedPath(null);
      setError(null);
    }
  }

  return (
    <ErrorBoundary>
      <div class="embed-prove not-prose my-6 rounded-lg border border-indigo-200 dark:border-indigo-900 bg-indigo-50/40 dark:bg-indigo-950/20 overflow-hidden">
        {/* Header */}
        <div class="flex items-center justify-between px-4 py-2 bg-indigo-100/60 dark:bg-indigo-900/30 border-b border-indigo-200 dark:border-indigo-900">
          <div class="flex items-center gap-2 min-w-0">
            <span class="text-xs font-semibold uppercase tracking-wide text-indigo-700 dark:text-indigo-300 shrink-0">
              {spec.title || 'Prove it'}
            </span>
            <Show when={exerciseId && isExerciseDone(props.slug, exerciseId!)}>
              <span class="text-xs text-green-600 dark:text-green-400">✓ done</span>
            </Show>
          </div>
          <div class="flex items-center gap-1.5">
            <Show when={spec.hint}>
              <button
                onClick={() => setShowHint(!showHint())}
                class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 text-gray-600 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-gray-700"
              >
                {showHint() ? 'Hide hint' : 'Hint'}
              </button>
            </Show>
            <button
              onClick={handleUndo}
              disabled={historyIndex() <= 0}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 text-gray-600 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-gray-700 disabled:opacity-40"
            >
              Undo
            </button>
            <button
              onClick={handleReset}
              class="px-2 py-0.5 text-xs rounded bg-white dark:bg-gray-800 border border-gray-200 dark:border-gray-700 text-gray-600 dark:text-gray-300 hover:bg-gray-50 dark:hover:bg-gray-700"
            >
              Reset
            </button>
          </div>
        </div>

        {/* Hint */}
        <Show when={showHint() && spec.hint}>
          <div class="px-4 py-2 text-sm text-amber-800 dark:text-amber-200 bg-amber-50 dark:bg-amber-900/20 border-b border-amber-200 dark:border-amber-800">
            {spec.hint}
          </div>
        </Show>

        {/* Error */}
        <Show when={error()}>
          <div class="px-4 py-2 text-sm text-red-700 dark:text-red-300 bg-red-50 dark:bg-red-900/20 border-b border-red-200 dark:border-red-800">
            {error()}
          </div>
        </Show>

        {/* Proof area */}
        <div class="p-4 overflow-x-auto">
          <Show
            when={proofTree()}
            fallback={<div class="text-sm text-gray-500">Goal: <code>{goal}</code></div>}
          >
            <div class="flex justify-center min-w-fit">
              <ClassicalProofTree
                pt={proofTree()!}
                selectedPath={selectedPath()}
                onNodeSelect={setSelectedPath}
                onRuleClick={(node) => setRuleDetail(getRuleApplicationDetails(node))}
              />
            </div>
          </Show>
        </div>

        {/* Footer */}
        <Show
          when={isComplete()}
          fallback={
            <div class="px-4 py-2 text-xs text-gray-500 dark:text-gray-400 border-t border-indigo-200 dark:border-indigo-900">
              Click an unproven sequent (marked <span class="font-mono">???</span>) to choose a rule.
            </div>
          }
        >
          <div class="px-4 py-3 text-center bg-green-50 dark:bg-green-900/20 border-t border-green-200 dark:border-green-800">
            <span class="text-green-700 dark:text-green-400 font-semibold">✓ Proof complete!</span>
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
              undefined,
              splitDialogRule()!._apiAction
            )}
            currentSequent={splitDialogNode()!.conclusion}
            position={splitDialogPosition()!}
            onApply={handleApplyWithSplit}
            onCancel={closeSplitDialog}
            onAutoSplit={handleAutoSplit}
          />
        </Show>

        {/* Rule detail dialog */}
        <RuleDetailDialog details={ruleDetail()} onClose={() => setRuleDetail(null)} />
      </div>
    </ErrorBoundary>
  );
}
