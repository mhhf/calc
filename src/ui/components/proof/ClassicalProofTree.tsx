import { For, Show, createMemo } from 'solid-js';
import KaTeX from '../math/KaTeX';
import { sequentToLatex, sequentToAscii, isProofComplete, type FocusInfo, type ProofTreeNode } from '../../lib/proofLogicV2';

interface ClassicalProofTreeProps {
  pt: ProofTreeNode;
  selectedPath: number[] | null;
  onNodeSelect: (path: number[]) => void;
  onRuleClick?: (node: ProofTreeNode) => void;
  currentPath?: number[];
}

/**
 * Classical bottom-up proof tree visualization.
 * Minimal design inspired by traditional proof theory notation.
 *
 * Structure:
 *     premise₁    premise₂
 *   ─────────────────────────── RuleName
 *          conclusion
 */
export default function ClassicalProofTree(props: ClassicalProofTreeProps) {
  const currentPath = () => props.currentPath || [];

  const isSelected = createMemo(() => {
    if (!props.selectedPath) return false;
    const cp = currentPath();
    if (cp.length !== props.selectedPath.length) return false;
    return cp.every((v, i) => v === props.selectedPath![i]);
  });

  const isUnproven = () => props.pt.type === '???';
  const isLeaf = () => props.pt.premisses.length === 0;
  const isNodeProven = createMemo(() => isProofComplete(props.pt));

  // Get focus info from delta_in if available
  const focusInfo = createMemo((): FocusInfo | undefined => {
    const deltaIn = props.pt.delta_in;
    if (!deltaIn || !deltaIn.focusPosition) return undefined;
    return {
      position: deltaIn.focusPosition as 'L' | 'R',
      id: deltaIn.focusId,
    };
  });

  const sequentLatex = createMemo(() => {
    try {
      return sequentToLatex(props.pt.conclusion, true, focusInfo());
    } catch {
      return props.pt.conclusion?.toString() || '?';
    }
  });

  const handleClick = () => {
    if (isUnproven()) {
      props.onNodeSelect(currentPath());
    }
  };

  // Axioms and proven rules get a line, unproven leaves (???) don't
  const showInferenceLine = () => props.pt.type !== '???';

  return (
    <div class="inference-rule">
      {/* Premises (above the line) - also shown empty for axioms */}
      <Show when={showInferenceLine()}>
        <div class="premisses">
          <For each={props.pt.premisses}>
            {(premise, index) => (
              <span
                class="formula"
                classList={{ 'pl-20': index() > 0 }}
              >
                <ClassicalProofTree
                  pt={premise}
                  selectedPath={props.selectedPath}
                  onNodeSelect={props.onNodeSelect}
                  onRuleClick={props.onRuleClick}
                  currentPath={[...currentPath(), index()]}
                />
              </span>
            )}
          </For>
        </div>
      </Show>

      {/* Inference line with rule name to the right */}
      <Show when={showInferenceLine()}>
        <div class="relative">
          <div class="border-b border-current" />
          <span
            class="absolute left-full top-1/2 -translate-y-1/2 pl-1 text-[0.7em] whitespace-nowrap text-gray-500 dark:text-gray-400 cursor-pointer hover:text-blue-600 dark:hover:text-blue-400"
            onClick={(e) => {
              e.stopPropagation();
              props.onRuleClick?.(props.pt);
            }}
          >
            <KaTeX latex={props.pt.type.replace(/_/g, '\\_')} />
          </span>
        </div>
      </Show>

      {/* Conclusion (below the line) */}
      <div class="conclusion text-center">
        <span
          class="formula rounded"
          classList={{
            'cursor-pointer clickable-sequent': isUnproven(),
            'bg-blue-100 dark:bg-blue-900/40': isSelected(),
            'opacity-50': isUnproven() && isLeaf(),
          }}
          onClick={handleClick}
        >
          <KaTeX latex={sequentLatex()} />
        </span>
      </div>
    </div>
  );
}
