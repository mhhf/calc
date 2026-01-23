import { For, Show, createMemo } from 'solid-js';
import ProofNode from './ProofNode';
import InferenceLine from './InferenceLine';
import { sequentToLatex, sequentToAscii, isProofComplete, FocusInfo } from '../../lib/proofLogic';

interface ProofTreeNode {
  conclusion: any;
  premisses: ProofTreeNode[];
  type: string;
  proven: boolean;
  proverState?: { focusPosition: 'L' | 'R' | null; focusId: string | null } | null;
}

interface ClassicalProofTreeProps {
  pt: ProofTreeNode;
  selectedPath: number[] | null;
  onNodeSelect: (path: number[]) => void;
  currentPath?: number[];
}

/**
 * Classical bottom-up proof tree visualization.
 * Conclusion at bottom, premises above, connected by inference lines.
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

  // Get focus info from prover state if available
  const focusInfo = createMemo((): FocusInfo | undefined => {
    const state = props.pt.proverState;
    if (!state || !state.focusPosition) return undefined;
    return {
      position: state.focusPosition as 'L' | 'R',
      id: state.focusId,
    };
  });

  const sequentLatex = createMemo(() => {
    try {
      return sequentToLatex(props.pt.conclusion, true, focusInfo());
    } catch {
      return props.pt.conclusion?.toString() || '?';
    }
  });

  const sequentAscii = createMemo(() => {
    try {
      return sequentToAscii(props.pt.conclusion);
    } catch {
      return props.pt.conclusion?.toString() || '?';
    }
  });

  const handleClick = () => {
    // Only allow clicking on unproven leaf nodes
    if (isUnproven()) {
      props.onNodeSelect(currentPath());
    }
  };

  return (
    <div class="flex flex-col items-center">
      {/* Premises (rendered above) */}
      <Show when={props.pt.premisses.length > 0}>
        <div class="flex gap-6 items-end mb-1">
          <For each={props.pt.premisses}>
            {(premise, index) => (
              <ClassicalProofTree
                pt={premise}
                selectedPath={props.selectedPath}
                onNodeSelect={props.onNodeSelect}
                currentPath={[...currentPath(), index()]}
              />
            )}
          </For>
        </div>

        {/* Inference line */}
        <InferenceLine ruleName={props.pt.type} />
      </Show>

      {/* Conclusion (this node) */}
      <ProofNode
        sequentLatex={sequentLatex()}
        sequentAscii={sequentAscii()}
        ruleName={props.pt.type}
        isLeaf={isLeaf()}
        isProven={isNodeProven()}
        isSelected={isSelected()}
        isClickable={isUnproven()}
        onClick={handleClick}
      />
    </div>
  );
}
