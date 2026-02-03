import { For, Show, createSignal } from 'solid-js';
import KaTeX from '../math/KaTeX';
import { type StructuredStep, type ProofTreeNode } from '../../lib/proofLogicV2';

interface StructuredProofViewProps {
  rootStep: StructuredStep;
  selectedPath: number[] | null;
  onNodeSelect: (path: number[]) => void;
  onRuleClick?: (step: StructuredStep) => void;
}

/**
 * Lamport-style structured proof view with hierarchical numbered steps.
 * Interactive - clicking on unproven steps selects them for rule application.
 */
export default function StructuredProofView(props: StructuredProofViewProps) {
  return (
    <div class="font-mono text-sm space-y-1 bg-white dark:bg-gray-800 rounded-lg p-4 border border-gray-200 dark:border-gray-700">
      {/* Goal header */}
      <div class="mb-4 pb-2 border-b border-gray-200 dark:border-gray-700">
        <span class="font-bold text-gray-700 dark:text-gray-300">GOAL: </span>
        <KaTeX latex={props.rootStep.sequentLatex} />
      </div>

      {/* Proof steps */}
      <StepRow
        step={props.rootStep}
        selectedPath={props.selectedPath}
        onNodeSelect={props.onNodeSelect}
        onRuleClick={props.onRuleClick}
      />
    </div>
  );
}

interface StepRowProps {
  step: StructuredStep;
  selectedPath: number[] | null;
  onNodeSelect: (path: number[]) => void;
  onRuleClick?: (step: StructuredStep) => void;
}

function StepRow(props: StepRowProps) {
  const [collapsed, setCollapsed] = createSignal(false);

  const indent = () => (props.step.level - 1) * 24;

  const isSelected = () => {
    if (!props.selectedPath) return false;
    if (props.step.path.length !== props.selectedPath.length) return false;
    return props.step.path.every((v, i) => v === props.selectedPath![i]);
  };

  const isUnproven = () => props.step.ruleName === '???';
  const hasChildren = () => props.step.children.length > 0;

  const handleClick = () => {
    if (isUnproven()) {
      props.onNodeSelect(props.step.path);
    }
  };

  const stepLabel = () => `<${props.step.level}>${props.step.step}.`;

  return (
    <div>
      {/* This step */}
      <div
        class="flex items-start gap-2 py-1 px-2 rounded -mx-2 transition-colors"
        style={{ "padding-left": `${indent() + 8}px` }}
        classList={{
          'bg-blue-100 dark:bg-blue-900/30': isSelected(),
          'hover:bg-gray-100 dark:hover:bg-gray-700/50 cursor-pointer': isUnproven(),
        }}
        onClick={handleClick}
      >
        {/* Collapse toggle for non-leaf nodes */}
        <Show
          when={hasChildren()}
          fallback={<span class="w-4" />}
        >
          <button
            class="w-4 h-4 flex items-center justify-center text-gray-400 hover:text-gray-600"
            onClick={(e) => {
              e.stopPropagation();
              setCollapsed(!collapsed());
            }}
          >
            <svg
              class="w-3 h-3 transition-transform"
              classList={{ '-rotate-90': collapsed() }}
              fill="none"
              viewBox="0 0 24 24"
              stroke="currentColor"
            >
              <path stroke-linecap="round" stroke-linejoin="round" stroke-width="2" d="M19 9l-7 7-7-7" />
            </svg>
          </button>
        </Show>

        {/* Step number */}
        <span class="text-blue-600 dark:text-blue-400 font-bold whitespace-nowrap">
          {stepLabel()}
        </span>

        {/* Sequent */}
        <div class="flex-1">
          <KaTeX latex={props.step.sequentLatex} />
        </div>

        {/* Justification / status */}
        <span
          class="ml-2 whitespace-nowrap"
          classList={{
            'text-gray-500 dark:text-gray-400': !isUnproven(),
            'text-blue-500 dark:text-blue-400': isUnproven(),
          }}
        >
          <Show
            when={props.step.ruleName !== '???'}
            fallback={
              <span class="italic">
                (click to prove)
              </span>
            }
          >
            <span
              class="cursor-pointer hover:text-blue-600 dark:hover:text-blue-400"
              onClick={(e) => {
                e.stopPropagation();
                props.onRuleClick?.(props.step);
              }}
            >
              BY {props.step.ruleName}
            </span>
            <Show when={props.step.isProven}>
              <span class="ml-1 text-green-500">✓</span>
            </Show>
          </Show>
        </span>
      </div>

      {/* Children (sub-steps) */}
      <Show when={!collapsed() && hasChildren()}>
        <For each={props.step.children}>
          {(child) => (
            <StepRow
              step={child}
              selectedPath={props.selectedPath}
              onNodeSelect={props.onNodeSelect}
              onRuleClick={props.onRuleClick}
            />
          )}
        </For>

        {/* QED step */}
        <div
          class="flex items-center gap-2 py-1 px-2 text-gray-500 dark:text-gray-400"
          style={{ "padding-left": `${indent() + 32}px` }}
        >
          <span class="w-4" />
          <span class="text-blue-600 dark:text-blue-400 font-bold">
            {`<${props.step.level}>${props.step.children.length + 1}.`}
          </span>
          <span>QED</span>
          <Show when={props.step.isProven}>
            <span class="text-green-500">✓</span>
          </Show>
        </div>
      </Show>
    </div>
  );
}
