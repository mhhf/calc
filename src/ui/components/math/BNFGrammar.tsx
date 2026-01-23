import { For, Show, createMemo } from 'solid-js';
import KaTeX from './KaTeX';

interface BNFProduction {
  sort: string;
  metavar: string;
  constructors: {
    name: string;
    ascii: string;
    latex: string;
    arity: string[];
  }[];
}

interface BNFGrammarProps {
  productions: BNFProduction[];
  useLatex?: boolean;
}

/**
 * Renders a BNF grammar in academic style:
 *
 * Formulas    A, B ::= p | A ⊗ B | A ⊸ B | ...
 * Structures  X, Y ::= A | X, Y | I
 * Sequents    S    ::= X ⊢ Y
 */
export default function BNFGrammar(props: BNFGrammarProps) {
  return (
    <div class="font-mono text-sm space-y-2">
      <For each={props.productions}>
        {(prod) => (
          <div class="flex items-start gap-4">
            {/* Sort name */}
            <span class="text-gray-600 dark:text-gray-400 min-w-24">
              {prod.sort}
            </span>

            {/* Metavariable */}
            <span class="text-blue-600 dark:text-blue-400 min-w-16">
              {prod.metavar}
            </span>

            {/* ::= */}
            <span class="text-gray-500 dark:text-gray-500">::=</span>

            {/* Productions */}
            <div class="flex flex-wrap items-center gap-x-2">
              <For each={prod.constructors}>
                {(cons, index) => (
                  <>
                    <Show when={index() > 0}>
                      <span class="text-gray-400">|</span>
                    </Show>
                    <Show
                      when={props.useLatex && cons.latex}
                      fallback={
                        <span class="text-gray-900 dark:text-gray-100">
                          {cons.ascii || cons.name}
                        </span>
                      }
                    >
                      <KaTeX latex={cons.latex} />
                    </Show>
                  </>
                )}
              </For>
            </div>
          </div>
        )}
      </For>
    </div>
  );
}

/**
 * Extract BNF productions from calc_structure
 */
export function extractBNFFromCalc(calcStructure: Record<string, any>): BNFProduction[] {
  const metavarMap: Record<string, string> = {
    'Formula': 'A, B, C',
    'Atprop': 'p, q, r',
    'Structure': 'X, Y, Z',
    'Sequent': 'S',
    'Term': 't',
    'FFormula': '[A]',
  };

  const productions: BNFProduction[] = [];

  // Process each sort
  for (const [sortName, constructors] of Object.entries(calcStructure)) {
    // Skip internal/operator sorts
    if (sortName.includes('_Op') || sortName.includes('_Bin_Op') || sortName.includes('_Zer_Op')) {
      continue;
    }

    const prod: BNFProduction = {
      sort: sortName,
      metavar: metavarMap[sortName] || sortName.charAt(0).toLowerCase(),
      constructors: [],
    };

    for (const [consName, consData] of Object.entries(constructors as Record<string, any>)) {
      // Skip freevar/metavariable constructors for cleaner display
      if (consName.includes('Freevar')) continue;

      const cons = {
        name: consName,
        ascii: consData.ascii || consName,
        latex: consData.latex || '',
        arity: Array.isArray(consData.type) ? consData.type : (consData.type ? [consData.type] : []),
      };

      // Clean up display format
      if (cons.ascii) {
        cons.ascii = cons.ascii.replace(/_/g, ' ').trim();
      }
      if (cons.latex) {
        cons.latex = cons.latex.replace(/_/g, ' ').trim();
      }

      prod.constructors.push(cons);
    }

    if (prod.constructors.length > 0) {
      productions.push(prod);
    }
  }

  // Sort: Formula first, then Structure, then Sequent
  const order = ['Formula', 'Structure', 'FFormula', 'Sequent', 'Atprop', 'Term'];
  productions.sort((a, b) => {
    const aIdx = order.indexOf(a.sort);
    const bIdx = order.indexOf(b.sort);
    if (aIdx === -1 && bIdx === -1) return a.sort.localeCompare(b.sort);
    if (aIdx === -1) return 1;
    if (bIdx === -1) return -1;
    return aIdx - bIdx;
  });

  return productions;
}
