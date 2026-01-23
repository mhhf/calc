/**
 * Type definitions for lib/calc.js
 * Calculus database initialization and rule management
 */

/** Format properties available for rules */
export type FormatStyle = 'ascii' | 'ascii_se' | 'latex' | 'latex_se' | 'isabelle' | 'isabelle_se';

/** Rule definition from ll.json calc_structure */
export interface RuleDefinition {
  type?: string | string[];
  precedence?: number[];
  ascii?: string;
  latex?: string;
  isabelle?: string;
  ascii_se?: string;
  latex_se?: string;
  isabelle_se?: string;
  shallow?: boolean;
  latex_brackets?: boolean;
  invertable?: boolean;
  _unused_by_proofstate?: boolean;
}

/** Processed rule stored in Calc.db */
export interface Rule extends RuleDefinition {
  ctxName: string;
  ruleName: string;
  polarity?: 'positive' | 'negative';
  isTermType?: boolean;
}

/** Context name to rule name to rule ID mapping */
export type ToIdsMap = Record<string, Record<string, number>>;

/** Calculus database structure */
export interface CalcDB {
  rules: Record<number, Rule>;
  toIds: ToIdsMap;
}

/** Polarity mapping for formulas */
export interface PolarityMap {
  [ruleName: string]: 'positive' | 'negative';
}

/** Calc structure rules metadata */
export interface CalcStructureRulesMeta {
  polarity: PolarityMap;
}

/** Root calculus definition from ll.json */
export interface CalcDefinition {
  calc_structure: Record<string, Record<string, RuleDefinition>>;
  calc_structure_rules_meta: CalcStructureRulesMeta;
  calc_rules?: Record<string, unknown>;
}

/** Callback for eachStructureRule iteration */
export interface StructureRuleCallback {
  (params: {
    ctxName: string;
    ctx: Record<string, RuleDefinition>;
    ruleName: string;
    rule: RuleDefinition;
  }): void;
}

/** Calc class - singleton for calculus database management */
export interface CalcStatic {
  rule_index: number;
  db: CalcDB;
  initialized: boolean;
  calc: CalcDefinition | null;

  /**
   * Initialize the calculus database from ll.json data
   * Must be called once before using any other lib modules
   */
  init(calc: CalcDefinition): void;

  /**
   * Iterate over all structure rules in the calculus
   */
  eachStructureRule(calc: CalcDefinition, f: StructureRuleCallback): void;
}

declare const Calc: CalcStatic;
export default Calc;
export { Calc };
