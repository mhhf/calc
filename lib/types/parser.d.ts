/**
 * Type definitions for lib/parser.js
 * Dynamic Jison parser generation from calculus definition
 */

import type { CalcDefinition, CalcStatic } from './calc';
import type { Node, NodeConstructor } from './node';

/** Jison parser interface */
export interface JisonParser {
  parse(input: string): Node;
  yy: {
    Node: NodeConstructor;
    [key: string]: unknown;
  };
}

/** Result of parser generation */
export interface ParserModule {
  parser: JisonParser;
  grammar: unknown;
  calc: CalcDefinition;
  Calc: CalcStatic;
}

/**
 * Generate a Jison parser from calculus definition
 * Note: This also calls Calc.init() as a side effect
 */
export function genParser(calc: CalcDefinition): ParserModule;

declare const parser: typeof genParser;
export default parser;
