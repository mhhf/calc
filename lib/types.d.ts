/** UI-facing type definitions for CALC */

export interface Rule {
  ctxName: string;
  ruleName: string;
  type?: string | string[];
  precedence?: number[];
  ascii?: string;
  latex?: string;
  invertable?: boolean;
  polarity?: 'positive' | 'negative';
  _unused_by_proofstate?: boolean;
}

export interface TreeNode {
  head: Record<string, string>;
  children: TreeNode[];
}

export interface PTTreeHead {
  conclusion: string;
  type: string;
  delta_out: string;
  delta_in: string;
  proven: string;
}

export interface PTTree {
  head: PTTreeHead;
  children: PTTree[];
}
