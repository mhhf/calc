/**
 * Formula pool → human-readable string.
 *
 * Tag-dispatched ASCII renderer for `proof-tree/v1` formulas. Not a LaTeX
 * renderer — layouts that want TeX can wrap this or walk the AST themselves.
 * Keeps the block viewer self-contained (no calculus/parser import on the
 * critical path; renders anything the serializer can emit).
 *
 * Precedence table mirrors ILL's grammar (`loli 50 < tensor 60 < oplus 65
 * < with 70 < bang 80`). Unknown tags fall through as `tag(arg, …)` so
 * new calculi still produce legible output without renderer updates.
 */
import type { FormulaAST } from './types';

type Pool = Record<string, FormulaAST>;

// Higher precedence = binds tighter. Parenthesize a child when its
// precedence is lower than the parent's, or when it equals and the
// connective is non-associative on that side (we conservatively add parens).
const PREC: Record<string, number> = {
  loli: 50,
  tensor: 60,
  oplus: 65,
  with: 70,
  bang: 80,
  monad: 80,
  exists: 40,
  forall: 40,
};

const OP: Record<string, string> = {
  tensor: ' * ',
  loli:   ' -o ',
  with:   ' & ',
  oplus:  ' + ',
};

const NULLARY: Record<string, string> = {
  one:  'I',
  zero: '0',
};

function parens(text: string, childPrec: number, parentPrec: number): string {
  return childPrec < parentPrec ? `(${text})` : text;
}

export function renderFormula(
  ref: string | null | undefined,
  pool: Pool,
  parentPrec = 0,
): string {
  if (!ref) return '·';
  const f = pool[ref];
  if (!f) return `?${ref}`;
  const tag = f.tag;

  // Leaves
  if (tag === 'atom' || tag === 'freevar' || tag === 'metavar') {
    return f.name || '?';
  }
  if (tag === 'strlit') return JSON.stringify(f.value ?? '');
  if (tag === 'binlit' || tag === 'bound' || tag === 'evar') return f.value ?? '0';
  if (tag === 'charlit') {
    const cp = f.codepoint;
    return typeof cp === 'number' ? `'${String.fromCodePoint(cp)}'` : '?';
  }
  if (tag === 'arrlit') {
    const elems = (f.elements || []).map((r) => renderFormula(r, pool, 0));
    return `[${elems.join(', ')}]`;
  }
  if (NULLARY[tag] !== undefined) return NULLARY[tag];

  const args = f.args || [];
  const prec = PREC[tag] ?? 0;

  // Infix binaries
  if (OP[tag] && args.length === 2) {
    const l = renderFormula(args[0], pool, prec + 1);
    const r = renderFormula(args[1], pool, prec);
    return parens(`${l}${OP[tag]}${r}`, prec, parentPrec);
  }

  // ! grade formula
  if (tag === 'bang' && args.length === 2) {
    const body = renderFormula(args[1], pool, prec);
    return parens(`!${body}`, prec, parentPrec);
  }
  // {A} monad
  if (tag === 'monad' && args.length === 1) {
    return `{${renderFormula(args[0], pool, 0)}}`;
  }

  // Quantifiers: `exists x. body` — the binder name is often in extras.
  if ((tag === 'exists' || tag === 'forall') && args.length >= 1) {
    const sym = tag === 'exists' ? '∃' : '∀';
    const body = renderFormula(args[args.length - 1], pool, prec);
    const varName = f.extras?.find((e) => e.kind === 'string')?.value;
    return parens(`${sym}${varName ? ' ' + varName : ''}. ${body}`, prec, parentPrec);
  }

  // Generic fallback: tag(arg, arg, …)
  const rendered = args.map((r) => renderFormula(r, pool, 0));
  return `${tag}(${rendered.join(', ')})`;
}

export function renderSequent(
  s: { contexts: Record<string, (string | null)[]>; succedent: string | null },
  pool: Pool,
): string {
  const parts: string[] = [];
  for (const name of Object.keys(s.contexts)) {
    const refs = s.contexts[name] || [];
    if (refs.length === 0) continue;
    const rendered = refs.map((r) => renderFormula(r, pool, 0)).join(', ');
    // Convention: bang-prefix cartesian zone, bare list for linear.
    parts.push(name === 'cartesian' && refs.length > 0 ? `!(${rendered})` : rendered);
  }
  const ante = parts.join(' ; ') || '·';
  const succ = s.succedent ? renderFormula(s.succedent, pool, 0) : '·';
  return `${ante} ⊢ ${succ}`;
}
