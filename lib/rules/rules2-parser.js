/**
 * .rules2 Parser
 *
 * Parses sequent-notation rule files directly into flat descriptors,
 * bypassing tree-sitter and analyze.js entirely.
 *
 * Input:  sequent notation (e.g. "G ; D, A * B |- C")
 * Output: same descriptor shape as analyze.js extractDescriptor()
 */

const Store = require('../kernel/store');

/**
 * Split string on separator, respecting balanced parens.
 */
function balancedSplit(str, sep) {
  const parts = [];
  let depth = 0, current = '';
  for (let i = 0; i < str.length; i++) {
    const ch = str[i];
    if (ch === '(') depth++;
    else if (ch === ')') depth--;
    if (depth === 0 && str.slice(i, i + sep.length) === sep) {
      parts.push(current.trim());
      current = '';
      i += sep.length - 1;
    } else {
      current += ch;
    }
  }
  if (current.trim()) parts.push(current.trim());
  return parts;
}

/**
 * Parse a sequent string "cart ; linear |- succedent"
 * Returns { cartesian: string[], linear: string[], succedent: string }
 */
function parseSequent(line) {
  const [left, succedent] = line.split('|-').map(s => s.trim());
  const sides = left.split(';').map(s => s.trim());
  const cartStr = sides.length > 1 ? sides[0] : '';
  const linStr = sides.length > 1 ? sides[1] : sides[0];
  return {
    cartesian: cartStr ? balancedSplit(cartStr, ',') : [],
    linear: linStr ? balancedSplit(linStr, ',') : [],
    succedent: succedent.trim()
  };
}

/**
 * Check if a token is a context variable.
 * Primed vars (D', G) are always context vars.
 * Unprimed single uppercase: parse with formula parser — if freevar
 * and not in formulaVars, it's a context var.
 */
function isContextVar(token, formulaVars, parseFormula) {
  // Primed variables are always context vars
  if (/^[A-Z]'+$/.test(token)) return true;
  // Single uppercase: check via parser
  if (/^[A-Z]$/.test(token)) {
    if (formulaVars.has(token)) return false;
    const h = parseFormula(token);
    return Store.tag(h) === 'freevar';
  }
  return false;
}

/**
 * Parse a rule block and extract descriptor + metadata.
 */
function parseRuleBlock(block, parseFormula, formulaVars) {
  const lines = block.split('\n').map(l => l.trim()).filter(l => l && !l.startsWith('%'));

  // First line: "name: sequent" or just "name: annotations..."
  const firstLine = lines[0];
  const colonIdx = firstLine.indexOf(':');
  const name = firstLine.slice(0, colonIdx).trim();
  const rest = firstLine.slice(colonIdx + 1).trim();

  // Collect premise lines and annotation lines
  const premises = [];
  const annotations = {};
  let conclusionStr = rest;

  for (let i = 1; i < lines.length; i++) {
    const line = lines[i];
    if (line.startsWith('<-')) {
      premises.push(line.slice(2).trim());
    } else if (line.startsWith('@')) {
      const match = line.match(/^@(\w+)\s+(.*)/);
      if (match) {
        let val = match[2].replace(/\.$/, '').trim();
        if (val === 'true') val = true;
        else if (val === 'false') val = false;
        else if (val.startsWith('"') && val.endsWith('"')) val = val.slice(1, -1);
        annotations[match[1]] = val;
      }
    }
  }

  // Remove trailing period from conclusion
  conclusionStr = conclusionStr.replace(/\.$/, '').trim();

  // Parse sequents
  const conclusion = parseSequent(conclusionStr);
  const premiseSeqs = premises.map(parseSequent);

  // Identify formula entries vs context vars in conclusion
  const concLinFormulas = [];
  const concLinContextVars = [];
  for (const entry of conclusion.linear) {
    if (isContextVar(entry, formulaVars, parseFormula)) concLinContextVars.push(entry);
    else concLinFormulas.push(entry);
  }

  const concCartFormulas = [];
  const concCartContextVars = [];
  for (const entry of conclusion.cartesian) {
    if (isContextVar(entry, formulaVars, parseFormula)) concCartContextVars.push(entry);
    else concCartFormulas.push(entry);
  }

  // Find principal formula
  let principal = null;
  let side = null;

  // Check succedent: parse it, if compound (not freevar/atom) → principal on right
  const succHash = parseFormula(conclusion.succedent);
  const succTag = Store.tag(succHash);
  if (succTag !== 'freevar' && succTag !== 'atom') {
    principal = succHash;
    side = 'r';
  }

  // Check linear context for principal (compound formula)
  if (!principal) {
    for (const entry of concLinFormulas) {
      const h = parseFormula(entry);
      const t = Store.tag(h);
      if (t !== 'freevar' && t !== 'atom') {
        principal = h;
        side = 'l';
        break;
      }
    }
  }

  // Extract connective info
  let connective = null;
  let arity = 0;
  let childMap = {}; // freevar name → child index

  if (principal) {
    connective = Store.tag(principal);
    const children = Store.children(principal);
    arity = children.length;
    for (let i = 0; i < children.length; i++) {
      const c = children[i];
      if (Store.tag(c) === 'freevar') {
        childMap[Store.child(c, 0)] = i;
      }
    }
  }

  // Context flow
  const emptyLinear = conclusion.linear.length === 0;
  let contextFlow;
  if (emptyLinear) {
    contextFlow = 'empty';
  } else if (premiseSeqs.length === 0) {
    contextFlow = 'axiom';
  } else if (premiseSeqs.length === 1) {
    contextFlow = 'preserved';
  } else {
    // Check if all conclusion context vars appear in all premises
    const allCopied = concLinContextVars.every(v =>
      premiseSeqs.every(p => p.linear.includes(v) || p.cartesian.includes(v))
    );
    contextFlow = allCopied ? 'copy' : 'split';
  }

  const copyContext = contextFlow === 'copy';
  const contextSplit = contextFlow === 'split';
  const structural = annotations.structural === true;

  // Build premise descriptors (only when principal exists, matching analyze.js)
  if (!principal) {
    const descriptor = {
      connective, side, arity,
      copyContext, emptyLinear, contextSplit, contextFlow,
      premises: []
    };
    return {
      name, descriptor,
      invertible: annotations.invertible ?? null,
      pretty: annotations.pretty || name,
      structural,
      bridge: annotations.bridge || null,
      numPremises: premiseSeqs.length
    };
  }

  const premiseDescs = premiseSeqs.map(p => {
    const desc = {};

    // Find new formula vars in linear (not in conclusion linear)
    const newLinFormulas = [];
    for (const entry of p.linear) {
      if (!isContextVar(entry, formulaVars, parseFormula) && !concLinFormulas.includes(entry)) {
        const h = parseFormula(entry);
        // Get the freevar name(s) from this formula
        if (Store.tag(h) === 'freevar') {
          const varName = Store.child(h, 0);
          if (childMap[varName] != null) newLinFormulas.push(childMap[varName]);
        }
      }
    }
    if (newLinFormulas.length > 0) desc.linear = newLinFormulas;

    // Find new formula vars in cartesian
    const newCartFormulas = [];
    for (const entry of p.cartesian) {
      if (!isContextVar(entry, formulaVars, parseFormula) && !concCartFormulas.includes(entry)) {
        const h = parseFormula(entry);
        if (Store.tag(h) === 'freevar') {
          const varName = Store.child(h, 0);
          if (childMap[varName] != null) newCartFormulas.push(childMap[varName]);
        }
      }
    }
    if (newCartFormulas.length > 0) desc.cartesian = newCartFormulas;

    // Check succedent change
    const premSuccHash = parseFormula(p.succedent);
    if (premSuccHash !== succHash) {
      if (Store.tag(premSuccHash) === 'freevar') {
        const varName = Store.child(premSuccHash, 0);
        if (childMap[varName] != null) desc.succedent = childMap[varName];
      }
    }

    return desc;
  });

  const descriptor = {
    connective,
    side,
    arity,
    copyContext,
    emptyLinear,
    contextSplit,
    contextFlow,
    premises: premiseDescs
  };
  if (annotations.binding) descriptor.binding = annotations.binding;

  return {
    name,
    descriptor,
    invertible: annotations.invertible ?? null,
    pretty: annotations.pretty || name,
    structural,
    bridge: annotations.bridge || null,
    numPremises: premiseSeqs.length
  };
}

/**
 * Parse a .rules2 file.
 * @param {string} text - File contents
 * @param {function} parseFormula - Formula parser (from buildParser)
 * @returns {Object} rules map { name → rule }
 */
function parseRules2(text, parseFormula) {
  // Extract @formulas directive
  const formulaMatch = text.match(/@formulas\s+([A-Z](?:\s*,\s*[A-Z])*)/);
  if (!formulaMatch) throw new Error('@formulas directive required');
  const formulaVars = new Set(formulaMatch[1].split(',').map(s => s.trim()));

  // Remove @formulas line, split into rule blocks on '.'
  const body = text.replace(/@formulas[^\n]*\n/, '');
  const blocks = body.split(/\.\s*\n/).filter(b => b.trim());

  const rules = {};
  for (const block of blocks) {
    const trimmed = block.trim();
    if (!trimmed || trimmed.startsWith('%')) continue;
    const rule = parseRuleBlock(trimmed, parseFormula, formulaVars);
    rules[rule.name] = rule;
  }

  return rules;
}

module.exports = { parseRules2 };
