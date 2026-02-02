/**
 * ll.json Generator
 *
 * Generates ll.json from parsed .calc and .rules files.
 * This enables migrating from the monolithic ll.json to
 * a more modular Extended Celf format.
 *
 * Usage:
 *   const generator = require('./generator');
 *   const llJson = await generator.generate(calcPath, rulesPath);
 */

const tsParser = require('./ts-parser');
const fs = require('fs');

/**
 * Helper: Get annotation value by key
 */
function getAnnotation(annotations, key) {
  const ann = annotations.find(a => a.key === key);
  if (!ann || !ann.value) return null;

  switch (ann.value.type) {
    case 'StringValue':
      return ann.value.value;
    case 'BoolValue':
      return ann.value.value;
    case 'IdentValue':
      return ann.value.name;
    case 'PrecValue':
      return {
        precedence: ann.value.precedence,
        associativity: ann.value.associativity
      };
    default:
      return null;
  }
}

/**
 * Helper: Check if annotation exists
 */
function hasAnnotation(annotations, key) {
  return annotations.some(a => a.key === key);
}

/**
 * Extract connective definitions from .calc AST
 *
 * Looks for patterns like:
 *   tensor: formula -> formula -> formula @ascii "_ * _" @latex "\\otimes" ...
 *
 * Returns a map of connective name -> metadata
 */
function extractConnectives(calcAst) {
  const connectives = {};

  for (const decl of calcAst.declarations) {
    if (decl.type !== 'TypeDecl') continue;
    if (decl.annotations.length === 0) continue;

    // Check if this has rendering annotations (ascii, latex)
    const ascii = getAnnotation(decl.annotations, 'ascii');
    const latex = getAnnotation(decl.annotations, 'latex');

    if (!ascii && !latex) continue;

    // Extract type signature
    const arity = countArrows(decl.typeExpr);

    connectives[decl.name] = {
      name: decl.name,
      arity,
      ascii,
      latex,
      isabelle: getAnnotation(decl.annotations, 'isabelle'),
      prec: getAnnotation(decl.annotations, 'prec'),
      polarity: getAnnotation(decl.annotations, 'polarity'),
      category: getAnnotation(decl.annotations, 'category'),
      shallow: getAnnotation(decl.annotations, 'shallow')
    };
  }

  return connectives;
}

/**
 * Count arrows in a type expression to determine arity
 */
function countArrows(typeExpr) {
  if (!typeExpr) return 0;
  if (typeExpr.type === 'TypeArrow') {
    return 1 + countArrows(typeExpr.right);
  }
  return 0;
}

/**
 * Extract rules from .rules AST
 *
 * Returns a map of rule name -> rule metadata
 */
function extractRules(rulesAst) {
  const rules = {};

  for (const decl of rulesAst.declarations) {
    if (decl.type !== 'ClauseDecl') continue;

    const pretty = getAnnotation(decl.annotations, 'pretty');
    const invertible = getAnnotation(decl.annotations, 'invertible');

    rules[decl.name] = {
      name: decl.name,
      head: decl.head,
      premises: decl.premises,
      pretty,
      invertible,
      numPremises: decl.premises.length
    };
  }

  return rules;
}

/**
 * Generate Formula_Bin_Op section from connectives
 */
function generateFormulaBinOps(connectives) {
  const binOps = {};

  // Only include actual formula binary operators
  const formulaBinOps = ['tensor', 'loli', 'with'];

  for (const [name, conn] of Object.entries(connectives)) {
    // Binary connectives have arity 2
    if (conn.arity !== 2) continue;

    // Only include formula-level binary operators
    if (!formulaBinOps.includes(name)) continue;

    // Generate ll.json style name (e.g., tensor -> Formula_Tensor)
    const llName = `Formula_${capitalize(name)}`;

    binOps[llName] = {};

    if (conn.ascii) {
      // Extract operator from pattern like "_ * _"
      const op = conn.ascii.replace(/_/g, '').trim();
      binOps[llName].ascii = op;
    }

    if (conn.latex) {
      // Extract operator
      const op = conn.latex.replace(/#\d+/g, '').trim();
      binOps[llName].latex = op;
    }

    if (conn.isabelle) {
      binOps[llName].isabelle = conn.isabelle;
    }
  }

  return binOps;
}

/**
 * Generate calc_structure_rules section
 */
function generateCalcStructureRules(rules) {
  const result = {
    RuleZer: {},
    RuleU: {},
    RuleBin: {}
  };

  for (const [name, rule] of Object.entries(rules)) {
    // Classify rule by number of premises
    let category;
    if (rule.numPremises === 0) {
      category = 'RuleZer';
    } else if (rule.numPremises === 1) {
      category = 'RuleU';
    } else {
      category = 'RuleBin';
    }

    const llName = toRuleName(name);
    result[category][llName] = {
      ascii: rule.pretty || name,
      latex: rule.pretty || name
    };
  }

  return result;
}

/**
 * Generate rules section (sequent patterns)
 *
 * This is the most complex part - converting Celf terms to ll.json string patterns
 */
function generateRulesSection(rules) {
  const result = {
    RuleZer: {},
    RuleU: {},
    RuleBin: {}
  };

  for (const [name, rule] of Object.entries(rules)) {
    let category;
    if (rule.numPremises === 0) {
      category = 'RuleZer';
    } else if (rule.numPremises === 1) {
      category = 'RuleU';
    } else {
      category = 'RuleBin';
    }

    const llName = toRuleName(name);

    // Convert head and premises to ll.json string format
    const patterns = [termToPattern(rule.head)];
    for (const premise of rule.premises) {
      patterns.push(termToPattern(premise));
    }

    result[category][llName] = patterns;
  }

  return result;
}

/**
 * Convert Celf term AST to ll.json string pattern
 *
 * This converts terms like:
 *   deriv (seq (comma G (struct (tensor A B))) C)
 * to patterns like:
 *   "?X, -- : F?A * F?B |- -- : F?C"
 */
function termToPattern(term) {
  if (!term) return '';

  switch (term.type) {
    case 'TermVar':
      return varToPattern(term.name);

    case 'TermIdent':
      return term.name;

    case 'TermApp':
      return appToPattern(term);

    default:
      return JSON.stringify(term);
  }
}

/**
 * Convert variable name to ll.json pattern variable
 * G, D -> ?X, ?Y (context vars)
 * A, B, C -> F?A, F?B, F?C (formula vars)
 */
function varToPattern(name, inFormula = false) {
  // Single uppercase letters are typically formula variables
  if (name.length === 1 && /[A-Z]/.test(name)) {
    // Context variables vs formula variables
    if (['G', 'D'].includes(name)) {
      // Map G->X, D->Y for ll.json compatibility
      const mapping = { 'G': 'X', 'D': 'Y' };
      return `?${mapping[name] || name}`;
    }
    if (['X', 'Y', 'Z'].includes(name)) {
      return `?${name}`;
    }
    // Formula variables
    return `F?${name}`;
  }
  return `?${name}`;
}

/**
 * Convert application to pattern
 */
function appToPattern(term) {
  // Flatten application to get function and all args
  const { func, args } = flattenApp(term);

  if (func.type !== 'TermIdent') {
    return termToPattern(term.func) + ' ' + termToPattern(term.arg);
  }

  const funcName = func.name;

  switch (funcName) {
    case 'deriv':
      // deriv(seq) -> just the sequent pattern
      return termToPattern(args[0]);

    case 'seq':
      // seq(context, formula) -> "context |- -- : formula"
      // The right side (conclusion) needs "-- : " prefix for formulas
      const left = termToPattern(args[0]);
      const right = termToPattern(args[1]);
      // Wrap right side with "-- : " if it's a formula (starts with F? or is a connective)
      const rightPattern = wrapFormulaPattern(right);
      return `${left} |- ${rightPattern}`;

    case 'comma':
      // comma(a, b) -> "a, b"
      // Check if the inner term is also a comma - add parens for grouping
      const commaLeft = termToPattern(args[0]);
      const commaRight = termToPattern(args[1]);
      // If right side contains comma, wrap in parens
      if (commaRight.includes(',') && !commaRight.startsWith('(')) {
        return `${commaLeft}, (${commaRight})`;
      }
      return `${commaLeft}, ${commaRight}`;

    case 'struct':
      // struct(formula) -> "-- : formula"
      return `-- : ${termToPattern(args[0])}`;

    case 'empty':
      return 'I';

    case 'tensor':
      return `${termToPattern(args[0])} * ${termToPattern(args[1])}`;

    case 'loli':
      return `${termToPattern(args[0])} -o ${termToPattern(args[1])}`;

    case 'with':
      return `${termToPattern(args[0])} & ${termToPattern(args[1])}`;

    case 'bang':
      return `! ${termToPattern(args[0])}`;

    case 'one':
      // Multiplicative unit maps to structure neutral I
      return 'I';

    case 'atom':
      // atom(name) -> A?name (atomic proposition)
      if (args[0] && args[0].type === 'TermVar') {
        return `A?${args[0].name}`;
      }
      return `A?${termToPattern(args[0])}`;

    default:
      // Generic: func arg1 arg2 ...
      return args.map(a => termToPattern(a)).join(' ');
  }
}

/**
 * Flatten nested applications: ((f a) b) -> { func: f, args: [a, b] }
 */
function flattenApp(term) {
  const args = [];
  let current = term;

  while (current.type === 'TermApp') {
    args.unshift(current.arg);
    current = current.func;
  }

  return { func: current, args };
}

/**
 * Convert Celf-style name to ll.json style
 * tensor_l -> Tensor_L
 */
function toRuleName(name) {
  return name
    .split('_')
    .map(part => capitalize(part))
    .join('_');
}

function capitalize(str) {
  return str.charAt(0).toUpperCase() + str.slice(1);
}

/**
 * Wrap a formula pattern with "-- : " if needed
 * Already wrapped patterns (starting with "-- :") pass through
 * Variable patterns like F?A get wrapped
 * Connective patterns like "F?A * F?B" get wrapped
 */
function wrapFormulaPattern(pattern) {
  // Already wrapped
  if (pattern.startsWith('-- :')) return pattern;
  // Context variables don't need wrapping
  if (/^\?[XYZGD]$/.test(pattern)) return pattern;
  // Neutral/unit
  if (pattern === 'I') return pattern;
  // Formula patterns need wrapping
  return `-- : ${pattern}`;
}

/**
 * Main generator function
 */
async function generate(calcPath, rulesPath, options = {}) {
  await tsParser.init();

  // Parse input files
  const calcResult = await tsParser.parseFile(calcPath);
  if (!calcResult.success) {
    throw new Error(`Failed to parse ${calcPath}: ${calcResult.error}`);
  }

  const rulesResult = await tsParser.parseFile(rulesPath);
  if (!rulesResult.success) {
    throw new Error(`Failed to parse ${rulesPath}: ${rulesResult.error}`);
  }

  // Extract data from ASTs
  const connectives = extractConnectives(calcResult.ast);
  const rules = extractRules(rulesResult.ast);

  // Generate ll.json structure
  const llJson = {
    calc_name: options.calcName || 'Generated',

    calc_structure: {
      // Minimal structure for now
      Formula: {
        Formula_Atprop: {
          type: 'Atprop',
          isabelle: '_ \\<^sub>A\\<^sub>F',
          isabelle_se: '_ \\<^sub>A\\<^sub>F',
          precedence: [320, 340]
        },
        Formula_Freevar: {
          type: 'string',
          isabelle: '?\\<^sub>F _',
          isabelle_se: '_',
          ascii: 'F? _',
          latex: '_',
          skip_end_user_syntax: true,
          latex_brackets: false,
          precedence: [340, 330],
          shallow: false
        },
        Formula_Bang: {
          type: ['Formula'],
          isabelle: '! _ ',
          ascii: '! _ ',
          latex: '! _ ',
          shallow: true,
          precedence: [330, 331]
        },
        Formula_Bin: {
          type: ['Formula', 'Formula_Bin_Op', 'Formula'],
          isabelle: 'B\\<^sub>F _',
          shallow: false,
          precedence: [330, 330, 330, 331]
        }
      },

      Formula_Bin_Op: generateFormulaBinOps(connectives),

      Atprop: {
        Atprop: {
          type: 'string',
          ascii: '_',
          isabelle: '_ \\<^sub>F',
          isabelle_se: '_ \\<^sub>F',
          precedence: [320, 320]
        },
        Atprop_Freevar: {
          type: 'string',
          isabelle: '?\\<^sub>A _',
          isabelle_se: '_',
          ascii: 'A? _',
          latex: '? _',
          precedence: [320, 320],
          shallow: false
        }
      },

      Structure: {
        Structure_Formula: {
          type: ['Formula'],
          ascii: '_',
          latex: '_',
          isabelle: '_ \\<^sub>S',
          precedence: [330, 340]
        },
        Structure_Freevar: {
          type: 'string',
          isabelle: '?\\<^sub>S _',
          isabelle_se: '_',
          ascii: '? _',
          latex: '? _',
          latex_brackets: false,
          precedence: [310, 310],
          shallow: false
        },
        Structure_Zer: {
          type: 'Structure_Zer_Op',
          isabelle: 'Z\\<^sub>S',
          latex_brackets: false,
          shallow: false,
          precedence: [310, 310]
        },
        Structure_Bin: {
          type: ['Structure', 'Structure_Bin_Op', 'Structure'],
          isabelle: 'B\\<^sub>S _',
          shallow: false,
          precedence: [310, 310, 310, 311]
        }
      },

      Structure_Zer_Op: {
        Structure_Neutral: {
          isabelle: 'I\\<^sub>S',
          ascii: 'I',
          latex: '\\cdot'
        }
      },

      Structure_Bin_Op: {
        Structure_Comma: {
          isabelle: ',\\<^sub>S',
          ascii: ',',
          latex: ','
        }
      },

      Sequent: {
        Sequent_Structure: {
          type: 'Structure'
        },
        Sequent: {
          type: ['Structure', 'Structure'],
          isabelle: '_ \\<turnstile>\\<^sub>S _',
          ascii: '_ |- _',
          latex: '_ \\vdash _',
          latex_brackets: false,
          precedence: [306, 306, 305]
        }
      },

      // Minimal Term/Atterm for proof terms
      Term: {
        Term_Any: {
          isabelle: 'I\\<^sub>T',
          ascii: '--',
          ascii_se: ' ',
          latex: '--'
        },
        Term_Freevar: {
          type: 'string',
          isabelle: '?\\<^sub>T _',
          isabelle_se: '_',
          ascii: 'T? _',
          ascii_se: ' _ ',
          latex: '?_T _',
          latex_brackets: false,
          precedence: [340, 330],
          shallow: false
        }
      },

      Atterm: {
        Atterm: {
          type: 'string',
          ascii: 'TT? _',
          ascii_se: ' _ ',
          latex: '_',
          isabelle: '_ \\<^sub>T',
          isabelle_se: '_ \\<^sub>T',
          precedence: [320, 320]
        }
      }
    },

    calc_structure_rules_meta: {
      Contexts: {
        RuleZer: { label: 'Axioms', simp: true },
        RuleU: { label: 'Unary logical rules', simp: true },
        RuleBin: { label: 'Binary logical rules', simp: true }
      }
    },

    calc_structure_rules: generateCalcStructureRules(rules),

    rules: generateRulesSection(rules)
  };

  return llJson;
}

/**
 * Generate ll.json and write to file
 */
async function generateToFile(calcPath, rulesPath, outputPath, options = {}) {
  const llJson = await generate(calcPath, rulesPath, options);
  fs.writeFileSync(outputPath, JSON.stringify(llJson, null, 2));
  return llJson;
}

module.exports = {
  generate,
  generateToFile,
  extractConnectives,
  extractRules,
  termToPattern,
  getAnnotation
};
