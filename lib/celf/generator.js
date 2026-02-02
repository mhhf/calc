/**
 * ll.json Generator
 *
 * Generates ll.json from parsed .calc and .rules files.
 * Fully calculus-agnostic: derives all connective information
 * from @annotations and type signatures.
 *
 * Usage:
 *   const generator = require('./generator');
 *   const llJson = await generator.generate(calcPath, rulesPath);
 */

const tsParser = require('./ts-parser');
const fs = require('fs');

// =============================================================================
// Annotation Helpers
// =============================================================================

/**
 * Get annotation value by key
 */
function getAnnotation(annotations, key) {
  if (!annotations) return null;
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

// =============================================================================
// @ascii Pattern Parsing
// =============================================================================

/**
 * Parse @ascii pattern into structured form
 *
 * "_ * _" → { arity: 2, parts: ['', ' * ', ''] }
 * "! _"   → { arity: 1, parts: ['! ', ''] }
 * "I"     → { arity: 0, parts: ['I'] }
 */
function parseAsciiPattern(ascii) {
  if (!ascii) return null;
  const parts = ascii.split('_');
  return { arity: parts.length - 1, parts };
}

/**
 * Apply parsed pattern to arguments
 *
 * { parts: ['', ' * ', ''] }, ['A', 'B'] → "A * B"
 * { parts: ['! ', ''] }, ['A'] → "! A"
 */
function applyPattern(pattern, args) {
  if (!pattern) return args.join(' ');
  if (pattern.arity === 0) return pattern.parts[0];

  let result = pattern.parts[0];
  for (let i = 0; i < args.length; i++) {
    result += args[i] + (pattern.parts[i + 1] || '');
  }
  return result;
}

/**
 * Extract operator from @ascii pattern (for ll.json binOp format)
 * "_ * _" → "*"
 * "_ -o _" → "-o"
 */
function extractOperator(ascii) {
  if (!ascii) return null;
  return ascii.replace(/_/g, '').trim();
}

// =============================================================================
// Type Signature Analysis
// =============================================================================

/**
 * Count arrows in type expression (determines arity)
 */
function countArrows(typeExpr) {
  if (!typeExpr) return 0;
  if (typeExpr.type === 'TypeArrow') {
    return 1 + countArrows(typeExpr.right);
  }
  return 0;
}

/**
 * Get return type from type expression (rightmost in arrow chain)
 */
function getReturnType(typeExpr) {
  if (!typeExpr) return null;
  if (typeExpr.type === 'TypeArrow') {
    return getReturnType(typeExpr.right);
  }
  // Type identifiers may be parsed as TermIdent or TypeIdent
  if (typeExpr.type === 'TypeIdent' || typeExpr.type === 'TermIdent') {
    return typeExpr.name;
  }
  return null;
}

// =============================================================================
// AST Extraction
// =============================================================================

/**
 * Extract connective definitions from .calc AST
 *
 * Builds a registry with all information needed for pattern generation:
 * - arity (from type signature)
 * - returnType (from type signature)
 * - asciiPattern (parsed @ascii)
 * - other annotations
 */
function extractConnectives(calcAst) {
  const connectives = {};

  for (const decl of calcAst.declarations) {
    if (decl.type !== 'TypeDecl') continue;

    const ascii = getAnnotation(decl.annotations, 'ascii');
    const arity = countArrows(decl.typeExpr);
    const returnType = getReturnType(decl.typeExpr);

    connectives[decl.name] = {
      name: decl.name,
      arity,
      returnType,
      ascii,
      asciiPattern: parseAsciiPattern(ascii),
      latex: getAnnotation(decl.annotations, 'latex'),
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

// =============================================================================
// ll.json Generation
// =============================================================================

/**
 * Generate Formula_Bin_Op section from connectives
 *
 * Identifies binary formula connectives by:
 * - arity === 2
 * - returnType === 'formula'
 * - has @ascii annotation
 */
function generateFormulaBinOps(connectives) {
  const binOps = {};

  for (const [name, conn] of Object.entries(connectives)) {
    // Binary formula connectives: arity 2, returns formula, has @ascii
    if (conn.arity !== 2) continue;
    if (conn.returnType !== 'formula') continue;
    if (!conn.ascii) continue;

    const llName = `Formula_${capitalize(name)}`;
    binOps[llName] = {};

    // Extract operator from @ascii pattern
    const op = extractOperator(conn.ascii);
    if (op) binOps[llName].ascii = op;

    // Extract operator from @latex pattern
    if (conn.latex) {
      const latexOp = conn.latex.replace(/#\d+/g, '').trim();
      binOps[llName].latex = latexOp;
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
 * Converts Celf terms to ll.json string patterns using
 * the connective registry for formula rendering.
 */
function generateRulesSection(rules, connectives) {
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

    // Convert head and premises using connective registry
    const patterns = [termToPattern(rule.head, connectives)];
    for (const premise of rule.premises) {
      patterns.push(termToPattern(premise, connectives));
    }

    result[category][llName] = patterns;
  }

  return result;
}

// =============================================================================
// Pattern Generation
// =============================================================================

/**
 * Convert Celf term AST to ll.json string pattern
 *
 * Uses the connective registry to render formula connectives
 * according to their @ascii patterns.
 *
 * Example:
 *   deriv (seq (comma G (struct (tensor A B))) C)
 *   → "?X, -- : F?A * F?B |- -- : F?C"
 */
function termToPattern(term, connectives = {}) {
  if (!term) return '';

  switch (term.type) {
    case 'TermVar':
      return varToPattern(term.name);

    case 'TermIdent':
      return term.name;

    case 'TermApp':
      return appToPattern(term, connectives);

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
 *
 * Infrastructure connectives (standard sequent calculus structure)
 * have special handling. All other connectives use the registry.
 */
function appToPattern(term, connectives) {
  const { func, args } = flattenApp(term);

  if (func.type !== 'TermIdent') {
    return termToPattern(term.func, connectives) + ' ' + termToPattern(term.arg, connectives);
  }

  const funcName = func.name;

  // ==========================================================================
  // Infrastructure connectives (standard for any sequent calculus)
  // ==========================================================================

  switch (funcName) {
    case 'deriv':
      // Judgment wrapper: deriv(seq) -> sequent pattern
      return termToPattern(args[0], connectives);

    case 'seq': {
      // Sequent: seq(context, formula) -> "context |- -- : formula"
      const left = termToPattern(args[0], connectives);
      const right = termToPattern(args[1], connectives);
      return `${left} |- ${wrapFormulaPattern(right)}`;
    }

    case 'comma': {
      // Context concatenation: comma(a, b) -> "a, b"
      const commaLeft = termToPattern(args[0], connectives);
      const commaRight = termToPattern(args[1], connectives);
      if (commaRight.includes(',') && !commaRight.startsWith('(')) {
        return `${commaLeft}, (${commaRight})`;
      }
      return `${commaLeft}, ${commaRight}`;
    }

    case 'struct':
      // Formula-to-structure lift: struct(formula) -> "-- : formula"
      return `-- : ${termToPattern(args[0], connectives)}`;

    case 'empty':
      // Empty context
      return 'I';

    case 'atom':
      // Atomic proposition: atom(name) -> A?name
      if (args[0] && args[0].type === 'TermVar') {
        return `A?${args[0].name}`;
      }
      return `A?${termToPattern(args[0], connectives)}`;
  }

  // ==========================================================================
  // Connective registry lookup (calculus-specific)
  // ==========================================================================

  const conn = connectives[funcName];
  if (conn && conn.asciiPattern) {
    const argPatterns = args.map(a => termToPattern(a, connectives));
    return applyPattern(conn.asciiPattern, argPatterns);
  }

  // Fallback for unknown constructors
  if (args.length === 0) {
    return funcName;
  }
  return args.map(a => termToPattern(a, connectives)).join(' ');
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

    rules: generateRulesSection(rules, connectives)
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
  getAnnotation,
  // Expose for testing
  parseAsciiPattern,
  applyPattern,
  getReturnType
};
