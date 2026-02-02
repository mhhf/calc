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
 * Get all argument types from a type expression
 * `a -> b -> c` → ['a', 'b']
 */
function getArgTypes(typeExpr) {
  const args = [];
  let current = typeExpr;
  while (current && current.type === 'TypeArrow') {
    const argType = current.left;
    if (argType.type === 'TermIdent' || argType.type === 'TypeIdent') {
      args.push(argType.name);
    }
    current = current.right;
  }
  return args;
}

/**
 * Extract connective definitions from .calc AST
 *
 * Handles two cases:
 * 1. TypeDecl: `tensor: formula -> formula -> formula @ascii "_ * _".`
 * 2. ClauseDecl with no premises: `one: formula @ascii "I".` (nullary constant)
 *
 * Builds a registry with all information needed for pattern generation.
 */
function extractConnectives(calcAst) {
  const connectives = {};

  for (const decl of calcAst.declarations) {
    if (decl.type === 'TypeDecl') {
      // Type declaration with arrow types
      const ascii = getAnnotation(decl.annotations, 'ascii');
      const arity = countArrows(decl.typeExpr);
      const returnType = getReturnType(decl.typeExpr);
      const argTypes = getArgTypes(decl.typeExpr);

      connectives[decl.name] = {
        name: decl.name,
        arity,
        returnType,
        argTypes,
        ascii,
        asciiPattern: parseAsciiPattern(ascii),
        latex: getAnnotation(decl.annotations, 'latex'),
        isabelle: getAnnotation(decl.annotations, 'isabelle'),
        prec: getAnnotation(decl.annotations, 'prec'),
        polarity: getAnnotation(decl.annotations, 'polarity'),
        category: getAnnotation(decl.annotations, 'category'),
        shallow: getAnnotation(decl.annotations, 'shallow')
      };
    } else if (decl.type === 'ClauseDecl' && decl.premises.length === 0) {
      // Nullary constant: `one: formula.` or `empty: structure.`
      // The head is just a type identifier
      if (decl.head && decl.head.type === 'TermIdent') {
        const returnType = decl.head.name;
        const ascii = getAnnotation(decl.annotations, 'ascii');

        connectives[decl.name] = {
          name: decl.name,
          arity: 0,
          returnType,
          argTypes: [],
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
    }
  }

  return connectives;
}

// =============================================================================
// Type Registry
// =============================================================================

/**
 * Build type registry from connectives
 *
 * Groups constructors by:
 * - Base types (X: type.)
 * - Return type category
 * - Arity and argument pattern
 */
function buildTypeRegistry(connectives) {
  const registry = {
    baseTypes: {},      // Types declared with `: type`
    constructors: {}    // All constructors grouped by return type
  };

  // First pass: find base types
  for (const [name, conn] of Object.entries(connectives)) {
    // `formula: type.` has returnType 'type' or null, arity 0
    if (conn.returnType === 'type' || (conn.returnType === null && conn.arity === 0)) {
      registry.baseTypes[name] = {
        name,
        llName: capitalize(name)
      };
      registry.constructors[name] = {
        nullary: [],
        unary: [],
        binary: [],
        crossType: []
      };
    }
  }

  // Second pass: classify constructors by return type
  for (const [name, conn] of Object.entries(connectives)) {
    const retType = conn.returnType;
    if (!retType || retType === 'type' || !registry.constructors[retType]) continue;

    const category = registry.constructors[retType];
    const allArgsSameType = conn.argTypes.every(t => t === retType);

    if (conn.arity === 0) {
      category.nullary.push(conn);
    } else if (conn.arity === 1 && allArgsSameType) {
      category.unary.push(conn);
    } else if (conn.arity === 2 && allArgsSameType) {
      category.binary.push(conn);
    } else {
      // Cross-type: args don't match return type
      category.crossType.push(conn);
    }
  }

  return registry;
}

// =============================================================================
// calc_structure Generation
// =============================================================================

/**
 * Generate calc_structure from type registry
 *
 * This replaces the hardcoded JSON blob with data-driven generation.
 */
function generateCalcStructure(registry, connectives) {
  const structure = {};

  for (const [typeName, typeInfo] of Object.entries(registry.baseTypes)) {
    const llName = typeInfo.llName;
    const category = registry.constructors[typeName];

    // Main category entry
    structure[llName] = {};

    // Add Freevar for metavariables (every type needs this)
    structure[llName][`${llName}_Freevar`] = {
      type: 'string',
      ascii: `${llName.charAt(0)}? _`,
      latex: '_',
      shallow: false
    };

    // Cross-type constructors (e.g., struct: formula -> structure)
    for (const conn of category.crossType) {
      const entryName = `${llName}_${capitalize(conn.name)}`;

      // Determine type reference
      let typeRef;
      if (conn.argTypes.length === 1) {
        typeRef = [capitalize(conn.argTypes[0])];
      } else {
        typeRef = conn.argTypes.map(t => capitalize(t));
      }

      structure[llName][entryName] = {
        type: typeRef,
        ascii: conn.ascii || '_',
        latex: conn.latex || '_'
      };

      // Special case: atom-like constructors that take 'string'
      if (conn.argTypes.includes('string')) {
        structure[llName][entryName].type = 'Atprop';
      }
    }

    // Unary same-type constructors (e.g., bang: formula -> formula)
    for (const conn of category.unary) {
      const entryName = `${llName}_${capitalize(conn.name)}`;
      structure[llName][entryName] = {
        type: [llName],
        ascii: conn.ascii,
        latex: conn.latex,
        shallow: conn.shallow ?? true
      };
      if (conn.prec) {
        structure[llName][entryName].precedence = [conn.prec.precedence, conn.prec.precedence + 1];
      }
    }

    // Binary same-type constructors → factored into Bin + Bin_Op
    if (category.binary.length > 0) {
      structure[llName][`${llName}_Bin`] = {
        type: [llName, `${llName}_Bin_Op`, llName],
        shallow: false
      };

      // Separate Bin_Op category
      structure[`${llName}_Bin_Op`] = {};
      for (const conn of category.binary) {
        const opName = `${llName}_${capitalize(conn.name)}`;
        structure[`${llName}_Bin_Op`][opName] = {
          ascii: extractOperator(conn.ascii),
          latex: conn.latex ? conn.latex.replace(/#\d+/g, '').trim() : null
        };
      }
    }

    // Nullary constructors → Zer_Op category
    if (category.nullary.length > 0) {
      // Add Zer reference in main category
      structure[llName][`${llName}_Zer`] = {
        type: `${llName}_Zer_Op`,
        shallow: false
      };

      // Separate Zer_Op category
      structure[`${llName}_Zer_Op`] = {};
      for (const conn of category.nullary) {
        const opName = `${llName}_${capitalize(conn.name)}`;
        structure[`${llName}_Zer_Op`][opName] = {
          ascii: conn.ascii,
          latex: conn.latex
        };
      }
    }
  }

  // Handle Atprop specially (for string-based atoms)
  if (!structure['Atprop']) {
    structure['Atprop'] = {
      Atprop: {
        type: 'string',
        ascii: '_',
        latex: '_'
      },
      Atprop_Freevar: {
        type: 'string',
        ascii: 'A? _',
        latex: '? _',
        shallow: false
      }
    };
  }

  // Add Term_Any for proof term wildcards (--) if Term category exists
  if (structure['Term']) {
    structure['Term']['Term_Any'] = {
      ascii: '--',
      latex: '--'
    };
  }

  return structure;
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
 *
 * Generates ll.json entirely from .calc and .rules files.
 * No hardcoded calculus-specific structure.
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

  // Build type registry from .calc declarations
  const typeRegistry = buildTypeRegistry(connectives);

  // Generate calc_structure from registry (data-driven, not hardcoded)
  const calcStructure = generateCalcStructure(typeRegistry, connectives);

  // Generate ll.json
  const llJson = {
    calc_name: options.calcName || 'Generated',
    calc_structure: calcStructure,
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
  getReturnType,
  getArgTypes,
  buildTypeRegistry,
  generateCalcStructure
};
