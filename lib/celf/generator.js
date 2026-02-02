/**
 * ll.json Generator (v2)
 *
 * Generates calc database from .family, .calc, and .rules files.
 * Supports the new minimal LNL design with 3-arg sequents.
 *
 * Usage:
 *   const generator = require('./generator');
 *   const calcDb = await generator.generate({
 *     familyPath: 'calculus/lnl.family',
 *     calcPath: 'calculus/ill.calc',
 *     rulesPath: 'calculus/ill.rules'
 *   });
 */

const tsParser = require('./ts-parser');
const fs = require('fs');
const path = require('path');

// =============================================================================
// Annotation Helpers
// =============================================================================

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

function getAllAnnotations(annotations) {
  if (!annotations) return {};
  const result = {};
  for (const ann of annotations) {
    if (ann.value) {
      result[ann.key] = getAnnotation(annotations, ann.key);
    } else {
      result[ann.key] = true;
    }
  }
  return result;
}

// =============================================================================
// Type Signature Analysis
// =============================================================================

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

function getReturnType(typeExpr) {
  if (!typeExpr) return null;
  if (typeExpr.type === 'TypeArrow') {
    return getReturnType(typeExpr.right);
  }
  if (typeExpr.type === 'TypeIdent' || typeExpr.type === 'TermIdent') {
    return typeExpr.name;
  }
  if (typeExpr.type === 'TypeKeyword') {
    return 'type';
  }
  return null;
}

// =============================================================================
// AST Extraction
// =============================================================================

/**
 * Extract type/constructor declarations from an AST
 * Returns { baseTypes, constructors, directives }
 */
function extractDeclarations(ast) {
  const baseTypes = {};      // name -> { annotations }
  const constructors = {};   // name -> { argTypes, returnType, annotations }
  const directives = {
    family: null,
    extends: null,
    metavars: [],
    schema: {}
  };

  for (const decl of ast.declarations) {
    if (decl.type === 'Comment') continue;

    // Handle directives
    if (decl.type === 'ClauseDecl' && decl.name.startsWith('@')) {
      const directive = decl.name.slice(1);
      if (directive === 'family') {
        directives.family = decl.head?.name;
      } else if (directive === 'extends') {
        directives.extends = decl.head?.name;
      } else if (directive === 'metavar') {
        // Parse metavar directive
        // Format: @metavar formula prefix="F?" examples="A B C".
        // Key-value pairs are in premises as Annotation objects
        const metavar = { type: decl.head?.name };
        for (const premise of decl.premises || []) {
          if (premise && premise.type === 'Annotation') {
            metavar[premise.key] = premise.value?.value || premise.value?.name;
          }
        }
        directives.metavars.push(metavar);
      } else if (directive === 'schema') {
        // Parse schema directive
        // Format: @schema bin_factorization formula structure.
        const schemaName = decl.head?.name;
        if (schemaName && decl.premises) {
          directives.schema[schemaName] = decl.premises.map(p => p.name);
        }
      }
      continue;
    }

    // Handle type declarations
    if (decl.type === 'TypeDecl') {
      const returnType = getReturnType(decl.typeExpr);
      const argTypes = getArgTypes(decl.typeExpr);

      if (returnType === 'type') {
        // Base type declaration: `formula: type.`
        baseTypes[decl.name] = {
          name: decl.name,
          annotations: getAllAnnotations(decl.annotations)
        };
      } else {
        // Constructor declaration: `tensor: formula -> formula -> formula.`
        constructors[decl.name] = {
          name: decl.name,
          argTypes,
          returnType,
          annotations: getAllAnnotations(decl.annotations)
        };
      }
      continue;
    }

    // Handle clause declarations (nullary constructors or rules)
    if (decl.type === 'ClauseDecl') {
      if (decl.premises.length === 0 && decl.head) {
        // Nullary constructor: `one: formula.` or `empty: structure.`
        const headType = decl.head.type === 'TermIdent' ? decl.head.name : null;
        if (headType && headType !== 'type') {
          constructors[decl.name] = {
            name: decl.name,
            argTypes: [],
            returnType: headType,
            annotations: getAllAnnotations(decl.annotations)
          };
        }
      }
      // Rules with premises are handled separately
    }
  }

  return { baseTypes, constructors, directives };
}

/**
 * Extract inference rules from .rules AST
 */
function extractRules(ast) {
  const rules = {};

  for (const decl of ast.declarations) {
    if (decl.type !== 'ClauseDecl') continue;
    if (decl.name.startsWith('@')) continue;  // Skip directives

    const annotations = getAllAnnotations(decl.annotations);

    rules[decl.name] = {
      name: decl.name,
      head: decl.head,
      premises: decl.premises,
      pretty: annotations.pretty,
      invertible: annotations.invertible,
      structural: annotations.structural,
      position: annotations.position,
      bridge: annotations.bridge,
      numPremises: decl.premises.length
    };
  }

  return rules;
}

// =============================================================================
// calc_structure Generation
// =============================================================================

function capitalize(str) {
  return str.charAt(0).toUpperCase() + str.slice(1);
}

/**
 * Generate calc_structure from extracted declarations
 */
function generateCalcStructure(baseTypes, constructors) {
  const structure = {};

  // Group constructors by return type
  const byReturnType = {};
  for (const [name, constr] of Object.entries(constructors)) {
    const rt = constr.returnType;
    if (!byReturnType[rt]) byReturnType[rt] = [];
    byReturnType[rt].push(constr);
  }

  // Generate structure for each base type
  for (const [typeName, typeInfo] of Object.entries(baseTypes)) {
    const llName = capitalize(typeName);
    structure[llName] = {};

    // Add freevar for metavariables
    const prefix = llName.charAt(0);
    structure[llName][`${llName}_Freevar`] = {
      type: 'string',
      ascii: `${prefix}? _`,
      latex: '_',
      shallow: false
    };

    // Process constructors for this type
    const constrs = byReturnType[typeName] || [];

    for (const constr of constrs) {
      const entryName = `${llName}_${capitalize(constr.name)}`;
      const ann = constr.annotations;

      const entry = {};

      // Set type based on argTypes
      if (constr.argTypes.length === 0) {
        // Nullary constructor - no type field
      } else if (constr.argTypes.length === 1) {
        entry.type = capitalize(constr.argTypes[0]);
      } else {
        entry.type = constr.argTypes.map(t => capitalize(t));
      }

      // Copy formatting annotations
      if (ann.ascii) entry.ascii = ann.ascii;
      if (ann.latex) entry.latex = ann.latex;
      if (ann.isabelle) entry.isabelle = ann.isabelle;

      // Handle precedence
      if (ann.prec) {
        const prec = ann.prec;
        const basePrec = typeof prec === 'object' ? prec.precedence : prec;
        // Generate precedence array based on arity
        const precedence = [];
        for (let i = 0; i < constr.argTypes.length; i++) {
          precedence.push(basePrec);
        }
        precedence.push(basePrec + 1);  // Own precedence is last
        entry.precedence = precedence;
      }

      // Handle special annotations
      if (ann.shallow === false) entry.shallow = false;
      if (ann.role) entry.role = ann.role;

      structure[llName][entryName] = entry;
    }
  }

  return structure;
}

// =============================================================================
// Rules Section Generation
// =============================================================================

/**
 * Convert Celf term AST to pattern string
 */
function termToPattern(term, constructors = {}) {
  if (!term) return '';

  switch (term.type) {
    case 'TermVar':
      return varToPattern(term.name);

    case 'TermIdent':
      return term.name;

    case 'TermApp':
      return appToPattern(term, constructors);

    case 'TermBang':
      return `! ${termToPattern(term.inner, constructors)}`;

    case 'TermTensor':
      return `${termToPattern(term.left, constructors)} * ${termToPattern(term.right, constructors)}`;

    case 'TermWith':
      return `${termToPattern(term.left, constructors)} & ${termToPattern(term.right, constructors)}`;

    case 'TermLoli':
      return `${termToPattern(term.left, constructors)} -o ${termToPattern(term.right, constructors)}`;

    default:
      return JSON.stringify(term);
  }
}

function varToPattern(name) {
  // Single uppercase letters
  if (name.length === 1 && /[A-Z]/.test(name)) {
    // Common context variables
    if (['G', 'H', 'J'].includes(name)) {
      return `?${name}`;  // Cartesian context
    }
    if (['D', 'X', 'Y', 'Z'].includes(name)) {
      return `?${name}`;  // Linear context / structure
    }
    // Formula variables
    return `F?${name}`;
  }
  // Multi-character or primed variables
  if (name.endsWith("'")) {
    return `?${name.slice(0, -1)}2`;  // D' -> ?D2
  }
  return `?${name}`;
}

function appToPattern(term, constructors) {
  const { func, args } = flattenApp(term);

  if (func.type !== 'TermIdent') {
    return `${termToPattern(term.func, constructors)} ${termToPattern(term.arg, constructors)}`;
  }

  const funcName = func.name;

  // Infrastructure constructors
  switch (funcName) {
    case 'deriv':
      return termToPattern(args[0], constructors);

    case 'seq': {
      // 3-arg sequent: seq(cartesian, linear, succedent)
      const cart = termToPattern(args[0], constructors);
      const lin = termToPattern(args[1], constructors);
      const succ = termToPattern(args[2], constructors);
      return `${cart} ; ${lin} |- ${succ}`;
    }

    case 'comma': {
      const left = termToPattern(args[0], constructors);
      const right = termToPattern(args[1], constructors);
      return `${left}, ${right}`;
    }

    case 'hyp': {
      // hyp(term, formula) -> "term : formula" or just "formula" if term is 'any'
      const termPart = termToPattern(args[0], constructors);
      const formulaPart = termToPattern(args[1], constructors);
      if (termPart === 'any' || termPart === '--') {
        return `-- : ${formulaPart}`;
      }
      return `${termPart} : ${formulaPart}`;
    }

    case 'empty':
      return 'I';

    case 'any':
      return '--';

    case 'var':
      return termToPattern(args[0], constructors);

    // Formula constructors - check constructor registry
    default: {
      const constr = constructors[funcName];
      if (constr && constr.annotations.ascii) {
        const ascii = constr.annotations.ascii;
        const argPatterns = args.map(a => termToPattern(a, constructors));
        // Replace _ placeholders with args
        let result = ascii;
        for (const arg of argPatterns) {
          result = result.replace('_', arg);
        }
        return result;
      }
      // Fallback
      if (args.length === 0) return funcName;
      return `${funcName}(${args.map(a => termToPattern(a, constructors)).join(', ')})`;
    }
  }
}

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
 * Generate rules section from extracted rules
 */
function generateRulesSection(rules, constructors) {
  const result = {
    RuleZer: {},
    RuleU: {},
    RuleBin: {},
    RuleStruct: {}
  };

  for (const [name, rule] of Object.entries(rules)) {
    // Classify rule by number of premises
    let category;
    if (rule.structural) {
      category = 'RuleStruct';
    } else if (rule.numPremises === 0) {
      category = 'RuleZer';
    } else if (rule.numPremises === 1) {
      category = 'RuleU';
    } else {
      category = 'RuleBin';
    }

    const llName = toRuleName(name);

    // Generate patterns
    const patterns = [termToPattern(rule.head, constructors)];
    for (const premise of rule.premises) {
      patterns.push(termToPattern(premise, constructors));
    }

    result[category][llName] = patterns;
  }

  return result;
}

/**
 * Generate calc_structure_rules section (rule display names)
 */
function generateCalcStructureRules(rules) {
  const result = {
    RuleZer: {},
    RuleU: {},
    RuleBin: {},
    RuleStruct: {}
  };

  for (const [name, rule] of Object.entries(rules)) {
    let category;
    if (rule.structural) {
      category = 'RuleStruct';
    } else if (rule.numPremises === 0) {
      category = 'RuleZer';
    } else if (rule.numPremises === 1) {
      category = 'RuleU';
    } else {
      category = 'RuleBin';
    }

    const llName = toRuleName(name);
    result[category][llName] = {
      ascii: rule.pretty || name,
      latex: rule.pretty || name,
      invertible: rule.invertible
    };
  }

  return result;
}

function toRuleName(name) {
  return name
    .split('_')
    .map(part => capitalize(part))
    .join('_');
}

// =============================================================================
// File Loading
// =============================================================================

/**
 * Resolve @extends directive to file path
 */
function resolveExtends(extendsName, basePath) {
  const dir = path.dirname(basePath);
  // Try common extensions
  for (const ext of ['.family', '.calc', '']) {
    const tryPath = path.join(dir, `${extendsName}${ext}`);
    if (fs.existsSync(tryPath)) {
      return tryPath;
    }
  }
  return null;
}

/**
 * Load and merge a file with its @extends chain
 */
async function loadWithExtends(filePath) {
  const result = await tsParser.parseFile(filePath);
  if (!result.success) {
    throw new Error(`Failed to parse ${filePath}: ${result.error}`);
  }

  const { baseTypes, constructors, directives } = extractDeclarations(result.ast);

  // Handle @extends
  if (directives.extends) {
    const extendsPath = resolveExtends(directives.extends, filePath);
    if (extendsPath) {
      const parent = await loadWithExtends(extendsPath);
      // Merge: child overrides parent, but preserve parent's family if child doesn't have one
      return {
        baseTypes: { ...parent.baseTypes, ...baseTypes },
        constructors: { ...parent.constructors, ...constructors },
        directives: {
          ...parent.directives,
          ...directives,
          // Preserve parent's family if child doesn't define one
          family: directives.family || parent.directives.family,
          metavars: [...parent.directives.metavars, ...directives.metavars],
          schema: { ...parent.directives.schema, ...directives.schema }
        }
      };
    }
  }

  return { baseTypes, constructors, directives };
}

// =============================================================================
// Main Generator
// =============================================================================

/**
 * Generate calc database from DSL files
 *
 * @param {Object|string} options - Options object or calcPath for legacy API
 * @param {string} options.calcPath - Path to .calc file
 * @param {string} options.rulesPath - Path to .rules file
 * @param {string} [options.familyPath] - Path to .family file (auto-resolved from @extends if not provided)
 * @returns {Object} calc database in ll.json format
 */
async function generate(options, rulesPath) {
  await tsParser.init();

  // Support legacy API: generate(calcPath, rulesPath)
  if (typeof options === 'string') {
    options = { calcPath: options, rulesPath };
  }

  const { calcPath } = options;
  rulesPath = options.rulesPath || rulesPath;

  // Load .calc with @extends chain (includes family)
  const calcData = await loadWithExtends(calcPath);

  // Load .rules
  const rulesResult = await tsParser.parseFile(rulesPath);
  if (!rulesResult.success) {
    throw new Error(`Failed to parse ${rulesPath}: ${rulesResult.error}`);
  }
  const rules = extractRules(rulesResult.ast);

  // Generate calc_structure from merged declarations
  const calcStructure = generateCalcStructure(
    calcData.baseTypes,
    calcData.constructors
  );

  // Generate rules sections
  const rulesSection = generateRulesSection(rules, calcData.constructors);
  const rulesMetaSection = generateCalcStructureRules(rules);

  return {
    calc_name: calcData.directives.family || 'Generated',
    calc_structure: calcStructure,
    calc_structure_rules_meta: {
      Contexts: {
        RuleZer: { label: 'Axioms', simp: true },
        RuleU: { label: 'Unary logical rules', simp: true },
        RuleBin: { label: 'Binary logical rules', simp: true },
        RuleStruct: { label: 'Structural rules', simp: true }
      }
    },
    calc_structure_rules: rulesMetaSection,
    rules: rulesSection
  };
}

/**
 * Generate and write to file
 */
async function generateToFile(options, outputPath) {
  const calcDb = await generate(options);
  fs.writeFileSync(outputPath, JSON.stringify(calcDb, null, 2));
  return calcDb;
}

// =============================================================================
// Family Infrastructure Extraction (for tests)
// =============================================================================

function extractFamilyInfrastructure(ast) {
  const { baseTypes, constructors, directives } = extractDeclarations(ast);

  // Build role registry from @role annotations (check both constructors and base types)
  const roleRegistry = {};

  for (const [name, constr] of Object.entries(constructors)) {
    if (constr.annotations.role) {
      roleRegistry[constr.annotations.role] = {
        name,
        ...constr
      };
    }
  }

  // Also check base types (e.g., deriv: sequent -> type @role judgment)
  for (const [name, baseType] of Object.entries(baseTypes)) {
    if (baseType.annotations.role) {
      roleRegistry[baseType.annotations.role] = {
        name,
        ...baseType
      };
    }
  }

  return {
    roleRegistry,
    connectives: constructors,
    directives
  };
}

module.exports = {
  generate,
  generateToFile,
  extractDeclarations,
  extractRules,
  extractFamilyInfrastructure,
  termToPattern,
  getAnnotation,
  loadWithExtends
};
