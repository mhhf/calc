/**
 * Calculus loader
 *
 * Loads and merges .family/.calc files via @extends chains.
 * Extracts type/constructor declarations for calculus module.
 *
 * Uses declaration parser + framework Earley parser.
 */

const Store = require('../kernel/store');
const { parseDeclarations } = require('../parser/declarations');
const { buildParserFromTables } = require('../calculus/builders');
const fs = require('fs');
const path = require('path');

// Framework expression parser (Earley): arrows + application, no connective operators.
// .calc/.family files DEFINE connectives; they don't USE them.
const _frameworkParser = buildParserFromTables({
  operators: [],
  nullary: {},
  unaryPrefix: {},
  arrows: true,
  application: true,
  multiCharFreevars: true,
});

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
// Type Signature Analysis (hash-based)
// =============================================================================

/** Follow right side of arrow chain to find return type name. */
function getReturnType(hash) {
  if (!Store.isTerm(hash)) return null;
  const tag = Store.tag(hash);
  if (tag === 'arrow') return getReturnType(Store.children(hash)[1]);
  if (tag === 'type') return 'type';
  if (tag === 'atom') return Store.children(hash)[0];
  return null;
}

/** Collect arg type names from left side of arrow chain. */
function getArgTypes(hash) {
  const args = [];
  let current = hash;
  while (Store.isTerm(current) && Store.tag(current) === 'arrow') {
    const children = Store.children(current);
    const left = children[0];
    if (Store.isTerm(left) && Store.tag(left) === 'atom') {
      args.push(Store.children(left)[0]);
    }
    current = children[1];
  }
  return args;
}

/** Check if hash represents a type expression (arrow chain or `type` keyword). */
function isTypeExpr(hash) {
  if (!Store.isTerm(hash)) return false;
  const tag = Store.tag(hash);
  return tag === 'arrow' || tag === 'type';
}

// =============================================================================
// Declaration Extraction
// =============================================================================

/**
 * Extract type/constructor declarations from parsed declarations.
 * @param {Array} decls - declarations from parseDeclarations()
 * @returns {{ baseTypes, constructors, directives }}
 */
function extractDeclarations(decls) {
  const baseTypes = {};
  const constructors = {};
  const directives = {
    family: null,
    extends: null,
    metavars: [],
    schema: {}
  };

  for (const decl of decls) {
    // Handle top-level directives
    if (decl.type === 'directive') {
      if (decl.key === 'family') {
        directives.family = decl.args[0]?.name;
      } else if (decl.key === 'extends') {
        directives.extends = decl.args[0]?.name;
      } else if (decl.key === 'metavar') {
        const metavar = { type: decl.args[0]?.name };
        for (const arg of decl.args.slice(1)) {
          if (arg.type === 'keyValue') {
            metavar[arg.key] = arg.value;
          }
        }
        directives.metavars.push(metavar);
      } else if (decl.key === 'schema') {
        const schemaName = decl.args[0]?.name;
        if (schemaName) {
          directives.schema[schemaName] = decl.args.slice(1).map(a => a.name);
        }
      }
      continue;
    }

    if (decl.type !== 'declaration') continue;
    const { name, bodyHash, premises, annotations } = decl;
    if (!bodyHash) continue;

    // Declarations with premises are structural rules — skip
    if (premises.length > 0) continue;

    const allAnns = getAllAnnotations(annotations);

    if (isTypeExpr(bodyHash)) {
      // Type declaration: arrow chain or `type` keyword
      const returnType = getReturnType(bodyHash);
      const argTypes = getArgTypes(bodyHash);

      if (returnType === 'type') {
        baseTypes[name] = { name, annotations: allAnns };
      } else {
        constructors[name] = { name, argTypes, returnType, annotations: allAnns };
      }
    } else {
      // Simple identifier body (nullary constructor): `one: formula`
      const returnType = getReturnType(bodyHash);
      if (returnType && returnType !== 'type') {
        constructors[name] = { name, argTypes: [], returnType, annotations: allAnns };
      }
    }
  }

  return { baseTypes, constructors, directives };
}

// =============================================================================
// File Loading
// =============================================================================

/**
 * Resolve @extends directive to file path
 */
function resolveExtends(extendsName, basePath) {
  const dir = path.dirname(basePath);
  for (const ext of ['.family', '.calc', '']) {
    const tryPath = path.join(dir, `${extendsName}${ext}`);
    if (fs.existsSync(tryPath)) {
      return tryPath;
    }
  }
  return null;
}

/**
 * Load and merge a file with its @extends chain (synchronous).
 */
function loadWithExtends(filePath) {
  const source = fs.readFileSync(filePath, 'utf8');
  const decls = parseDeclarations(source, _frameworkParser, { annotations: true });
  const { baseTypes, constructors, directives } = extractDeclarations(decls);

  if (directives.extends) {
    const extendsPath = resolveExtends(directives.extends, filePath);
    if (extendsPath) {
      const parent = loadWithExtends(extendsPath);
      return {
        baseTypes: { ...parent.baseTypes, ...baseTypes },
        constructors: { ...parent.constructors, ...constructors },
        directives: {
          ...parent.directives,
          ...directives,
          family: directives.family || parent.directives.family,
          metavars: [...parent.directives.metavars, ...directives.metavars],
          schema: { ...parent.directives.schema, ...directives.schema }
        }
      };
    }
  }

  return { baseTypes, constructors, directives };
}

module.exports = {
  loadWithExtends
};
