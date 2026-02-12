/**
 * Calculus loader
 *
 * Loads and merges .family/.calc files via @extends chains.
 * Extracts type/constructor declarations for v2 calculus module.
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
        const metavar = { type: decl.head?.name };
        for (const premise of decl.premises || []) {
          if (premise && premise.type === 'Annotation') {
            metavar[premise.key] = premise.value?.value || premise.value?.name;
          }
        }
        directives.metavars.push(metavar);
      } else if (directive === 'schema') {
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
        baseTypes[decl.name] = {
          name: decl.name,
          annotations: getAllAnnotations(decl.annotations)
        };
      } else {
        constructors[decl.name] = {
          name: decl.name,
          argTypes,
          returnType,
          annotations: getAllAnnotations(decl.annotations)
        };
      }
      continue;
    }

    // Handle clause declarations (nullary constructors)
    if (decl.type === 'ClauseDecl') {
      if (decl.premises.length === 0 && decl.head) {
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
 * Load and merge a file with its @extends chain
 */
async function loadWithExtends(filePath) {
  const result = await tsParser.parseFile(filePath);
  if (!result.success) {
    throw new Error(`Failed to parse ${filePath}: ${result.error}`);
  }

  const { baseTypes, constructors, directives } = extractDeclarations(result.ast);

  if (directives.extends) {
    const extendsPath = resolveExtends(directives.extends, filePath);
    if (extendsPath) {
      const parent = await loadWithExtends(extendsPath);
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
  extractDeclarations,
  getAnnotation,
  getAllAnnotations,
  getArgTypes,
  getReturnType,
  loadWithExtends
};
