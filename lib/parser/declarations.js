/**
 * Declaration Parser
 *
 * Calculus-agnostic parser for .ill, .calc, .family files.
 * Handles declaration structure; delegates expression parsing to provided function.
 *
 * Syntax:
 *   name: body.                          → TypeDecl or ClauseDecl
 *   name: body <- premise <- premise.    → ClauseDecl with premises
 *   name: body -o { consequent }.        → ForwardRule (detected by caller via hasMonad)
 *   name: body @key value @key "str".    → Annotations on declaration
 *   @key value.                          → Directive
 *   @key value1 value2.                  → Directive with multiple args
 *   #kind body.                          → QueryDirective
 *   % comment                            → skipped
 *   #import(path)                        → ImportDirective
 */

const { balancedSplit } = require('./balanced-split');

/**
 * Recursively substitute specific hashes in a term.
 * Used by query eigenvariable processing to replace metavar → bound.
 */
function _substituteHashes(h, subs, Store) {
  if (subs.has(h)) return subs.get(h);
  if (!Store.isTerm(h)) return h;
  const t = Store.tag(h);
  if (!t) return h;
  if (t === 'atom' || t === 'freevar' || t === 'metavar' || t === 'binlit' || t === 'bound') return h;
  if (t === 'arrlit') {
    const elems = Store.getArrayElements(h);
    if (!elems || elems.length === 0) return h;
    let changed = false;
    const ne = new Uint32Array(elems.length);
    for (let i = 0; i < elems.length; i++) {
      ne[i] = _substituteHashes(elems[i], subs, Store);
      if (ne[i] !== elems[i]) changed = true;
    }
    return changed ? Store.putArray(ne) : h;
  }
  const a = Store.arity(h);
  if (a === 0) return h;
  let changed = false;
  const nc = [];
  for (let i = 0; i < a; i++) {
    const c = Store.child(h, i);
    if (Store.isTermChild(c)) {
      const r = _substituteHashes(c, subs, Store);
      if (r !== c) changed = true;
      nc.push(r);
    } else {
      nc.push(c);
    }
  }
  return changed ? Store.put(t, nc) : h;
}

/**
 * Parse declarations from source text.
 * @param {string} source - source code
 * @param {Function} parseExpr - expression parser (string → hash)
 * @param {Object} [opts]
 * @param {boolean} [opts.annotations] - parse @key value annotations (for .calc/.family)
 * @returns {Array} array of declaration objects
 */
function parseDeclarations(source, parseExpr, opts = {}) {
  const declarations = [];
  const parseAnnotations = opts.annotations || false;
  let pos = 0;

  /** Compute line:col for current pos (on-demand, only for errors). */
  function posInfo() {
    let line = 1, col = 1;
    for (let i = 0; i < pos && i < source.length; i++) {
      if (source[i] === '\n') { line++; col = 1; } else col++;
    }
    return `${line}:${col}`;
  }

  while (pos < source.length) {
    skipWhitespaceAndComments();
    if (pos >= source.length) break;

    // Import directive: #import(path)
    if (source.slice(pos, pos + 8) === '#import(') {
      const end = source.indexOf(')', pos + 8);
      if (end === -1) throw new Error(`Unterminated #import at ${posInfo()}`);
      const importPath = source.slice(pos + 8, end).trim();
      declarations.push({ type: 'import', path: importPath });
      pos = end + 1;
      continue;
    }

    // Query directive: #kind [eigenvars...] body.
    // Optional [X Y Z] declares universally-quantified eigenvariables.
    // These wrap the body in nested forall nodes for proper ∀-elimination.
    if (source[pos] === '#') {
      pos++; // skip #
      const kind = readIdentifier();
      skipWs();

      // Parse optional eigenvariable declaration [X Y Z]
      const eigenVars = [];
      if (pos < source.length && source[pos] === '[') {
        pos++; // skip [
        while (pos < source.length && source[pos] !== ']') {
          if (/\s/.test(source[pos])) { pos++; continue; }
          const vm = source.slice(pos).match(/^[A-Z][a-zA-Z0-9_']*/);
          if (vm) {
            eigenVars.push(vm[0]);
            pos += vm[0].length;
          } else {
            pos++; // skip unexpected char
          }
        }
        if (pos < source.length) pos++; // skip ]
        skipWs();
      }

      const bodyStart = pos;
      const bodyEnd = findDeclEnd();
      let bodyText = source.slice(bodyStart, bodyEnd).trim();
      pos = bodyEnd + 1; // skip .
      bodyText = stripComments(bodyText);

      let bodyHash = bodyText ? parseExpr(bodyText) : null;

      // Wrap body in nested forall nodes for eigenvariables.
      // The body already has metavar(name) for uppercase vars from the parser.
      // Convert those specific metavars → bound(N), then wrap in forall nodes.
      // De Bruijn convention: outermost binder = highest index.
      if (bodyHash && eigenVars.length > 0) {
        const Store = require('../kernel/store');
        // Build metavar→bound substitution
        const depth = eigenVars.length;
        const subs = new Map();
        for (let i = 0; i < depth; i++) {
          const mvHash = Store.put('metavar', [eigenVars[i]]);
          // Outer var (i=0) gets highest de Bruijn index (depth-1)
          const boundHash = Store.put('bound', [BigInt(depth - 1 - i)]);
          subs.set(mvHash, boundHash);
        }
        // Substitute metavars → bound indices in the body
        bodyHash = _substituteHashes(bodyHash, subs, Store);
        // Wrap in nested forall (innermost var last)
        for (let i = depth - 1; i >= 0; i--) {
          bodyHash = Store.put('forall', [bodyHash]);
        }
      }

      declarations.push({
        type: 'query',
        kind,
        body: bodyText,
        bodyHash,
        eigenVars: eigenVars.length > 0 ? eigenVars : undefined
      });
      continue;
    }

    // Directive: @key args.
    if (source[pos] === '@') {
      pos++; // skip @
      const key = readIdentifier();
      skipWs();
      const argsStart = pos;
      const argsEnd = findDeclEnd();
      const argsText = source.slice(argsStart, argsEnd).trim();
      pos = argsEnd + 1; // skip .
      declarations.push({
        type: 'directive',
        key,
        args: parseDirectiveArgs(argsText)
      });
      continue;
    }

    // Declaration: name: body [<- premise]* [@annotations]* .
    const name = readDeclName();
    if (!name) {
      // Skip unknown character
      pos++;
      continue;
    }
    skipWs();
    if (pos >= source.length || source[pos] !== ':') {
      throw new Error(`Expected ':' after declaration name '${name}' at ${posInfo()}`);
    }
    pos++; // skip :
    skipWs();

    // Find the end of the declaration (the terminating '.')
    const declEnd = findDeclEnd();
    let declBody = source.slice(pos, declEnd);
    pos = declEnd + 1; // skip .

    // Split off annotations (@key value) from the body
    const annotations = [];
    if (parseAnnotations) {
      const { body: cleanBody, anns } = extractAnnotations(declBody);
      declBody = cleanBody;
      annotations.push(...anns);
    }

    // Strip inline comments from body before parsing
    declBody = stripComments(declBody);

    // Split body and premises on '<-'
    const parts = balancedSplit(declBody, '<-');
    const bodyText = parts[0].trim();
    const premiseTexts = parts.slice(1).map(p => p.trim()).filter(p => p.length > 0);

    const bodyHash = bodyText ? parseExpr(bodyText) : null;
    const premises = premiseTexts.map(p => parseExpr(p));

    declarations.push({
      type: 'declaration',
      name,
      bodyText,
      bodyHash,
      premises,
      annotations
    });
  }

  return declarations;

  // ── Helpers ──────────────────────────────────────────────────────────

  function skipWs() {
    while (pos < source.length && /\s/.test(source[pos])) pos++;
  }

  function skipWhitespaceAndComments() {
    while (pos < source.length) {
      if (/\s/.test(source[pos])) { pos++; continue; }
      if (source[pos] === '%') {
        // Skip to end of line
        while (pos < source.length && source[pos] !== '\n') pos++;
        continue;
      }
      break;
    }
  }

  function readIdentifier() {
    const m = source.slice(pos).match(/^[A-Za-z_][A-Za-z0-9_]*/);
    if (!m) return null;
    pos += m[0].length;
    skipWs();
    return m[0];
  }

  function readDeclName() {
    // Declaration names can include '/' for case prefixes: eq/z, plus/s4
    const m = source.slice(pos).match(/^[A-Za-z_][A-Za-z0-9_/]*/);
    if (!m) return null;
    pos += m[0].length;
    return m[0];
  }

  /** Find the position of the terminating '.' for a declaration.
   *  Handles nested parens and braces. */
  function findDeclEnd() {
    let depth = 0;
    let braceDepth = 0;
    let i = pos;
    while (i < source.length) {
      const c = source[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      else if (c === '{') braceDepth++;
      else if (c === '}') braceDepth--;
      else if (c === '%') {
        // Skip comment to end of line
        while (i < source.length && source[i] !== '\n') i++;
        continue;
      }
      else if (c === '"') {
        // Skip string literal
        i++;
        while (i < source.length && source[i] !== '"') {
          if (source[i] === '\\') i++; // skip escaped char
          i++;
        }
      }
      else if (c === '.' && depth === 0 && braceDepth === 0) {
        return i;
      }
      i++;
    }
    throw new Error(`Unterminated declaration at ${posInfo()}`);
  }

  /** Extract @key value annotations from the end of a declaration body. */
  function extractAnnotations(text) {
    const anns = [];
    // Find annotations: @key followed by value (string, number+assoc, identifier, or boolean)
    // Annotations are at the end, after the main expression
    const annotRe = /@(\w+)\s+(?:"([^"]*)"|(true|false)|(\d+)\s+(left|right|none)|(\d+)|(\w+))/g;
    let body = text;
    let match;
    // Find the first @ that starts an annotation
    const firstAt = findFirstAnnotationAt(text);
    if (firstAt >= 0) {
      body = text.slice(0, firstAt).trim();
      const annotPart = text.slice(firstAt);
      annotRe.lastIndex = 0;
      while ((match = annotRe.exec(annotPart)) !== null) {
        const key = match[1];
        if (match[2] !== undefined) {
          // Unescape string: \\ → \, \n → newline, \t → tab
          const raw = match[2].replace(/\\(.)/g, (_, c) => c === 'n' ? '\n' : c === 't' ? '\t' : c);
          anns.push({ key, value: { type: 'StringValue', value: raw } });
        } else if (match[3] !== undefined) {
          anns.push({ key, value: { type: 'BoolValue', value: match[3] === 'true' } });
        } else if (match[4] !== undefined) {
          anns.push({ key, value: { type: 'PrecValue', precedence: parseInt(match[4], 10), associativity: match[5] } });
        } else if (match[6] !== undefined) {
          anns.push({ key, value: { type: 'PrecValue', precedence: parseInt(match[6], 10), associativity: null } });
        } else if (match[7] !== undefined) {
          anns.push({ key, value: { type: 'IdentValue', name: match[7] } });
        }
      }
    }
    return { body, anns };
  }

  /** Find the position of the first '@' that starts an annotation (not inside expression). */
  function findFirstAnnotationAt(text) {
    let depth = 0;
    for (let i = 0; i < text.length; i++) {
      const c = text[i];
      if (c === '(') depth++;
      else if (c === ')') depth--;
      else if (c === '@' && depth === 0) {
        // Check it's followed by a word char (annotation key)
        if (i + 1 < text.length && /[a-zA-Z]/.test(text[i + 1])) {
          return i;
        }
      }
    }
    return -1;
  }

  /** Strip % comments from body text. */
  function stripComments(text) {
    return text.replace(/%[^\n]*/g, '').replace(/\n/g, ' ');
  }

  /** Parse directive arguments: handles identifiers, key=value pairs, strings. */
  function parseDirectiveArgs(text) {
    const args = [];
    const re = /(\w+)="([^"]*)"|"([^"]*)"|(\w+)/g;
    let match;
    while ((match = re.exec(text)) !== null) {
      if (match[1] !== undefined && match[2] !== undefined) {
        args.push({ type: 'keyValue', key: match[1], value: match[2] });
      } else if (match[3] !== undefined) {
        args.push({ type: 'string', value: match[3] });
      } else if (match[4] !== undefined) {
        args.push({ type: 'ident', name: match[4] });
      }
    }
    return args;
  }
}

module.exports = { parseDeclarations };
