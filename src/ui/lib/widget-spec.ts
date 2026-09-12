/**
 * widget-spec — parsing of book widget bodies (the `key: value` spec headers and
 * inline program source). Pure, no framework/JSX imports, so it is unit-testable
 * in plain node and shared by every widget component and the chapter validator.
 */

/**
 * Parse a `key: value` widget body. Recognized `keys` capture their value; other
 * lines continue the previous value. A value of `|` (or `|-`, `>`, `>-`) starts a
 * YAML-style block scalar: subsequent more-indented lines form the value with the
 * common leading indent stripped, ending at the first line indented less.
 */
export function parseSpecBody(body: string, keys: string[]): Record<string, string> {
  const spec: Record<string, string> = {};
  let current: string | null = null;
  // While inside a `key: |` block scalar: -1 = awaiting the first content line
  // (which fixes the base indent), else the base indent to strip.
  let blockIndent: number | null = null;
  for (const line of body.split('\n')) {
    if (blockIndent !== null && current !== null) {
      if (line.trim() === '') { spec[current] += '\n'; continue; }
      const indent = line.length - line.trimStart().length;
      if (blockIndent === -1) blockIndent = indent;
      if (indent >= blockIndent) {
        spec[current] += (spec[current] ? '\n' : '') + line.slice(blockIndent);
        continue;
      }
      blockIndent = null; // dedent ends the block; reprocess this line as a key
    }
    const m = line.match(/^(\w+)\s*:\s*(.*)$/);
    if (m && keys.includes(m[1])) {
      current = m[1];
      const v = m[2].trim();
      if (v === '|' || v === '|-' || v === '>' || v === '>-') {
        spec[current] = '';
        blockIndent = -1;
      } else {
        spec[current] = m[2];
      }
    } else if (current !== null && blockIndent === null && line.trim() !== '') {
      spec[current] += '\n' + line;
    }
  }
  for (const k of Object.keys(spec)) spec[k] = spec[k].replace(/\s+$/, '');
  return spec;
}

/**
 * The inline program for a server-run widget with no `file:`. Prefers an explicit
 * `source: |` block; otherwise the body itself is the program, with recognized
 * `key:` spec lines (maxSteps/title/…) removed so only program text is sent to
 * the parser.
 */
export function inlineProgram(body: string, specKeys: string[], spec: Record<string, string>): string {
  if (spec.source != null && spec.source !== '') return spec.source;
  return body
    .split('\n')
    .filter((l) => {
      const m = l.match(/^(\w+)\s*:/);
      return !(m && specKeys.includes(m[1]));
    })
    .join('\n')
    .trim();
}
