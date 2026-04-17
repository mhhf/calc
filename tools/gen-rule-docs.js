#!/usr/bin/env node
/**
 * gen-rule-docs — generate one `doc/def/<NNNN>_rule-<name>.md` per ILL
 * inference rule.
 *
 * Each doc carries the rule's shape (premises → conclusion as parsed from
 * `calculus/ill/ill.rules`), its structural metadata (connective, side,
 * arity, invertibility, structural/bridge flags), and a stable identifier
 * used by the proof viewer to link rule chips back to the matching doc
 * (slug: `rule-<name>`).
 *
 * Numbering discipline
 * ────────────────────
 * Rules are numbered once, then kept stable across regeneration. The
 * mapping `rule-name → NNNN` is persisted in `doc/def/meta.yaml` under
 * `rule_mappings:` so subsequent runs:
 *   - keep existing files at their assigned numbers (overwrite in place)
 *   - assign the next free NNNN to newly-added rules only
 *
 * Design choice: these are machine-derived reference stubs, not
 * hand-written encyclopedia entries. Each file begins with an
 * `autogen: true` frontmatter key and carries a visible "Auto-generated…"
 * note. Humans may extend with a "Notes" section, but the frontmatter /
 * shape / properties tables WILL be overwritten on regeneration.
 *
 * Invocation:
 *   node tools/gen-rule-docs.js               # preview + write
 *   node tools/gen-rule-docs.js --dry-run     # preview only
 */

'use strict';

const fs = require('fs');
const path = require('path');

const DEF_DIR = path.resolve(__dirname, '../doc/def');
const META_PATH = path.join(DEF_DIR, 'meta.yaml');
const RULES_SRC = path.resolve(__dirname, '../calculus/ill/ill.rules');

const DRY_RUN = process.argv.includes('--dry-run');

// ─────────────────────────── .rules parser ─────────────────────────────
/**
 * Parse `ill.rules` into an array of { name, conclusion, premises[], annotations{} }.
 * The grammar is small enough that a hand-rolled scan is clearer than
 * importing the full calculus loader (and keeps this tool runnable in
 * isolation).
 */
function parseRulesFile(src) {
  // Strip `%` comments and line continuations that end with `.` (rule term).
  const lines = src.split('\n');
  const blocks = [];
  let cur = null;
  for (const raw of lines) {
    const line = raw.replace(/%.*$/, '').trimEnd();
    if (!line.trim()) continue;
    // new rule block starts on a non-indented `name: ...` line
    if (!line.startsWith(' ') && !line.startsWith('\t')) {
      if (cur) blocks.push(cur);
      cur = { head: line, body: [] };
    } else if (cur) {
      cur.body.push(line.trim());
    }
  }
  if (cur) blocks.push(cur);

  const rules = [];
  for (const b of blocks) {
    const head = b.head;
    // Skip directive lines like `@formulas A, B, C`
    if (head.startsWith('@')) continue;
    const m = head.match(/^([a-zA-Z_][\w]*)\s*:\s*(.+?)\.?$/);
    if (!m) continue;
    const name = m[1];
    const conclusion = m[2].trim();
    const premises = [];
    const annotations = {};
    for (const line of b.body) {
      let t = line;
      if (t.endsWith('.')) t = t.slice(0, -1).trimEnd();
      if (t.startsWith('<-')) {
        premises.push(t.slice(2).trim());
      } else if (t.startsWith('@')) {
        const am = t.match(/^@(\w+)\s*(.*)$/);
        if (am) annotations[am[1]] = am[2].replace(/^"|"$/g, '').trim();
      }
    }
    rules.push({ name, conclusion, premises, annotations });
  }
  return rules;
}

// ───────────────────────────── meta.yaml ───────────────────────────────
function readMeta() {
  const raw = fs.readFileSync(META_PATH, 'utf-8');
  const currentMatch = raw.match(/^current_number:\s*(\d+)/m);
  const current_number = currentMatch ? parseInt(currentMatch[1], 10) : 1;
  const mapping = {};
  const lines = raw.split('\n');
  let inBlock = false;
  for (const line of lines) {
    if (/^rule_mappings:\s*$/.test(line)) { inBlock = true; continue; }
    if (inBlock) {
      const mm = line.match(/^\s+(\w+):\s*(\d+)\s*$/);
      if (mm) {
        mapping[mm[1]] = parseInt(mm[2], 10);
      } else if (/^\S/.test(line)) {
        inBlock = false;
      }
    }
  }
  return { current_number, rule_mappings: mapping };
}

function writeMeta(meta) {
  const lines = [`current_number: ${meta.current_number}`];
  const names = Object.keys(meta.rule_mappings).sort();
  if (names.length > 0) {
    lines.push('rule_mappings:');
    for (const n of names) {
      lines.push(`  ${n}: ${meta.rule_mappings[n]}`);
    }
  }
  fs.writeFileSync(META_PATH, lines.join('\n') + '\n');
}

// ─────────────────────── rule → markdown body ──────────────────────────
const CONN_SYMBOL = {
  tensor: '⊗', loli: '⊸', with: '&', oplus: '⊕', bang: '!',
  monad: '{·}', one: '1', zero: '0', exists: '∃', forall: '∀',
};

const CONN_NAME = {
  tensor: 'Tensor', loli: 'Linear Implication', with: 'With',
  oplus: 'Plus', bang: 'Bang', monad: 'Monad', one: 'One', zero: 'Zero',
  exists: 'Exists', forall: 'Forall',
};

function inferSideKind(conclusion) {
  // Everything before `|-` is the antecedent. We decide "left" vs "right"
  // by where the principal connective shows up relative to the turnstile.
  // This is only used for a fallback human-readable label.
  const [ante, succ] = conclusion.split(/\s*\|-\s*/);
  return { antecedent: ante || '', succedent: succ || '' };
}

function detectConnective(rule) {
  // Pull the connective name out of the rule name by suffix convention:
  // tensor_r, tensor_l, loli_r, loli_l, with_l1, with_l2, oplus_r1, oplus_r2,
  // oplus_l, exists_r, one_r, etc. Falls back to 'structural' for id, copy.
  const m = rule.name.match(/^([a-zA-Z]+?)(_[rl]\d?)?$/);
  if (!m) return null;
  const base = m[1];
  if (CONN_NAME[base]) return base;
  return null;
}

function titleFor(rule) {
  const conn = detectConnective(rule);
  const pretty = rule.annotations.pretty || rule.name;
  if (conn) {
    const s = sideOf(rule.name);
    const side = s === 'l' ? ' Left' : s === 'r' ? ' Right' : '';
    return `${rule.name} — ${CONN_NAME[conn]}${side} (${pretty})`;
  }
  // Structural (id, copy, promotion, dereliction, absorption, monad_r, monad_l)
  const special = {
    id: 'Identity Axiom',
    copy: 'Contraction (Cartesian Copy)',
    promotion: 'Promotion (!R)',
    dereliction: 'Dereliction (!D)',
    absorption: 'Absorption (!L)',
  }[rule.name];
  if (special) return `${rule.name} — ${special}`;
  return `${rule.name} — ${pretty}`;
}

function sideOf(name) {
  if (/_l(\d+)?$/.test(name)) return 'l';
  if (/_r(\d+)?$/.test(name)) return 'r';
  return null;
}

function summaryFor(rule) {
  const conn = detectConnective(rule);
  const side = sideOf(rule.name);
  if (rule.name === 'id') return 'Identity axiom: `A ⊢ A`. Closes a branch when the succedent matches a linear assumption.';
  if (rule.name === 'copy') return 'Contraction on cartesian context: duplicates a reusable (`!`-wrapped) assumption into the linear zone.';
  if (rule.name === 'promotion') return 'Promotion: introduces `!A` when `A` is provable under an empty linear context (exponential right-introduction).';
  if (rule.name === 'dereliction') return 'Dereliction: uses a `!A` resource once, as if it were `A` in the linear zone.';
  if (rule.name === 'absorption') return 'Absorption: moves `!A` from the linear zone into the cartesian (persistent) zone.';
  if (conn && side) {
    const direction = side === 'r' ? 'Introduces' : 'Eliminates';
    const zone = side === 'r' ? 'right' : 'left';
    return `${direction} the \`${conn}\` (${CONN_SYMBOL[conn]}) connective on the ${zone} of the sequent.`;
  }
  return rule.annotations.pretty ? `Inference rule ${rule.annotations.pretty}.` : `Inference rule ${rule.name}.`;
}

function fmtInferenceBlock(rule) {
  // Render the rule as
  //     premise₁    premise₂
  //     ───────────────────── rulename
  //         conclusion
  // inside a code block so it survives in every markdown renderer.
  const premStr = rule.premises.length > 0
    ? rule.premises.map((p) => p.trim()).join('      ')
    : '  (no premises)';
  const conc = rule.conclusion.trim();
  const label = rule.annotations.pretty || rule.name;
  const width = Math.max(premStr.length, conc.length) + 2;
  const bar = '─'.repeat(Math.min(80, width));
  return ['```', premStr, `${bar}  ${label}`, conc, '```'].join('\n');
}

function propertiesTable(rule, meta) {
  const rows = [
    ['Name', '`' + rule.name + '`'],
    ['Pretty', rule.annotations.pretty ? '`' + rule.annotations.pretty + '`' : '—'],
    ['Connective', detectConnective(rule) || '—'],
    ['Side', sideOf(rule.name) === 'l' ? 'left' : sideOf(rule.name) === 'r' ? 'right' : '—'],
    ['Premises', String(rule.premises.length)],
    ['Invertible', meta.invertible !== null && meta.invertible !== undefined ? String(meta.invertible) : 'unspecified'],
    ['Structural', meta.structural ? 'true' : 'false'],
    ['Bridge', meta.bridge || '—'],
    ['Binding', rule.annotations.binding || '—'],
  ];
  const head = '| Property | Value |\n|---|---|\n';
  return head + rows.map(([k, v]) => `| ${k} | ${v} |`).join('\n');
}

function classifyConnective(rule) {
  const conn = detectConnective(rule);
  if (!conn) return null;
  const POLARITY = {
    tensor: 'positive', loli: 'negative', with: 'negative', oplus: 'positive',
    bang: 'positive', monad: 'negative', one: 'positive', zero: 'positive',
    exists: 'positive', forall: 'negative',
  };
  return POLARITY[conn] || null;
}

function buildMarkdown(rule, meta) {
  const title = titleFor(rule);
  const summary = summaryFor(rule);
  const conn = detectConnective(rule);
  const polarity = classifyConnective(rule);
  const synthesized = !!meta.synthesized;

  const tags = ['ill', 'inference-rule'];
  if (conn) tags.push(conn);
  if (polarity) tags.push(polarity + '-connective');
  const sideTag = sideOf(rule.name) === 'l' ? 'left-rule' : sideOf(rule.name) === 'r' ? 'right-rule' : 'structural-rule';
  tags.push(sideTag);
  if (meta.structural) tags.push('structural');
  if (meta.bridge) tags.push('bridge');

  const fmYaml = [
    '---',
    `term: "${title}"`,
    `summary: "${summary.replace(/"/g, '\\"')}"`,
    `tags: [${tags.map((t) => t).join(', ')}]`,
    'autogen: true',
    'autogen_source: calculus/ill/ill.rules',
    'see_also: []',
    '---',
    '',
  ].join('\n');

  const parts = [];
  parts.push(fmYaml);
  parts.push(`# \`${rule.name}\` — ${title.replace(rule.name + ' — ', '')}`);
  parts.push('');
  parts.push(summary);
  parts.push('');
  parts.push('## Shape');
  parts.push('');
  parts.push(fmtInferenceBlock(rule));
  parts.push('');
  parts.push('## Properties');
  parts.push('');
  parts.push(propertiesTable(rule, meta));
  parts.push('');
  parts.push('## In CALC');
  parts.push('');
  if (synthesized) {
    parts.push(
      `Emitted by the focused prover as \`${rule.name}\`. Proof-tree/v1 nodes ` +
      `serialize with \`"rule": "${rule.name}"\`. This rule is **synthesized** ` +
      'by the calculus loader from the connective declaration in ' +
      '[`calculus/ill/ill.calc`](../../calculus/ill/ill.calc) — it is not written ' +
      'out explicitly in `ill.rules`. Dispatch is handled by the rule interpreter ' +
      '(`lib/prover/rule-interpreter.js`).',
    );
  } else {
    parts.push(
      `Emitted by the focused prover as \`${rule.name}\`. Proof-tree/v1 nodes ` +
      `serialize with \`"rule": "${rule.name}"\`. The rule is loaded from ` +
      '[`calculus/ill/ill.rules`](../../calculus/ill/ill.rules) and dispatched ' +
      'by the rule interpreter (`lib/prover/rule-interpreter.js`).',
    );
  }
  parts.push('');
  if (conn) {
    parts.push(
      `See also the connective definition in [\`calculus/ill/ill.calc\`](../../calculus/ill/ill.calc), ` +
      `which assigns \`${conn}\` its arity and polarity.`,
    );
    parts.push('');
  }
  parts.push('---');
  parts.push('');
  parts.push('> _Auto-generated from `calculus/ill/ill.rules` by `tools/gen-rule-docs.js`. ' +
    'Regenerate after any change to the rule set; manual edits above the `---` separator WILL be preserved if placed below a `## Notes` header._');
  parts.push('');

  return parts.join('\n');
}

// ─────────────────────────── loader glue ───────────────────────────────
async function loadCalculusMeta() {
  // Loading the calculus gives us invertible / structural / bridge / numPremises
  // which are derived from the same source (ill.rules) but may include
  // post-processing. We prefer the calculus loader's view where it disagrees
  // with the raw file, since that's what the prover actually uses.
  const calc = require('../lib');
  const ill = await calc.loadILL();
  return ill.rules || {};
}

// For rules that are synthesized by the calculus loader (e.g. monad_r /
// monad_l are derived from connective declarations in ill.calc, not
// ill.rules), construct a plausible shape from what we know.
function synthesizeShape(name, cmeta) {
  const side = sideOf(name);
  const conn = cmeta.descriptor?.connective;
  if (conn === 'monad' && side === 'r') {
    return { conclusion: 'G ; D |- { A }', premises: ['G ; D |- A'] };
  }
  if (conn === 'monad' && side === 'l') {
    return { conclusion: 'G ; D, { A } |- { C }', premises: ['G ; D, A |- { C }'] };
  }
  return { conclusion: `-- rule ${name} --`, premises: [] };
}

// ─────────────────────────────── main ──────────────────────────────────
(async function main() {
  const src = fs.readFileSync(RULES_SRC, 'utf-8');
  const parsedRules = parseRulesFile(src);
  const parsedByName = new Map(parsedRules.map((r) => [r.name, r]));

  const calcRules = await loadCalculusMeta();
  if (Object.keys(calcRules).length === 0) {
    console.error('No rules from loaded calculus');
    process.exit(1);
  }

  const meta = readMeta();
  const usedNumbers = new Set(Object.values(meta.rule_mappings));
  let nextNumber = meta.current_number;

  const results = [];
  for (const name of Object.keys(calcRules)) {
    const cmeta = calcRules[name] || {};
    const parsed = parsedByName.get(name);
    const shape = parsed
      ? { conclusion: parsed.conclusion, premises: parsed.premises }
      : synthesizeShape(name, cmeta);
    const rule = {
      name,
      conclusion: shape.conclusion,
      premises: shape.premises,
      annotations: parsed?.annotations || {
        pretty: cmeta.pretty || name,
        invertible: cmeta.invertible !== null && cmeta.invertible !== undefined ? String(cmeta.invertible) : undefined,
      },
    };
    let num = meta.rule_mappings[name];
    if (num === undefined) {
      nextNumber = nextNumber + 1;
      while (usedNumbers.has(nextNumber)) nextNumber++;
      num = nextNumber;
      usedNumbers.add(num);
      meta.rule_mappings[name] = num;
    }
    const padded = String(num).padStart(4, '0');
    const slug = `${padded}_rule-${name}`;
    const file = path.join(DEF_DIR, slug + '.md');
    const body = buildMarkdown(rule, {
      invertible: cmeta.invertible ?? (rule.annotations.invertible === 'true' ? true : (rule.annotations.invertible === 'false' ? false : null)),
      structural: cmeta.structural || rule.annotations.structural === 'true',
      bridge: cmeta.bridge || rule.annotations.bridge || null,
      synthesized: !parsed,
    });
    results.push({ file, slug, body, existed: fs.existsSync(file) });
  }
  meta.current_number = Math.max(meta.current_number, ...Object.values(meta.rule_mappings));

  // Write out
  for (const r of results) {
    if (DRY_RUN) {
      console.log(`[dry-run] would write ${path.basename(r.file)} (${r.body.length}B)${r.existed ? ' — replaces existing' : ''}`);
    } else {
      fs.writeFileSync(r.file, r.body);
    }
  }
  if (!DRY_RUN) {
    writeMeta(meta);
  }

  const written = results.filter((r) => !r.existed).length;
  const replaced = results.length - written;
  console.log(`${DRY_RUN ? '[dry-run] ' : ''}${written} new, ${replaced} replaced, ${results.length} total`);
  console.log(`current_number = ${meta.current_number}`);
})().catch((e) => {
  console.error(e);
  process.exit(1);
});
