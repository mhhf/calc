/**
 * validate-chapter.js — machine-check book chapters (TODO_0308).
 *
 * Usage: node tools/validate-chapter.js doc/book/*.md
 *
 * Checks, per chapter:
 *   frontmatter   — title/part/partTitle/chapter/summary present
 *   {prove}       — goal parses AND is provable by the auto prover;
 *                   restricted `rules:` names exist
 *   {rule}        — every named rule exists in the calculus
 *   {formula}     — body parses as a formula (when non-empty)
 *   {calc}        — body parses as a formula
 *   {quiz}        — every question has >= 2 options and >= 1 correct
 *   [[wiki]]      — every wiki-link resolves against the doc manifest
 *   {exec/game/collapse} — referenced file: exists on disk
 *
 * Exit code 0 iff every checked chapter is clean.
 */

import fs from 'fs';
import path from 'path';
import { fileURLToPath } from 'url';

const ROOT = path.join(path.dirname(fileURLToPath(import.meta.url)), '..');

const browser = await import(path.join(ROOT, 'lib/browser.js'));
const bundle = JSON.parse(fs.readFileSync(path.join(ROOT, 'out/ill.json'), 'utf8'));
browser.initFromBundle(bundle);

const docScan = await import(path.join(ROOT, 'src/ui/plugins/doc-scan.js'));
const manifest = docScan.getDocManifest(path.join(ROOT, 'doc'));

const BLOCK_RE = /```(?:\{([^}]+)\}|(mermaid|katex|graphviz|viz|calc|proof))\n([\s\S]*?)```/g;

function parseHeader(optionsStr) {
  const commaParts = optionsStr.split(',').map(s => s.trim());
  const headTokens = commaParts[0].split(/\s+/);
  const options = {};
  for (let i = 1; i < commaParts.length; i++) {
    const [k, v] = commaParts[i].split('=');
    options[k.trim()] = v?.trim() || 'true';
  }
  return { processor: headTokens[0], positional: headTokens.slice(1), options };
}

function parseSpecBody(body, keys) {
  const spec = {};
  let current = null;
  for (const line of body.split('\n')) {
    const m = line.match(/^(\w+)\s*:\s*(.*)$/);
    if (m && keys.includes(m[1])) {
      current = m[1];
      spec[current] = m[2];
    } else if (current !== null && line.trim() !== '') {
      spec[current] += '\n' + line;
    }
  }
  return spec;
}

function knownRule(name) {
  const calc = browser.getCalculus();
  return !!calc.rules[name];
}

function resolveWiki(raw, sourceRoute) {
  const RESOLVE_ROUTE = { theory: 'theory', def: 'def', docs: 'docs', documentation: 'docs', book: 'book' };
  let targetRoute = sourceRoute;
  let name = raw.trim();
  if (name.includes('/')) {
    const parts = name.split('/').filter(p => p !== '..' && p.length > 0);
    if (parts.length < 2) return false;
    const resolved = RESOLVE_ROUTE[parts[0]];
    if (!resolved) return false;
    targetRoute = resolved;
    name = parts.slice(1).join('/');
  }
  const slugs = manifest[targetRoute] || [];
  if (slugs.includes(name)) return true;
  return slugs.filter(s => /^\d{4}_/.test(s) && s.slice(5) === name).length === 1;
}

function validateFile(file) {
  const problems = [];
  const content = fs.readFileSync(file, 'utf8');

  // Frontmatter
  const fmMatch = content.match(/^---\n([\s\S]*?)\n---\n/);
  if (!fmMatch) {
    problems.push('missing frontmatter');
  } else {
    for (const key of ['title', 'part', 'partTitle', 'chapter', 'summary']) {
      if (!new RegExp(`^${key}\\s*:`, 'm').test(fmMatch[1])) {
        problems.push(`frontmatter missing "${key}"`);
      }
    }
  }

  // Fenced special blocks
  let m;
  BLOCK_RE.lastIndex = 0;
  const fences = [];
  while ((m = BLOCK_RE.exec(content)) !== null) {
    fences.push({ header: m[1] || m[2], body: m[3], at: content.slice(0, m.index).split('\n').length });
  }

  for (const { header, body, at } of fences) {
    const { processor, positional } = parseHeader(header);

    if (processor === 'prove') {
      const spec = parseSpecBody(body, ['goal', 'rules', 'mode', 'hint', 'id', 'title']);
      if (!spec.goal || !spec.goal.trim()) {
        problems.push(`line ${at}: {prove} has no goal`);
        continue;
      }
      let seq;
      try {
        seq = browser.parseSequent(spec.goal.trim());
      } catch (e) {
        problems.push(`line ${at}: {prove} goal does not parse: ${e.message.slice(0, 100)}`);
        continue;
      }
      try {
        const r = browser.proveString(spec.goal.trim(), { maxDepth: 200 });
        const proven = r && (r.proven || r.success || r.complete || r.pt || r.tree);
        if (!proven) problems.push(`line ${at}: {prove} goal is NOT provable: ${spec.goal.trim()}`);
      } catch (e) {
        problems.push(`line ${at}: {prove} prover error on "${spec.goal.trim()}": ${e.message.slice(0, 100)}`);
      }
      if (spec.rules) {
        for (const rn of spec.rules.split(',').map(s => s.trim()).filter(Boolean)) {
          if (!knownRule(rn)) problems.push(`line ${at}: {prove} unknown rule in restriction: ${rn}`);
        }
      }
    } else if (processor === 'rule') {
      const names = [...positional, ...body.split('\n').map(s => s.trim()).filter(Boolean)];
      if (names.length === 0) problems.push(`line ${at}: {rule} block names no rule`);
      for (const name of names) {
        if (!knownRule(name)) problems.push(`line ${at}: {rule} unknown rule: ${name}`);
      }
    } else if (processor === 'formula' || processor === 'calc') {
      const text = body.trim();
      if (text) {
        try {
          browser.parseFormula(text);
        } catch (e) {
          problems.push(`line ${at}: {${processor}} does not parse: "${text.slice(0, 60)}" — ${e.message.slice(0, 80)}`);
        }
      }
    } else if (processor === 'quiz') {
      const questions = body.split(/^Q\s*:/m).slice(1);
      if (questions.length === 0) problems.push(`line ${at}: {quiz} has no Q:`);
      questions.forEach((q, qi) => {
        const opts = [...q.matchAll(/^\s*-\s*\[([ xX])\]/gm)];
        if (opts.length < 2) problems.push(`line ${at}: {quiz} Q${qi + 1} has < 2 options`);
        if (!opts.some(o => o[1].toLowerCase() === 'x')) {
          problems.push(`line ${at}: {quiz} Q${qi + 1} has no correct option`);
        }
      });
    } else if (processor === 'exec' || processor === 'game' || processor === 'collapse') {
      const spec = parseSpecBody(body, ['file', 'query', 'init', 'seed', 'title', 'maxSteps', 'step']);
      if (spec.file) {
        const p = path.join(ROOT, spec.file.trim());
        if (!fs.existsSync(p)) problems.push(`line ${at}: {${processor}} file not found: ${spec.file.trim()}`);
      } else if (processor !== 'exec') {
        problems.push(`line ${at}: {${processor}} needs a file:`);
      }
    }
  }

  // Wiki links (outside fences — strip fenced blocks first)
  const noFences = content.replace(BLOCK_RE, '').replace(/```[\s\S]*?```/g, '');
  for (const wm of noFences.matchAll(/\[\[([^\]|]+)(?:\|[^\]]+)?\]\]/g)) {
    if (!resolveWiki(wm[1], 'book')) problems.push(`unresolved wiki-link: [[${wm[1]}]]`);
  }

  return problems;
}

const files = process.argv.slice(2);
if (files.length === 0) {
  console.error('usage: node tools/validate-chapter.js doc/book/*.md');
  process.exit(2);
}

let failed = 0;
for (const file of files) {
  const problems = validateFile(file);
  if (problems.length === 0) {
    console.log(`✓ ${path.basename(file)}`);
  } else {
    failed++;
    console.log(`✗ ${path.basename(file)}`);
    for (const p of problems) console.log(`    ${p}`);
  }
}
process.exit(failed === 0 ? 0 : 1);
