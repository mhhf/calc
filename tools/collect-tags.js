#!/usr/bin/env node
/**
 * Collect all tags from doc/ frontmatter and write doc/tags.yaml
 *
 * Parses YAML frontmatter from all markdown files in doc/ subdirectories,
 * counts tag frequency across documents, and writes a sorted tag map.
 *
 * Usage: node tools/collect-tags.js
 */

const fs = require('fs');
const path = require('path');
const matter = require('gray-matter');

const ROOT = path.resolve(__dirname, '..');
const DOC_DIR = path.join(ROOT, 'doc');
const OUTPUT = path.join(DOC_DIR, 'tags.yaml');

const SUBDIRS = ['research', 'theory', 'def', 'todo', 'documentation'];

function collectMarkdownFiles(dir) {
  const files = [];
  if (!fs.existsSync(dir)) return files;
  for (const entry of fs.readdirSync(dir)) {
    if (entry.endsWith('.md')) {
      files.push(path.join(dir, entry));
    }
  }
  return files;
}

function main() {
  const tagCounts = new Map();

  for (const subdir of SUBDIRS) {
    const dir = path.join(DOC_DIR, subdir);
    for (const file of collectMarkdownFiles(dir)) {
      try {
        const content = fs.readFileSync(file, 'utf8');
        const { data } = matter(content);
        if (Array.isArray(data.tags)) {
          // deduplicate within a single document
          const seen = new Set();
          for (const tag of data.tags) {
            const t = String(tag).trim();
            if (t && !seen.has(t)) {
              seen.add(t);
              tagCounts.set(t, (tagCounts.get(t) || 0) + 1);
            }
          }
        }
      } catch (e) {
        console.error(`warning: ${path.relative(ROOT, file)}: ${e.message}`);
      }
    }
  }

  // sort by frequency descending, then alphabetically
  const sorted = [...tagCounts.entries()].sort((a, b) => {
    if (b[1] !== a[1]) return b[1] - a[1];
    return a[0].localeCompare(b[0]);
  });

  const lines = ['tags:'];
  for (const [tag, count] of sorted) {
    // quote tags that contain special YAML characters
    const needsQuote = /[:#\[\]{},>|&*!%@`]/.test(tag) || tag.includes("'");
    const key = needsQuote ? `"${tag}"` : tag;
    lines.push(`  ${key}: ${count}`);
  }
  lines.push('');

  fs.writeFileSync(OUTPUT, lines.join('\n'), 'utf8');
  console.log(`${sorted.length} tags written to doc/tags.yaml`);
}

main();
