---
title: "Wiki-Link Backlinks"
created: 2026-02-18
modified: 2026-02-18
summary: "Generate and display backlinks from [[wiki-link]] references across docs"
tags: [tooling, documentation, backlinks]
type: implementation
status: planning
priority: 3
depends_on: []
required_by: []
---

# Wiki-Link Backlinks

Extracted from TODO_0025. Scan all markdown files for `[[target]]` links and generate a backlinks section for each document.

- [ ] Build backlink index at build time (scan all .md files for wiki-links)
- [ ] Inject backlinks section into processDocument output
- [ ] UI: display backlinks at bottom of doc page
