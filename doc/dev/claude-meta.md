# Claude Code Configuration & Documentation System

Research on how to structure CALC's documentation, Claude Code integration, and workflow automation.

---

## 1. Documentation System

### 1.1 Current State

CALC uses a custom markdown renderer in `src/ui/routes/research/[slug].tsx`:
- Wiki-links `[[doc]]` → route links
- YAML frontmatter extraction (title only)
- Basic markdown → HTML conversion
- SSR via SolidStart

**Limitations:** No executable code blocks, no diagrams, minimal metadata.

### 1.2 Recommended Architecture: Hybrid Rendering

Inspired by `~/src/docgen`, use a hybrid approach where you control what renders where:

**Rendering Strategy:**

| Processor | Where | Why |
|-----------|-------|-----|
| `graphviz` | **Server** | WASM init is slow, produces static SVG |
| `mermaid` | **Client** | Interactive/animated, fast client-side |
| `katex` | **Server** | Static math, no interaction needed |
| `calc` | **Server** | Uses Node libs (lib/parser.js) |
| `proof` | **Client** | Interactive proof navigation |

**Code Block Syntax:**

```markdown
\`\`\`{graphviz}           # Server-rendered
digraph G { A -> B }
\`\`\`

\`\`\`{mermaid, client}    # Explicit client rendering
graph LR; A --> B
\`\`\`

\`\`\`{calc}               # Server-rendered formula
A -o B
\`\`\`
```

**Implementation approach:**

```javascript
// Hybrid processor (docgen-style)
const serverProcessors = {
  graphviz: async (code) => {
    const { Graphviz } = await import('@hpcc-js/wasm-graphviz');
    const gv = await Graphviz.load();
    return gv.dot(code); // Returns SVG string
  },
  calc: (code) => {
    const calc = require('../../lib/calc');
    const node = calc.parse(code);
    return `<span class="katex">${katex.renderToString(node.toLatex())}</span>`;
  },
  katex: (code) => katex.renderToString(code, { displayMode: true })
};

// Client blocks are passed through with markers for hydration
const clientBlocks = ['mermaid', 'proof'];
const renderClientBlock = (lang, code) =>
  `<div class="client-render" data-lang="${lang}">${escapeHtml(code)}</div>`;
```

**Client-side hydration:**

```javascript
// In browser, hydrate client blocks
document.querySelectorAll('.client-render').forEach(async (el) => {
  const lang = el.dataset.lang;
  const code = el.textContent;
  if (lang === 'mermaid') {
    const { default: mermaid } = await import('mermaid');
    const { svg } = await mermaid.render('m' + Date.now(), code);
    el.innerHTML = svg;
  }
});
```

### 1.3 Unified Frontmatter Schema

All markdown files in `doc/` use the same schema:

```yaml
---
title: Document Title
created: 2026-02-10
modified: 2026-02-10
summary: One-line description
tags: [tag1, tag2]
status: draft | review | stable  # optional
priority: HIGH | MEDIUM | LOW    # optional, for dev/todo items
---
```

**Fields:**
- `title` (required): Document title
- `created` (required): ISO date
- `modified` (auto-updated): Last modification date
- `summary` (required): Brief description for INDEX listings
- `tags` (optional): For filtering/search
- `status` (optional): Document maturity
- `priority` (optional): For TODO items

### 1.4 Interlinking

- **Wiki-links**: `[[document-name]]` → `/research/document-name`
- **Cross-folder**: `[[research/document]]`, `[[dev/todo]]`
- **Anchors**: `[[document#section]]` → `/research/document#section`
- **Backlinks**: Auto-generate backlinks section showing which docs link to current

---

## 2. Claude Code Configuration

### 2.1 File Hierarchy

```
CALC/
├── CLAUDE.md                    # Main project instructions (team-shared)
├── .claude/
│   ├── settings.json            # Team permissions, env vars
│   ├── settings.local.json      # Personal overrides (gitignored)
│   ├── rules/                   # Pattern-specific instructions
│   │   ├── research.md          # Rules for doc/research/
│   │   ├── lib.md               # Rules for lib/
│   │   └── tests.md             # Rules for tests/
│   └── skills/                  # Reusable workflows
│       ├── research/
│       │   └── SKILL.md
│       ├── commit/
│       │   └── SKILL.md
│       └── todo/
│           └── SKILL.md
└── doc/
    ├── dev/
    │   ├── INDEX.md             # Development docs index
    │   ├── todo.md              # Active tasks
    │   └── ANKI.md              # Flashcards
    ├── research/
    │   ├── INDEX.md             # Research docs index
    │   └── todo.md              # Research questions
    └── documentation/
        └── INDEX.md             # Technical docs index
```

### 2.2 CLAUDE.md Enhancements

Current CLAUDE.md should add:

```markdown
## Document Conventions

**Folder structure:**
- `doc/research/` - Research documents, theory, explorations
- `doc/dev/` - Development notes, architecture, TODOs
- `doc/documentation/` - User-facing technical docs

**Each folder has:**
- `INDEX.md` - Overview and links to all documents
- `todo.md` - Folder-specific tasks and questions

**Markdown format:**
- YAML frontmatter with: title, created, modified, summary, tags
- Wiki-links `[[doc]]` for interlinking
- Executable code blocks: mermaid, graphviz, calc, proof

**When creating documents:**
1. Add frontmatter with all required fields
2. Add entry to folder's INDEX.md
3. Use wiki-links to connect related docs
```

### 2.3 Rules Directory

**.claude/rules/research.md:**
```markdown
---
globs: ["doc/research/**/*.md"]
---

When working in doc/research/:

1. Always include YAML frontmatter: title, created, modified, summary, tags
2. Update doc/research/INDEX.md when creating/deleting docs
3. Use [[wiki-links]] for cross-references
4. Tag documents appropriately for discoverability
5. Keep documents concise - prefer depth over breadth
6. Add to doc/dev/ANKI.md if discovering flashcard-worthy concepts
```

**.claude/rules/lib.md:**
```markdown
---
globs: ["lib/**/*.js"]
---

When working in lib/:

1. Add JSDoc comments for public functions
2. Update lib/types/*.d.ts for TypeScript definitions
3. Write unit tests in tests/ for new functionality
4. Run `npm test` before committing
5. Isolate and test bugs before fixing
```

### 2.4 Skills

**.claude/skills/research/SKILL.md:**
```markdown
---
name: research
description: Create a new research document with proper structure
---

When /research is invoked with a topic:

1. Create `doc/research/{topic-slug}.md` with:
   - YAML frontmatter (title, created, modified, summary, tags)
   - Outline based on topic

2. Add entry to `doc/research/INDEX.md` in appropriate section

3. Search for related docs and add [[wiki-links]]

4. If concepts are flashcard-worthy, add to `doc/dev/ANKI.md`
```

**.claude/skills/todo/SKILL.md:**
```markdown
---
name: todo
description: Manage project tasks in doc/dev/todo.md
---

When /todo is invoked:

- `/todo` - Show current HIGH priority tasks
- `/todo add <task>` - Add task to appropriate priority section
- `/todo done <task>` - Mark task complete, move to DONE.md
- `/todo research <question>` - Add to doc/research/todo.md

Format tasks as:
### Task Name
**Priority:** HIGH | MEDIUM | LOW
**Status:** Not started | In progress | Blocked

Description...
```

---

## 3. Implementation Plan

### Phase 1: Documentation Processor (SSR)

1. **Extend markdown processor** (`src/ui/lib/markdown.ts`):
   - Parse YAML frontmatter
   - Detect executable code blocks
   - Route to processors (mermaid, graphviz, calc, etc.)
   - Return processed HTML

2. **Add WASM dependencies**:
   - `@hpcc-js/wasm-graphviz` for GraphViz
   - `mermaid` with SSR rendering
   - Already have KaTeX

3. **Update routes** to use new processor

### Phase 2: Metadata & Interlinking

1. **Add frontmatter to existing docs**
2. **Generate backlinks** at build/SSR time
3. **Create search/filter** by tags

### Phase 3: Claude Code Integration

1. **Enhance CLAUDE.md** with document conventions
2. **Create .claude/rules/** for pattern-specific guidance
3. **Create .claude/skills/** for workflow automation

---

## 4. Library Comparison

### Markdown Parsers

| Library | Size | Features | Notes |
|---------|------|----------|-------|
| marked | 38KB | Fast, extensible | Used by docgen |
| markdown-it | 65KB | Plugin ecosystem | Used by VitePress |
| unified/remark | ~200KB | AST manipulation | Most powerful, heaviest |

**Recommendation:** Stick with custom regex-based parser for simplicity, or migrate to marked.js for better extension support.

### Diagram Libraries

| Library | Size | SSR | Notes |
|---------|------|-----|-------|
| mermaid | ~2MB | Via CLI/puppeteer | Most diagram types |
| @hpcc-js/wasm-graphviz | ~3MB WASM | Yes (Node) | GraphViz DOT |
| viz.js | ~1.5MB | Yes | Archived, use hpcc-js |

### Math Rendering

| Library | Size | Notes |
|---------|------|-------|
| KaTeX | 300KB | Fast, subset of LaTeX (already using) |
| MathJax | 2.5MB | Full LaTeX, slower |

---

## 5. Sources

### Documentation Systems
- [Quarto Execution Options](https://quarto.org/docs/computations/execution-options.html)
- [Material for MkDocs - Diagrams](https://squidfunk.github.io/mkdocs-material/reference/diagrams/)
- [MDX](https://mdxjs.com/)
- [Using Frontmatter in Markdown](https://www.markdownlang.com/advanced/frontmatter.html)
- [GitHub Docs - YAML frontmatter](https://docs.github.com/en/contributing/writing-for-github-docs/using-yaml-frontmatter)

### Diagram Libraries
- [Mermaid.js](https://mermaid.js.org/)
- [@hpcc-js/wasm-graphviz](https://www.npmjs.com/package/@hpcc-js/wasm-graphviz)
- [d3-graphviz](https://github.com/magjac/d3-graphviz)

### Claude Code
- [Claude Code Memory](https://code.claude.com/docs/en/memory)
- [Claude Code Skills](https://code.claude.com/docs/en/skills)
- [Claude Code Settings](https://code.claude.com/docs/en/settings)
- [Writing a good CLAUDE.md](https://www.humanlayer.dev/blog/writing-a-good-claude-md)
- [Using CLAUDE.MD files](https://claude.com/blog/using-claude-md-files)

### Interlinking & Knowledge Management
- [Obsidian Internal Links](https://help.obsidian.md/links)
- [Dendron](https://wiki.dendron.so/)
