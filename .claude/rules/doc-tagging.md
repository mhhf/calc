---
paths:
  - "doc/**"
---

# Document Tagging Discipline

When creating a new document or significantly extending an existing one in `doc/`:

1. **Read `doc/tags.yaml`** to see the current tag vocabulary with frequencies.
2. **Review existing tags** — pick relevant tags that already exist before inventing new ones. Prefer high-frequency tags for discoverability.
3. **Add new tags** only when no existing tag covers the concept. Use lowercase kebab-case (e.g., `proof-theory`, `forward-chaining`).
4. **Update the document's `tags:` frontmatter** with both existing and new tags.
5. **Run `npm run tags`** to regenerate `doc/tags.yaml` with updated counts.
