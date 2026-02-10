import { createAsync, cache } from "@solidjs/router";
import { A } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense, For } from "solid-js";
import fs from "fs";
import path from "path";

const RESEARCH_DIR = path.resolve(process.cwd(), "doc/research");

interface ResearchDoc {
  slug: string;
  title: string;
  description: string;
  tags: string[];
}

// Parse metadata from markdown file
function parseMetadata(content: string, filename: string): ResearchDoc {
  const lines = content.split("\n");
  const slug = filename.replace(".md", "");

  // Extract title from first # heading
  const titleLine = lines.find(l => l.startsWith("# "));
  const title = titleLine ? titleLine.replace("# ", "") : slug;

  // Extract description from first paragraph after title
  let description = "";
  let inDescription = false;
  for (const line of lines) {
    if (line.startsWith("# ")) {
      inDescription = true;
      continue;
    }
    if (inDescription && line.trim() && !line.startsWith("#") && !line.startsWith(">") && !line.startsWith("-")) {
      description = line.trim().slice(0, 200);
      break;
    }
  }

  // Extract tags from **Tags:** line
  const tagsLine = lines.find(l => l.startsWith("**Tags:**"));
  const tags: string[] = [];
  if (tagsLine) {
    const tagMatches = tagsLine.match(/`([^`]+)`/g);
    if (tagMatches) {
      tags.push(...tagMatches.map(t => t.replace(/`/g, "")));
    }
  }

  return { slug, title, description, tags: tags.slice(0, 5) };
}

// Server-side data loading with caching
const getResearchIndex = cache(async () => {
  "use server";

  const files = fs.readdirSync(RESEARCH_DIR).filter(f => f.endsWith(".md"));

  const docs: ResearchDoc[] = [];
  for (const file of files) {
    const content = fs.readFileSync(path.join(RESEARCH_DIR, file), "utf-8");
    docs.push(parseMetadata(content, file));
  }

  // Sort: INDEX first, then alphabetically
  docs.sort((a, b) => {
    if (a.slug === "INDEX") return -1;
    if (b.slug === "INDEX") return 1;
    return a.slug.localeCompare(b.slug);
  });

  return docs;
}, "research-index");

export const route = {
  load: () => getResearchIndex(),
};

export default function ResearchIndex() {
  const docs = createAsync(() => getResearchIndex());

  return (
    <>
      <Title>Research Index - CALC</Title>

      <div class="prose-research">
        <h1>Research Documents</h1>
        <p class="text-gray-600 text-lg mb-8">
          Cross-reference and summary of research documents on linear logic,
          display calculus, ownership semantics, and proof theory.
        </p>

        <Suspense fallback={<div class="text-gray-500">Loading research index...</div>}>
          <Show when={docs()}>
            <div class="space-y-3">
              <For each={docs()}>
                {(doc) => (
                  <div class="border border-gray-200 rounded-md p-4 hover:border-blue-300 hover:bg-blue-50/30 transition-colors">
                    <A
                      href={`/research/${doc.slug}`}
                      class="text-lg font-semibold text-blue-600 hover:underline"
                    >
                      {doc.title}
                    </A>
                    <Show when={doc.description}>
                      <p class="text-gray-600 text-sm mt-1">{doc.description}</p>
                    </Show>
                    <Show when={doc.tags.length > 0}>
                      <div class="mt-2 flex flex-wrap gap-1">
                        <For each={doc.tags}>
                          {(tag) => (
                            <span class="inline-block bg-blue-100 text-blue-800 text-xs px-2 py-0.5 rounded">
                              {tag}
                            </span>
                          )}
                        </For>
                      </div>
                    </Show>
                  </div>
                )}
              </For>
            </div>
          </Show>
        </Suspense>
      </div>
    </>
  );
}
