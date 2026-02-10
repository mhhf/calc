import { createAsync, cache } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense } from "solid-js";
import fs from "fs";
import path from "path";
import { processDocument, clientHydrationScript } from "../../lib/markdown";

const RESEARCH_DIR = path.resolve(process.cwd(), "doc/research");

// Load INDEX.md
const getResearchIndex = cache(async () => {
  "use server";

  const filePath = path.join(RESEARCH_DIR, "INDEX.md");
  const content = fs.readFileSync(filePath, "utf-8");
  const doc = await processDocument(content, { basePath: '/research', slug: 'INDEX' });

  return { title: doc.title, html: doc.html };
}, "research-index");

export const route = {
  load: () => getResearchIndex(),
};

export default function ResearchIndex() {
  const doc = createAsync(() => getResearchIndex());

  return (
    <Suspense fallback={<div class="text-gray-500">Loading research index...</div>}>
      <Show when={doc()}>
        {(data) => (
          <>
            <Title>{data().title} - CALC</Title>
            <article class="prose-research" innerHTML={data().html} />
            <div innerHTML={clientHydrationScript} />
          </>
        )}
      </Show>
    </Suspense>
  );
}
