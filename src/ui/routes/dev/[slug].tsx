import { createAsync, cache } from "@solidjs/router";
import { useParams } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense, ErrorBoundary } from "solid-js";
import fs from "fs";
import path from "path";
import { processDocument, clientHydrationScript, type Frontmatter } from "../../lib/markdown";

const DEV_DIR = path.resolve(process.cwd(), "doc/dev");

const getDevDoc = cache(async (slug: string) => {
  "use server";

  const filePath = path.join(DEV_DIR, `${slug}.md`);

  if (!fs.existsSync(filePath)) {
    throw new Error(`Document not found: ${slug}`);
  }

  const content = fs.readFileSync(filePath, "utf-8");
  const doc = await processDocument(content, { basePath: '/dev', slug });

  return {
    title: doc.title,
    html: doc.html,
    frontmatter: doc.frontmatter,
  };
}, "dev-doc");

export const route = {
  load: ({ params }: { params: { slug: string } }) => getDevDoc(params.slug),
};

export default function DevDocument() {
  const params = useParams();
  const doc = createAsync(() => getDevDoc(params.slug));

  return (
    <ErrorBoundary fallback={(err) => (
      <div class="prose-research">
        <h1>Document Not Found</h1>
        <p class="text-red-600">{err.message}</p>
      </div>
    )}>
      <Suspense fallback={<div class="text-gray-500">Loading document...</div>}>
        <Show when={doc()}>
          {(data) => (
            <>
              <Title>{data().title} - CALC Dev</Title>
              <Show when={data().frontmatter.summary || data().frontmatter.tags}>
                <div class="mb-6 p-4 bg-gray-50 rounded-lg border border-gray-200 text-gray-900">
                  <Show when={data().frontmatter.summary}>
                    <p class="text-gray-700 italic mb-2">{data().frontmatter.summary as string}</p>
                  </Show>
                  <Show when={data().frontmatter.tags}>
                    <div class="flex flex-wrap gap-2">
                      {(data().frontmatter.tags as string[])?.map((tag) => (
                        <span class="px-2 py-1 bg-blue-100 text-blue-800 text-xs rounded">{tag}</span>
                      ))}
                    </div>
                  </Show>
                  <Show when={data().frontmatter.modified}>
                    <p class="text-xs text-gray-400 mt-2">Last modified: {data().frontmatter.modified as string}</p>
                  </Show>
                </div>
              </Show>
              <article class="prose-research" innerHTML={data().html} />
              <div innerHTML={clientHydrationScript} />
            </>
          )}
        </Show>
      </Suspense>
    </ErrorBoundary>
  );
}
