import { createAsync, cache } from "@solidjs/router";
import { Title } from "@solidjs/meta";
import { Show, Suspense } from "solid-js";
import fs from "fs";
import path from "path";

const RESEARCH_DIR = path.resolve(process.cwd(), "doc/research");

// Simple markdown to HTML conversion (same as in [slug].tsx)
function markdownToHtml(markdown: string): string {
  let html = markdown;

  // Convert wiki-style links [[doc]] to HTML links
  html = html.replace(/\[\[([^\]]+)\]\]/g, (_, doc) => {
    return `<a href="/research/${doc}">${doc}</a>`;
  });

  // Escape HTML in code blocks first (preserve them)
  const codeBlocks: string[] = [];
  html = html.replace(/```(\w+)?\n([\s\S]*?)```/g, (_, lang, code) => {
    const idx = codeBlocks.length;
    const escaped = code
      .replace(/&/g, "&amp;")
      .replace(/</g, "&lt;")
      .replace(/>/g, "&gt;");
    codeBlocks.push(`<pre><code class="language-${lang || ""}">${escaped}</code></pre>`);
    return `__CODE_BLOCK_${idx}__`;
  });

  // Inline code
  html = html.replace(/`([^`]+)`/g, "<code>$1</code>");

  // Headers
  html = html.replace(/^#### (.+)$/gm, "<h4>$1</h4>");
  html = html.replace(/^### (.+)$/gm, "<h3>$1</h3>");
  html = html.replace(/^## (.+)$/gm, "<h2>$1</h2>");
  html = html.replace(/^# (.+)$/gm, "<h1>$1</h1>");

  // Bold and italic
  html = html.replace(/\*\*([^*]+)\*\*/g, "<strong>$1</strong>");
  html = html.replace(/\*([^*]+)\*/g, "<em>$1</em>");

  // Links [text](url)
  html = html.replace(/\[([^\]]+)\]\(([^)]+)\)/g, (_, text, url) => {
    if (url.endsWith(".md")) {
      url = "/research/" + url.replace(".md", "");
    }
    if (url.startsWith("#")) {
      return `<a href="${url}">${text}</a>`;
    }
    return `<a href="${url}" target="_blank" rel="noopener">${text}</a>`;
  });

  // Blockquotes
  html = html.replace(/^> (.+)$/gm, "<blockquote>$1</blockquote>");
  html = html.replace(/<\/blockquote>\n<blockquote>/g, "\n");

  // Horizontal rules
  html = html.replace(/^---+$/gm, "<hr>");

  // Tables
  const tableRegex = /\|(.+)\|\n\|[-| ]+\|\n((?:\|.+\|\n?)+)/g;
  html = html.replace(tableRegex, (_, header, body) => {
    const headers = header.split("|").filter((h: string) => h.trim());
    const rows = body.trim().split("\n").map((row: string) =>
      row.split("|").filter((c: string) => c.trim())
    );

    let table = "<table><thead><tr>";
    headers.forEach((h: string) => {
      table += `<th>${h.trim()}</th>`;
    });
    table += "</tr></thead><tbody>";
    rows.forEach((row: string[]) => {
      table += "<tr>";
      row.forEach((cell: string) => {
        table += `<td>${cell.trim()}</td>`;
      });
      table += "</tr>";
    });
    table += "</tbody></table>";
    return table;
  });

  // Unordered lists
  html = html.replace(/^- (.+)$/gm, "<li>$1</li>");
  html = html.replace(/(<li>.*<\/li>\n?)+/g, (match) => `<ul>${match}</ul>`);

  // Ordered lists
  html = html.replace(/^\d+\. (.+)$/gm, "<li>$1</li>");

  // Paragraphs
  html = html.replace(/^(?!<[a-z]|__CODE_BLOCK)(.+)$/gm, (_, content) => {
    if (content.trim()) {
      return `<p>${content}</p>`;
    }
    return content;
  });

  // Restore code blocks
  codeBlocks.forEach((block, idx) => {
    html = html.replace(`__CODE_BLOCK_${idx}__`, block);
  });

  html = html.replace(/\n{3,}/g, "\n\n");

  return html;
}

// Load INDEX.md
const getResearchIndex = cache(async () => {
  "use server";

  const filePath = path.join(RESEARCH_DIR, "INDEX.md");
  const content = fs.readFileSync(filePath, "utf-8");

  const titleMatch = content.match(/^# (.+)$/m);
  const title = titleMatch ? titleMatch[1] : "Research Index";

  const html = markdownToHtml(content);

  return { title, html };
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
          </>
        )}
      </Show>
    </Suspense>
  );
}
