import { APIEvent } from "@solidjs/start/server";
import fs from "fs";
import path from "path";

// Get research docs directory
const RESEARCH_DIR = path.resolve(process.cwd(), "dev/research");

interface ResearchDoc {
  slug: string;
  title: string;
  description: string;
  tags: string[];
}

// Parse frontmatter-like metadata from first few lines
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

export async function GET(event: APIEvent) {
  try {
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

    return new Response(JSON.stringify(docs), {
      headers: { "Content-Type": "application/json" },
    });
  } catch (error) {
    console.error("Error listing research docs:", error);
    return new Response(JSON.stringify({ error: "Failed to list documents" }), {
      status: 500,
      headers: { "Content-Type": "application/json" },
    });
  }
}
