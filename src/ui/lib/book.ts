/**
 * Book manifest — chapter list from /api/docs/book, grouped into parts.
 * Chapters carry `part`, `partTitle`, `chapter` frontmatter; ordering is
 * (part, chapter).
 */

export interface BookChapterMeta {
  slug: string;
  title: string;
  summary: string;
  part?: number;
  partTitle?: string;
  chapter?: number;
}

export interface BookPart {
  part: number;
  title: string;
  chapters: BookChapterMeta[];
}

let bookPromise: Promise<BookChapterMeta[]> | null = null;

export function fetchBook(): Promise<BookChapterMeta[]> {
  if (!bookPromise) {
    bookPromise = fetch('/api/docs/book')
      .then(r => (r.ok ? r.json() : []))
      .then((docs: BookChapterMeta[]) =>
        docs
          .filter(d => d.chapter !== undefined && !isNaN(Number(d.chapter)))
          .sort((a, b) => (a.part! - b.part!) || (a.chapter! - b.chapter!))
      )
      .catch(() => []);
  }
  return bookPromise;
}

export function groupParts(chapters: BookChapterMeta[]): BookPart[] {
  const parts: BookPart[] = [];
  for (const ch of chapters) {
    const p = ch.part ?? 0;
    let entry = parts.find(x => x.part === p);
    if (!entry) {
      entry = { part: p, title: ch.partTitle || `Part ${p}`, chapters: [] };
      parts.push(entry);
    }
    if (ch.partTitle && entry.title.startsWith('Part ')) entry.title = ch.partTitle;
    entry.chapters.push(ch);
  }
  return parts.sort((a, b) => a.part - b.part);
}

export function romanPart(n: number): string {
  const numerals = ['', 'I', 'II', 'III', 'IV', 'V', 'VI', 'VII', 'VIII'];
  return numerals[n] || String(n);
}
