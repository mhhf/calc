/**
 * Book progress store — chapter completion + per-exercise state,
 * persisted to localStorage. No accounts, no backend.
 */
import { createSignal } from 'solid-js';

export interface ChapterProgress {
  completed: boolean;
  /** exercise/widget id → done */
  exercises: Record<string, boolean>;
}

type ProgressMap = Record<string, ChapterProgress>;

const STORAGE_KEY = 'calc-book-progress';

function load(): ProgressMap {
  if (typeof localStorage === 'undefined') return {};
  try {
    return JSON.parse(localStorage.getItem(STORAGE_KEY) || '{}');
  } catch {
    return {};
  }
}

const [progress, setProgress] = createSignal<ProgressMap>(load());

function persist(map: ProgressMap) {
  setProgress(map);
  try {
    localStorage.setItem(STORAGE_KEY, JSON.stringify(map));
  } catch {
    /* storage full / private mode — progress is best-effort */
  }
}

export { progress };

export function chapterProgress(slug: string): ChapterProgress {
  return progress()[slug] || { completed: false, exercises: {} };
}

export function isChapterComplete(slug: string): boolean {
  return chapterProgress(slug).completed;
}

export function setChapterComplete(slug: string, completed: boolean) {
  const map = { ...progress() };
  map[slug] = { ...chapterProgress(slug), completed };
  persist(map);
}

export function markExercise(slug: string, exerciseId: string, done = true) {
  const map = { ...progress() };
  const ch = chapterProgress(slug);
  map[slug] = { ...ch, exercises: { ...ch.exercises, [exerciseId]: done } };
  persist(map);
}

export function isExerciseDone(slug: string, exerciseId: string): boolean {
  return !!chapterProgress(slug).exercises[exerciseId];
}

export function completedCount(slugs: string[]): number {
  const map = progress();
  return slugs.filter(s => map[s]?.completed).length;
}
