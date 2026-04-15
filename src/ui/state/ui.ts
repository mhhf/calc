import { createSignal } from 'solid-js';

// Dark mode state
const getInitialDarkMode = () => {
  if (typeof window === 'undefined') return false;
  const stored = localStorage.getItem('darkMode');
  if (stored !== null) return stored === 'true';
  return window.matchMedia('(prefers-color-scheme: dark)').matches;
};

export const [darkMode, setDarkMode] = createSignal(getInitialDarkMode());

export function toggleDarkMode() {
  const newValue = !darkMode();
  setDarkMode(newValue);
  if (typeof window !== 'undefined') {
    localStorage.setItem('darkMode', String(newValue));
  }
}
