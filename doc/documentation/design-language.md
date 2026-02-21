# Design Language

CALC is a neo-academic tool — theoretical math and computer science research presented with clarity and precision. The visual language reflects this: clean, minimal, typographically disciplined, never decorative.

## Principles

1. **White space is structure.** Let content breathe. Margins and padding do the work that borders and backgrounds shouldn't.
2. **Hierarchy through typography, not color.** Font weight, size, and spacing establish reading order. Color is reserved for semantics.
3. **Minimal palette, maximum clarity.** Few colors, each with a defined role. No ad-hoc hex values.
4. **Code is a first-class citizen.** Monokai code blocks are visually distinct from prose — dark islands in a light sea.
5. **Light by default.** White/gray is the canvas. Dark mode inverts the canvas, not the logic.

## Color Palette

### Neutrals (canvas + text)

| Token         | Light              | Dark               | Use                          |
|---------------|--------------------|---------------------|------------------------------|
| `canvas`      | white `#ffffff`    | gray-900 `#111827`  | Page background              |
| `surface`     | gray-50 `#f9fafb`  | gray-800 `#1f2937`  | Cards, panels, header        |
| `border`      | gray-200 `#e5e7eb` | gray-700 `#374151`  | Dividers, card borders       |
| `text`        | gray-900 `#111827` | gray-100 `#f3f4f6`  | Body text                    |
| `text-muted`  | gray-500 `#6b7280` | gray-400 `#9ca3af`  | Secondary text, labels       |
| `hover`       | gray-100 `#f3f4f6` | gray-700 `#374151`  | Interactive hover background |

### Primary — Blue (interactive + focus)

| Token           | Value                | Use                               |
|-----------------|----------------------|-----------------------------------|
| `primary`       | blue-600 `#2563eb`   | Buttons, active tabs, links       |
| `primary-light` | blue-400 `#60a5fa`   | Dark-mode active, accents         |
| `primary-wash`  | blue-50 `#eff6ff`    | Selected backgrounds (light)      |
| `primary-wash`  | blue-900/20          | Selected backgrounds (dark)       |

### Secondary — Amber/Orange (attention + highlights)

| Token             | Value                  | Use                              |
|-------------------|------------------------|----------------------------------|
| `accent`          | amber-500 `#f59e0b`   | Highlights, warnings, stars      |
| `accent-text`     | amber-700 / amber-300  | Text on accent wash              |
| `accent-wash`     | amber-50 / amber-900/20| Background tints                 |
| `accent-strong`   | orange-500 `#f97316`  | Priority badges, hot indicators  |

### Semantic

| Role    | Light             | Dark              |
|---------|-------------------|-------------------|
| Success | green-600         | green-400         |
| Danger  | red-600           | red-400           |
| Info    | purple-600        | purple-400        |

### Code — Monokai Sublime

Code blocks use a fixed dark palette regardless of light/dark mode:

| Token      | Value     | Role                  |
|------------|----------|-----------------------|
| Background | `#23241f` | Code block bg         |
| Text       | `#f8f8f2` | Default code text     |
| Keyword    | `#f92672` | Keywords, operators   |
| String     | `#e6db74` | Strings, types        |
| Number     | `#ae81ff` | Numbers, literals     |
| Comment    | `#75715e` | Comments              |
| Symbol     | `#66d9ef` | Attributes, symbols   |
| Function   | `#a6e22e` | Titles, class names   |

## Typography

**System fonts only** — no web font loading.

| Role   | Stack                                                                 | Weight | Size   |
|--------|-----------------------------------------------------------------------|--------|--------|
| Body   | system-ui, -apple-system, BlinkMacSystemFont, Segoe UI, Roboto, sans | 400    | 16px   |
| Heading| same stack                                                            | 600    | scale  |
| Code   | ui-monospace, SFMono-Regular, SF Mono, Menlo, Consolas, monospace     | 400    | 85%    |

Line height: 1.6 body, 1.25 headings, 1.5 code.

## Component Patterns

### Main Tabs (left — tool pages)

Light canvas background. Active tab: white bg, blue-600 text, 2px blue bottom border. Inactive: gray text, hover to gray-100 bg.

### Doc Tabs (right — dark, inverted)

Dark background to visually separate documentation from interactive tool pages. Active tab: darkest bg (gray-900), **white text**, blue-400 bottom border accent. Inactive: gray-700 bg, gray-300 text, hover lightens.

The key: active doc tab uses **white text** (not blue) for readability on dark backgrounds. The blue accent is on the border only.

### Cards

White (light) / gray-800 (dark) background. 1px border in `border` token. Rounded-lg. Shadow-sm. Hover: shadow-md + blue-300 border.

### Buttons

Primary: blue-600 bg, white text, rounded-lg, hover blue-700. Secondary: outline style with border-gray-300.

### Form Inputs

2px border, rounded-lg. Focus: blue-500 border + blue ring. Error: red-500 border.

### Status Badges

Pill shape (rounded-full). Wash background + dark text of same hue:
- Draft: yellow
- Review: blue
- Stable: green
- Research: purple

### Proof View Toggles

Button group with rounded-lg container + border. Active: blue-600 bg, white text. Mode toggles (focused/unfocused): purple-600 bg.

## Dark Mode

Class-based (`dark:` prefix on root). Inverts canvas/surface/text. Colors shift from 600→400 weight. Backgrounds shift from 50→900/20 wash. Persisted in localStorage, defaults to system preference.

## Anti-Patterns

- No gradient backgrounds
- No drop shadows heavier than shadow-md
- No ad-hoc hex colors outside this palette (prose-research GitHub styling is an allowed exception for markdown rendering)
- No decorative borders or ornamental elements
- No color as the sole differentiator (always pair with text/icon/position)
