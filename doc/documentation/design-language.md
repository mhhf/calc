# Design Language

CALC is a neo-academic tool — theoretical math and computer science research presented with clarity and precision. The visual language reflects this: clean, minimal, typographically disciplined, never decorative.

## Methodology

A design language is built bottom-up through four layers:

1. **Design Tokens** — atomic values (colors, sizes, spacing, radii, shadows). Platform-agnostic primitives.
2. **Foundations** — how tokens compose into rules: color roles, type scale, spacing rhythm, dark mode mapping.
3. **Components** — reusable UI blocks (tabs, cards, inputs, buttons) built from foundations.
4. **Patterns** — component compositions solving recurring problems (navigation, form layouts, proof display).

References: IBM Carbon (layering model), GitHub Primer (token → semantic mapping), Tailwind (utility-first tokens).

### Academic-Specific Considerations

From typographic research (Schwen, PLOS Comp Bio) and proof assistant UIs (Lean, Coq):

- **75-80 character line width** for prose — optimal reading measure (~600-700px at 16px)
- **Monospaced for formal notation** — sequents, terms, rules
- **Inference trees as Gentzen-style derivations** — traditional proof theory rendering
- **Restrained, low-saturation palettes** — neutral-heavy, one accent for interaction, semantic colors for status only
- **White space over decorative grid lines** — spacing and subtle shading do the structuring
- **Right-align numbers in tables**, use tabular/monospaced figures

## Principles

1. **White space is structure.** Let content breathe. Margins and padding do the work that borders and backgrounds shouldn't.
2. **Hierarchy through typography, not color.** Font weight, size, and spacing establish reading order. Color is reserved for semantics.
3. **Minimal palette, maximum clarity.** Few colors, each with a defined role. No ad-hoc hex values.
4. **Code is a first-class citizen.** Monokai code blocks are visually distinct from prose — dark islands in a light sea.
5. **Light by default.** White/gray is the canvas. Dark mode inverts the canvas, not the logic.
6. **Three levels of visual weight maximum** per view: primary (what you act on), secondary (supporting info), tertiary (metadata/chrome).

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

Fixed dark palette regardless of light/dark mode:

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

**Type scale** (base 16px, ratio 1.25 — Major Third): xs 10px, sm 13px, base 16px, lg 20px, xl 25px, 2xl 31px. Ratio 1.25 gives clear hierarchy without wasting vertical space in a data-dense tool.

**Line height**: 1.6 body, 1.25 headings, 1.5 code. Snap to 4px grid (e.g. 16px × 1.5 = 24px).

## Spacing

4px base unit. All spacing is a multiple of 4.

| Token | Value | Use |
|-------|-------|-----|
| 1 | 4px | Icon-to-text gap, tight padding |
| 2 | 8px | Intra-component spacing |
| 3 | 12px | Related element gaps |
| 4 | 16px | Default padding, card padding |
| 6 | 24px | Section gaps |
| 8 | 32px | Major section separation |
| 12 | 48px | Page-level margins |

**Proximity heuristic** (Gestalt): tightly related = 4-8px, within component = 8-12px, between components = 16-24px, between sections = 32-48px.

## Contrast Requirements (WCAG AA)

| Context | Minimum ratio |
|---------|---------------|
| Normal text | 4.5:1 |
| Large text (18px bold / 24px) | 3:1 |
| Non-text UI elements | 3:1 |

Rule of thumb: 5 Tailwind shade steps apart gives ~4.5:1 contrast (e.g. gray-900 on white, gray-100 on gray-800).

## Component Patterns

### Main Tabs (left — tool pages)

Light canvas background. Active: white bg, blue-600 text, 2px blue bottom border. Inactive: gray text, hover to gray-100 bg.

### Doc Tabs (right — dark, inverted)

Dark background visually separates documentation from interactive tool pages. Active: gray-900 bg, **white text**, blue-400 bottom border accent. Inactive: gray-700 bg, gray-300 text, hover lightens.

Key: active doc tab uses **white text** (not blue) for readability on dark backgrounds. Blue accent on border only.

### Cards

White / gray-800 (dark) background. 1px border. Rounded-lg. Shadow-sm. Hover: shadow-md + blue-300 border.

### Buttons

Primary: blue-600 bg, white text, rounded-lg, hover blue-700. Secondary: outline with border-gray-300.

### Form Inputs

2px border, rounded-lg. Focus: blue-500 border + blue ring. Error: red-500 border.

### Status Badges

Pill shape. Wash background + dark text of same hue: draft (yellow), review (blue), stable (green), research (purple).

### Proof View Toggles

Button group with rounded-lg container + border. Active: blue-600 bg, white text. Mode toggles (focused/unfocused): purple-600 bg.

## Dark Mode

Class-based (`dark:` prefix on root). Inverts canvas/surface/text. Colors shift 600→400. Backgrounds shift 50→900/20 wash. Persisted in localStorage, defaults to system preference.

Dark mode is not just inversion — it requires reduced saturation and different shade mappings (Primer approach).

## Anti-Patterns

- No gradient backgrounds
- No drop shadows heavier than shadow-md
- No ad-hoc hex colors outside this palette (prose-research GitHub styling is an allowed exception)
- No decorative borders or ornamental elements
- No color as the sole differentiator (always pair with text/icon/position)
- No serif fonts for UI chrome (reserve for long-form prose if ever added)
