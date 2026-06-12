# Writing style

How we write reader-facing markdown — expositions, theory notes, claim discussion. The target
renderer is the **scholium** viewer (pymdownx markdown). This policy is expected to evolve;
sharpen it when the style improves.

## Purpose

The bottleneck is a human understanding what the agents did. Reader-facing docs exist to
discharge that, and are judged **correct > elegant > efficient**, in that order.

- **Correct** — a faithful account of what was actually done and found: real hypotheses and
  scope, caveats co-located with claims, no overclaim, every claim traceable to its thread or
  Lean. A well-shaped doc that misrepresents the work is a failure (fidelity, applied to prose).
- **Elegant** — given correctness: elementary build-up, clear narrative, good structure.
- **Efficient** — given both: concise and layered, so a reader gets the gist fast and drills
  only as needed.

Never trade correctness for elegance, nor elegance for brevity.

## Elementary, precisely

Build explanations up from precise but simple objects, established locally in the document.
"Elementary" is not "imprecise" or "dumbed-down" — every step stays mathematically exact. It
means: introduce the objects you use before you use them; do not lean on context (notation,
prior results, domain background) the reader has not been given here; prefer a chain of small
exact statements over one dense one. Reach for an analogy only when it is exact and
load-bearing — most are not. (Disposition: [`../../CLAUDE.md`](../../CLAUDE.md).)

Concretely: name-dropping an object as prose ("the multiplication map, a product of composable
matrices") is not enough — define it with an equation before you use it
($\operatorname{mult}(A_\ast)=A_N\cdots A_1$, having first said what a composable tuple is), and
carry a small running example.

## Object-level focus

The wording discipline applies: no meta-hedging or selling phrasing; state what is true and
why. The banned-wording list and the review function that enforces it are in
[`review.md`](review.md).

## Mathematics is TeX

Write mathematics as TeX — inline `$…$`, display `$$…$$` (KaTeX). Never put math in code spans
(`` `x` ``). Reserve code spans for code, identifiers (Lean names), file paths, commit hashes,
and literal markdown/CLI syntax. A symbol such as $\operatorname{Rep}_{\underline d}$, $\operatorname{mult}$, or $\Sigma^r$ is
math; `Set.image_inter_preimage` and `lean/DLNFibre/Core/Orbit.lean` are code. Display
math must be a **block** (fences on their own lines, blank line above and below) — see
**Rendering rules** below; a single-line `$$…$$` does not render.

## Layered detail — keep one clean reading line

Top-level prose carries a single narrative line that reads top to bottom. Anything that would
interrupt it, or that a reader who already knows it would skip, goes one layer down:

- **Footnotes** (`[^id]`) — a short aside, a definition of a term used in passing, a caveat
  attached to one sentence, a pointer to a source.
- **Collapsibles** (`??? note "Title"`) — derivations, proofs, worked computations,
  side-discussions. Collapsed by default; `???+` opens expanded; indent the body 4 spaces.
  Use these rather than raw `<details>` — they compose inside lists, where raw HTML does not.
- **Callouts** (`!!! note "…"`, non-collapsible) — a highlight that must stay visible (a
  warning, a load-bearing definition). Types: `note`, `tip`, `warning`, `danger`, `info`,
  `question`, and custom.

Rule of thumb: the main line states *what* holds and *why*, in elementary steps; the *how*
(the full derivation, the index bookkeeping, the proof) goes into a footnote or collapsible.

## Structure

- One topic per file.
- Open with a short **framing paragraph**, and for anything long, a "the story is short: 1…N"
  list of the moves the doc makes. (No `[TOC]` — scholium renders its own; see Rendering rules.)
- Close with **cross-references** to related docs, the expedition/threads, and the Lean.
- **Traceability:** every formal claim cites its Lean module / theorem name and statement card
  ([`statement-cards.md`](statement-cards.md)), or its primary source. A claim a reader cannot
  trace is not finished.

## Frontmatter

Begin each doc with a frontmatter block (the viewer reads it):

```
---
title: "…"
status: draft        # draft = controller may refactor freely; stable = human-read, protected
source: original
topics: [ … ]
created: "YYYY-MM-DDTHH:MM:SS"
updated: "YYYY-MM-DDTHH:MM:SS"
---
```

`status` is the **refactor gate**: a `draft` doc is fluid (the controller may restructure it
freely, including a massive refactor); a `stable` doc has been read and blessed by the operator
and is protected — additive or careful edits only. See [`expedition.md`](expedition.md) § Expositions.

## Scholia (anchored discussion)

In-progress discussion is **anchored scholia** in a `*.data.yaml` sidecar next to the doc,
created and resolved through the scholium viewer (or its MCP tools) — **not** hand-written in
the markdown body. The body stays clean; the apparatus lives beside it. Resolve a thread by
editing the doc and replying in the sidecar.

## Renderer syntax (scholium / pymdownx)

| Syntax | Effect |
|---|---|
| `[^id]` … `[^id]: text` | Footnote |
| `??? note "Title"` (body indented 4 spaces) | Collapsible callout (`???+` opens expanded) |
| `!!! warning "Title"` | Non-collapsible callout |
| `$…$`, `$$…$$` | Inline / display math (KaTeX) |
| `[[wikilink]]` | Vault link |
| `# Heading {: #anchor}` | Stable anchor id (useful for scholia) |
| `==highlight==`, `~~strike~~`, `H~2~O`, `E=mc^2^` | Inline formatters |

Math and `[[wikilinks]]` survive inside collapsibles.

## Rendering rules (must-follow)

Scholium's markdown+KaTeX renderer is strict about block boundaries. These rules are learned
failures — violating them silently breaks the render:

- **Display math is a block.** Write `$$…$$` with the fences on their **own lines**, a blank line
  above and below:

  ```
  introducing text:

  $$
  \lambda = \tfrac12 \operatorname{rank} J
  $$

  following text.
  ```

  A single-line `$$ … $$` does **not** render as display math. Inside a blockquote or a
  `???`/`!!!` callout, put the **same prefix** (`> `, or the 4-space body indent) on all three
  lines, and do not insert blank lines there (they break the quote/callout).
- **KaTeX commands only.** Use commands KaTeX supports. For a star write `\ast` or `^*` — never
  `\*` (invalid; renders as a red error). Do not backslash-escape `*` inside math: `$…$` is math,
  so `*` is already safe there.
- **Blank line before every list.** A bullet (`- `) or numbered item glued directly to the
  previous paragraph, `$$` block, or heading is not parsed as a list. Precede every list with one
  blank line. (Wrapped continuation lines of a list item are indented 2 spaces; consecutive items
  need no blank between them.)
- **No `[TOC]`.** Scholium renders its own table of contents; an explicit `[TOC]` duplicates it.
- **The editor is read-only.** Scholium's *editor* corrupts files on save (duplicates the body,
  mangles `$$` fences, reflows frontmatter). Edit these docs with normal file tools; if one is
  corrupted, restore with `git checkout HEAD -- <file>` (the corruption is only in the working
  tree, never in commits).
