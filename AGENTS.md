# Agent instructions

**Claude Code:** the disposition, research process, team structure, branch discipline, and memory
policy are in [`CLAUDE.md`](CLAUDE.md) (auto-loaded). This file is the codex-facing entry point and
the reader-facing exposition workflow below.

This workspace is for digesting and formalising the paper in
`paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/` (see [`README.md`](README.md)): building
mathematical understanding, reader-facing exposition, and a Lean library.

## Exposition workflow

When writing or editing reader-facing exposition under `docs/expositions/`,
use these policies:

- `docs/policies/scholium-writing-format.md` for markdown formatting,
  frontmatter, collapsibles, theorem-like blocks, math rendering, images, and
  `.data.yaml` sidecar conventions.
- `docs/policies/writing-style-graduate-math-textbook.md` for prose style,
  reader model, proof pacing, examples, theorem restatement, and source
  traceability.

The legacy policy `docs/policies/writing-style-agent-exposition.md` is for
agent-work summaries and synthesis notes, not for the graduate textbook-style
expositions unless explicitly requested.

## Reader model

Write exposition for a general mathematics graduate student. The reader is
mathematically mature but should not be assumed to know this repo, the paper's
notation, quiver representation theory, equivariant cohomology, or singular
learning theory. Recap bespoke notation and local conventions before using
them.

## Scholium workflow

Treat scholium primarily as a read/comment viewer. Keep markdown bodies clean;
comments and discussion belong in neighboring `.data.yaml` sidecars. Do not add
bespoke `[TOC]` blocks; scholium should provide the table of contents from
headings.

Thread resolving/reopening is normally done by the human reader in the UI.
Agents may edit markdown and add useful sidecar labels or replies, but should
not treat sidecar-only replies as a substitute for fixing the exposition.

## Writing defaults

Prefer mostly standalone expositions with local recaps over a tightly linear
chapter sequence. Use academic "we". Use proof sketches inline and put detailed
bookkeeping in collapsibles. Use the paper's theorem numbering where possible,
clearly labeled as being from the paper, and cite source results inline only
when the reference is load-bearing.
