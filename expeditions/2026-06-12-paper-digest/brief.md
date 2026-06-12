# Expedition brief — paper-digest

## Central question

Produce a **faithful, formalisation-ready digest** of Lehalleur–Rimányi, *"Geometry of the fibers of the
multiplication map of deep linear neural networks"* — and the two things that let the next expedition start
formalising with confidence:

1. a **Core/DLN formalisation-target ladder** (a sized list of statements, grouped by the four roadmap
   bundles, each marked reachable / cited / deferred), and
2. a **map of what Mathlib already provides** vs what we must build from scratch — quiver representations,
   the type-A / `A_n` story, Gabriel's theorem, `Ext` for quiver reps, equivariant cohomology, and the
   combinatorics (Kostant partitions, rank patterns, the QIP, lattice points).

This is the scoping expedition. It is a *paper-section's worth* of understanding work, not one lemma; it
ends by handing the next expedition a clear first formalisation target on bedrock footing.

## Why this first

The paper's content is quiver-representation theory + type-A combinatorics + a thin SLT cap. The
load-bearing unknown for the whole programme is **how much of the engine Mathlib already gives us** — that
decides what is reuse vs the (high-value, reusable) build-from-scratch core. Resolving it is the highest
value-of-information move before any Lean is written.

## What exists already

- `docs/expositions/paper-digest/high-level-overview.md` — a strong reader-facing map (status: draft), with
  one open scholium note: *add a sentence motivating this via DLN learning behaviour, and cite Aoyagi up
  front*. Addressing that note is in scope.
- `theory/setup.md` — a stub of the core objects to flesh out.
- `ROADMAP.md` — a first-cut bundle map to sharpen into the sized ladder.

## Closing criterion

The expedition closes when:

1. the digest is **verified against the paper** section by section (claims, theorem numbers, the corrected
   rank-closure convention noted in the overview's footnote), the scholium note addressed, and the operator
   has read it (→ promote `high-level-overview.md` toward `stable`);
2. `ROADMAP.md` carries a **sized Core/DLN target ladder** — each target a precise statement with a
   reachability tag and its dependencies;
3. a **Mathlib-coverage map** exists (what to reuse, what to build), at least for Bundle 1 (combinatorial
   core) and Bundle 2 (quiver/orbit);
4. a **recommended first formalisation target** is named, with a one-paragraph justification of why it is
   whole-in-reach and bedrock-worthy.

No Lean theorems are required to close — but a first `DLNFibre.Core` definition skeleton (the ambient
objects: `Rep_d`, `mult`, the rank loci) is a fine bonus if it lands green.

## Pointers

- Disposition + process: `../../CLAUDE.md`, `../../docs/policies/expedition.md`.
- Paper: `../../paper-sources/lehalleur-rimanyi-2024-geometry-of-dln-fibre/source/main.tex` (+ PDF).
- Reference: Aoyagi (DLN learning coefficient) in `../../paper-sources/aoyagi-2023-...`.
