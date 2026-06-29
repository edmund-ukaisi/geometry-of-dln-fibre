---
title: "The Affine Dimension Library (DLNFibre.Core.Dimension)"
status: draft
source: expedition-note
topics: [foundations, commutative-algebra, krull-dimension, affine-geometry, mathlib-library]
created: "2026-06-29T12:00:00+00:00"
updated: "2026-06-29T12:00:00+00:00"
---

# The Affine Dimension Library (`DLNFibre.Core.Dimension`)

A self-contained, general-purpose library for the **dimension theory of finitely generated algebras and
affine varieties over a field** — the catenary equality, integral-extension dimension invariance, the
codimension/height bridge, and the smooth ⟹ regular-local implication. It was built because Mathlib `v4.29`
lacks these standard facts: every headline below was grep-confirmed absent, and the catenary equality in
particular is a commonly-requested missing piece.

It is the programme's first **"build the buildable"** foundation (see
[`../../docs/policies/library-building.md`](../policies/library-building.md)): well-established, detail-at-scale,
Mathlib-absent mathematics *built* to upstream grade rather than cited. The only genuine monument here — the
deep analytic singular-learning core behind `rlct = ½·codim` — stays cited. The DLN application's own
codimension and orbit-dimension results now *tag to* this library rather than carrying bespoke proofs.

## What it provides

All declarations live in `namespace DLNFibre.Core.Dimension`, over a base field `k` (no algebraic-closure or
characteristic hypothesis except where stated), and each module's namespace mirrors its eventual Mathlib home
so an upstream extraction is a file-move.

| Module | Headline | Hypotheses | Stacks |
|--------|----------|------------|--------|
| `Integral` | `ringKrullDim S = ringKrullDim A` for an integral injective ring map `A → S` | `CommRing` only | `00OK` / `00OJ` (≤-half) |
| `Basic` | polynomial-over-field dimension + quotient/coheight foundations | `[Field k]` | — |
| `Catenary` | `height p + dim(R/p) = n` for `R = k[Fin n]` (+ the re-derived monic-positioning) | `[Field k]` | `00OS` (00OX prose-cited) |
| `AffineDomain` | `height p + dim(A/p) = dim A` for any finite-type **domain** `A = k[Fin n]/I` + closed-point corollaries + integral height transport | `[Field k]`, domain | `00OS`, `00H8` |
| `Codimension` | the geometric height↔dim bridge `height(vanishingIdeal Z) + varietyDim Z = #σ` (irreducible `Z` / prime vanishing ideal), **plus** the ideal form `height I + dim(R/I) = #σ` for any proper ideal `I ≠ ⊤` | `[Field k] [Finite σ]` | — |
| `Smooth` | étale preserves height; the non-circular smooth-point local-dimension bridge | `[Field k]` | — |
| `Regular` | a smooth point of a finite-type algebra ⟹ `Aₘ` is a regular local ring | `[PerfectField k]` | `00TV` (forward) |

The module dependency graph is a clean acyclic DAG: `Basic`/`Integral` are roots; `Catenary` builds on them;
`AffineDomain`, `Codimension`, `Smooth` build on `Catenary`; `Regular` is the capstone on `Smooth`.

## A few precise statements

- **Catenary equality.** For the polynomial ring $R = k[x_1,\dots,x_n]$ over any field and a prime
  $\mathfrak p \subset R$, $\operatorname{height}\mathfrak p + \dim(R/\mathfrak p) = n$. The proof
  re-derives the one ingredient Mathlib keeps `private` (a Noether-normalization monic-positioning
  substitution), with provenance documented; no public route exists at `v4.29`.

- **Codimension bridge.** For a Zariski-closed $Z$ with prime vanishing ideal over a field on a finite
  index set $\sigma$, $\operatorname{height}(\mathcal I(Z)) + \operatorname{varietyDim} Z = \#\sigma$ — the
  field-general core, with the `[IsAlgClosed]` geometric (Nullstellensatz) reading kept as a thin separate
  layer. A separate, purely ideal-theoretic form needs no irreducibility — for **any proper ideal**
  $I \ne \top$, $\operatorname{height} I + \dim(R/I) = \#\sigma$ — though the geometric $\operatorname{varietyDim}$
  reading itself still requires $Z$ irreducible (a prime vanishing ideal).

- **Smooth ⟹ regular.** Over a perfect field, a maximal ideal at which a finite-type algebra is smooth has
  regular local localization. The local Krull dimension is computed via an étale-over-affine-space route
  (not the cotangent identity), keeping the argument non-circular; `[PerfectField]` enters only through the
  residue field's formal smoothness.

## Status and reuse

- **Verification.** Sorry-free, axiom-clean (`[propext, Classical.choice, Quot.sound]`), full-aggregator
  green; each rung fidelity-reviewed with a decorrelated second-model check, and a final principles/taste
  pass on the assembled stack.
- **Generality.** No declaration carries a decorative hypothesis; field-general throughout except `Regular`
  (`[PerfectField]`, the clean sufficient hypothesis — not claimed as the absolute pointwise minimum).
- **Extraction-ready.** The namespaces mirror `Mathlib.RingTheory.KrullDimension.*`,
  `Mathlib.AlgebraicGeometry.Codimension`, and `Mathlib.RingTheory.Smooth.Regular`; an actual mathlib4 PR is
  future work (the build was internal-first and is not blocked on upstream review). A sibling
  neuroalgebraic/ReLU programme is the anticipated second consumer.
