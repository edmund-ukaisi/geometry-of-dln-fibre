---
title: The DLN fibre family over the rank-r open — an honest local-product geometry
status: draft
expedition: 2026-06-27-fibration-geometry
---

# The DLN fibre family over the rank-`r` open

This expedition hardens the geometry of the deep-linear-network (DLN) multiplication fibre into a
flat, locally-trivial family — to the precise extent that is genuinely proved, with every gap named.
The headline: over the locus where the universal product matrix has rank exactly `r`, the reduced
fibre family is **locally (per chart) a product over its base direction, and flat over that base** —
together with a smooth-block certificate that supplies the first slab of the eventual RLCT bridge.
All statements are formalised in Lean 4 + Mathlib, sorry-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), and each carries its own honesty fences.

## The objects

Fix a dimension vector `d : Fin (N+2) → ℕ` and a rank `r`. The relevant rings (all in
`DLNFibre.Core`):

- `sweepSigmaRing k d r` — the coordinate ring of the sweep/Σ̄^r model (the rank-`≤ r` closure in
  the sweep coordinates); its prime spectrum is the **base** of the family.
- `rankROpen d r ⊆ Spec(sweepSigmaRing k d r)` — *defined* as the complement of the common-vanishing
  locus of the `r × r` pivot minors `chartDsigAt s t`.
- `sweepFibreRing k d r hp hq` — the standard fibre coordinate ring.
- `SchurLoc k (d 0) (d_N) r = Localization.Away (detSchurS …)` — the in-chart **Schur-direction**
  coordinate ring (the base direction *within* a chart).

## 1. The rank-bridge keystone (S1)

`rankROpen` is defined as a cover-complement; the geometrically meaningful statement is that it *is*
the rank-exactly-`r` locus. That is now a theorem
(`FibreRankBridge.mem_rankROpen_iff_rank_universalMatrixResidue_eq`):

> for every prime `P`, `P ∈ rankROpen d r ↔ (universal product matrix over κ(P)).rank = r`.

The `≤` direction holds for *every* prime (rank `≤ r` is baked into Σ̄^r, pushed into the residue
field via the banked over-field minor criterion `rank_le_iff_forall_submatrix_det_eq_zero`); the `≥`
direction is a non-vanishing pivot minor giving an invertible `r × r` submatrix over the field `κ(P)`.
This is a **set-of-primes** identity; no structure-sheaf object is claimed, and in the
rank-unachievable regime the ring is trivial and the statement is vacuously (but soundly) true.

## 2. The smooth-block certificate (S2, S2c) — the RLCT-runway's first slab

At a smooth closed point of a top-dimensional fibre component, the local **Kähler** module is free,
with its rank pinned to the *proved* geometric codimension
(`FibreSmoothBlock.fibre_smoothBlock_certificate`):

> `Ω[A_m⁄k]` is free, and `rank(Ω) + codimRepCanonical(fibre d B) = ambient`,

i.e. `rank(Ω) = ambient − codim = dim(component)` — the **relative** dimension. (The module that is
free of rank `= codim` is the *conormal* `I/I²`, a different object — a deliberate distinction; the
conormal statement is roadmapped, not claimed.) The certificate is **hypothesis-free** under the
Kostant gate: `FibreSmoothBlockExists.exists_topComponent_smoothBlock_certificate` discharges the
top-component input via a generic engine (`topDimMinPrimes_nonempty`: a nontrivial Noetherian ring has
a minimal prime realising the full Krull dimension). This is the smooth-locus *upper-bound* local
model the future RLCT bridge consumes.

## 3. The over-base local product, with flatness (S4, S4b, S5)

The per-pivot atlas trivialises each chart's total ring as `SchurLoc ⊗_k sweepFibreRing`. The first
honest statement (S4, `FibreLocallyTrivial`) recorded this only as a bare `k`-algebra product — a
trivialization is supposed to respect the base. The convergent keystone (S4b, `FibreOverBaseTriv`)
upgrades it to a genuine **over-base** trivialization:

> `Away(chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`,

where `SchurLoc` acts via an **honest structure map** `schurToDsigAt` (a composite of the banked
connecting map, the deep-chart equivalence, and a gauge transport) — *not* a pullback along the
equivalence being upgraded. This non-circularity is the load-bearing point (machine-verified, and
independently re-checked): it is what makes the `≃ₐ[SchurLoc]` and the consequent flatness
non-vacuous. From it the flatness falls out chartwise
(`chartDsigAt_flat_over_schurLoc : Module.Flat SchurLoc (Away(chartDsigAt s t))`), by transporting the
standard model's freeness across the over-base equivalence.

The capstone (S5, `FibreBundleHeadline.reducedFibre_existsOverBaseProductChartAt_rankEq`) packages
this for the reader:

> every rank-`= r` prime `P` lies in a pivot chart carrying an honest structure map `φ` over which the
> chart total ring is the product `SchurLoc ⊗_k sweepFibreRing` (a `SchurLoc`-algebra iso) **and** is
> flat over `SchurLoc`.

## What is proved, and what is not (the honest fences)

**Proved (chartwise, over `SchurLoc`):** the rank-locus identity; the open cover; per chart an
over-base product trivialization and flatness over the in-chart Schur ring `SchurLoc`; the smooth-block
certificate with a hypothesis-free existence form.

**Named open items (not claimed):**

1. **The chart-base bridge** `SchurLoc ≅ sweepSigmaRing` restricted to `basicOpen(chartDsigAt s t)`
   (with structure-map compatibility). `SchurLoc` is the Schur-direction ring; the actual base
   restriction `Away(chartDsigAt s t)` (a localization *of* `sweepSigmaRing`) is a different ring, and
   the two are not yet identified. This bridge is the prerequisite for reading the chartwise
   `SchurLoc`-flatness as flatness over the genuine base `rankROpen` — a real build, **ahead of** the
   gluing cocycle.
2. **The global morphism (R1).** A single `Flat π` / fibre-bundle statement over all of `rankROpen`
   needs the target-side overlap-gluing cocycle (`targetOverlapTransition`) to assemble the per-chart
   data into one morphism. The present results are chartwise.
3. **The conormal companion (S2b):** `I/I²` free of rank `= codim` (the RLCT-relevant dual of the
   Kähler smooth-block) is a separate build.
4. **The singular locus / RLCT lower bound:** the smooth-block gives only the upper-bound local model;
   the genuine `rlct = ½·codim` needs a singular-locus *lower* bound — the next expedition's wall, teed
   up here, not closed.

## Why it matters

The paper's *used* consequence of the local-triviality picture — the arbitrary-`B` component count —
is already proved independently (`FibreThetaCountArbitrary`), so this geometry is not load-bearing for
that count; its value is the hardened, honest substrate for the RLCT direction. The smooth-block
certificate is the first concrete deliverable of that runway. The remaining geometry to make the
bundle picture global (chart-base bridge → R1) and to turn the upper-bound into the RLCT equality
(singular-locus lower bound) is mapped, with the kill-conditions identified.
