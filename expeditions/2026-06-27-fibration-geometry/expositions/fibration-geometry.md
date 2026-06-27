---
title: The DLN fibre family over the rank-r open — an honest local-product geometry
status: draft
expedition: 2026-06-27-fibration-geometry
---

# The DLN fibre family over the rank-`r` open

This expedition hardens the geometry of the deep-linear-network (DLN) multiplication fibre — to the
precise extent genuinely proved, with every gap named. The headline: over the rank-exactly-`r` open of
the **source/total** space `Σ̄^r`, each localized source chart is, **over its in-chart base direction
`SchurLoc`, a product `SchurLoc ⊗ (fibre)` and flat over `SchurLoc`** (chartwise) — together with a
smooth-block certificate that supplies the first slab of the eventual RLCT bridge. This is *not* (yet)
a global flat, locally-trivial family: that the in-chart structure map is `mult`'s projection
(source/base projection compatibility) and the global gluing are named open items. All statements are
formalised in Lean 4 + Mathlib, sorry-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), and each carries its own honesty fences.

## The objects

Fix a dimension vector `d : Fin (N+2) → ℕ` and a rank `r`. The relevant rings (all in
`DLNFibre.Core`):

- `sweepSigmaRing k d r` — the coordinate ring of the **source/total** space `Σ̄^r`, the rank-`≤ r`
  locus in the source representation coordinates `RepCoord d`
  (`= MvPolynomial (RepCoord d) k / I(sweepSigma)`, `sweepSigma = canonicalCoord '' productRankLocus`).
  So `Spec(sweepSigmaRing)` is the **source/total**, *not* the base. (The genuine base is the target
  rank-`r` matrices `Mat^{=r}`, presented in-chart by `SchurLoc`.)
- `rankROpen d r ⊆ Spec(sweepSigmaRing k d r)` — the rank-exactly-`r` open of the **source/total**;
  *defined* as the complement of the common-vanishing locus of the `r × r` pivot minors `chartDsigAt s t`.
- `sweepFibreRing k d r hp hq` — the **fibre** coordinate ring.
- `SchurLoc k (d 0) (d_N) r = Localization.Away (detSchurS …)` — the in-chart **base direction**: the
  Schur/determinantal rank-chart ring presenting the target base. Each total chart `Away(chartDsigAt s t)`
  is, as proved, the product `SchurLoc ⊗_k sweepFibreRing` (base-direction ⊗ fibre).

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
conormal statement is roadmapped, not claimed.) Under the Kostant gate (and for a rank-`r` target `B`),
the certificate is **closed over the top-component input** — the `I, hI` inputs are discharged:
`FibreSmoothBlockExists.exists_topComponent_smoothBlock_certificate` produces a top component via a
generic engine (`topDimMinPrimes_nonempty`: a nontrivial Noetherian ring has a minimal prime realising
the full Krull dimension). Two incidence caveats sit next to this claim: the component `I` and the
local point live on the **standard/normal-form fibre ring** `sweepFibreRing` (the target `B` enters
only through same-rank codimension invariance — *not* a smooth point transported to `fibre d B`); and
the smooth closed point produced is *some* point of the dense smooth open, not a prescribed θ-generic
point or a named chart incidence. This is the smooth-locus *upper-bound* local model the future RLCT
bridge consumes.

## 3. The over-base local product, with flatness (S4, S4b, S5)

The per-pivot atlas trivialises each chart's total ring as `SchurLoc ⊗_k sweepFibreRing`. The first
honest statement (S4, `FibreLocallyTrivial`) recorded this only as a bare `k`-algebra product — a
trivialization is supposed to respect the base. The convergent keystone (S4b, `FibreOverBaseTriv`)
upgrades it to a genuine **over-base** trivialization:

> `Away(chartDsigAt s t) ≃ₐ[SchurLoc] SchurLoc ⊗_k sweepFibreRing`,

where `SchurLoc` acts via an **honest structure map** `schurToDsigAt` (a composite of the banked
connecting map, the deep-chart equivalence, and a gauge transport) — *not* a pullback along the
equivalence being upgraded. This non-circularity is what makes the `≃ₐ[SchurLoc]` and the consequent
flatness non-vacuous rather than a tautology. From it the flatness falls out chartwise
(`chartDsigAt_flat_over_schurLoc : Module.Flat SchurLoc (Away(chartDsigAt s t))`), by transporting the
standard model's freeness across the over-base equivalence.

The capstone (S5, `FibreBundleHeadline`) packages this. The honest carrier is the structure-side
`reducedFibre_rankROpenOverBaseLocalProduct`, whose per-pivot `OverBaseChartDatum` carries the
geometric structure map `schurToDsigAt` as a *named field*. The reader-facing pointwise theorem
`reducedFibre_existsOverBaseProductChartAt_rankEq` is stated over that **named geometric structure**
(the pivot datum's `chartDsigAtSchurLocAlgebra`, i.e. `schurToDsigAt`) — not an unconstrained
existential `φ`, which would carry no more content than S4's bare `≃ₐ[k]`:

> every rank-`= r` prime `P` lies in a pivot chart whose total ring is, over the geometric structure
> map `schurToDsigAt`, the product `SchurLoc ⊗_k sweepFibreRing` (a `SchurLoc`-algebra iso) **and** flat
> over `SchurLoc`.

## What is proved, and what is not (the honest fences)

**Proved (chartwise, over `SchurLoc`):** the rank-locus identity; the open cover; per chart an
over-base product trivialization and flatness over the in-chart Schur ring `SchurLoc`; the smooth-block
certificate with a hypothesis-free existence form.

**Named open items (not claimed):**

1. **Projection compatibility.** The flatness/triviality is over `SchurLoc` via the named structure map
   `schurToDsigAt : SchurLoc → Away(chartDsigAt s t)`. `SchurLoc` is the in-chart base direction and
   `Away(chartDsigAt s t)` is the **total** chart (already the product `SchurLoc ⊗ fibre`), so reading
   "flat over `SchurLoc`" as the genuine **fibre-family flatness over the base** requires `schurToDsigAt`
   to be the pullback of `mult`'s projection from the target/base rank-chart — which is **not yet
   proved**. A real build, **ahead of** the gluing cocycle. (There is no "`SchurLoc ≅ Away(chartDsigAt)`"
   bridge — that would equate the base direction with the whole total chart, losing the fibre.)
2. **The global morphism (R1).** A single `Flat π` / fibre-bundle statement over all of `rankROpen`
   needs the target-side overlap-gluing cocycle (`targetOverlapTransition`) to assemble the per-chart
   data into one morphism. The present results are chartwise.
3. **The conormal companion (S2b):** `I/I²` free of rank `= codim` (the RLCT-relevant dual of the
   Kähler smooth-block) is a separate build.
4. **The singular locus / RLCT lower bound:** the smooth-block gives only the upper-bound local model;
   the genuine `rlct = ½·codim` needs a singular-locus *lower* bound — the next expedition's wall, teed
   up here, not closed.

## Why it matters

The paper's *used* consequence of the local-product picture — the arbitrary-`B` component count —
is already proved independently (`FibreThetaCountArbitrary`), so this geometry is not load-bearing for
that count; its value is the hardened, honest substrate for the RLCT direction. The smooth-block
certificate is the first concrete deliverable of that runway. The remaining geometry to make the
bundle picture global (chart-base bridge → R1) and to turn the upper-bound into the RLCT equality
(singular-locus lower bound) is mapped, with the kill-conditions identified.
