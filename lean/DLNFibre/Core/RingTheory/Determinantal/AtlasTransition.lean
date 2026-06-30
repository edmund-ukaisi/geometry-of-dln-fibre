/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.RingTheory.Localization.Overlap
import DLNFibre.Core.RingTheory.Determinantal.Atlas
import DLNFibre.Core.Algebra.AlgEquiv.Groupoid

/-!
# `Algebra` — overlap transition maps of a constructive pivot-chart atlas

A constructive pivot-chart atlas of a Zariski-locally-trivial affine product is, over a base ring
`k`, a family of charts — each a principal open `D(chartElt)` of a fixed global base ring `Base`
together with a trivialization of the localized chart total ring as a fixed standard fibre model
`M` (the local product, a `k`-algebra iso). The transitions between two charts live on their
**overlap** `D(f) ∩ D(g)`, the explicit change-of-coordinates between the two trivialized
presentations of that overlap. This file packages that **transition datum** abstractly, over
arbitrary `k`-algebras, network-free.

## The chart-element pairing (and why)

The per-chart fibre model `Algebra.StandardFibreChart` deliberately dropped the principal-open base
element (it belongs with the cover, not the fibre model). The transitions live on overlaps
`D(f) ∩ D(g)`, so a chart must be **paired with its base element**. `Algebra.AtlasChart` is that
minimal pairing: a base element `chartElt : Base` cutting the chart `D(chartElt)`, and a bare
`k`-algebra trivialization `trivK : Localization.Away chartElt ≃ₐ[k] M` of the localized chart total
ring as the fixed model `M`. (`Algebra.AtlasFibreChart` extends it with the over-base
`StandardFibreChart`, recording the over-base content for the capstone without burdening the
transition with the over-base scalar-tower cost — the transition consumes only the bare `k` iso.)

Two base rings are in play and are kept distinct throughout: the GLOBAL base `Base` (where the
chart elements and the overlap localizations live) and, in `AtlasFibreChart`, the per-chart base
DIRECTION `BaseLoc` of the fibre model. A chart element is always `: Base`, never `: BaseLoc`.

## What is built

* `Algebra.AtlasChart k Base M` — the **chart-element pairing**: `chartElt : Base` + the bare
  `k`-algebra trivialization `trivK : Away chartElt ≃ₐ[k] M`.
* `Algebra.AtlasChart.overlapElt C D` — the chart-`D` element localized into the chart-`C` total
  ring `Away C.chartElt`; its `Localization.Away` is the base-side overlap
  `awayOverlap C.chartElt D.chartElt = O(D(C.chartElt) ∩ D(D.chartElt))`.
* `Algebra.AtlasChart.targetChartLoc C D` — the chart-`C` TARGET presentation of the overlap: the
  model `M` localized at the image `trivK (overlapElt C D)` (the double-localized object the
  transition lives on).
* `Algebra.AtlasChart.overlapTriv C D` — the base→target transport
  `awayOverlap C.chartElt D.chartElt ≃ₐ[k] targetChartLoc C D` (`Localization.awayCongr'` of
  `trivK`).
* `Algebra.AtlasChart.chartOverlapTransitionK C D` — the base-side overlap transition (the abstract
  `Localization.awayOverlapTransition`) `k`-restricted to a `k`-algebra iso.
* `Algebra.AtlasChart.overlapTransition C D` — **the overlap transition map** on the target/model
  side: the `k`-algebra iso `targetChartLoc C D ≃ₐ[k] targetChartLoc D C`, the explicit
  change-of-coordinates between the two trivialized presentations of the overlap, obtained by
  conjugating `chartOverlapTransitionK` through the two base→target transports.
* `Algebra.AtlasFibreChart …` — `AtlasChart` paired with the over-base `StandardFibreChart` (the
  capstone's per-chart fibre model), with the same `chartElt`.

**Scope.** This builds the transition OBJECTS + their basic identities (the base-side round-trip
`chartOverlapTransitionK_trans_symm`). The **cocycle compatibility** (the target-side round-trip
`overlapTransition C D ≪≫ overlapTransition D C = refl`, and triple-overlap associativity) is NOT
proved here — the transitions are set up (stable `AlgEquiv.trans` parenthesization + the base-side
round-trip named) so the cocycle is reachable via the `AlgEquiv` groupoid laws
(`AlgEquiv.trans_assoc`/`trans_refl`/`refl_trans`) without entering localization elements, but the
cocycle proof is a separate rung.

The eventual home is the localization-atlas library, so the data live in the bare `Algebra`
namespace (L7 Mathlib-mirror), network-free over arbitrary `k`-algebras.

**Dependency rule:** network-free `Core` — never import `DLNFibre.DLN`.
-/

open scoped TensorProduct

namespace Algebra

universe u

/-! ## The chart-element pairing -/

/-- **A chart of a constructive pivot-chart atlas, paired with its base element.** Over a base ring
`k`, this bundles ONE chart's transition-relevant data: the principal-open base element
`chartElt : Base` cutting the chart `D(chartElt)` of the global base `Base`, and a bare `k`-algebra
trivialization `trivK : Localization.Away chartElt ≃ₐ[k] M` of the localized chart total ring as the
fixed standard fibre model `M`. This is the minimal pairing the overlap transitions need: the
per-chart fibre-model datum (`Algebra.StandardFibreChart`) dropped the base element, but the
transitions live on overlaps `D(f) ∩ D(g)`, so the base element must travel with the chart. (Single
universe `Type u` throughout, matching the sibling `Algebra.StandardFibreChart` /
`LocalTrivializationDatum`.) -/
structure AtlasChart (k : Type u) [CommRing k]
    (Base : Type u) [CommRing Base] [Algebra k Base]
    (M : Type u) [CommRing M] [Algebra k M] where
  /-- The principal-open base element cutting the chart `D(chartElt)` of the global base `Base`. -/
  chartElt : Base
  /-- The bare `k`-algebra trivialization of the localized chart total ring `Away chartElt` as the
  fixed standard fibre model `M`. -/
  trivK : Localization.Away chartElt ≃ₐ[k] M

namespace AtlasChart

variable {k : Type u} [CommRing k]
  {Base : Type u} [CommRing Base] [Algebra k Base]
  {M : Type u} [CommRing M] [Algebra k M]

/-! ## The overlap of two charts, and its two target presentations -/

/-- **The chart-`D` element localized into the chart-`C` total ring.** `algebraMap Base
(Localization.Away C.chartElt) D.chartElt` — the element of the chart-`C` total ring whose inversion
cuts the overlap `D(C.chartElt) ∩ D(D.chartElt)`. Its `Localization.Away` is exactly the base-side
overlap `Localization.awayOverlap C.chartElt D.chartElt`. -/
noncomputable def overlapElt (C D : AtlasChart k Base M) :
    Localization.Away C.chartElt :=
  algebraMap Base (Localization.Away C.chartElt) D.chartElt

/-- **The chart-`C` target presentation of the overlap.** The standard fibre model `M` localized at
the image, under the chart-`C` trivialization `C.trivK`, of the chart-`D` element (`overlapElt C D`)
— the double-localized object on which the target-side overlap transition lives. `@[reducible]` so
its `CommRing` / `Algebra k` instances fire transparently (needed by `Localization.awayCongr'`). -/
@[reducible] noncomputable def targetChartLoc (C D : AtlasChart k Base M) : Type u :=
  Localization.Away (C.trivK (overlapElt C D))

/-- **The base→target transport of the chart-`C` overlap presentation.** The generalized
localization transport `Localization.awayCongr'` of the chart-`C` trivialization `C.trivK`,
carrying the
base-side overlap `awayOverlap C.chartElt D.chartElt = Localization.Away (overlapElt C D)` to the
chart-`C` target presentation `targetChartLoc C D` (the model `M` localized at
`C.trivK (overlapElt C D)`). -/
noncomputable def overlapTriv (C D : AtlasChart k Base M) :
    Localization.awayOverlap C.chartElt D.chartElt ≃ₐ[k] targetChartLoc C D :=
  Localization.awayCongr' C.trivK (overlapElt C D) (C.trivK (overlapElt C D)) rfl

/-! ## The base-side overlap transition, restricted to `k` -/

/-- **The base-side overlap transition as a `k`-algebra equiv.** The abstract overlap transition
`Localization.awayOverlapTransition C.chartElt D.chartElt` is a `Base`-algebra equiv; restricting
scalars along the tower `k → Base → awayOverlap` gives the `k`-algebra version that the target-side
transition conjugates the trivializations through. The two `IsScalarTower k Base (awayOverlap …)`
instances are pinned explicitly (`letI … := inferInstance`) so `restrictScalars` reuses them rather
than re-searching over the iterated localization. -/
noncomputable def chartOverlapTransitionK (C D : AtlasChart k Base M) :
    Localization.awayOverlap C.chartElt D.chartElt
      ≃ₐ[k] Localization.awayOverlap D.chartElt C.chartElt := by
  letI tower : IsScalarTower k Base
      (Localization.awayOverlap C.chartElt D.chartElt) := inferInstance
  letI tower2 : IsScalarTower k Base
      (Localization.awayOverlap D.chartElt C.chartElt) := inferInstance
  exact (Localization.awayOverlapTransition C.chartElt D.chartElt).restrictScalars k

/-- The `k`-restricted base transition agrees with the underlying base transition as a function. -/
@[simp] theorem chartOverlapTransitionK_apply (C D : AtlasChart k Base M)
    (x : Localization.awayOverlap C.chartElt D.chartElt) :
    chartOverlapTransitionK C D x = Localization.awayOverlapTransition C.chartElt D.chartElt x :=
  rfl

/-- **The base-side overlap transition round-trips to the identity.** The `k`-restriction of the
abstract base-side round-trip `Localization.awayOverlapTransition_trans_symm`: the pairwise round
trip `(C, D)` then `(D, C)` is the identity on the overlap. This is the base-side evidence behind
the (separately-proved) target-side cocycle; it is named here so the target-side round-trip is
reachable by the `AlgEquiv` groupoid laws. -/
theorem chartOverlapTransitionK_trans_symm (C D : AtlasChart k Base M) :
    (chartOverlapTransitionK C D).trans (chartOverlapTransitionK D C) = AlgEquiv.refl (R := k) := by
  refine AlgEquiv.ext (fun x ↦ ?_)
  simp only [chartOverlapTransitionK, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.coe_refl, id_eq]
  have := AlgEquiv.ext_iff.mp
    (Localization.awayOverlapTransition_trans_symm C.chartElt D.chartElt) x
  simpa [AlgEquiv.trans_apply] using this

/-! ## The overlap transition map on the target/model side -/

/-- **The overlap transition map of the atlas.** The explicit change-of-coordinates between the two
trivialized presentations of the overlap `D(C.chartElt) ∩ D(D.chartElt)` on the standard fibre model
`M`: the `k`-algebra iso between the chart-`C` presentation `targetChartLoc C D` and the chart-`D`
presentation `targetChartLoc D C`, obtained by conjugating the base-side overlap transition
`chartOverlapTransitionK C D` through the two base→target transports `overlapTriv`. The
parenthesization is fixed as `(overlapTriv C D).symm ≪≫ (chartOverlapTransitionK C D ≪≫
overlapTriv D C)` so the cocycle round-trip is reachable by the `AlgEquiv` groupoid laws. -/
noncomputable def overlapTransition (C D : AtlasChart k Base M) :
    targetChartLoc C D ≃ₐ[k] targetChartLoc D C :=
  (overlapTriv C D).symm.trans
    ((chartOverlapTransitionK C D).trans (overlapTriv D C))

/-! ## The target-side overlap round-trip (cocycle compatibility) -/

/-- **The target-side overlap transition round-trips to the identity (cocycle compatibility).** The
pairwise round trip `(C, D)` then `(D, C)` on the target/model presentations is the identity on
`targetChartLoc C D`. Unfolding `overlapTransition`, the composite collapses by the `AlgEquiv`
groupoid laws WITHOUT entering localization elements: the inner `overlapTriv D C ≪≫ (overlapTriv D
C).symm = refl`, then the base-side round-trip `chartOverlapTransitionK C D ≪≫
chartOverlapTransitionK D C = refl`, then `(overlapTriv C D).symm ≪≫ overlapTriv C D = refl`. -/
theorem overlapTransition_trans_symm (C D : AtlasChart k Base M) :
    (overlapTransition C D).trans (overlapTransition D C) = AlgEquiv.refl (R := k) := by
  simp only [overlapTransition, AlgEquiv.trans_assoc]
  rw [← AlgEquiv.trans_assoc (overlapTriv D C) (overlapTriv D C).symm,
    AlgEquiv.self_trans_symm, AlgEquiv.refl_trans,
    ← AlgEquiv.trans_assoc (chartOverlapTransitionK C D) (chartOverlapTransitionK D C),
    chartOverlapTransitionK_trans_symm, AlgEquiv.refl_trans,
    AlgEquiv.symm_trans_self]

/-- **The inverse of the target-side overlap transition is the swapped transition.**
`(overlapTransition C D).symm = overlapTransition D C` — the cocycle round-trip
(`overlapTransition_trans_symm`) read as a characterization of the inverse. -/
theorem overlapTransition_symm (C D : AtlasChart k Base M) :
    (overlapTransition C D).symm = overlapTransition D C := by
  rw [← AlgEquiv.trans_refl (overlapTransition C D).symm,
    ← overlapTransition_trans_symm C D, ← AlgEquiv.trans_assoc,
    AlgEquiv.symm_trans_self, AlgEquiv.refl_trans]

end AtlasChart

/-! ## The atlas chart paired with its over-base fibre model -/

/-- **A chart paired with its over-base fibre model.** `AtlasChart` (the chart-element + bare
`k`-trivialization the transitions consume) extended with the over-base per-chart fibre model
`Algebra.StandardFibreChart` (the structure map, the `≃ₐ[BaseLoc]` trivialization, and the flatness)
on the same localized chart total ring `Localization.Away chartElt`. This records the over-base
content of the chart for the capstone, while keeping the transition decoupled from the over-base
scalar-tower cost: the transitions read only `AtlasChart`. The two base rings are distinct — `Base`
is the GLOBAL base (where `chartElt` lives) and `BaseLoc` is the per-chart base DIRECTION of the
fibre model. -/
structure AtlasFibreChart (k : Type u) [CommRing k]
    (Base : Type u) [CommRing Base] [Algebra k Base]
    (M : Type u) [CommRing M] [Algebra k M]
    (BaseLoc : Type u) [CommRing BaseLoc] [Algebra k BaseLoc]
    (Fibre : Type u) [CommRing Fibre] [Algebra k Fibre]
    extends AtlasChart k Base M where
  /-- The over-base per-chart fibre model on the localized chart total ring `Away chartElt`. -/
  fibreModel :
    Algebra.StandardFibreChart k (Localization.Away toAtlasChart.chartElt) BaseLoc Fibre

end Algebra
