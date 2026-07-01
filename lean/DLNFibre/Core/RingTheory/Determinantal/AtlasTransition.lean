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
* `Algebra.AtlasChart.overlapTransition_trans_symm` / `…_symm` — the **2-fold cocycle**: the
  target-side pairwise round-trip is the identity (P2.c), by the `AlgEquiv` groupoid laws.
* `Algebra.AtlasChart.targetTripleLoc C D E` / `tripleTriv` / `chartTripleTransitionK` /
  `tripleTransition` — the **triple-overlap** layer: the symmetric pivot-`C` triple presentation
  (the chart localized at the PRODUCT `D.chartElt * E.chartElt` of the two non-pivot elements), its
  base→target transport, the base-side pivot-swap triple transition, and the canonical target-side
  triple transition `tripleTransition C D E : targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C`.
* `Algebra.AtlasChart.tripleTransition_cocycle` — the **triple cocycle** (P2.f): the cyclic
  composite of the three pivot-swap triple transitions on a fixed triple is the identity (standard
  form `g_jk ∘ g_ij = g_ik`), by the same conjugation/groupoid collapse one denominator up.
* `Algebra.AtlasChart.restrictedOverlapTripleTransition` / `restrictTriple` /
  `restrict_overlapTransition_eq_tripleTransition` / `restrictTriple_comp_overlapTransition` /
  `overlapTransition_restricted_triple_cocycle` — the **naturality layer** (P2.g): the
  further-localization of the 2-fold `overlapTransition` to the triple, the restriction map, the
  naturality (iv) tying the restricted 2-fold to the canonical `tripleTransition`, the commuting
  square exhibiting it as the restriction of the ACTUAL `overlapTransition`, and the cocycle of the
  restricted 2-fold transitions.
* `Algebra.AtlasFibreChart …` — `AtlasChart` paired with the over-base `StandardFibreChart` (the
  capstone's per-chart fibre model), with the same `chartElt`.

**Scope.** This builds the transition OBJECTS + the cocycle COMPATIBILITIES (the 2-fold round-trip
`overlapTransition_trans_symm`, P2.c; the triple cocycle `tripleTransition_cocycle`, P2.f — both by
the `AlgEquiv` groupoid laws without entering localization elements) AND the **naturality** (P2.g)
tying the triple transition to the further-localization of the 2-fold `overlapTransition`. The
symmetric triple localizes at the PRODUCT `D·E` and the 2-fold at `D` alone, so the tie goes through
the `Away.mul'` refinement (the base further-localization `baseRestrTriple`) and a
`Base`-subsingleton naturality argument, transported through the trivializations. This is a
per-triple compatibility (`restrict_overlapTransition_eq_tripleTransition` +
`restrictTriple_comp_overlapTransition`); the GLOBAL gluing of the per-chart data into one fibration
morphism is a separate rung (R1, not built here).

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

/-! ## The triple overlap, its symmetric target presentation, and the triple cocycle

The triple-overlap presentations are indexed `(pivot, other, other)` and made **symmetric in the
two non-pivot charts** (canonical symmetry of the overlap, NOT a Lean-definitional one):
`targetTripleLoc C D E` is the chart-`C` presentation of the triple overlap
`D(C.chartElt) ∩ D(D.chartElt) ∩ D(E.chartElt)`, localized at the PRODUCT `D.chartElt * E.chartElt`
of the other two elements (not nested `D` then `E`). This symmetry is what makes the standard
**pairwise-swap-on-a-fixed-triple** cocycle `g_jk ∘ g_ij = g_ik` well-typed: each transition swaps
the pivot on the fixed triple `{C, D, E}`, so `targetTripleLoc C D E → targetTripleLoc D E C →
targetTripleLoc E C D → targetTripleLoc C D E` has matching composition targets. (The same symmetry
is also what would let the further localization of the 2-fold `overlapTransition C D` be compared to
this triple presentation — the naturality tie — but that comparison is NOT built here: it is roadmap
R1, see `tripleTransition`'s scope note. The asymmetric nested-`D`-then-`E` presentation makes the
cocycle's composition targets fail to type.) -/

/-- **The product of the two non-pivot chart elements, localized into the pivot-`C` total ring.**
`algebraMap Base (Localization.Away C.chartElt) (D.chartElt * E.chartElt)` — the element of the
pivot-`C` chart total ring whose inversion cuts the rest of the triple overlap
`D(C.chartElt) ∩ D(D.chartElt) ∩ D(E.chartElt)`. Localizing at the PRODUCT keeps the construction
symmetric in the non-pivot charts `D, E`. Its `Localization.Away` is the localization of `Base` at
`C.chartElt * (D.chartElt * E.chartElt)` (`IsLocalization.Away.mul'`). `@[reducible]` so the
`Localization.Away` instance fires at the unfolded `algebraMap` form (needed by `Away.mul'`). -/
@[reducible] noncomputable def tripleElt (C D E : AtlasChart k Base M) :
    Localization.Away C.chartElt :=
  algebraMap Base (Localization.Away C.chartElt) (D.chartElt * E.chartElt)

/-- **The base-side triple-overlap ring as a localization of `Base` at the triple element.** The
pivot-`C` triple overlap `Localization.Away (tripleElt C D E)` is the localization of `Base` at
**any** `x = C.chartElt * D.chartElt * E.chartElt` (any reordering): instance-wise it is
`IsLocalization.Away (C.chartElt * (D.chartElt * E.chartElt))`, realigned to `x` by
`IsLocalization.Away.of_associated`. This is the explicit common-submonoid instance the cyclic
cocycle consumes — every pivot presentation localizes `Base` at the same `powers (C·D·E)`. -/
theorem isLocalization_tripleElt (C D E : AtlasChart k Base M) {x : Base}
    (hx : x = C.chartElt * D.chartElt * E.chartElt) :
    IsLocalization (Submonoid.powers x) (Localization.Away (tripleElt C D E)) := by
  haveI : IsLocalization.Away (C.chartElt * (D.chartElt * E.chartElt))
      (Localization.Away (tripleElt C D E)) :=
    IsLocalization.Away.mul' (Localization.Away C.chartElt)
      (Localization.Away (tripleElt C D E)) C.chartElt (D.chartElt * E.chartElt)
  have hassoc : Associated (C.chartElt * (D.chartElt * E.chartElt)) x := by
    rw [hx, mul_assoc]
  exact IsLocalization.Away.of_associated (S := Localization.Away (tripleElt C D E)) hassoc

/-- **The chart-`C` (symmetric) target presentation of the triple overlap.** The model `M`'s
pivot-`C` chart trivialization localized at the image, under `C.trivK`, of the non-pivot product
element `tripleElt C D E` — the triple-localized object on which the target-side triple transition
lives. Symmetric in the non-pivot charts `D, E` (it localizes at the product `D.chartElt *
E.chartElt`). `@[reducible]` so its `CommRing` / `Algebra k` instances fire transparently. -/
@[reducible] noncomputable def targetTripleLoc (C D E : AtlasChart k Base M) : Type u :=
  Localization.Away (C.trivK (tripleElt C D E))

/-- **The base→target transport of the chart-`C` triple-overlap presentation.** The generalized
localization transport `Localization.awayCongr'` of the chart-`C` trivialization `C.trivK`, carrying
the base-side triple overlap `Localization.Away (tripleElt C D E)` to the chart-`C` target
presentation `targetTripleLoc C D E`. The exact analogue of `overlapTriv` (which transports the
2-fold overlap through `C.trivK`), one denominator further. -/
noncomputable def tripleTriv (C D E : AtlasChart k Base M) :
    Localization.Away (tripleElt C D E) ≃ₐ[k] targetTripleLoc C D E :=
  Localization.awayCongr' C.trivK (tripleElt C D E) (C.trivK (tripleElt C D E)) rfl

/-- **The base-side triple transition between two pivot presentations on a fixed triple, restricted
to `k`.** The canonical localization iso `IsLocalization.algEquiv` between the pivot-`C`
presentation `Localization.Away (tripleElt C D E)` and the pivot-`D` presentation
`Localization.Away (tripleElt D E C)` of the SAME triple overlap `{C, D, E}` (both localizations of
`Base` at `powers (C.chartElt * D.chartElt * E.chartElt)`, `isLocalization_tripleElt`),
`k`-restricted along the tower `k → Base → Away`. The pivot moves `C → D`; the non-pivot args are
written `E C` so
the three cyclic transitions chain with matching targets (`targetTripleLoc` is symmetric in its two
non-pivot args, so the order there is immaterial to the overlap — only to type-level chaining). -/
noncomputable def chartTripleTransitionK (C D E : AtlasChart k Base M) :
    Localization.Away (tripleElt C D E) ≃ₐ[k] Localization.Away (tripleElt D E C) := by
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  haveI := isLocalization_tripleElt D E C (x := C.chartElt * D.chartElt * E.chartElt) (by ring)
  exact (IsLocalization.algEquiv (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
    (Localization.Away (tripleElt C D E))
    (Localization.Away (tripleElt D E C))).restrictScalars k

/-- **The canonical triple-overlap transition (pivot swap on a fixed triple).** The
change-of-coordinates between the pivot-`C` and pivot-`D` target presentations
`targetTripleLoc C D E` and `targetTripleLoc D E C` of the SAME triple overlap
`D(C.chartElt) ∩ D(D.chartElt) ∩ D(E.chartElt)`, obtained by conjugating the base-side triple
transition `chartTripleTransitionK C D E` through the two base→target transports `tripleTriv` —
constructed identically to the 2-fold `overlapTransition` (conjugate the canonical base localization
transition through the canonical trivialization transports), one denominator further. Parenthesized
as `(tripleTriv C D E).symm ≪≫ (chartTripleTransitionK C D E ≪≫ tripleTriv D E C)` so the cocycle is
reachable by the `AlgEquiv` groupoid laws.

**Scope (name = content).** This is the CANONICAL triple transition of the two charts (the unique
`k`-restriction of the localization iso between the two triple presentations). Its coincidence with
the further-localization of the 2-fold `overlapTransition C D` — the symmetric triple
`targetTripleLoc C D E` localizes the pivot-`C` chart at the PRODUCT `D.chartElt * E.chartElt`,
whereas `targetChartLoc C D` localizes at `D.chartElt` alone — is proved by the P2.g naturality
layer below (`restrict_overlapTransition_eq_tripleTransition` and the commuting square
`restrictTriple_comp_overlapTransition`), through the `Away.mul'` refinement `baseRestrTriple`. The
cocycle immediately below is the cocycle of THESE canonical triple transitions; the restricted
2-fold form is `overlapTransition_restricted_triple_cocycle`. -/
noncomputable def tripleTransition (C D E : AtlasChart k Base M) :
    targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D E C :=
  (tripleTriv C D E).symm.trans
    ((chartTripleTransitionK C D E).trans (tripleTriv D E C))

/-! ## The triple-overlap cocycle on the target/model side -/

/-- **The base-side triple cocycle, restricted to `k`.** The cyclic composite of the three base-side
pivot-swap triple transitions `chartTripleTransitionK C D E` (pivot `C → D`),
`chartTripleTransitionK D E C` (pivot `D → E`), `chartTripleTransitionK E C D` (pivot `E → C`) on
the fixed triple `{C, D, E}` is the identity on `Localization.Away (tripleElt C D E)`. Automatic by
localization initiality: it is a `Base`-algebra endo of the localization, whose only such endo is
`id` (`IsLocalization.algHom_subsingleton`). -/
theorem chartTripleTransitionK_cocycle (C D E : AtlasChart k Base M) :
    ((chartTripleTransitionK C D E).trans (chartTripleTransitionK D E C)).trans
        (chartTripleTransitionK E C D)
      = AlgEquiv.refl (R := k) := by
  -- The cyclic composite is the `k`-restriction of a composite of `Base`-algebra isos; that
  -- `Base`-algebra composite is an endo of `Localization.Away (tripleElt C D E)`, whose only
  -- `Base`-algebra endo is `id`. Each edge is realigned to the common submonoid `powers (C·D·E)`,
  -- so the unrestricted composite is `refl`, and `restrictScalars` preserves it.
  -- Mirror, per edge, the SAME submonoid `chartTripleTransitionK X Y Z` uses internally
  -- (`powers (X·Y·Z)`): supply `IsLocalization` of both endpoints at that submonoid (source by
  -- `rfl`, target realigned `by ring`). Then `hbase`'s edges match the unfolded goal's edges
  -- termwise — no submonoid-label mismatch.
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  haveI := isLocalization_tripleElt D E C (x := C.chartElt * D.chartElt * E.chartElt) (by ring)
  haveI := isLocalization_tripleElt D E C (x := D.chartElt * E.chartElt * C.chartElt) rfl
  haveI := isLocalization_tripleElt E C D (x := D.chartElt * E.chartElt * C.chartElt) (by ring)
  haveI := isLocalization_tripleElt E C D (x := E.chartElt * C.chartElt * D.chartElt) rfl
  haveI := isLocalization_tripleElt C D E (x := E.chartElt * C.chartElt * D.chartElt) (by ring)
  have hbase :
      (((IsLocalization.algEquiv (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
            (Localization.Away (tripleElt C D E))
            (Localization.Away (tripleElt D E C))).trans
          (IsLocalization.algEquiv (Submonoid.powers (D.chartElt * E.chartElt * C.chartElt))
            (Localization.Away (tripleElt D E C))
            (Localization.Away (tripleElt E C D)))).trans
        (IsLocalization.algEquiv (Submonoid.powers (E.chartElt * C.chartElt * D.chartElt))
          (Localization.Away (tripleElt E C D))
          (Localization.Away (tripleElt C D E))))
        = AlgEquiv.refl (R := Base) :=
    have : Subsingleton
        (Localization.Away (tripleElt C D E) →ₐ[Base] Localization.Away (tripleElt C D E)) :=
      IsLocalization.algHom_subsingleton (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
    AlgEquiv.coe_algHom_injective (Subsingleton.elim _ _)
  refine AlgEquiv.ext (fun x ↦ ?_)
  have hpt := AlgEquiv.ext_iff.mp hbase x
  simp only [chartTripleTransitionK, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.coe_refl, id_eq] at hpt ⊢
  -- Each edge of `chartTripleTransitionK X Y Z` is `IsLocalization.algEquiv` at `powers (X·Y·Z)`,
  -- matching the corresponding edge of `hbase` termwise.
  exact hpt

/-- **The target-side triple cocycle (standard pivot-swap form `g_jk ∘ g_ij = g_ik`).** On the fixed
triple overlap `D(C.chartElt) ∩ D(D.chartElt) ∩ D(E.chartElt)`, the three pivot-swap atlas
transitions `tripleTransition C D E` (pivot `C → D`), `tripleTransition D E C` (pivot `D → E`),
`tripleTransition E C D` (pivot `E → C`) compose, around the cycle, to the identity on
`targetTripleLoc C D E` — the genuine cocycle condition (in cyclic form `g_{CD} ≫ g_{DE} ≫ g_{EC} =
1`, equivalently `g_{DE} ∘ g_{CD} = (g_{EC})⁻¹ = g_{CE}` on the triple). The composite collapses by
the `AlgEquiv` groupoid laws WITHOUT entering localization elements: the inner `tripleTriv`
round-trips cancel, then the base-side cocycle `chartTripleTransitionK_cocycle` collapses the
middle, then the outer `(tripleTriv C D E).symm ≪≫ tripleTriv C D E = refl`. -/
theorem tripleTransition_cocycle (C D E : AtlasChart k Base M) :
    ((tripleTransition C D E).trans (tripleTransition D E C)).trans
        (tripleTransition E C D)
      = AlgEquiv.refl (R := k) := by
  -- Conjugation collapse: re-associate, cancel each adjacent `tripleTriv`/`tripleTriv.symm` pair
  -- (the inner round-trips), then the base-side cocycle collapses the middle and the outer
  -- `tripleTriv` round-trip closes it. No localization elements are entered.
  simp only [tripleTransition, AlgEquiv.trans_assoc]
  rw [← AlgEquiv.trans_assoc (tripleTriv D E C) (tripleTriv D E C).symm,
    AlgEquiv.self_trans_symm, AlgEquiv.refl_trans,
    ← AlgEquiv.trans_assoc (tripleTriv E C D) (tripleTriv E C D).symm,
    AlgEquiv.self_trans_symm, AlgEquiv.refl_trans,
    ← AlgEquiv.trans_assoc (chartTripleTransitionK D E C) (chartTripleTransitionK E C D),
    ← AlgEquiv.trans_assoc (chartTripleTransitionK C D E)
      ((chartTripleTransitionK D E C).trans (chartTripleTransitionK E C D)),
    ← AlgEquiv.trans_assoc (chartTripleTransitionK C D E) (chartTripleTransitionK D E C),
    chartTripleTransitionK_cocycle, AlgEquiv.refl_trans, AlgEquiv.symm_trans_self]

/-! ## Naturality (P2.g): the restricted 2-fold transition IS the triple transition

The triple cocycle above is of the CANONICAL triple transitions `tripleTransition`. This section
proves the NATURALITY tying them to the further-localization of the 2-fold `overlapTransition` — the
R1 gap P2.f flagged. The genuine content is a per-triple compatibility (a commuting square), NOT the
global gluing.

The proof route is base-side subsingleton, then trivialization conjugation (mirroring the cocycle):
the restricted 2-fold and the canonical triple transition are BOTH `Base`-algebra isos between the
same two triple presentations (localizations of `Base` at `powers (C·D·E)`), so they agree by
`IsLocalization.algHom_subsingleton` OVER `Base`; the target-side statement then follows by pure
`AlgEquiv`-groupoid conjugation through `tripleTriv`. (Subsingleton over the model `M` would be
unsound — the maps are not `M`-algebra maps.) -/

/-- **The base-side restricted 2-fold transition (canonical, at the triple).** The canonical
`Base`-algebra iso between the pivot-`C` and pivot-`D` triple presentations of the SAME triple
overlap, at the common submonoid `powers (C·D·E)` — the further-localization of the 2-fold base
transition `awayOverlapTransition C.chartElt D.chartElt` one denominator up (from `powers (C·D)` to
`powers (C·D·E)`), realized as `IsLocalization.algEquiv` at the triple submonoid. -/
noncomputable def chartOverlapTripleBase (C D E : AtlasChart k Base M) :
    Localization.Away (tripleElt C D E) ≃ₐ[Base] Localization.Away (tripleElt D C E) := by
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  haveI := isLocalization_tripleElt D C E (x := C.chartElt * D.chartElt * E.chartElt) (by ring)
  exact IsLocalization.algEquiv (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
    (Localization.Away (tripleElt C D E)) (Localization.Away (tripleElt D C E))

/-- **The base-side non-pivot reorder `D·C·E → D·E·C`.** The canonical `Base`-algebra iso
`Away (tripleElt D C E) ≃ₐ[Base] Away (tripleElt D E C)` — same pivot `D`, non-pivot product
reordered by `mul_comm` (`C·E = E·C`) — via `Localization.awayCongr'` of the identity
`AlgEquiv.refl` on the pivot-`D` chart ring. Absorbs the mismatch between the restricted 2-fold's
codomain (`D C E`) and the canonical triple transition's codomain (`D E C`). -/
noncomputable def tripleReorderBase (C D E : AtlasChart k Base M) :
    Localization.Away (tripleElt D C E) ≃ₐ[Base] Localization.Away (tripleElt D E C) :=
  Localization.awayCongr' (AlgEquiv.refl (R := Base) (A₁ := Localization.Away D.chartElt))
    (tripleElt D C E) (tripleElt D E C)
    (by simp only [AlgEquiv.coe_refl, id_eq, tripleElt]; rw [mul_comm])

/-- **The base-side canonical triple transition (unrestricted `Base`).** `IsLocalization.algEquiv`
at `powers (C·D·E)` between the pivot-`C` and pivot-`D` presentations `Away (tripleElt C D E)` and
`Away (tripleElt D E C)`; `chartTripleTransitionK` is its `k`-restriction (`rfl`). Named so the base
naturality can be stated and proved over `Base` (subsingleton), then `k`-restricted. -/
noncomputable def chartTripleTransitionBase (C D E : AtlasChart k Base M) :
    Localization.Away (tripleElt C D E) ≃ₐ[Base] Localization.Away (tripleElt D E C) := by
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  haveI := isLocalization_tripleElt D E C (x := C.chartElt * D.chartElt * E.chartElt) (by ring)
  exact IsLocalization.algEquiv (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
    (Localization.Away (tripleElt C D E)) (Localization.Away (tripleElt D E C))

/-- `chartTripleTransitionK` is the `k`-restriction of `chartTripleTransitionBase` (definitionally —
both are `IsLocalization.algEquiv` at the same triple submonoid). -/
theorem chartTripleTransitionK_eq_restrict (C D E : AtlasChart k Base M) :
    chartTripleTransitionK C D E = (chartTripleTransitionBase C D E).restrictScalars k := rfl

/-- **Base naturality (crux).** `chartOverlapTripleBase C D E ≪≫ tripleReorderBase C D E =
chartTripleTransitionBase C D E`: the restricted 2-fold transition, followed by the non-pivot
reorder, is the canonical triple transition. Both are `Base`-algebra maps out of the localization
`Away (tripleElt C D E)`, so they agree by the universal property
(`IsLocalization.algHom_subsingleton` at `powers (C·D·E)`). -/
theorem chartOverlapTripleBase_trans_reorder (C D E : AtlasChart k Base M) :
    (chartOverlapTripleBase C D E).trans (tripleReorderBase C D E)
      = chartTripleTransitionBase C D E := by
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  have : Subsingleton
      (Localization.Away (tripleElt C D E) →ₐ[Base] Localization.Away (tripleElt D E C)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (C.chartElt * D.chartElt * E.chartElt))
  exact AlgEquiv.coe_algHom_injective (Subsingleton.elim _ _)

/-- **The target-side restricted 2-fold transition (the further-localization of `overlapTransition`
to the triple).** The change-of-coordinates on the triple presentations obtained by conjugating the
base restricted 2-fold `chartOverlapTripleBase` through the trivializations `tripleTriv` — built
identically to `overlapTransition` (conjugate the canonical base transition through the canonical
trivialization transports), one denominator further. This is the further-localization of
`overlapTransition C D`; `restrictTriple_comp_overlapTransition` below is the commuting square
making that identification literal. -/
noncomputable def restrictedOverlapTripleTransition (C D E : AtlasChart k Base M) :
    targetTripleLoc C D E ≃ₐ[k] targetTripleLoc D C E :=
  (tripleTriv C D E).symm.trans
    (((chartOverlapTripleBase C D E).restrictScalars k).trans (tripleTriv D C E))

/-- **The target-side non-pivot reorder** `targetTripleLoc D C E ≃ₐ[k] targetTripleLoc D E C`,
conjugating `tripleReorderBase` through `tripleTriv`. -/
noncomputable def targetTripleReorder (C D E : AtlasChart k Base M) :
    targetTripleLoc D C E ≃ₐ[k] targetTripleLoc D E C :=
  (tripleTriv D C E).symm.trans
    (((tripleReorderBase C D E).restrictScalars k).trans (tripleTriv D E C))

/-- `restrictScalars` distributes over `trans` (the underlying functions compose identically). -/
theorem restrictScalars_trans {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra Base A] [Algebra k B] [Algebra Base B] [Algebra k C] [Algebra Base C]
    [IsScalarTower k Base A] [IsScalarTower k Base B] [IsScalarTower k Base C]
    (e : A ≃ₐ[Base] B) (f : B ≃ₐ[Base] C) :
    (e.restrictScalars k).trans (f.restrictScalars k) = (e.trans f).restrictScalars k := rfl

/-- The `k`-restriction of the base naturality: the restricted 2-fold ≪≫ reorder (both
`k`-restricted) is `chartTripleTransitionK`. -/
theorem chartOverlapTripleK_trans_reorder (C D E : AtlasChart k Base M) :
    (((chartOverlapTripleBase C D E).restrictScalars k).trans
        ((tripleReorderBase C D E).restrictScalars k))
      = chartTripleTransitionK C D E := by
  rw [restrictScalars_trans, chartOverlapTripleBase_trans_reorder,
    chartTripleTransitionK_eq_restrict]

/-- **Naturality (iv): the restricted 2-fold transition IS the triple transition.** On the target/
model triple presentations, the further-localization of the 2-fold `overlapTransition C D`
(`restrictedOverlapTripleTransition`), followed by the non-pivot reorder, equals the canonical
triple transition `tripleTransition C D E`. Unfolds the conjugations and collapses by the `AlgEquiv`
groupoid laws to the `k`-restricted base naturality `chartOverlapTripleK_trans_reorder`, WITHOUT
entering localization elements: the inner `tripleTriv D C E` round-trip cancels, then the base
naturality
identifies the middle with `chartTripleTransitionK`. This closes the R1 gap for the 2-fold ↔ triple
tie. -/
theorem restrict_overlapTransition_eq_tripleTransition (C D E : AtlasChart k Base M) :
    (restrictedOverlapTripleTransition C D E).trans (targetTripleReorder C D E)
      = tripleTransition C D E := by
  simp only [restrictedOverlapTripleTransition, targetTripleReorder, tripleTransition,
    AlgEquiv.trans_assoc]
  rw [← AlgEquiv.trans_assoc (tripleTriv D C E) (tripleTriv D C E).symm,
    AlgEquiv.self_trans_symm, AlgEquiv.refl_trans,
    ← AlgEquiv.trans_assoc ((chartOverlapTripleBase C D E).restrictScalars k)
      ((tripleReorderBase C D E).restrictScalars k),
    chartOverlapTripleK_trans_reorder]

/-! ### The genuine restriction map + the commuting square (tie to the ACTUAL 2-fold transition) -/

/-- **The base-side further-localization of the chart-`C` overlap presentation to the triple.** The
`Base`-algebra map `awayOverlap C.chartElt D.chartElt →ₐ[Base] Away (tripleElt C D E)`: the overlap
`Away (overlapElt C D)` (loc of `Base` at `powers (C·D)`) localized further at the third element
`E`. Built by the localization universal property (`IsLocalization.liftAlgHom`): `powers (C·D)` are
units in the triple ring because `C·D·E` is (the localizing element) and `C·D ∣ C·D·E`. -/
noncomputable def baseRestrTriple (C D E : AtlasChart k Base M) :
    Localization.awayOverlap C.chartElt D.chartElt →ₐ[Base]
      Localization.Away (tripleElt C D E) := by
  haveI := isLocalization_tripleElt C D E (x := C.chartElt * D.chartElt * E.chartElt) rfl
  refine IsLocalization.liftAlgHom (M := Submonoid.powers (C.chartElt * D.chartElt))
    (f := Algebra.ofId Base (Localization.Away (tripleElt C D E))) ?_
  rintro ⟨_, n, rfl⟩
  rw [Algebra.ofId_apply, map_pow]
  refine IsUnit.pow n ?_
  have hu : IsUnit (algebraMap Base (Localization.Away (tripleElt C D E))
      (C.chartElt * D.chartElt * E.chartElt)) :=
    IsLocalization.map_units (Localization.Away (tripleElt C D E))
      ⟨C.chartElt * D.chartElt * E.chartElt, Submonoid.mem_powers _⟩
  rw [map_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- **The restriction map** `targetChartLoc C D →ₐ[k] targetTripleLoc C D E`: the
further-localization of the chart-`C` overlap presentation to the triple, conjugating
`baseRestrTriple` through the two base→target transports (`overlapTriv`, `tripleTriv`) — the
target-side analogue of `baseRestrTriple`, built by conjugation so it agrees with the base
restriction by construction (the inferred `targetChartLoc C D → targetTripleLoc C D E` localization
tower is NOT automatic). -/
noncomputable def restrictTriple (C D E : AtlasChart k Base M) :
    targetChartLoc C D →ₐ[k] targetTripleLoc C D E :=
  ((tripleTriv C D E).toAlgHom.restrictScalars k).comp
    (((baseRestrTriple C D E).restrictScalars k).comp
      ((overlapTriv C D).symm.toAlgHom.restrictScalars k))

/-- **The base commuting square (crux of the literal tie).** `baseRestrTriple D C E ∘
awayOverlapTransition C.chartElt D.chartElt = chartOverlapTripleBase C D E ∘ baseRestrTriple C D E`:
the base 2-fold transition, further-localized at `E`, is the base restricted 2-fold transition. Both
are `Base`-algebra maps out of `awayOverlap C.chartElt D.chartElt` (loc at `powers (C·D)`), so they
agree by `IsLocalization.algHom_subsingleton`. -/
theorem baseRestr_square (C D E : AtlasChart k Base M) :
    (baseRestrTriple D C E).comp
        (Localization.awayOverlapTransition C.chartElt D.chartElt).toAlgHom
      = (chartOverlapTripleBase C D E).toAlgHom.comp (baseRestrTriple C D E) := by
  have : Subsingleton
      (Localization.awayOverlap C.chartElt D.chartElt →ₐ[Base]
        Localization.Away (tripleElt D C E)) :=
    IsLocalization.algHom_subsingleton (Submonoid.powers (C.chartElt * D.chartElt))
  exact Subsingleton.elim _ _

/-- The base commuting square, pointwise. -/
theorem baseRestr_square_apply (C D E : AtlasChart k Base M)
    (z : Localization.awayOverlap C.chartElt D.chartElt) :
    baseRestrTriple D C E (Localization.awayOverlapTransition C.chartElt D.chartElt z)
      = chartOverlapTripleBase C D E (baseRestrTriple C D E z) := by
  have := AlgHom.ext_iff.mp (baseRestr_square C D E) z
  simpa only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgEquiv.coe_algHom,
    AlgHom.coe_coe] using this

/-- The restriction map applied (pointwise unfolding). -/
theorem restrictTriple_apply (C D E : AtlasChart k Base M) (x : targetChartLoc C D) :
    restrictTriple C D E x
      = tripleTriv C D E (baseRestrTriple C D E ((overlapTriv C D).symm x)) := by
  rfl

/-- The target restricted 2-fold transition applied (pointwise unfolding). -/
theorem restrictedOverlapTripleTransition_apply (C D E : AtlasChart k Base M)
    (y : targetTripleLoc C D E) :
    restrictedOverlapTripleTransition C D E y
      = tripleTriv D C E (chartOverlapTripleBase C D E ((tripleTriv C D E).symm y)) := by
  simp only [restrictedOverlapTripleTransition, AlgEquiv.trans_apply,
    AlgEquiv.restrictScalars_apply]

/-- **The commuting square: the restricted 2-fold IS the further-localization of the ACTUAL
`overlapTransition`.** `restrictTriple D C E ∘ overlapTransition C D =
restrictedOverlapTripleTransition C D E ∘ restrictTriple C D E` (as `k`-algebra maps
`targetChartLoc C D → targetTripleLoc D C E`) — the naturality square exhibiting
`restrictedOverlapTripleTransition` genuinely as the restriction (further localization) of the
honest 2-fold transition to the triple overlap. Reduces, after unfolding the
restriction/transition applications and cancelling an `overlapTriv D C` round-trip, to the base
commuting square `baseRestr_square`. -/
theorem restrictTriple_comp_overlapTransition (C D E : AtlasChart k Base M) :
    (restrictTriple D C E).comp (overlapTransition C D).toAlgHom
      = (restrictedOverlapTripleTransition C D E).toAlgHom.comp (restrictTriple C D E) := by
  apply AlgHom.ext
  intro x
  simp only [AlgHom.comp_apply, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe]
  rw [restrictTriple_apply, restrictedOverlapTripleTransition_apply, restrictTriple_apply,
    AlgEquiv.symm_apply_apply]
  rw [show (overlapTriv D C).symm ((overlapTransition C D) x)
        = Localization.awayOverlapTransition C.chartElt D.chartElt
            ((overlapTriv C D).symm x) from by
      simp only [overlapTransition, chartOverlapTransitionK, AlgEquiv.trans_apply,
        AlgEquiv.symm_apply_apply, AlgEquiv.restrictScalars_apply]]
  rw [baseRestr_square_apply]

/-- **The restricted 2-fold cocycle (standard form `g_jk ∘ g_ij = g_ik`).** The cyclic composite of
the three restricted 2-fold transitions — each `restrictedOverlapTripleTransition` re-symmetrized by
its non-pivot reorder `targetTripleReorder` — is the identity on `targetTripleLoc C D E`. This is
`tripleTransition_cocycle` rewritten along naturality (iv)
`restrict_overlapTransition_eq_tripleTransition`: the restricted 2-fold transitions of the atlas
(the honest further-localizations of `overlapTransition`) satisfy the genuine cocycle condition on
the triple overlap. -/
theorem overlapTransition_restricted_triple_cocycle (C D E : AtlasChart k Base M) :
    ((((restrictedOverlapTripleTransition C D E).trans (targetTripleReorder C D E)).trans
          ((restrictedOverlapTripleTransition D E C).trans (targetTripleReorder D E C))).trans
        ((restrictedOverlapTripleTransition E C D).trans (targetTripleReorder E C D)))
      = AlgEquiv.refl (R := k) := by
  rw [restrict_overlapTransition_eq_tripleTransition,
    restrict_overlapTransition_eq_tripleTransition,
    restrict_overlapTransition_eq_tripleTransition]
  exact tripleTransition_cocycle C D E

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
