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
* `Algebra.AtlasFibreChart …` — `AtlasChart` paired with the over-base `StandardFibreChart` (the
  capstone's per-chart fibre model), with the same `chartElt`.

**Scope.** This builds the transition OBJECTS + the cocycle COMPATIBILITIES (the 2-fold round-trip
`overlapTransition_trans_symm`, P2.c; the triple cocycle `tripleTransition_cocycle`, P2.f) — both by
the `AlgEquiv` groupoid laws without entering localization elements. What is NOT proved here is the
**naturality** tying the triple transition to the further-localization of the 2-fold
`overlapTransition` (the symmetric triple localizes at the PRODUCT `D·E`, the 2-fold at `D` alone,
so the tie needs the `Away.mul'` refinement + a compatibility lemma — roadmap R1). The cocycle is
the cocycle of the CANONICAL triple transitions, which are built identically to `overlapTransition`.

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
`k`-restriction of the localization iso between the two triple presentations). It is NOT proved here
to coincide with the further-localization of the 2-fold `overlapTransition C D`: the symmetric
triple `targetTripleLoc C D E` localizes the pivot-`C` chart at the PRODUCT
`D.chartElt * E.chartElt`, whereas `targetChartLoc C D` localizes at `D.chartElt` alone, so the tie
needs the `Away.mul'` refinement iso `Away (d * e) ≃ (Away d) away e` plus a
transition-compatibility lemma — a separate naturality rung (roadmap R1). The cocycle below is the
cocycle of THESE canonical triple transitions, on the triple overlap. -/
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
