/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleLocallyTrivialFull
import DLNFibre.Core.RingTheory.Determinantal.AtlasTransition

/-!
# `DLNFibre.Core.FibreTargetOverlap` — the target-side overlap transition (R1, pairwise)

The atlas (`Core.FibreBundleLocallyTrivialFull`) carries the **base-side** overlap cocycle
`chartOverlapTransition I J` (over `sweepSigmaRing`) and the per-pivot trivializations into the
standard fibre model `M := SchurLoc ⊗_k sweepFibreRing`. The S5 capstone names R1 — the
**target-side** overlap-trivialization cocycle — as the residual to a single global `Flat π` /
`FiberBundle`. This module builds the genuine target-side transition, **pairwise**, as the **DLN
instance of the abstract constructive-atlas overlap transition**
`Algebra.AtlasChart.overlapTransition`
(`DLNFibre.Core.RingTheory.Determinantal.AtlasTransition`): the **double-localized** transition on
the product model `M`, transported from the base-side overlap through the per-pivot trivializations.

## The DLN bundle as an instance of the abstract atlas

Each pivot `I` is an `Algebra.AtlasChart` `pivotAtlasChart I` over the global base
`Base = sweepSigmaRing`: base element the pivot minor `pivotElt I = chartDsigAt I.s I.t` (cutting
the chart `D(pivotElt I)`), bare `k`-algebra trivialization the gauge-transported tensor package
`perPivotLocalTrivializationDatum.trivialization` (`Away (chartDsigAt I.s I.t) ≃ₐ[k] M`). The
base-side overlap transition `chartOverlapTransitionK I J` and its round-trip
`chartOverlapTransitionK_trans_symm` are then **literally the abstract atlas transition** at the
pivot charts (`Algebra.AtlasChart.chartOverlapTransitionK (pivotAtlasChart I) (pivotAtlasChart J)`
&c.). The target-side data (`overlapElt`, `targetChartLoc`, `overlapTriv`,
`targetProductOverlapTransition`) are the abstract construction unfolded to a single
`Localization.Away` layer (so the doubly-localized `targetChartLoc`'s instances fire — routing them
through the abstract `AtlasChart` structure projection makes `Semiring`-synthesis whnf-reduce the
heavy per-pivot trivialization and time out); they are definitionally the abstract data at
`pivotAtlasChart`.

## The construction (double-localized)

For two pivots `I, J`, the base-side overlap `awayOverlap (pivotElt I) (pivotElt J)` is
`Localization.Away eIJ` where `eIJ := algebraMap sweepSigmaRing (Away (chartDsigAt I.s I.t))
(pivotElt J)` is the chart-`J` minor localized into the chart-`I` total ring (`pivotElt I =
chartDsigAt I.s I.t`, so `Away (pivotElt I)` IS the chart-`I` total ring). Transporting along the
per-pivot trivialization `triv I : Away (chartDsigAt I.s I.t) ≃ₐ[k] M` (the re-homed generalized
localization transport `Localization.awayCongr'`) lands `awayOverlap (pivotElt I)(pivotElt J) ≃ₐ[k]
Localization.Away (triv I eIJ)` — `M` localized at the image of the chart-`J` minor. The
target-side transition is then

> `targetProductOverlapTransition I J :
>    Localization.Away (triv I eIJ) ≃ₐ[k] Localization.Away (triv J eJI)`,

obtained by conjugating the base-side `chartOverlapTransitionK I J` through the two transports — a
`k`-algebra iso between the two double-localized presentations of the overlap on the product model
`M`.

## Main results

* `pivotAtlasChart I` — the `Algebra.AtlasChart` of a pivot (the DLN bundle as the abstract
  instance).
* `targetChartLoc I J` — the chart-`I` target presentation of the overlap: `M` localized at the
  image `triv I eIJ` of the chart-`J` minor.
* `overlapTriv I J` — the base→target transport `awayOverlap (pivotElt I)(pivotElt J) ≃ₐ[k]
  targetChartLoc I J` (`Localization.awayCongr'` of `triv I`).
* `chartOverlapTransitionK I J` + `chartOverlapTransitionK_trans_symm` — the base-side transition as
  a `k`-algebra equiv and its round-trip to the identity, **the abstract atlas transition at the
  pivot charts**.
* `targetProductOverlapTransition I J` — the **target-side overlap transition** on the product model
  (double-localized), pairwise.

## Scope (honest)

This is the **pairwise** target-side transition (the domains are chart-dependent double
localizations). The transition OBJECT is built (as the DLN instance of the abstract atlas
transition); its **round-trip cocycle** `(I, J) ∘ (J, I) = id` is now PROVED — it is the abstract
`Algebra.AtlasChart.overlapTransition_trans_symm` (P2.c, LANDED in `AtlasTransition`) at the pivot
charts, and fires on the DLN instance via
`Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm`
(`Core.FibreZariskiLocalTriviality`). The canonical triple cocycle (P2.f) and the naturality tying
the triple to the further-localized 2-fold transition (P2.g) are likewise proved abstractly and
inherited. Only a single GLOBAL `Flat π` / `FiberBundle` over all of `rankROpen` stays roadmapped
(R1): the GLOBAL gluing of the per-chart data into one fibration morphism + a local-to-global
flatness assembly (see `Core.FibreBundleHeadline`) — NOT the local pairwise/triple coherence, which
is landed. What this module removes is "the target-side transition does not exist" — it does,
pairwise, as an instance of the abstract atlas, with the pairwise round-trip a free theorem.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Localization
open scoped TensorProduct

universe u

/-! ## The target-side overlap transition on the product model -/

section Target

variable {k : Type} [Field k] [Infinite k] {N : ℕ}
variable (d : Fin (N + 2) → ℕ) (r : ℕ)
  (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)

/-- **The atlas chart of a pivot — the DLN bundle as the abstract instance.** The
`Algebra.AtlasChart` over the global base `Base = sweepSigmaRing`: base element the pivot minor
`pivotElt I = chartDsigAt I.s I.t` (cutting the chart `D(pivotElt I)`), bare `k`-algebra
trivialization the gauge-transported tensor package
`perPivotLocalTrivializationDatum.trivialization` (`Away (chartDsigAt I.s I.t) ≃ₐ[k] M`,
`M = SchurLoc ⊗_k sweepFibreRing`). This exhibits the DLN reduced-fibre bundle as an instance of the
Core constructive-atlas transition layer (`Algebra.AtlasChart`); the base-side transition below is
the abstract `Algebra.AtlasChart.…` at this instance. -/
noncomputable def pivotAtlasChart (I : PivotDatum d r hp hq) :
    Algebra.AtlasChart k (sweepSigmaRing k d r)
      (SchurLoc (k := k) (d 0) (d (Fin.last (N + 1))) r ⊗[k] sweepFibreRing k d r hp hq) where
  chartElt := pivotElt d r hp hq I
  trivK :=
    (perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization

@[simp] theorem pivotAtlasChart_chartElt (I : PivotDatum d r hp hq) :
    (pivotAtlasChart (k := k) d r hp hq I).chartElt = pivotElt d r hp hq I := rfl

@[simp] theorem pivotAtlasChart_trivK (I : PivotDatum d r hp hq) :
    (pivotAtlasChart (k := k) d r hp hq I).trivK
      = (perPivotLocalTrivializationDatum (k := k) d r hp hq
          I.s I.t I.σ I.τ I.hσ I.hτ).trivialization :=
  rfl

/-- **The chart-`J` minor localized into the chart-`I` total ring.** `algebraMap sweepSigmaRing
(Away (chartDsigAt I.s I.t)) (pivotElt J)` — the element of the chart-`I` total ring whose inversion
cuts the overlap `D(pivotElt I · pivotElt J)`. Since `pivotElt I = chartDsigAt I.s I.t`, its
`Localization.Away` is exactly the base-side overlap `awayOverlap (pivotElt I)(pivotElt J)`.
Definitionally the abstract `Algebra.AtlasChart.overlapElt (pivotAtlasChart I)
(pivotAtlasChart J)`. -/
noncomputable def overlapElt (I J : PivotDatum d r hp hq) :
    Localization.Away (chartDsigAt (k := k) d r I.s I.t) :=
  algebraMap (sweepSigmaRing k d r) (Localization.Away (chartDsigAt (k := k) d r I.s I.t))
    (pivotElt d r hp hq J)

/-- **The chart-`I` target presentation of the overlap.** The product model `M = SchurLoc ⊗_k
sweepFibreRing` localized at the image, under the chart-`I` trivialization `triv I`, of the
chart-`J` minor (`overlapElt I J`) — the double-localized object on which the target-side
transition lives. `@[reducible]` so its `CommRing` / `Algebra k` instances fire transparently
(needed by `Localization.awayCongr'`). Definitionally the abstract
`Algebra.AtlasChart.targetChartLoc (pivotAtlasChart I) (pivotAtlasChart J)`, kept in this
one-`Localization.Away`-layer shape so its
`Semiring` instance fires (routing through the abstract structure projection times out). -/
@[reducible] noncomputable def targetChartLoc (I J : PivotDatum d r hp hq) : Type :=
  Localization.Away
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization
      (overlapElt d r hp hq I J))

/-- **The base→target transport of the chart-`I` overlap presentation.** The re-homed generalized
localization transport `Localization.awayCongr'` of the per-pivot trivialization `triv I`, carrying
the base-side overlap `awayOverlap (pivotElt I)(pivotElt J) = Localization.Away (overlapElt I J)` to
the chart-`I` target presentation `targetChartLoc I J = M` localized at `triv I (overlapElt I J)`.
Definitionally the abstract `Algebra.AtlasChart.overlapTriv (pivotAtlasChart I)
(pivotAtlasChart J)`, unfolded so the doubly-localized `targetChartLoc` instances fire. -/
noncomputable def overlapTriv (I J : PivotDatum d r hp hq) :
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[k] targetChartLoc (k := k) d r hp hq I J :=
  Localization.awayCongr'
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization)
    (overlapElt d r hp hq I J)
    ((perPivotLocalTrivializationDatum (k := k) d r hp hq I.s I.t I.σ I.τ I.hσ I.hτ).trivialization
      (overlapElt d r hp hq I J)) rfl

/-- **The base-side overlap transition as a `k`-algebra equiv — the abstract atlas transition at the
pivot charts.** `Algebra.AtlasChart.chartOverlapTransitionK (pivotAtlasChart I)
(pivotAtlasChart J)`: the abstract base-side overlap transition
(`Localization.awayOverlapTransition` at the pivot minors, `k`-restricted) at the DLN instance. The
`k`-algebra version the target-side transition conjugates the trivializations through; the abstract
def pins the scalar-tower instances internally. -/
noncomputable def chartOverlapTransitionK (I J : PivotDatum d r hp hq) :
    awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)
      ≃ₐ[k] awayOverlap (pivotElt (k := k) d r hp hq J) (pivotElt (k := k) d r hp hq I) :=
  Algebra.AtlasChart.chartOverlapTransitionK
    (pivotAtlasChart d r hp hq I) (pivotAtlasChart d r hp hq J)

/-- The `k`-restricted base transition agrees with the underlying `sweepSigmaRing`-algebra base
transition as a function. -/
@[simp] theorem chartOverlapTransitionK_apply (I J : PivotDatum d r hp hq)
    (x : awayOverlap (pivotElt (k := k) d r hp hq I) (pivotElt (k := k) d r hp hq J)) :
    chartOverlapTransitionK d r hp hq I J x = chartOverlapTransition d r hp hq I J x := rfl

/-- **The target-side overlap transition (R1, pairwise, double-localized).** The `k`-algebra iso
between the two chart presentations of the overlap on the product model `M`: the chart-`I`
presentation `targetChartLoc I J` and the chart-`J` presentation `targetChartLoc J I`, obtained by
conjugating the base-side overlap transition `chartOverlapTransitionK I J` (the `k`-restricted base
transition) through the two base→target transports `overlapTriv`. This is the genuine target-side
transition the S5 capstone named as residual R1 — here pairwise, as a double-localized object, and
the DLN instance of the abstract `Algebra.AtlasChart.overlapTransition` (same construction:
`(overlapTriv I J).symm ≪≫ (chartOverlapTransitionK I J ≪≫ overlapTriv J I)`, parenthesized so the
cocycle round-trip is reachable by the `AlgEquiv` groupoid laws). -/
noncomputable def targetProductOverlapTransition (I J : PivotDatum d r hp hq) :
    targetChartLoc (k := k) d r hp hq I J ≃ₐ[k] targetChartLoc (k := k) d r hp hq J I :=
  (overlapTriv d r hp hq I J).symm.trans
    ((chartOverlapTransitionK d r hp hq I J).trans (overlapTriv d r hp hq J I))

/-- **The base transition round-trips to the identity — the abstract atlas round-trip at the pivot
charts.** `Algebra.AtlasChart.chartOverlapTransitionK_trans_symm (pivotAtlasChart I)
(pivotAtlasChart J)`: the pairwise round trip `(I, J)` then `(J, I)` is the identity on the overlap.
This is the base-level evidence the target-side cocycle (P2.c, LANDED) is built from. -/
theorem chartOverlapTransitionK_trans_symm (I J : PivotDatum d r hp hq) :
    (chartOverlapTransitionK d r hp hq I J).trans (chartOverlapTransitionK d r hp hq J I)
      = AlgEquiv.refl (R := k) :=
  Algebra.AtlasChart.chartOverlapTransitionK_trans_symm
    (pivotAtlasChart d r hp hq I) (pivotAtlasChart d r hp hq J)

/-! ### The target-side cocycle round-trip — LANDED (P2.c), inherited from the abstract atlas

The pairwise target-side **transition object** `targetProductOverlapTransition` is the DLN instance
of the abstract `Algebra.AtlasChart.overlapTransition`. Its **round-trip cocycle**
`(I, J) ∘ (J, I) = id` is now PROVED abstractly: `Algebra.AtlasChart.overlapTransition_trans_symm`
(P2.c, in `AtlasTransition`) collapses the conjugation `T_IJ.symm ≪≫ K_IJ ≪≫ (T_JI ≪≫ T_JI.symm) ≪≫
K_JI ≪≫ T_IJ` by the `AlgEquiv` groupoid laws `AlgEquiv.trans_assoc` / `trans_refl` / `refl_trans`
(supplied by `DLNFibre.Core.Algebra.AlgEquiv.Groupoid`) at the abstract `AlgEquiv` level — off the
heavy double-localized `targetChartLoc`, so no pointwise-`ext` kernel cost — using the base-side
`chartOverlapTransitionK_trans_symm` (just above) for the middle cancellation. On the DLN instance
it fires as `Algebra.IsZariskiLocallyTrivialAffineProduct.overlapTransition_trans_symm`
(`Core.FibreZariskiLocalTriviality`). The canonical triple cocycle (P2.f
`tripleTransition_cocycle`) and the naturality tie of the triple to the further-localized 2-fold
(P2.g) are likewise landed abstractly and inherited. Only the GLOBAL gluing into one `Flat π` /
`FiberBundle` stays roadmapped (R1). -/

end Target

/-! ## Non-vacuity witnesses -/

section Witness

variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-- **Target transition witness.** The target-side overlap transition exists at every pair of
pivots — a genuine double-localized `k`-algebra iso on the product model. -/
noncomputable example (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    targetChartLoc (k := k) d r hp hq I J ≃ₐ[k] targetChartLoc (k := k) d r hp hq J I :=
  targetProductOverlapTransition d r hp hq I J

/-- **Base round-trip witness.** The base transition round-trips to the identity — the base-level
evidence the LANDED target-side cocycle (P2.c) is built from. -/
example (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0) (I J : PivotDatum d r hp hq) :
    (chartOverlapTransitionK d r hp hq I J).trans (chartOverlapTransitionK d r hp hq J I)
      = AlgEquiv.refl (R := k) :=
  chartOverlapTransitionK_trans_symm d r hp hq I J

end Witness

end DLNFibre.Core
