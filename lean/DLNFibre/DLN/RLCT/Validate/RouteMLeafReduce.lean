import DLNFibre.DLN.RLCT.Validate.RouteMLeafEngine

/-!
# `RouteMLeafReduce` — stripping `paramsEquivFlat`: reduce `hdet` to a `Params M`-level determinant

`BchartLeaf ha y = paramsEquivFlat M (BparamsLeaf ha y)` and `paramsEquivFlat` is a
measure-preserving ℝ-linear equivalence (`|det| = 1`). This module records that the chart Jacobian
`|det (fderiv BchartLeaf y₀)|` equals the determinant of the INNER boundary-factor derivative
`Dtot y₀ := paramsEquivFlatLinear ∘ₗ (fderiv BparamsLeaf y₀)` — an endomorphism of
`Fin (routeMAmbient M) → ℝ` (since `routeMAmbient M = flatDim M`). The outer reindex contributes
`|det| = 1`, so the entire chart determinant is carried by the boundary-factor block determinant on
`Params M`. This leaves the single remaining obligation `|det (Dtot y₀)| = engineFreeK_0` — the
free-K Schur frame determinant, the staircase-det piece.

* `BparamsLeaf_hasFDerivAt` — `BparamsLeaf` has its `fderiv` (the chain is polynomial in `y`).
* `Dtot` — `paramsEquivFlat ∘ₗ (fderiv BparamsLeaf y₀)`, an endo of `Fin (flatDim M) → ℝ`.
* `Bchart_abs_det_eq_Dtot` — `|det (fderiv BchartLeaf y₀)| = |det (Dtot y₀)|`.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (calculus + the banked linear flattening).
-/

open Matrix
open scoped BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

section L2

variable {M : Fin (2 + 1) → ℕ}

/-- `BparamsLeaf` has its `fderiv` at every point (the chain is polynomial in `y`; the inner half of
`Bchart_differentiableAt`). -/
theorem BparamsLeaf_hasFDerivAt (ha : StructAdm M (tach M)) (y : Fin (routeMAmbient M) → ℝ) :
    HasFDerivAt (fun z => BparamsLeaf ha z) (fderiv ℝ (fun z => BparamsLeaf ha z) y) y := by
  have hchart : DifferentiableAt ℝ (fun z => BparamsLeaf ha z) y := by
    apply differentiableAt_pi.mpr
    intro s
    exact diffAt_reindex_finCongr _ _ _ y (diffAt_Agen_live ha y s.val)
  exact hchart.hasFDerivAt

/-- **The inner boundary-factor derivative** `Dtot y₀` — the `toLinearMap` of the chain-rule
CLM composite `paramsEquivFlatCLE ∘L (D BparamsLeaf y₀)`, an endomorphism of `Fin (flatDim M) → ℝ`
(`= Fin (routeMAmbient M) → ℝ`). The outer factor is the measure-preserving linear flattening
`paramsEquivFlat`; the inner is the boundary-factor `BparamsLeaf` derivative. -/
noncomputable def Dtot (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    (Fin (flatDim M) → ℝ) →ₗ[ℝ] (Fin (flatDim M) → ℝ) :=
  ((paramsEquivFlatCLE M).toContinuousLinearMap.comp
    (fderiv ℝ (fun z => BparamsLeaf ha z) y₀)).toLinearMap

/-- **The chart Jacobian determinant is carried entirely by the inner boundary-factor block** —
`|det (fderiv BchartLeaf y₀)| = |det (Dtot y₀)|`. The outer reindex `paramsEquivFlat` is the
measure-preserving linear flattening (`|det| = 1`); the chain rule moves it onto the inner
derivative, where it composes into `Dtot`. -/
theorem Bchart_abs_det_eq_Dtot (ha : StructAdm M (tach M)) (y₀ : Fin (routeMAmbient M) → ℝ) :
    |LinearMap.det (fderiv ℝ (BchartLeaf ha) y₀).toLinearMap|
      = |LinearMap.det (Dtot ha y₀)| := by
  -- `BchartLeaf = paramsEquivFlat ∘ BparamsLeaf`; chain rule with the linear flattening.
  have hBp := BparamsLeaf_hasFDerivAt ha y₀
  have hcomp : HasFDerivAt (BchartLeaf ha)
      ((paramsEquivFlatCLE M).toContinuousLinearMap.comp
        (fderiv ℝ (fun z => BparamsLeaf ha z) y₀)) y₀ :=
    (hasFDerivAt_paramsEquivFlat M (BparamsLeaf ha y₀)).comp y₀ hBp
  -- `HasFDerivAt.unique` (NOT `.fderiv`, which trips the opaque-width `ContinuousAdd` synthesis)
  -- identifies `fderiv BchartLeaf` with the composite; its `toLinearMap` IS `Dtot` (defeq).
  have hself : HasFDerivAt (BchartLeaf ha) (fderiv ℝ (BchartLeaf ha) y₀) y₀ :=
    (Bchart_differentiableAt ha y₀).hasFDerivAt
  rw [hself.unique hcomp]
  rfl

end L2

end DLNFibre.DLN.RLCT
