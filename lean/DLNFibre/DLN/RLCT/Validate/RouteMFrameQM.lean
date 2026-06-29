import DLNFibre.DLN.RLCT.Foundations.ParamsReshapeMP
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import DLNFibre.DLN.RLCT.Validate.RouteMExtraction

/-!
# `RouteMFrameQM` — b-FrameM-1a: the outer reshape `Q_M` and `|det Q_M| = 1`

The first sub-piece of the (A') aligned-basis `Frame_M` build (`item3-frameM-buildspec.md`): the outer
coordinate-reshape `Q_M = paramsEquivFlat ∘ pack_M`, where `pack_M = (flatEquivOf M e).symm` is the
RESHAPE into the matrix slots specified by ANY chosen index equiv `e : Fin N ≃ FlatIdx M`. The clean
factorization `phiFlatLiveR1 = Q_M ∘ T_M` (with `T_M := pack_M.symm ∘ chartParamsGen` the aligned-basis
frame) is then DEFINITIONAL (`pack_M.symm ∘ pack_M = id`), sidestepping the Codex-refuted
`composeFold` map-equality entirely. The chart Jacobian splits `|det Dφ| = |det Q_M| · |det DT_M| =
1 · |det DT_M|` — the aligned frame's det, where the role-grading (the `frameB` generalization) gives
square+triangular blocks (#eval-confirmed at (3,3,3,3): the aligned-basis SCC is 13 square blocks whose
product is the global det).

`Q_M` is a coordinate PERMUTATION (a measure-preserving continuous linear equiv), so `|det Q_M| = 1`
(the banked `continuousLinearMap_abs_det_eq_one_of_measurePreserving`). This is the (1,2,1)/(3,3,3,3)
`Q121`/`Q3333` outer-reshape, generalized to arbitrary `M` and arbitrary slot-bijection `e`.

* `flatEquivOfLinear` — the ℝ-LINEAR mirror of `flatEquivOf` (the measurable reshape), via
  `LinearEquiv.piCurry` + `funCongrLeft` (same underlying function, `flatEquivOfLinear_coe`).
* `QMcle` — `Q_M` as a `ContinuousLinearEquiv` `(Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)`
  (`paramsEquivFlatLinear ∘ pack_M`), with `QMcle_coe : ⇑(QMcle M e) = paramsEquivFlat ∘ pack_M`.
* `QMcle_abs_det` — **`|det Q_M| = 1`**, via measure-preservation (`flatEquivOf` MP × `paramsEquivFlat`
  MP) + the banked finite-dim MP-det lemma.

Axiom-clean `[propext, Classical.choice, Quot.sound]` (the banked reshape-MP + linear flattening; no S2).
-/

open scoped BigOperators
open MeasureTheory

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **The ℝ-linear reshape from a chosen `Fin N ≃ FlatIdx H`.** The `LinearEquiv` mirror of
`flatEquivOf` (`ParamsReshapeMP`): two `LinearEquiv.piCurry` currying steps (`.symm`) then the reindex
`LinearEquiv.funCongrLeft ℝ ℝ e` (the computable `e` in place of the noncomputable `Fintype.equivFin`).
Same underlying function as `flatEquivOf H e` (`flatEquivOfLinear_coe`), now carrying ℝ-linearity. -/
noncomputable def flatEquivOfLinear {N : ℕ} (H : Fin (L + 1) → ℕ) (e : Fin N ≃ FlatIdx H) :
    Params H ≃ₗ[ℝ] (Fin N → ℝ) :=
  (LinearEquiv.piCurry ℝ
      (fun (s : Fin L) (_ : Fin (H s.castSucc)) => Fin (H s.succ) → ℝ)).symm.trans
    ((LinearEquiv.piCurry ℝ (fun (q : FlatRowIdx H) (_ : Fin (H q.1.succ)) => ℝ)).symm.trans
      (LinearEquiv.funCongrLeft ℝ ℝ e))

/-- **Agreement: `flatEquivOfLinear` has the same underlying function as `flatEquivOf`.** Both are the
two `piCurry.symm` collapses + the reindex by `e` (`funCongrLeft e` matches `arrowCongr' e.symm`);
definitionally equal coe. -/
theorem flatEquivOfLinear_coe {N : ℕ} (H : Fin (L + 1) → ℕ) (e : Fin N ≃ FlatIdx H) :
    ⇑(flatEquivOfLinear H e) = ⇑(flatEquivOf H e) := by funext P; rfl

/-- **The outer reshape `Q_M = paramsEquivFlat ∘ pack_M` as a continuous linear equivalence**
`(Fin N → ℝ) ≃L[ℝ] (Fin N → ℝ)` (`pack_M = (flatEquivOfLinear M e).symm`). Specialized to `H = M`, so
`flatDim M = routeMAmbient M = N` and the endpoints align. The outer-reshape factor of the chart c-o-v
(the `Q121`/`Q3333` generalization). -/
noncomputable def QMcle (M : Fin (L + 1) → ℕ) (e : Fin (routeMAmbient M) ≃ FlatIdx M) :
    (Fin (routeMAmbient M) → ℝ) ≃L[ℝ] (Fin (routeMAmbient M) → ℝ) :=
  ((flatEquivOfLinear M e).symm.trans (paramsEquivFlatLinear M)).toContinuousLinearEquiv

/-- **`Q_M` is `paramsEquivFlat ∘ pack_M`** (the underlying function), tying the linear `QMcle` to the
measurable reshape `flatEquivOf` used for the measure-preservation. -/
theorem QMcle_coe (M : Fin (L + 1) → ℕ) (e : Fin (routeMAmbient M) ≃ FlatIdx M) :
    ⇑(QMcle M e) = fun w => paramsEquivFlat M ((flatEquivOf M e).symm w) := by
  funext w
  show paramsEquivFlatLinear M ((flatEquivOfLinear M e).symm w) = _
  rw [paramsEquivFlatLinear_coe]
  congr 1

/-- **b-FrameM-1a: `|det Q_M| = 1`.** The outer reshape is a measure-preserving coordinate permutation
(`flatEquivOf` MP composed with `paramsEquivFlat` MP), so its Jacobian determinant has absolute value
`1` (the banked `continuousLinearMap_abs_det_eq_one_of_measurePreserving`). The trivial outer factor of
`|det Dφ| = |det Q_M| · |det DT_M|`. -/
theorem QMcle_abs_det (M : Fin (L + 1) → ℕ) (e : Fin (routeMAmbient M) ≃ FlatIdx M) :
    |LinearMap.det ((QMcle M e).toContinuousLinearMap :
      (Fin (routeMAmbient M) → ℝ) →ₗ[ℝ] (Fin (routeMAmbient M) → ℝ))| = 1 := by
  apply continuousLinearMap_abs_det_eq_one_of_measurePreserving
  rw [show ⇑(QMcle M e).toContinuousLinearMap = ⇑(QMcle M e) from rfl, QMcle_coe]
  have hpack : MeasurePreserving (fun w => (flatEquivOf M e).symm w)
      (volume : Measure (Fin (routeMAmbient M) → ℝ)) (volume : Measure (Params M)) :=
    (measurePreserving_flatEquivOf M e).symm _
  exact (measurePreserving_paramsEquivFlat M).comp hpack

end DLNFibre.DLN.RLCT
