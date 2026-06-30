import DLNFibre.DLN.RLCT.Validate.RouteMFrameDiff
import DLNFibre.DLN.RLCT.Validate.RouteMFlatLive
import DLNFibre.DLN.RLCT.Validate.RouteMGenChartId
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# `RouteMChartDiff` — b-FrameM-2 assembly (1): `DifferentiableAt phiFlatLiveR1` ⟸ per-layer `Agen`

The first chain-telescope assembly step of b-FrameM-2 (`item3-frameM-buildspec.md`): REDUCE the chart
differentiability `DifferentiableAt phiFlatLiveR1` to the per-layer differentiability of `Agen` (the
chain's layer matrices), via the three cast-light reductions:

* **A** (linear CLE comp): `phiFlatLiveR1 = paramsEquivFlat ∘ chartParamsGen`, and `paramsEquivFlat`
  is the LINEAR reshape (`paramsEquivFlatCLE`, banked), so `DifferentiableAt phiFlatLiveR1 ⟸
  DifferentiableAt chartParamsGen` (`HasFDerivAt.comp` of the CLE).
* **B** (Params Pi): `Params M = ∀ s, Fin _ → Fin _ → ℝ` is Pi-normed, so `DifferentiableAt
  chartParamsGen ⟸ ∀ s, DifferentiableAt (component s)` (`differentiableAt_pi`).
* **C** (reindex): `component s = reindex (finCongr …) (finCongr …) (Agen … s.val)`, and a
  `finCongr`-reindex permutes indices, so `DifferentiableAt (component s) ⟸ DifferentiableAt
  (Agen … s.val)` (each entry is an entry of `Agen` at a cast index — `RouteMFrameDiff.diffAt_entry`).

The composite (`phiFlatLiveR1_differentiableAt_of_Agen`) leaves EXACTLY the per-layer residual: `∀ s,
DifferentiableAt (fun x => (Agen … (genBlkFlatLiveR1 … x) … s.val))` — the next sub-piece (threading
`RouteMFrameDiff`'s matrix-op atoms through `chainA`/`chainQ`/`Cgen`/the decoder reads). All three
reductions are cast-light (no `finSplit` index decomposition — that lives in the residual).

Axiom-clean `[propext, Classical.choice, Quot.sound]` (Mathlib calculus + the banked linear reshape).
-/

open scoped BigOperators
open Matrix

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- **Reduction C (reindex preserves differentiability).** A `finCongr`-reindex of a differentiable
Pi-matrix-map is differentiable: each output entry `(i,j)` is the input entry at the cast index
`((finCongr h₁).symm i, (finCongr h₂).symm j)`, differentiable by `diffAt_entry`. The `chartParamsGen`
component's ambient→`M` width reindex. -/
theorem diffAt_reindex_finCongr {N a b a' b' : ℕ} (hw1 : a = a') (hw2 : b = b')
    (g : (Fin N → ℝ) → (Fin a → Fin b → ℝ)) (u : Fin N → ℝ) (hg : DifferentiableAt ℝ g u) :
    DifferentiableAt ℝ (fun x => Matrix.reindex (finCongr hw1) (finCongr hw2) (g x)) u := by
  apply differentiableAt_pi.mpr; intro i
  apply differentiableAt_pi.mpr; intro j
  have heq : (fun x => Matrix.reindex (finCongr hw1) (finCongr hw2) (g x) i j)
      = fun x => g x ((finCongr hw1).symm i) ((finCongr hw2).symm j) := by
    funext x; rw [Matrix.reindex_apply, Matrix.submatrix_apply]
  rw [heq]
  exact diffAt_entry g u hg _ _

/-- **b-FrameM-2 assembly (1): `DifferentiableAt phiFlatLiveR1` from per-layer `Agen`.** If every chain
layer `Agen … s.val` (as a function of `x`, the live decoder threaded through) is differentiable at
`x₀`, then the full chart `phiFlatLiveR1` is differentiable at `x₀`. Composes reductions A (linear CLE),
B (Params Pi), C (reindex). The hypothesis is the precise residual the matrix-op atoms discharge. -/
theorem phiFlatLiveR1_differentiableAt_of_Agen (M t : Fin (L + 1) → ℕ) (ha : StructAdm M t)
    (hN : 0 < routeMAmbient M) (p : ℕ)
    (hp1 : Text M t (p + 1) ≤ Text M t p) (hp2 : Text M t (p + 1) ≤ Wext M p)
    (rfin : (Fin (routeMAmbient M) → ℝ) → Matrix (Fin (Text M t L)) (Fin (Wext M L)) ℝ)
    (x0 : Fin (routeMAmbient M) → ℝ)
    (hAgen : ∀ s : Fin L, DifferentiableAt ℝ
      (fun x => Agen (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha) s.val) x0) :
    DifferentiableAt ℝ (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin) x0 := by
  -- A: reduce through the linear reshape `paramsEquivFlat`.
  have hcle : (phiFlatLiveR1 M t ha hN p hp1 hp2 rfin)
      = fun x => paramsEquivFlat M (chartParamsGen (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)) := by
    funext x; rfl
  rw [hcle]
  -- B+C: `chartParamsGen` differentiable from per-layer `Agen` (Params Pi + reindex).
  have hchart : DifferentiableAt ℝ
      (fun x => chartParamsGen (x (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x) x) (hleStruct M t ha)) x0 := by
    apply differentiableAt_pi.mpr
    intro s
    -- component s = reindex (finCongr …) (finCongr …) (Agen … s.val) (the chartParamsGen def)
    exact diffAt_reindex_finCongr _ _ _ x0 (hAgen s)
  -- the linear reshape is differentiable (its own constant fderiv) — compose.
  have hlin : DifferentiableAt ℝ (fun P => paramsEquivFlat M P)
      (chartParamsGen (x0 (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x0) x0) (hleStruct M t ha)) := by
    have hd := (paramsEquivFlatCLE M).differentiableAt
      (x := chartParamsGen (x0 (structPivot M hN)) M t
        (genBlkFlatLiveR1 M t ha p hp1 hp2 (rfin x0) x0) (hleStruct M t ha))
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards with P; rw [paramsEquivFlatCLE_coe]
  exact hlin.comp x0 hchart

end DLNFibre.DLN.RLCT
