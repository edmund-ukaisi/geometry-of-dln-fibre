import DLNFibre.DLN.RLCT.Engine.EngineObligations
import DLNFibre.DLN.RLCT.Validate.RegionGlueModelRead
import DLNFibre.DLN.RLCT.Foundations.ParamsFlatLinear
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `DLNFibre.DLN.RLCT.Engine.RegionGluePerLeaf` — the per-leaf area-formula read

The engine-facing half of `region_glue`'s per-leaf step: given a leaf `l`'s `ChartBridge` data
(measurable bounded `srcBox`, injective/disjoint `divCoord`/`resCoord`, a.e.-injectivity off a null
set, `LeafPullback`, `LeafJacobian`) and the ratio hypotheses (`c' > 0` below half every terminal
exponent), the box integral over the chart IMAGE is finite:

    ∫⁻ A in l.chartMap '' l.srcBox, ofReal (frobSq (prod M A) ^ (-c')) < ⊤.

Route (elder-ratified fork-8 revision): Mathlib's AREA FORMULA
(`lintegral_image_eq_lintegral_abs_det_fderiv_mul`) on `srcBox ∖ N̄` (null exceptional fibre
discarded), the `LeafJacobian` upper determinant bound + the `LeafPullback` squeeze reducing the
pulled-back integrand to the monomialised model, then the flat-coordinate `model_read_lt_top`
(`RegionGlueModelRead`) after the measure-preserving transport to `Fin (flatDim M) → ℝ`.

The area formula runs on `Params M` directly, consuming `LeafJacobian`'s `Params`-level derivatives;
this needs `volume` on `Params M` to be an additive Haar measure, supplied here (`Params M` is a
finite-dim normed ℝ-space linearly iso to the flat cube via the banked `paramsEquivFlatCLE`).
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace DLNFibre.DLN.RLCT

variable {L : ℕ}

/-- `BorelSpace (Params M)` (the pi Borel σ-algebra is the norm-topology Borel one); banked as
`instBorelSpaceParams` in `RouteMSJResolution`, re-exposed here to avoid that heavy import. -/
instance instBorelSpaceParamsGlue (M : Fin (L + 1) → ℕ) : BorelSpace (Params M) :=
  inferInstanceAs (BorelSpace (∀ s : Fin L, Fin (M s.castSucc) → Fin (M s.succ) → ℝ))

/-- **`volume` on `Params M` is an additive Haar measure.** `Params M` is a finite-dim normed
ℝ-space; the banked ℝ-linear iso `paramsEquivFlatCLE` to the flat cube `Fin (flatDim M) → ℝ` (whose
Lebesgue `volume` is Haar) pushes Haar-ness back through `ContinuousLinearEquiv.isAddHaarMeasure_map`,
the measure agreeing by the measure-preserving `paramsEquivFlat`. -/
instance instIsAddHaarMeasureParams (M : Fin (L + 1) → ℕ) :
    (volume : Measure (Params M)).IsAddHaarMeasure := by
  have hsymm : ⇑(paramsEquivFlatCLE M).symm = ⇑(paramsEquivFlat M).symm := by
    funext x
    apply (paramsEquivFlat M).injective
    rw [(paramsEquivFlat M).apply_symm_apply, ← paramsEquivFlatCLE_coe,
      (paramsEquivFlatCLE M).apply_symm_apply]
  have hmap : (volume : Measure (Params M))
      = (volume : Measure (Fin (flatDim M) → ℝ)).map (paramsEquivFlatCLE M).symm := by
    rw [hsymm]
    exact ((measurePreserving_paramsEquivFlat M).symm).map_eq.symm
  rw [hmap]
  infer_instance

end DLNFibre.DLN.RLCT
