import DLNFibre.DLN.Aoyagi.OriginalPrior
import DLNFibre.DLN.Aoyagi.ChartTopology
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar properties of original DLN coordinate volume

This file records that the original flattened and tuple-side coordinate
volumes are additive Haar measures.  It is pure coordinate/Haar infrastructure:
it does not compare the original volume with any Aoyagi source chart, prove a
Jacobian transport theorem, construct normal crossings, or extract an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core

variable {N : ℕ}

/-- The canonical matrix-entry flattening as a linear equivalence. -/
noncomputable def canonicalCoordLinearEquiv
    (d : Fin (N + 1) → ℕ) :
    Tuple (k := ℝ) d ≃ₗ[ℝ] (RepCoord d → ℝ) where
  toFun := canonicalCoord d
  invFun := (canonicalCoord d).symm
  map_add' A B := by
    ext x
    rfl
  map_smul' a A := by
    ext x
    rfl
  left_inv := (canonicalCoord d).left_inv
  right_inv := (canonicalCoord d).right_inv

@[simp]
theorem canonicalCoordLinearEquiv_apply
    (d : Fin (N + 1) → ℕ) (A : Tuple (k := ℝ) d) :
    canonicalCoordLinearEquiv d A = canonicalCoord d A :=
  rfl

@[simp]
theorem canonicalCoordLinearEquiv_symm_apply
    (d : Fin (N + 1) → ℕ) (x : RepCoord d → ℝ) :
    (canonicalCoordLinearEquiv d).symm x = (canonicalCoord d).symm x :=
  rfl

/-- Flattened original coordinate volume is product Lebesgue measure, hence
an additive Haar measure. -/
instance isAddHaarMeasure_originalCoordinateVolume
    (d : Fin (N + 1) → ℕ) :
    Measure.IsAddHaarMeasure (originalCoordinateVolume d) := by
  simpa [originalCoordinateVolume] using
    (MeasureTheory.isAddHaarMeasure_volume_pi (RepCoord d))

/-- Tuple-side original coordinate volume is an additive Haar measure. -/
instance isAddHaarMeasure_originalTupleVolume
    (d : Fin (N + 1) → ℕ) :
    Measure.IsAddHaarMeasure (originalTupleVolume d) := by
  haveI : Measure.IsAddHaarMeasure (originalCoordinateVolume d) :=
    isAddHaarMeasure_originalCoordinateVolume d
  let e : (RepCoord d → ℝ) ≃L[ℝ] Tuple (k := ℝ) d :=
    (canonicalCoordLinearEquiv d).symm.toContinuousLinearEquiv
  have hmap : Measure.IsAddHaarMeasure ((originalCoordinateVolume d).map e) :=
    e.isAddHaarMeasure_map (originalCoordinateVolume d)
  simpa [originalTupleVolume, canonicalCoordLinearEquiv, e] using hmap

/-- Any additive Haar measure on tuple space differs from the original tuple
volume by the canonical Haar scalar factor. -/
theorem originalTupleVolume_eq_addHaarScalarFactor_smul
    (d : Fin (N + 1) → ℕ)
    (ν : Measure (Tuple (k := ℝ) d)) [ν.IsAddHaarMeasure] :
    originalTupleVolume d =
      (originalTupleVolume d).addHaarScalarFactor ν • ν :=
  by
    haveI :
        ∀ i : Fin N,
          LocallyCompactSpace
            (Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ) := by
      intro i
      change LocallyCompactSpace
        (Fin (d i.succ) → Fin (d i.castSucc) → ℝ)
      infer_instance
    haveI : LocallyCompactSpace (Tuple (k := ℝ) d) := by
      change LocallyCompactSpace
        (∀ i : Fin N, Matrix (Fin (d i.succ)) (Fin (d i.castSucc)) ℝ)
      infer_instance
    exact
      MeasureTheory.Measure.isAddLeftInvariant_eq_smul
        (originalTupleVolume d) ν

/-- The Haar scalar comparing original tuple volume to another additive Haar
measure is positive. -/
theorem originalTupleVolume_addHaarScalarFactor_pos
    (d : Fin (N + 1) → ℕ)
    (ν : Measure (Tuple (k := ℝ) d)) [ν.IsAddHaarMeasure] :
    0 < (originalTupleVolume d).addHaarScalarFactor ν :=
  MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (originalTupleVolume d) ν

end Aoyagi
end DLN
end DLNFibre

end
