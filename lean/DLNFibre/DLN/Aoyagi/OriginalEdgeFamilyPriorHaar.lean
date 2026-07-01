import DLNFibre.DLN.Aoyagi.OriginalPriorHaar
import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPrior

/-!
# Haar properties of original DLN edge-family volume

This file records that fixed bases identify continuous edge families with the
original matrix tuple space by a continuous linear equivalence.  Consequently
the fixed-basis original edge-family volume is an additive Haar measure, and
any other additive Haar measure on the same full edge-family space differs by
Mathlib's positive Haar scalar factor.

This is full-space Haar normalization only. It does not identify the original
edge-family volume with a retained-passive or selected-entry chart-produced
source-image measure, does not compare restricted determinant-chart measures,
and does not prove a Jacobian transport theorem, normal crossings, pole order,
or RLCT extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core

variable {N : ℕ}
variable {V : Fin (N + 1) → Type*}
variable [∀ j, AddCommGroup (V j)]
variable [∀ j, TopologicalSpace (V j)]
variable [∀ j, IsTopologicalAddGroup (V j)]
variable [∀ j, T2Space (V j)]
variable [∀ j, Module ℝ (V j)]
variable [∀ j, ContinuousSMul ℝ (V j)]
variable [∀ j, FiniteDimensional ℝ (V j)]
variable {d : Fin (N + 1) → ℕ}

/-- Fixed-basis matrix readout as a linear equivalence from continuous edge
families to original matrix tuples. -/
def edgeFamilyMatrixTupleLinearEquiv
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) ≃ₗ[ℝ] Tuple (k := ℝ) d where
  toFun := edgeFamilyMatrixTuple (V := V) b
  invFun := tupleToEdgeFamily (V := V) b
  map_add' E F := by
    funext p r c
    simp [edgeFamilyMatrixTuple, chainMapMatrixTuple]
  map_smul' a E := by
    funext p r c
    simp [edgeFamilyMatrixTuple, chainMapMatrixTuple]
  left_inv := tupleToEdgeFamily_edgeFamilyMatrixTuple (V := V) b
  right_inv := edgeFamilyMatrixTuple_tupleToEdgeFamily (V := V) b

@[simp]
theorem edgeFamilyMatrixTupleLinearEquiv_apply
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (E : ∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :
    edgeFamilyMatrixTupleLinearEquiv (V := V) b E =
      edgeFamilyMatrixTuple (V := V) b E :=
  rfl

@[simp]
theorem edgeFamilyMatrixTupleLinearEquiv_symm_apply
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (A : Tuple (k := ℝ) d) :
    (edgeFamilyMatrixTupleLinearEquiv (V := V) b).symm A =
      tupleToEdgeFamily (V := V) b A :=
  rfl

/-- Fixed-basis matrix readout as a continuous linear equivalence. -/
def edgeFamilyMatrixTupleContinuousLinearEquiv
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) ≃L[ℝ] Tuple (k := ℝ) d where
  toLinearEquiv := edgeFamilyMatrixTupleLinearEquiv (V := V) b
  continuous_toFun := continuous_edgeFamilyMatrixTuple (V := V) b
  continuous_invFun := continuous_tupleToEdgeFamily (V := V) b

/-- Fixed-basis original edge-family volume is an additive Haar measure on the
full edge-family space. -/
instance isAddHaarMeasure_originalEdgeFamilyVolume
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j)) :
    Measure.IsAddHaarMeasure (originalEdgeFamilyVolume (V := V) b) := by
  haveI : Measure.IsAddHaarMeasure (originalTupleVolume d) :=
    isAddHaarMeasure_originalTupleVolume d
  let e : Tuple (k := ℝ) d ≃L[ℝ]
      (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ) :=
    (edgeFamilyMatrixTupleContinuousLinearEquiv (V := V) b).symm
  have hmap : Measure.IsAddHaarMeasure ((originalTupleVolume d).map e) :=
    e.isAddHaarMeasure_map (originalTupleVolume d)
  simpa [originalEdgeFamilyVolume, edgeFamilyMatrixTupleContinuousLinearEquiv,
    edgeFamilyMatrixTupleLinearEquiv, e] using hmap

/-- Any additive Haar measure on the full edge-family space differs from the
fixed-basis original edge-family volume by the canonical Haar scalar factor. -/
theorem originalEdgeFamilyVolume_eq_addHaarScalarFactor_smul
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [LocallyCompactSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [SecondCountableTopology (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (ν : Measure (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ))
    [ν.IsAddHaarMeasure] :
    originalEdgeFamilyVolume (V := V) b =
      (originalEdgeFamilyVolume (V := V) b).addHaarScalarFactor ν • ν :=
  MeasureTheory.Measure.isAddLeftInvariant_eq_smul
    (originalEdgeFamilyVolume (V := V) b) ν

/-- The Haar scalar comparing fixed-basis original edge-family volume to
another additive Haar measure on the same full edge-family space is positive. -/
theorem originalEdgeFamilyVolume_addHaarScalarFactor_pos
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (ν : Measure (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ))
    [ν.IsAddHaarMeasure] :
    0 < (originalEdgeFamilyVolume (V := V) b).addHaarScalarFactor ν :=
  MeasureTheory.Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
    (originalEdgeFamilyVolume (V := V) b) ν

/-- The same Haar scalar is finite when viewed as an `ℝ≥0∞` scalar. -/
theorem originalEdgeFamilyVolume_addHaarScalarFactor_coe_lt_top
    [MeasurableSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    [BorelSpace (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ)]
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (V j))
    (ν : Measure (∀ p : Fin N, V p.castSucc →L[ℝ] V p.succ))
    [ν.IsAddHaarMeasure] :
    ((originalEdgeFamilyVolume (V := V) b).addHaarScalarFactor ν : ℝ≥0∞) < ∞ :=
  ENNReal.coe_lt_top

end Aoyagi
end DLN
end DLNFibre

end
