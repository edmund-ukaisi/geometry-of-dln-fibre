import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyPrior
import DLNFibre.DLN.Aoyagi.RetainedPassiveLocalSource

/-!
# Original edge-family coordinates in Aoyagi p.13 fixed bases

This file bridges the original `Fin (d j)` tuple-coordinate convention to
Aoyagi's p.13 fixed endpoint bases, whose indices are
`Fin (finrank U₀) ⊕ κ' j`. The bridge is only finite reindexing of basis
labels. It does not identify original edge-family volume with a chart
pushforward measure, prove a Jacobian transport theorem, construct normal
crossings, or extract an RLCT.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

section OriginalEdgeFamilyP13Coordinates

set_option linter.unusedSectionVars false

universe v

variable {M : ℕ}
variable (W : Fin (M + 2) → Type v)
variable [∀ i, AddCommGroup (W i)]
variable [∀ i, TopologicalSpace (W i)]
variable [∀ i, IsTopologicalAddGroup (W i)]
variable [∀ i, T2Space (W i)]
variable [∀ i, Module ℝ (W i)]
variable [∀ i, ContinuousSMul ℝ (W i)]
variable (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)

/-- The p.13 fixed endpoint basis index at one reversed vertex. -/
abbrev paperEndpointFixedBaseCoordinateIndex
    [∀ j, FiniteDimensional ℝ (W j)]
    (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (j : Fin (M + 2)) :=
  Fin (Module.finrank ℝ U₀) ⊕
    throughSubspaceEndpointComplementIndex (reverseVertex W) (reverseEdge W B) U₀ j

/-- The `Fin` dimension matching the p.13 fixed endpoint basis index. -/
def paperEndpointFixedBaseDim
    [∀ j, FiniteDimensional ℝ (W j)]
    (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (j : Fin (M + 2)) : ℕ :=
  Fintype.card (paperEndpointFixedBaseCoordinateIndex W B U₀ j)

/-- Aoyagi's p.13 fixed endpoint basis reindexed by `Fin (card I_j)`, so it
can be used with the original tuple-coordinate convention. -/
def paperEndpointFixedBaseFinBasis
    [∀ j, FiniteDimensional ℝ (W j)]
    (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B)))
    (j : Fin (M + 2)) :
    Module.Basis (Fin (paperEndpointFixedBaseDim W B U₀ j)) ℝ (reverseVertex W j) :=
  (paperEndpointFixedBaseBasis W B U₀ hU₀ j).reindex
    (Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j))

/-- Original edge-family matrix coordinates in reindexed p.13 fixed bases
are the p.13 fixed-base edge matrices with row and column indices renamed by
the same finite equivalences. -/
theorem edgeFamilyMatrixTuple_p13Basis_reindex_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {d : Fin (M + 2) → ℕ}
    (e : ∀ j, paperEndpointFixedBaseCoordinateIndex W B U₀ j ≃ Fin (d j))
    (E : ∀ p : Fin (M + 1), reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :
    edgeFamilyMatrixTuple (V := reverseVertex W) (d := d)
        (fun j ↦ (paperEndpointFixedBaseBasis W B U₀ hU₀ j).reindex (e j)) E =
      fun p ↦
        Matrix.reindex (e p.succ) (e p.castSucc)
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun q : Fin (M + 1) ↦
              (E q : reverseVertex W q.castSucc →ₗ[ℝ] reverseVertex W q.succ)) p) := by
  funext p i j
  simp [edgeFamilyMatrixTuple, chainMapMatrixTuple,
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges, Matrix.reindex_apply,
    LinearMap.toMatrix_apply]

/-- On the retained-passive raw-order p.13 determinant chart, the generic
reindexed original edge-family matrix coordinates read as the raw-order
tuple's edge matrices, up to the same finite row and column renaming. -/
theorem edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {d : Fin (M + 2) → ℕ}
    (e : ∀ j, paperEndpointFixedBaseCoordinateIndex W B U₀ j ≃ Fin (d j))
    {y :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ}
    (hy : y ∈
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    edgeFamilyMatrixTuple (V := reverseVertex W) (d := d)
        (fun j ↦ (paperEndpointFixedBaseBasis W B U₀ hU₀ j).reindex (e j))
        (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
          (K := ℝ) W B U₀ hU₀ y) =
      fun p ↦
        Matrix.reindex (e p.succ) (e p.castSucc)
          (edgeFamilyOfRawOrderTuple (K := ℝ)
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) y p) := by
  rw [edgeFamilyMatrixTuple_p13Basis_reindex_eq
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) e]
  have hread :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13RawOrderSourceChart_eq
      (K := ℝ) (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) hy
  funext p
  rw [congrFun hread p]

/-- Canonical `Fin (card I_j)` specialization of the p.13 fixed-basis
coordinate readout. -/
theorem edgeFamilyMatrixTuple_p13FinBasis_eq_reindex_edgeMatrix
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    (E : ∀ p : Fin (M + 1), reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ) :
    edgeFamilyMatrixTuple (V := reverseVertex W)
        (d := paperEndpointFixedBaseDim W B U₀)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀) E =
      fun p ↦
        Matrix.reindex
          (Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ p.succ))
          (Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ p.castSucc))
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W B U₀ hU₀
            (fun q : Fin (M + 1) ↦
              (E q : reverseVertex W q.castSucc →ₗ[ℝ] reverseVertex W q.succ)) p) := by
  simpa [paperEndpointFixedBaseFinBasis] using
    edgeFamilyMatrixTuple_p13Basis_reindex_eq
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (d := paperEndpointFixedBaseDim W B U₀)
      (fun j ↦ Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j)) E

/-- Canonical `Fin (card I_j)` specialization of the retained-passive
raw-order p.13 source-chart readout in original edge-family coordinates. -/
theorem edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq
    [∀ j, FiniteDimensional ℝ (W j)]
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {y :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ}
    (hy : y ∈
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)) :
    edgeFamilyMatrixTuple (V := reverseVertex W)
        (d := paperEndpointFixedBaseDim W B U₀)
        (paperEndpointFixedBaseFinBasis W B U₀ hU₀)
        (paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
          (K := ℝ) W B U₀ hU₀ y) =
      fun p ↦
        Matrix.reindex
          (Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ p.succ))
          (Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ p.castSucc))
          (edgeFamilyOfRawOrderTuple (K := ℝ)
            (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W) (reverseEdge W B) U₀) y p) := by
  simpa [paperEndpointFixedBaseFinBasis] using
    edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq
      (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
      (d := paperEndpointFixedBaseDim W B U₀)
      (fun j ↦ Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j)) hy

end OriginalEdgeFamilyP13Coordinates

end Aoyagi
end DLN
end DLNFibre

end
