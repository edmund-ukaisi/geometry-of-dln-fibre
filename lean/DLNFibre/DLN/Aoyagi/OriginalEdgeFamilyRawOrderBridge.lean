import DLNFibre.DLN.Aoyagi.OriginalEdgeFamilyP13Coordinates

/-!
# Raw-order retained-passive coordinates and original edge-family tuples

This file packages the finite coordinate bridge from retained-passive raw-order
tuples to original matrix tuples.  The map first reassembles raw blocks into
edge matrices and then reindexes each edge matrix into the chosen original
`Fin (d j)` coordinate labels.

The bridge is a global linear and continuous-linear equivalence on the full
ambient raw tuple space.  The public p.13 raw-order source chart agrees with
this readout only on the raw-order source-recursive determinant chart, where
the chart's readback inverse is valid.

This is not a measure-transport theorem.  It does not identify restricted
determinant-chart or source-chart measures as Haar measures, does not compare
chart pushforwards with original edge-family volume, and does not prove a
Jacobian theorem, normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open Matrix

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core
open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

universe v

section RawOrderBridge

variable {M : ℕ}
variable {ρ : Type*}
variable {κ' : Fin (M + 2) → Type*}
variable {d : Fin (M + 2) → ℕ}

/-- Edgewise finite reindexing from retained-passive raw edge matrices to
original tuple matrix coordinates. -/
def edgeFamilyTupleReindexLinearEquiv
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    EdgeFamilyTuple ρ κ' ℝ ≃ₗ[ℝ] Tuple (k := ℝ) d where
  toFun E := fun p ↦
    Matrix.reindex (e p.succ) (e p.castSucc) (E p)
  invFun A := fun p ↦
    Matrix.reindex (e p.succ).symm (e p.castSucc).symm (A p)
  map_add' E F := by
    funext p i j
    rfl
  map_smul' a E := by
    funext p i j
    rfl
  left_inv E := by
    funext p i j
    simp [Matrix.reindex_apply]
  right_inv A := by
    funext p i j
    simp [Matrix.reindex_apply]

@[simp]
theorem edgeFamilyTupleReindexLinearEquiv_apply
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (E : EdgeFamilyTuple ρ κ' ℝ) :
    edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e E =
      fun p ↦ Matrix.reindex (e p.succ) (e p.castSucc) (E p) :=
  rfl

@[simp]
theorem edgeFamilyTupleReindexLinearEquiv_symm_apply
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (A : Tuple (k := ℝ) d) :
    (edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e).symm A =
      fun p ↦ Matrix.reindex (e p.succ).symm (e p.castSucc).symm (A p) :=
  rfl

/-- Reassemble raw-order blocks and read them as an original matrix tuple. -/
def rawOrderMatrixTuple
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (y : TopologyTuple ρ κ' ℝ) :
    Tuple (k := ℝ) d :=
  edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e
    (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y)

@[simp]
theorem rawOrderMatrixTuple_apply
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (y : TopologyTuple ρ κ' ℝ) (p : Fin (M + 1)) :
    rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y p =
      Matrix.reindex (e p.succ) (e p.castSucc)
        (edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ') y p) :=
  rfl

/-- The raw-order-to-original matrix tuple readout is a linear equivalence on
the full raw tuple space. -/
def rawOrderMatrixTupleLinearEquiv
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    TopologyTuple ρ κ' ℝ ≃ₗ[ℝ] Tuple (k := ℝ) d :=
  (edgeFamilyRawOrderLinearEquiv (K := ℝ) (ρ := ρ) (κ' := κ')).symm.trans
    (edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e)

@[simp]
theorem rawOrderMatrixTupleLinearEquiv_apply
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j))
    (y : TopologyTuple ρ κ' ℝ) :
    rawOrderMatrixTupleLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e y =
      rawOrderMatrixTuple (ρ := ρ) (κ' := κ') (d := d) e y :=
  rfl

/-- Edgewise finite reindexing of raw edge families is continuous. -/
theorem continuous_edgeFamilyTupleReindex
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    Continuous
      (edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e :
        EdgeFamilyTuple ρ κ' ℝ → Tuple (k := ℝ) d) := by
  refine continuous_pi ?_
  intro p
  simpa [edgeFamilyTupleReindexLinearEquiv, Matrix.reindex] using
    (continuous_apply p).matrix_submatrix (e p.succ).symm (e p.castSucc).symm

/-- The inverse finite reindexing of raw edge families is continuous. -/
theorem continuous_edgeFamilyTupleReindex_symm
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    Continuous
      ((edgeFamilyTupleReindexLinearEquiv
          (ρ := ρ) (κ' := κ') (d := d) e).symm :
        Tuple (k := ℝ) d → EdgeFamilyTuple ρ κ' ℝ) := by
  refine continuous_pi ?_
  intro p
  simpa [edgeFamilyTupleReindexLinearEquiv, Matrix.reindex] using
    (continuous_apply p).matrix_submatrix (e p.succ) (e p.castSucc)

/-- Edgewise finite reindexing of raw edge families as a continuous linear
equivalence. -/
def edgeFamilyTupleReindexContinuousLinearEquiv
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    EdgeFamilyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d where
  toLinearEquiv :=
    edgeFamilyTupleReindexLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e
  continuous_toFun :=
    continuous_edgeFamilyTupleReindex (ρ := ρ) (κ' := κ') (d := d) e
  continuous_invFun :=
    continuous_edgeFamilyTupleReindex_symm (ρ := ρ) (κ' := κ') (d := d) e

/-- The raw-order-to-original matrix tuple readout as a continuous linear
equivalence on the full raw tuple space. -/
def rawOrderMatrixTupleContinuousLinearEquiv
    (e : ∀ j, ρ ⊕ κ' j ≃ Fin (d j)) :
    TopologyTuple ρ κ' ℝ ≃L[ℝ] Tuple (k := ℝ) d where
  toLinearEquiv :=
    rawOrderMatrixTupleLinearEquiv (ρ := ρ) (κ' := κ') (d := d) e
  continuous_toFun :=
    (continuous_edgeFamilyTupleReindex (ρ := ρ) (κ' := κ') (d := d) e).comp
      (continuous_edgeFamilyOfRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ'))
  continuous_invFun :=
    (continuous_edgeFamilyRawOrderTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp
      (continuous_edgeFamilyTupleReindex_symm
        (ρ := ρ) (κ' := κ') (d := d) e)

end RawOrderBridge

section P13RawOrderBridge

set_option linter.unusedSectionVars false

variable {M : ℕ}
variable (W : Fin (M + 2) → Type v)
variable [∀ i, AddCommGroup (W i)]
variable [∀ i, TopologicalSpace (W i)]
variable [∀ i, IsTopologicalAddGroup (W i)]
variable [∀ i, T2Space (W i)]
variable [∀ i, Module ℝ (W i)]
variable [∀ i, ContinuousSMul ℝ (W i)]
variable [∀ i, FiniteDimensional ℝ (W i)]
variable (B : ∀ i : Fin (M + 1), W i.succ →ₗ[ℝ] W i.castSucc)

/-- The p.13 raw-order retained-passive coordinate readout as a linear
equivalence to original matrix tuples in the canonical `Fin (card I_j)`
endpoint basis labels. -/
def paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv
    (U₀ : Submodule ℝ (reverseVertex W 0)) :
    TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ ≃ₗ[ℝ]
      Tuple (k := ℝ) (paperEndpointFixedBaseDim W B U₀) :=
  rawOrderMatrixTupleLinearEquiv
    (ρ := Fin (Module.finrank ℝ U₀))
    (κ' := throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀)
    (d := paperEndpointFixedBaseDim W B U₀)
    (fun j ↦ Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j))

@[simp]
theorem paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv_apply
    (U₀ : Submodule ℝ (reverseVertex W 0))
    (y :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ) :
    paperEndpointFixedBaseRawOrderMatrixTupleLinearEquiv W B U₀ y =
      rawOrderMatrixTuple
        (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
        (d := paperEndpointFixedBaseDim W B U₀)
        (fun j ↦
          Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j)) y :=
  rfl

/-- The p.13 raw-order retained-passive coordinate readout as a continuous
linear equivalence to original matrix tuples. -/
def paperEndpointFixedBaseRawOrderMatrixTupleContinuousLinearEquiv
    (U₀ : Submodule ℝ (reverseVertex W 0)) :
    TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀) ℝ ≃L[ℝ]
      Tuple (k := ℝ) (paperEndpointFixedBaseDim W B U₀) :=
  rawOrderMatrixTupleContinuousLinearEquiv
    (ρ := Fin (Module.finrank ℝ U₀))
    (κ' := throughSubspaceEndpointComplementIndex
      (reverseVertex W) (reverseEdge W B) U₀)
    (d := paperEndpointFixedBaseDim W B U₀)
    (fun j ↦ Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j))

/-- The generic p.13 fixed-basis source-chart readout agrees with the
raw-order matrix tuple readout on the raw-order source-recursive determinant
chart. -/
theorem edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq_rawOrderMatrixTuple
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
      rawOrderMatrixTuple
        (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
        (d := d) e y := by
  rw [edgeFamilyMatrixTuple_p13Basis_reindex_rawOrderSourceChart_eq
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) e hy]
  rfl

/-- In the canonical `Fin (card I_j)` p.13 endpoint basis labels, the public
raw-order p.13 source chart has original edge-family matrix coordinates equal
to the raw-order matrix tuple readout on the raw-order source-recursive
determinant chart. -/
theorem edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq_rawOrderMatrixTuple
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
      rawOrderMatrixTuple
        (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀)
        (d := paperEndpointFixedBaseDim W B U₀)
        (fun j ↦
          Fintype.equivFin (paperEndpointFixedBaseCoordinateIndex W B U₀ j)) y := by
  rw [edgeFamilyMatrixTuple_p13FinBasis_rawOrderSourceChart_eq
    (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) hy]
  rfl

end P13RawOrderBridge

end Aoyagi
end DLN
end DLNFibre

end
