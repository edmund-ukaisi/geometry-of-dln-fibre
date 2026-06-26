import DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure
import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates

/-!
# Product-step inverse density along Aoyagi's p. 13 regular coordinates

This file connects the chart-side inverse Jacobian density for one p. 13
product-reduction step to the explicit multi-edge regular-coordinate family
from `RegularSuspensionCoordinates`.

The result is only a local chart-tuple and local density-unit handoff.  It does
not prove source coverage, original DLN prior transport, normal crossings,
pole order, or RLCT extraction.
-/

noncomputable section

open scoped Matrix.Norms.Operator Topology

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.unusedSectionVars false in
/-- The raw-shaped target tuple for the left-endpoint p. 13 product step
inside the multi-edge regular-coordinate construction.

The tuple is ordered as
`(Ctop, Dtail, F3, A1, F2, A3, C0)`, using the raw tuple shape expected by
`productReductionStepChartCoordinatesOfRawOrderTopologyTuple`.  For the
left-endpoint product-coordinate matrix one has `A1 = Ctop` and `A3 = 0`;
`Dtail` is the residual product of the already-treated tail, while `C0` is the
left residual block. -/
def paperEndpointFixedBaseP13RawOrderTuple
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ) :
    α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)) →
      ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) :=
  fun xu ↦ by
    classical
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ :=
      fun j ↦ throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ j
    let Coord := AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
    let Ebase : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeBase xu.1 p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
    let F2 : Matrix ρ (κ 0) ℝ :=
      AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ xu.2 c)
    let F3 : Matrix (κ (Fin.last (M + 2))) ρ ℝ :=
      AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ xu.2 c)
    let Ctop : Matrix ρ ρ ℝ :=
      AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ xu.2 c)
    let p0 : Fin (M + 2) := 0
    let j : Fin (M + 3) := Fin.last (M + 2)
    let Dtail : Matrix (κ j) (κ p0.succ) ℝ :=
      ChartLocalSuffixState.residualProduct Ebase j p0.succ p0.succ.le_last
    let C0 : Matrix (κ p0.succ) (κ p0.castSucc) ℝ :=
      ChartLocalSuffixState.residualBlock Ebase j p0 p0.succ.le_last
    exact
      (Ctop,
        (Dtail,
          (F3,
            (Ctop,
              (F2,
                ((0 : Matrix (κ p0.succ) ρ ℝ), C0))))))

set_option linter.unusedSectionVars false in
/-- The p. 13 raw-shaped target tuple lies in the target determinant chart
whenever its regular `Ctop` block has unit determinant.

The determinant chart asks for the first tuple block and the passive `A1`
block to be determinant units.  In the left-endpoint p. 13 tuple these are the
same `Ctop` matrix. -/
theorem paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (xu : α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix
          (fun c : AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)).det) :
    paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu ∈
      productReductionStepRawDetChartSet
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) := by
  classical
  change IsUnit
      (paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu).1.det ∧
    IsUnit
      (paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu).2.2.2.1.det
  constructor
  · simpa [paperEndpointFixedBaseP13RawOrderTuple]
      using hCtop
  · simpa [paperEndpointFixedBaseP13RawOrderTuple]
      using hCtop

set_option linter.unusedSectionVars false in
/-- Centered regular-coordinate version of determinant-chart membership for
the p. 13 raw-shaped target tuple. -/
theorem paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (x₀ : α) :
    paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase
        (x₀,
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ 0)))) ∈
      productReductionStepRawDetChartSet
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) := by
  classical
  exact
    paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase)
      (xu := (x₀,
        (0 : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)))))
      (AoyagiRegularBlockCoordinateIndex.isUnit_det_ctopMatrix_euclidean_zero
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))

set_option linter.unusedSectionVars false in
/-- The p. 13 raw-shaped target tuple is continuous at a self-base point. -/
theorem continuousAt_paperEndpointFixedBaseP13RawOrderTuple_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p)) :
    ContinuousAt
      (paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase)
      (x₀,
        (0 : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)))) := by
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ :=
    fun j ↦ throughSubspaceEndpointComplementIndex
      (reverseVertex V) (reverseEdge V Bv) U₀ j
  let Coord := AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
  let X := α × EuclideanSpace ℝ Coord
  let p0 : Fin (M + 2) := 0
  let j : Fin (M + 3) := Fin.last (M + 2)
  let Ebase : α → ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    fun x ↦
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeBase x p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  have hEbase : ContinuousAt Ebase x₀ := by
    simpa [Ebase, ρ, κ] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousAt
        (K := ℝ) V Bv U₀ hU₀ CedgeBase hCedgeBase
  have hfst : ContinuousAt (fun xu : X ↦ xu.1) (x₀, 0) :=
    continuous_fst.continuousAt
  have hEpair : ContinuousAt (fun xu : X ↦ Ebase xu.1) (x₀, 0) :=
    by
      simpa [Function.comp] using hEbase.comp hfst
  have hchart :
      ∀ (p : Fin (M + 2)) (hpj : p.succ ≤ j),
        identityCornerDetChart
          (ChartLocalSuffixState.transformedEdge (Ebase x₀) p
            (ChartLocalSuffixState.suffixState (Ebase x₀) j p.succ hpj)) := by
    have hchart0 :=
      paperEndpointFixedBaseContinuousEdges_selfBase_recursiveBprev_detChart
        (K := ℝ) V Bv U₀ hU₀ CedgeBase hbase
    intro p hpj
    simpa [Ebase, j, paperEndpointFixedBaseEdgeMatrixOfReverseEdges] using hchart0 p
  have hF2 : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ xu.2 c)) (x₀, 0) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  have hF3 : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ xu.2 c)) (x₀, 0) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  have hCtop : ContinuousAt
      (fun xu : X ↦
        AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ xu.2 c)) (x₀, 0) :=
    AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean.continuousAt.comp
      continuous_snd.continuousAt
  have hDtail : ContinuousAt
      (fun xu : X ↦
        ChartLocalSuffixState.residualProduct (Ebase xu.1) j p0.succ p0.succ.le_last)
      (x₀, 0) :=
    continuousAt_chartLocalSuffixState_residualProduct
      (K := ℝ) (ρ := ρ) (κ := κ) (E := fun xu : X ↦ Ebase xu.1)
      hEpair (hij := p0.succ.le_last) hchart
  have hC0 : ContinuousAt
      (fun xu : X ↦
        ChartLocalSuffixState.residualBlock (Ebase xu.1) j p0 p0.succ.le_last)
      (x₀, 0) :=
    continuousAt_chartLocalSuffixState_residualBlock
      (K := ℝ) (ρ := ρ) (κ := κ) (E := fun xu : X ↦ Ebase xu.1)
      hEpair hchart p0 p0.succ.le_last
  have hA3 : ContinuousAt
      (fun _xu : X ↦ (0 : Matrix (κ p0.succ) ρ ℝ)) (x₀, 0) :=
    continuousAt_const
  have htuple :=
    hCtop.prodMk
      (hDtail.prodMk
        (hF3.prodMk
          (hCtop.prodMk
            (hF2.prodMk
              (hA3.prodMk hC0)))))
  simpa [paperEndpointFixedBaseP13RawOrderTuple,
    Ebase, ρ, κ, Coord, X, p0, j] using htuple

set_option linter.unusedSectionVars false in
/-- The chart-side inverse product-step Jacobian density is continuous along
the centered p. 13 raw-shaped target tuple. -/
theorem continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p)) :
    ContinuousAt
      (fun xu : α × EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)) ↦
        productReductionStepRawOrderInverseJacobianDensity
          (paperEndpointFixedBaseP13RawOrderTuple
            V Bv U₀ hU₀ CedgeBase xu))
      (x₀,
        (0 : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)))) := by
  classical
  apply
    continuousAt_productReductionStepRawOrderInverseJacobianDensity_comp_of_mem_rawDetChartSet
      (Y :=
        paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
  · exact
      continuousAt_paperEndpointFixedBaseP13RawOrderTuple_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) hCedgeBase hbase
  · exact
      paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) x₀

set_option linter.unusedSectionVars false in
/-- The chart-side inverse product-step Jacobian density is positive at the
centered p. 13 raw-shaped target tuple. -/
theorem paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (x₀ : α) :
    0 <
      productReductionStepRawOrderInverseJacobianDensity
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase
          (x₀,
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ 0))))) := by
  classical
  exact
    productReductionStepRawOrderInverseJacobianDensity_comp_pos_of_mem_rawDetChartSet
      (Y :=
        paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
      (a₀ := (x₀,
        (0 : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0)))))
      (paperEndpointFixedBaseP13RawOrderTuple_mem_rawDetChartSet_center
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) x₀)

end Aoyagi
end DLN
end DLNFibre
