import DLNFibre.DLN.Aoyagi.ProductReductionStepMeasure

/-!
# Product-step inverse density along suffix-state step coordinates

This file connects the deterministic suffix-state raw step coordinates to the
raw-order product-step determinant chart and chart-side inverse Jacobian
density.

The results are local product-step chart handoffs. They do not prove source
coverage, original DLN prior transport, signed-box density identification,
normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator Topology

namespace DLNFibre
namespace DLN
namespace Aoyagi

/-- The raw-order product-step chart map is continuous at determinant-chart
points. -/
theorem continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet
    {ρ π μ ν : Type*} [Fintype ρ] [DecidableEq ρ] [Finite π]
    [Fintype μ] [Finite ν]
    (z₀ : ProductReductionStepRawTopologyTuple ρ π μ ν)
    (hz₀ : z₀ ∈ productReductionStepRawDetChartSet ρ π μ ν) :
    ContinuousAt
      (productReductionStepTopologyTupleToChartRawOrder
        (ρ := ρ) (π := π) (μ := μ) (ν := ν))
      z₀ := by
  classical
  let x : ProductReductionStepRawCoordinates ρ π μ ν ℝ :=
    productReductionStepRawCoordinatesOfTopologyTuple z₀
  have hx : x.detChart := by
    simpa [x, productReductionStepRawDetChartSet] using hz₀
  have hderiv :=
    hasFDerivAt_productReductionStepTopologyTupleToChart_rawOrder
      (ρ := ρ) (π := π) (μ := μ) (ν := ν) x hx.1 hx.2
  simpa [productReductionStepTopologyTupleToChartRawOrder, x] using hderiv.continuousAt

/-- Raw-shaped target tuple obtained by applying the product-step chart map to
one deterministic suffix-state raw step. -/
def chartLocalSuffixStateStepRawOrderTargetTuple
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : Matrix (κ j) ρ ℝ) :
    ProductReductionStepRawTopologyTuple ρ (κ j) (κ p.succ) (κ p.castSucc) :=
  productReductionStepTopologyTupleToChartRawOrder
    (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc)
    ((ChartLocalSuffixState.stepRawCoordinates E p S F3prev).topologyTuple)

/-- The arbitrary suffix-state step target tuple lies in the raw-shaped target
determinant chart whenever the previous `Ctop` block and the transformed edge
top-left block are determinant units. -/
theorem chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : Matrix (κ j) ρ ℝ)
    (hCtop : IsUnit S.Ctop.det)
    (hM : identityCornerDetChart (ChartLocalSuffixState.transformedEdge E p S)) :
    chartLocalSuffixStateStepRawOrderTargetTuple E p S F3prev ∈
      productReductionStepRawDetChartSet ρ (κ j) (κ p.succ) (κ p.castSucc) := by
  classical
  have hx :
      (ChartLocalSuffixState.stepRawCoordinates E p S F3prev).topologyTuple ∈
        productReductionStepRawDetChartSet ρ (κ j) (κ p.succ) (κ p.castSucc) := by
    simpa using
      (ChartLocalSuffixState.stepRawCoordinates_detChart
        (E := E) (p := p) (S := S) (F3prev := F3prev) hCtop hM)
  exact
    mapsTo_productReductionStepTopologyTupleToChartRawOrder_detChart
      (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc) hx

/-- The raw suffix-state step tuple is continuous when the previous suffix
fields, input edge, and previous `F3` choice are continuous. -/
theorem continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple
    {α : Type*} [TopologicalSpace α] {a₀ : α}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (hE : ContinuousAt (fun a : α ↦ E a p) a₀)
    (hB : ContinuousAt (fun a : α ↦ (S a).B) a₀)
    (hCtop : ContinuousAt (fun a : α ↦ (S a).Ctop) a₀)
    (hD : ContinuousAt (fun a : α ↦ (S a).D) a₀)
    (hF3prev : ContinuousAt F3prev a₀) :
    ContinuousAt
      (fun a : α ↦
        (ChartLocalSuffixState.stepRawCoordinates (E a) p (S a) (F3prev a)).topologyTuple)
      a₀ := by
  let M : α → Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    fun a ↦ ChartLocalSuffixState.transformedEdge (E a) p (S a)
  have hleft : ContinuousAt
      (fun a : α ↦
        fromBlocks (1 : Matrix ρ ρ ℝ) (S a).B 0
          (1 : Matrix (κ p.succ) (κ p.succ) ℝ)) a₀ := by
    have hfrom : Continuous
        (fun B : Matrix ρ (κ p.succ) ℝ ↦
          fromBlocks (1 : Matrix ρ ρ ℝ) B 0
            (1 : Matrix (κ p.succ) (κ p.succ) ℝ)) :=
      continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const
    exact hfrom.continuousAt.comp hB
  have hM : ContinuousAt M a₀ := by
    have hmul : Continuous (fun q :
        Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.succ) ℝ ×
          Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ ↦ q.1 * q.2) :=
      continuous_fst.matrix_mul continuous_snd
    simpa [M, ChartLocalSuffixState.transformedEdge] using
      ContinuousAt.comp₂ hmul.continuousAt hleft hE
  have hA1 : ContinuousAt (fun a : α ↦ topLeftCorner (M a)) a₀ :=
    continuous_topLeftCorner.continuousAt.comp hM
  have hA2 : ContinuousAt (fun a : α ↦ upperRightBlock (M a)) a₀ := by
    have hupper : Continuous
        (fun M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ ↦ upperRightBlock M) :=
      continuous_id.matrix_submatrix Sum.inl Sum.inr
    exact hupper.continuousAt.comp hM
  have hA3 : ContinuousAt (fun a : α ↦ lowerLeftBlock (M a)) a₀ := by
    have hlower : Continuous
        (fun M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ ↦ lowerLeftBlock M) :=
      continuous_id.matrix_submatrix Sum.inr Sum.inl
    exact hlower.continuousAt.comp hM
  have hA4 : ContinuousAt (fun a : α ↦ lowerRightBlock (M a)) a₀ := by
    have hright : Continuous
        (fun M : Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ ↦ lowerRightBlock M) :=
      continuous_id.matrix_submatrix Sum.inr Sum.inr
    exact hright.continuousAt.comp hM
  have htuple :=
    hCtop.prodMk
      (hD.prodMk
        (hF3prev.prodMk
          (hA1.prodMk
            (hA2.prodMk
              (hA3.prodMk hA4)))))
  simpa [ChartLocalSuffixState.stepRawCoordinates,
    ProductReductionStepRawCoordinates.topologyTuple, M] using htuple

/-- The arbitrary suffix-state step raw-shaped target tuple is continuous if
the underlying raw step tuple is continuous and the basepoint lies in the
determinant chart. -/
theorem continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_of_raw
    {α : Type*} [TopologicalSpace α] {a₀ : α}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (hraw : ContinuousAt
      (fun a : α ↦
        (ChartLocalSuffixState.stepRawCoordinates (E a) p (S a) (F3prev a)).topologyTuple)
      a₀)
    (hCtop : IsUnit ((S a₀).Ctop.det))
    (hM : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge (E a₀) p (S a₀))) :
    ContinuousAt
      (fun a : α ↦
        chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a))
      a₀ := by
  classical
  let raw : α → ProductReductionStepRawTopologyTuple ρ (κ j) (κ p.succ) (κ p.castSucc) :=
    fun a ↦
      (ChartLocalSuffixState.stepRawCoordinates (E a) p (S a) (F3prev a)).topologyTuple
  have hraw₀ :
      raw a₀ ∈ productReductionStepRawDetChartSet ρ (κ j) (κ p.succ) (κ p.castSucc) := by
    simpa [raw] using
      (ChartLocalSuffixState.stepRawCoordinates_detChart
        (E := E a₀) (p := p) (S := S a₀) (F3prev := F3prev a₀) hCtop hM)
  have hchart :
      ContinuousAt
        (productReductionStepTopologyTupleToChartRawOrder
          (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc))
        (raw a₀) :=
    continuousAt_productReductionStepTopologyTupleToChartRawOrder_of_mem_rawDetChartSet
      (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc)
      (raw a₀) hraw₀
  simpa [chartLocalSuffixStateStepRawOrderTargetTuple, raw] using hchart.comp hraw

/-- Fully fieldwise continuity handoff for the arbitrary suffix-state
raw-shaped target tuple. -/
theorem continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple
    {α : Type*} [TopologicalSpace α] {a₀ : α}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (hE : ContinuousAt (fun a : α ↦ E a p) a₀)
    (hB : ContinuousAt (fun a : α ↦ (S a).B) a₀)
    (hCtopCont : ContinuousAt (fun a : α ↦ (S a).Ctop) a₀)
    (hD : ContinuousAt (fun a : α ↦ (S a).D) a₀)
    (hF3prev : ContinuousAt F3prev a₀)
    (hCtop : IsUnit ((S a₀).Ctop.det))
    (hM : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge (E a₀) p (S a₀))) :
    ContinuousAt
      (fun a : α ↦
        chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a))
      a₀ := by
  exact
    continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_of_raw
      (E := E) (p := p) (S := S) (F3prev := F3prev)
      (continuousAt_chartLocalSuffixState_stepRawCoordinates_topologyTuple
        (E := E) (p := p) (S := S) (F3prev := F3prev)
        hE hB hCtopCont hD hF3prev)
      hCtop hM

/-- The chart-side inverse product-step Jacobian density is continuous along
an arbitrary suffix-state step target tuple. -/
theorem continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity
    {α : Type*} [TopologicalSpace α] {a₀ : α}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (hY : ContinuousAt
      (fun a : α ↦
        chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a))
      a₀)
    (hCtop : IsUnit ((S a₀).Ctop.det))
    (hM : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge (E a₀) p (S a₀))) :
    ContinuousAt
      (fun a : α ↦
        productReductionStepRawOrderInverseJacobianDensity
          (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc)
          (chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a)))
      a₀ := by
  classical
  apply
    continuousAt_productReductionStepRawOrderInverseJacobianDensity_comp_of_mem_rawDetChartSet
      (Y := fun a : α ↦
        chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a))
  · exact hY
  · exact
      chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet
        (E := E a₀) (p := p) (S := S a₀) (F3prev := F3prev a₀) hCtop hM

/-- Fieldwise continuity version of inverse-density continuity along an
arbitrary suffix-state step target tuple. -/
theorem continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_of_fields
    {α : Type*} [TopologicalSpace α] {a₀ : α}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (hE : ContinuousAt (fun a : α ↦ E a p) a₀)
    (hB : ContinuousAt (fun a : α ↦ (S a).B) a₀)
    (hCtopCont : ContinuousAt (fun a : α ↦ (S a).Ctop) a₀)
    (hD : ContinuousAt (fun a : α ↦ (S a).D) a₀)
    (hF3prev : ContinuousAt F3prev a₀)
    (hCtop : IsUnit ((S a₀).Ctop.det))
    (hM : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge (E a₀) p (S a₀))) :
    ContinuousAt
      (fun a : α ↦
        productReductionStepRawOrderInverseJacobianDensity
          (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc)
          (chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a)))
      a₀ := by
  exact
    continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity
      (E := E) (p := p) (S := S) (F3prev := F3prev)
      (continuousAt_chartLocalSuffixStateStepRawOrderTargetTuple
        (E := E) (p := p) (S := S) (F3prev := F3prev)
        hE hB hCtopCont hD hF3prev hCtop hM)
      hCtop hM

/-- The chart-side inverse product-step Jacobian density is positive at an
arbitrary suffix-state step target tuple. -/
theorem chartLocalSuffixStateStepRawOrderTargetTuple_inverseJacobianDensity_pos
    {α : Type*}
    {N : ℕ} {ρ : Type*} {κ : Fin (N + 1) → Type*}
    [Fintype ρ] [DecidableEq ρ] [∀ j, Fintype (κ j)] [∀ j, DecidableEq (κ j)]
    (E : α → ∀ p : Fin N, Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ)
    {j : Fin (N + 1)} (p : Fin N)
    (S : α → ChartLocalSuffixState ρ κ ℝ j p.succ)
    (F3prev : α → Matrix (κ j) ρ ℝ)
    (a₀ : α)
    (hCtop : IsUnit ((S a₀).Ctop.det))
    (hM : identityCornerDetChart
      (ChartLocalSuffixState.transformedEdge (E a₀) p (S a₀))) :
    0 <
      productReductionStepRawOrderInverseJacobianDensity
        (ρ := ρ) (π := κ j) (μ := κ p.succ) (ν := κ p.castSucc)
        (chartLocalSuffixStateStepRawOrderTargetTuple (E a₀) p (S a₀) (F3prev a₀)) := by
  classical
  exact
    productReductionStepRawOrderInverseJacobianDensity_comp_pos_of_mem_rawDetChartSet
      (Y := fun a : α ↦
        chartLocalSuffixStateStepRawOrderTargetTuple (E a) p (S a) (F3prev a))
      (a₀ := a₀)
      (chartLocalSuffixStateStepRawOrderTargetTuple_mem_rawDetChartSet
        (E := E a₀) (p := p) (S := S a₀) (F3prev := F3prev a₀) hCtop hM)

end Aoyagi
end DLN
end DLNFibre
