import DLNFibre.DLN.Aoyagi.ProductReductionStepSuffixDensity
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
open MeasureTheory

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
/-- The raw source tuple whose one-step product-reduction image is the p. 13
raw-shaped target tuple.

The tuple is ordered as `(C1,D,F3old,A1,A2,A3,A4)`.  For the left-endpoint
p. 13 construction this is
`(1,Dtail,F3,Ctop,-Ctop*F2,0,C0)`. -/
def paperEndpointFixedBaseP13RawPreimageTuple
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
      ((1 : Matrix ρ ρ ℝ),
        (Dtail,
          (F3,
            (Ctop,
              (-(Ctop * F2),
                ((0 : Matrix (κ p0.succ) ρ ℝ), C0))))))

set_option linter.unusedSectionVars false in
/-- The p. 13 raw preimage tuple is a section of the full raw tuple space:
its raw `C1` block is fixed to the identity. -/
theorem paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
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
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    (paperEndpointFixedBaseP13RawPreimageTuple
      V Bv U₀ hU₀ CedgeBase xu).1 =
      (1 : Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ) := by
  classical
  simp [paperEndpointFixedBaseP13RawPreimageTuple]

set_option linter.unusedSectionVars false in
/-- The p. 13 raw preimage tuple is a section of the full raw tuple space:
its raw `A3` block is fixed to zero. -/
theorem paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
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
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    (paperEndpointFixedBaseP13RawPreimageTuple
      V Bv U₀ hU₀ CedgeBase xu).2.2.2.2.2.1 =
      (0 : Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (Fin (Module.finrank ℝ U₀)) ℝ) := by
  classical
  simp [paperEndpointFixedBaseP13RawPreimageTuple]

set_option linter.unusedSectionVars false in
/-- The source-dependent multi-edge p. 13 product-coordinate matrix family used
for the left-endpoint raw product-step handoff.

This wraps the existing multi-edge product-coordinate matrix constructor around
the fixed-base edge matrices determined by `CedgeBase`. -/
def paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
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
      ∀ p : Fin (M + 2), Matrix
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.castSucc) ℝ :=
  fun xu ↦ by
    classical
    let Ebase : ∀ p : Fin (M + 2), Matrix
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
        (Fin (Module.finrank ℝ U₀) ⊕
          throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeBase xu.1 p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
    exact
      paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
        V Bv U₀ xu.2 Ebase

set_option linter.unusedSectionVars false in
/-- The actual left-endpoint raw suffix-step topology tuple of the constructed
p. 13 product-coordinate matrix family. -/
def p13ProductCoordinateLeftStepRawTopologyTuple
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
    let G :=
      paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
        V Bv U₀ hU₀ CedgeBase xu
    let p0 : Fin (M + 2) := 0
    let j : Fin (M + 3) := Fin.last (M + 2)
    let F3 : Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ j)
        (Fin (Module.finrank ℝ U₀)) ℝ :=
      AoyagiRegularBlockCoordinateIndex.f3Matrix
        (fun c : AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
    exact
      (ChartLocalSuffixState.stepRawCoordinates G p0
        (ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last) F3).topologyTuple

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
/-- The p. 13 raw preimage tuple lies in the source determinant chart whenever
its regular `Ctop` block has unit determinant. -/
theorem paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
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
    paperEndpointFixedBaseP13RawPreimageTuple
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
      (paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase xu).1.det ∧
    IsUnit
      (paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase xu).2.2.2.1.det
  constructor
  · simp [paperEndpointFixedBaseP13RawPreimageTuple]
  · simpa [paperEndpointFixedBaseP13RawPreimageTuple]
      using hCtop

set_option linter.unusedSectionVars false in
/-- Centered determinant-chart membership for the p. 13 raw preimage tuple. -/
theorem paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet_center
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
    paperEndpointFixedBaseP13RawPreimageTuple
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
    paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
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
/-- The raw-order product-step map sends the p. 13 raw preimage tuple to the
p. 13 raw-shaped target tuple. -/
theorem productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
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
    productReductionStepTopologyTupleToChartRawOrder
        (paperEndpointFixedBaseP13RawPreimageTuple
          V Bv U₀ hU₀ CedgeBase xu) =
      paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu := by
  classical
  rw [show
      paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase xu =
        productReductionStepChartTangentRawOrderEquiv
          (ρ := Fin (Module.finrank ℝ U₀))
          (π := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (μ := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (ν := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))
          (K := ℝ)
          ((productReductionStepChartCoordinatesOfRawOrderTopologyTuple
            (paperEndpointFixedBaseP13RawOrderTuple
              V Bv U₀ hU₀ CedgeBase xu)).topologyTuple) from by
      exact (productReductionStepChartCoordinatesOfRawOrderTopologyTuple_rawOrder
        (z := paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase xu)).symm]
  simp only [productReductionStepTopologyTupleToChartRawOrder]
  congr 1
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ :=
    fun j ↦ throughSubspaceEndpointComplementIndex
      (reverseVertex V) (reverseEdge V Bv) U₀ j
  let Coord := AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
  let Ctop : Matrix ρ ρ ℝ :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ xu.2 c)
  let F2 : Matrix ρ (κ 0) ℝ :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ xu.2 c)
  let Ebase : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
      (fun p ↦
        (CedgeBase xu.1 p :
          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
  let p0 : Fin (M + 2) := 0
  let jLast : Fin (M + 3) := Fin.last (M + 2)
  let Dtail : Matrix (κ jLast) (κ p0.succ) ℝ :=
    ChartLocalSuffixState.residualProduct Ebase jLast p0.succ p0.succ.le_last
  let C0 : Matrix (κ p0.succ) (κ 0) ℝ := by
    simpa [p0] using
      (ChartLocalSuffixState.residualBlock Ebase jLast p0 p0.succ.le_last)
  have hCtop' : IsUnit Ctop.det := by
    simpa [Ctop, ρ, κ, Coord] using hCtop
  have hcancel : Ctop⁻¹ * (Ctop * F2) = F2 :=
    Matrix.nonsing_inv_mul_cancel_left (A := Ctop) F2 hCtop'
  simp [paperEndpointFixedBaseP13RawPreimageTuple,
    paperEndpointFixedBaseP13RawOrderTuple,
    productReductionStepChartCoordinatesOfRawOrderTopologyTuple,
    ProductReductionStepChartCoordinates.topologyTuple,
    productReductionStepTopologyTupleToChart]
  constructor
  · change -(Ctop⁻¹ * -(Ctop * F2)) = F2
    rw [Matrix.mul_neg, hcancel]
    exact neg_neg F2
  · constructor
    · change Dtail * (0 : Matrix (κ p0.succ) ρ ℝ) * Ctop⁻¹ = 0
      rw [Matrix.mul_zero, Matrix.zero_mul]
    · change C0 - (0 : Matrix (κ p0.succ) ρ ℝ) * Ctop⁻¹ * (-(Ctop * F2)) = C0
      rw [Matrix.zero_mul, Matrix.zero_mul, sub_zero]

set_option linter.unusedSectionVars false in
/-- The left-endpoint raw suffix-step coordinates of the constructed multi-edge
p. 13 product-coordinate matrix family are exactly the explicit p. 13 raw
preimage tuple. -/
theorem p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
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
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    let G :=
      paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
        V Bv U₀ hU₀ CedgeBase xu
    let p0 : Fin (M + 2) := 0
    let j : Fin (M + 3) := Fin.last (M + 2)
    let F3 : Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ j)
        (Fin (Module.finrank ℝ U₀)) ℝ :=
      AoyagiRegularBlockCoordinateIndex.f3Matrix
        (fun c : AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
    (ChartLocalSuffixState.stepRawCoordinates G p0
        (ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last) F3).topologyTuple =
      paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase xu := by
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
  let G : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ xu.2 Ebase
  let F2 :=
    AoyagiRegularBlockCoordinateIndex.f2Matrix
      (fun c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
  let F3 :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
  let Ctop :=
    AoyagiRegularBlockCoordinateIndex.ctopMatrix
      (fun c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
  let p0 : Fin (M + 2) := 0
  let j : Fin (M + 3) := Fin.last (M + 2)
  let C : ∀ p : Fin (M + 2), Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ p.succ)
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ p.castSucc) ℝ :=
    fun p ↦ ChartLocalSuffixState.residualBlock Ebase
      (Fin.last (M + 2)) p p.succ.le_last
  let S := ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last
  have hLastG :
      G (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3
          (C (Fin.last (M + 1))) := by
    simp [G, F3, C, Ebase,
      paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean]
  have hMidG :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        G p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix
            (ρ := ρ) (C p) := by
    intro p hp0 hplast
    have hnotLast : p ≠ Fin.last (M + 1) := by
      intro hp
      have hval : p.val = M + 1 := by
        simp [hp]
      omega
    have hnotZero : p ≠ 0 := by
      intro hp
      have hval : p.val = 0 := by
        simp [hp]
      omega
    simp [G, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast, hnotZero]
  have hLeftG :
      G p0 =
        ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
    have hnotLast : p0 ≠ Fin.last (M + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp [p0] at hval
    simp [G, F2, Ctop, C, p0,
      paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean, hnotLast]
  have hp0_succ : p0.succ = (⟨1, by omega⟩ : Fin (M + 3)) := by
    ext
    simp [p0]
  have htail :
      S.B = 0 ∧ S.Ctop = 1 ∧
        S.L =
          Matrix.fromBlocks (1 : Matrix ρ ρ ℝ) 0 F3
            (1 : Matrix (κ j) (κ j) ℝ) := by
    have htail' :
        let one : Fin (M + 3) := ⟨1, by omega⟩
        let Sone := ChartLocalSuffixState.suffixState G j one one.le_last
        Sone.B = 0 ∧ Sone.Ctop = 1 ∧
          Sone.L =
            Matrix.fromBlocks (1 : Matrix ρ ρ ℝ) 0 F3
              (1 : Matrix (κ j) (κ j) ℝ) := by
      simpa [j] using
        ChartLocalSuffixState.suffixState_tail_fields_of_productCoordinateEdges
          (K := ℝ) G F3 C hLastG hMidG
    cases hp0_succ
    simpa [S, p0, j] using htail'
  have hblocks_last :
      ∀ p : Fin (M + 2),
        ChartLocalSuffixState.residualBlock G j p p.succ.le_last =
          ChartLocalSuffixState.residualBlock Ebase j p p.succ.le_last := by
    intro p
    simpa [C, j] using
      ChartLocalSuffixState.residualBlock_productCoordinateEdges_succSucc
        (K := ℝ) G F2 F3 Ctop C hLastG hMidG hLeftG p
  have hblocks :
      ∀ (p : Fin (M + 2)) (hpj : p.succ ≤ j),
        ChartLocalSuffixState.residualBlock G j p hpj =
          ChartLocalSuffixState.residualBlock Ebase j p hpj := by
    intro p hpj
    have hhp : hpj = p.succ.le_last := Subsingleton.elim _ _
    cases hhp
    exact hblocks_last p
  have hDtail :
      S.D =
        ChartLocalSuffixState.residualProduct Ebase j p0.succ p0.succ.le_last := by
    have hDG :
        S.D = ChartLocalSuffixState.residualProduct G j p0.succ p0.succ.le_last := by
      simpa [S, G, j, p0] using
        ChartLocalSuffixState.suffixState_D_eq_residualProduct
          (K := ℝ) G p0.succ.le_last
    have hprod :
        ChartLocalSuffixState.residualProduct G j p0.succ p0.succ.le_last =
          ChartLocalSuffixState.residualProduct Ebase j p0.succ p0.succ.le_last := by
      simpa [G, Ebase, j, p0] using
        ChartLocalSuffixState.residualProduct_eq_of_residualBlock_eq
          (K := ℝ) G Ebase p0.succ.le_last hblocks
    exact hDG.trans hprod
  have hM :
      ChartLocalSuffixState.transformedEdge G p0 S =
        Matrix.fromBlocks Ctop (-(Ctop * F2)) (0 : Matrix (κ p0.succ) ρ ℝ) (C p0) := by
    have hB0 : S.B = 0 := htail.1
    dsimp [ChartLocalSuffixState.transformedEdge]
    rw [hB0, hLeftG]
    dsimp [ChartLocalSuffixState.productCoordinateLeftEndpointMatrix]
    rw [Matrix.fromBlocks_one]
    exact Matrix.one_mul _
  change
    (ChartLocalSuffixState.stepRawCoordinates G p0 S F3).topologyTuple =
      paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase xu
  simp [ChartLocalSuffixState.stepRawCoordinates,
    ProductReductionStepRawCoordinates.topologyTuple,
    paperEndpointFixedBaseP13RawPreimageTuple,
    htail.2.1, hDtail, hM, topLeftCorner_fromBlocks,
    upperRightBlock_fromBlocks, lowerLeftBlock_fromBlocks,
    lowerRightBlock_fromBlocks, Ebase, G, F2, F3, Ctop, C, p0, j, ρ, κ]

set_option linter.unusedSectionVars false in
/-- The actual p. 13 left-step raw tuple lies in the raw determinant chart
whenever its regular `Ctop` block has unit determinant.

This is a section-domain theorem only: the tuple still has raw `C1 = 1` and
raw `A3 = 0`, so this does not identify its image with the full raw
determinant chart. -/
theorem p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
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
    p13ProductCoordinateLeftStepRawTopologyTuple
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
  have htuple :
      p13ProductCoordinateLeftStepRawTopologyTuple
          V Bv U₀ hU₀ CedgeBase xu =
        paperEndpointFixedBaseP13RawPreimageTuple
          V Bv U₀ hU₀ CedgeBase xu :=
    p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu
  rw [htuple]
  exact
    paperEndpointFixedBaseP13RawPreimageTuple_mem_rawDetChartSet
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu hCtop

set_option linter.unusedSectionVars false in
/-- The actual p. 13 left-step raw tuple is supported in the raw determinant
chart on a sufficiently small regular-coordinate ball. -/
theorem
    exists_pos_radius_le_forall_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
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
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∀ (x : α)
        (u : EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0))),
        u ∈ Metric.ball 0 R →
          p13ProductCoordinateLeftStepRawTopologyTuple
              V Bv U₀ hU₀ CedgeBase (x, u) ∈
            productReductionStepRawDetChartSet
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) := by
  classical
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro x u hu
  exact
    p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (xu := (x, u)) (hunit u hu)

set_option linter.unusedSectionVars false in
/-- A measure supported a.e. on a regular-coordinate ball whose `Ctop`
determinants are units is supported a.e. in the actual p. 13 left-step raw
determinant chart. -/
theorem
    ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    {R : ℝ}
    (hunit :
      ∀ u : EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)),
        u ∈ Metric.ball 0 R →
          IsUnit
            (AoyagiRegularBlockCoordinateIndex.ctopMatrix
              (fun c : AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ u c)).det)
    (hsupport :
      ∀ᵐ xu ∂η,
        xu.2 ∈ Metric.ball
          (0 : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ 0))) R) :
    ∀ᵐ xu ∂η,
      p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu ∈
        productReductionStepRawDetChartSet
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) := by
  filter_upwards [hsupport] with xu hball
  exact
    p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (xu := xu) (hunit xu.2 hball)

set_option linter.unusedSectionVars false in
/-- Small-ball a.e. support version of the actual p. 13 left-step raw
determinant-chart support theorem. -/
theorem
    exists_pos_radius_le_ae_p13LeftStepRaw_mem_rawDetChartSet_of_ae_regular_mem_ball
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ R : ℝ, 0 < R ∧ R ≤ Rmax ∧
      ∀ η : Measure (α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0))),
        (∀ᵐ xu ∂η,
          xu.2 ∈ Metric.ball
            (0 : EuclideanSpace ℝ
              (AoyagiRegularBlockCoordinateIndex
                (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex V) (reverseEdge V Bv) U₀ 0))) R) →
          ∀ᵐ xu ∂η,
            p13ProductCoordinateLeftStepRawTopologyTuple
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
  rcases
      AoyagiRegularBlockCoordinateIndex.exists_pos_radius_le_forall_isUnit_det_ctopMatrix_euclidean
        (ι := Fin (Module.finrank ℝ U₀))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
        hRmax with
    ⟨R, hR, hRle, hunit⟩
  refine ⟨R, hR, hRle, ?_⟩
  intro η hsupport
  exact
    ae_p13ProductCoordinateLeftStepRawTopologyTuple_mem_rawDetChartSet_of_ae_regular_mem_ball
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) hunit hsupport

set_option linter.unusedSectionVars false in
/-- The actual p. 13 left-step raw tuple has raw `C1` fixed to the identity. -/
theorem p13ProductCoordinateLeftStepRawTopologyTuple_C1_eq_one
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
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    (p13ProductCoordinateLeftStepRawTopologyTuple
      V Bv U₀ hU₀ CedgeBase xu).1 =
      (1 : Matrix (Fin (Module.finrank ℝ U₀)) (Fin (Module.finrank ℝ U₀)) ℝ) := by
  have htuple :
      p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu =
        paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase xu :=
    p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu
  exact (congrArg Prod.fst htuple).trans
    (paperEndpointFixedBaseP13RawPreimageTuple_C1_eq_one
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu)

set_option linter.unusedSectionVars false in
/-- The actual p. 13 left-step raw tuple has raw `A3` fixed to zero. -/
theorem p13ProductCoordinateLeftStepRawTopologyTuple_A3_eq_zero
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
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))) :
    (p13ProductCoordinateLeftStepRawTopologyTuple
      V Bv U₀ hU₀ CedgeBase xu).2.2.2.2.2.1 =
      (0 : Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (Fin (Module.finrank ℝ U₀)) ℝ) := by
  have htuple :
      p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu =
        paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase xu :=
    p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu
  exact (congrArg (fun z => z.2.2.2.2.2.1) htuple).trans
    (paperEndpointFixedBaseP13RawPreimageTuple_A3_eq_zero
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu)

set_option linter.unusedSectionVars false in
/-- If the explicit p. 13 raw preimage tuple pushes a source measure to the raw
determinant chart, then its `Ctop` determinant is a unit a.e. -/
theorem ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (m : Measure
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    (hpre :
      AEMeasurable
        (paperEndpointFixedBaseP13RawPreimageTuple
          V Bv U₀ hU₀ CedgeBase)
        η)
    (hpre_map :
      Measure.map
          (paperEndpointFixedBaseP13RawPreimageTuple
            V Bv U₀ hU₀ CedgeBase) η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))) :
    ∀ᵐ xu ∂η,
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix
          (fun c : AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)).det := by
  classical
  have hmem :
      ∀ᵐ xu ∂η,
        paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase xu ∈
          productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) :=
    ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
      (η := η) (m := m)
      (pre := paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase)
      hpre hpre_map
  filter_upwards [hmem] with xu hx
  simpa [paperEndpointFixedBaseP13RawPreimageTuple,
    productReductionStepRawDetChartSet] using hx.2

set_option linter.unusedSectionVars false in
/-- If the actual p. 13 left-step raw tuple pushes a source measure to the raw
determinant chart, then its `Ctop` determinant is a unit a.e. -/
theorem ae_isUnit_ctopMatrix_det_of_p13LeftStepRaw_map_eq_restrict_rawDetChart
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (m : Measure
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    (hraw :
      AEMeasurable
        (p13ProductCoordinateLeftStepRawTopologyTuple
          V Bv U₀ hU₀ CedgeBase)
        η)
    (hraw_map :
      Measure.map
          (p13ProductCoordinateLeftStepRawTopologyTuple
            V Bv U₀ hU₀ CedgeBase) η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))) :
    ∀ᵐ xu ∂η,
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix
          (fun c : AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)).det := by
  classical
  have hmem :
      ∀ᵐ xu ∂η,
        p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu ∈
          productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) :=
    ae_mem_productReductionStepRawDetChartSet_of_map_eq_restrict
      (η := η) (m := m)
      (pre := p13ProductCoordinateLeftStepRawTopologyTuple
        V Bv U₀ hU₀ CedgeBase)
      hraw hraw_map
  filter_upwards [hmem] with xu hx
  have htuple :
      p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu =
        paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase xu :=
    p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) xu
  have hx_pre :
      paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase xu ∈
          productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) := by
    simpa [htuple] using hx
  simpa [paperEndpointFixedBaseP13RawPreimageTuple,
    productReductionStepRawDetChartSet] using hx_pre.2

set_option linter.unusedSectionVars false in
/-- The explicit p. 13 raw preimage tuple is measurable whenever the fixed-base
edge matrix family consumed by the suffix recursion is measurable. -/
theorem measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) :
    Measurable
      (paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase) := by
  classical
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ : Fin (M + 3) → Type :=
    fun j =>
      throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ j
  let Coord := AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
  let X := α × EuclideanSpace ℝ Coord
  let Ebase : X → ∀ p : Fin (M + 2),
      Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
    fun xu p =>
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges
        (K := ℝ) V Bv U₀ hU₀
        (fun q : Fin (M + 2) =>
          (CedgeBase xu.1 q :
            reverseVertex V q.castSucc →ₗ[ℝ] reverseVertex V q.succ)) p
  let p0 : Fin (M + 2) := 0
  let j : Fin (M + 3) := Fin.last (M + 2)
  have hE : Measurable Ebase := by
    simpa [Ebase] using hEdgeMatrix.comp measurable_fst
  have hC1 : Measurable (fun _xu : X => (1 : Matrix ρ ρ ℝ)) :=
    measurable_const
  have hDtail : Measurable
      (fun xu : X =>
        ChartLocalSuffixState.residualProduct (Ebase xu) j p0.succ p0.succ.le_last) :=
    measurable_chartLocalSuffixState_residualProduct_real
      (E := Ebase) hE p0.succ.le_last
  have hF2 : Measurable
      (fun xu : X =>
        AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord => xu.2 c)) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f2Matrix_euclidean.measurable.comp
      measurable_snd
  have hF3 : Measurable
      (fun xu : X =>
        AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord => xu.2 c)) :=
    AoyagiRegularBlockCoordinateIndex.continuous_f3Matrix_euclidean.measurable.comp
      measurable_snd
  have hCtop : Measurable
      (fun xu : X =>
        AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord => xu.2 c)) :=
    AoyagiRegularBlockCoordinateIndex.continuous_ctopMatrix_euclidean.measurable.comp
      measurable_snd
  have hCtopF2 : Measurable
      (fun xu : X =>
        AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord => xu.2 c) *
          AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord => xu.2 c)) := by
    have hmul : Continuous (fun q : Matrix ρ ρ ℝ × Matrix ρ (κ 0) ℝ => q.1 * q.2) :=
      continuous_fst.matrix_mul continuous_snd
    exact hmul.measurable.comp (hCtop.prodMk hF2)
  have hA2 : Measurable
      (fun xu : X =>
        -((AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord => xu.2 c)) *
          AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord => xu.2 c))) :=
    hCtopF2.neg
  have hA3 : Measurable (fun _xu : X => (0 : Matrix (κ p0.succ) ρ ℝ)) :=
    measurable_const
  have hC0 : Measurable
      (fun xu : X =>
        ChartLocalSuffixState.residualBlock (Ebase xu) j p0 p0.succ.le_last) :=
    measurable_chartLocalSuffixState_residualBlock_real
      (E := Ebase) hE p0 p0.succ.le_last
  have htuple :=
    hC1.prodMk
      (hDtail.prodMk
        (hF3.prodMk
          (hCtop.prodMk
            (hA2.prodMk
              (hA3.prodMk hC0)))))
  simpa [paperEndpointFixedBaseP13RawPreimageTuple,
    Ebase, ρ, κ, Coord, X, p0, j] using htuple

set_option linter.unusedSectionVars false in
/-- A.e.-measurability form of
`measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix`. -/
theorem aemeasurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) :
    AEMeasurable
      (paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase) η :=
  (measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
    (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
    (CedgeBase := CedgeBase) hEdgeMatrix).aemeasurable

set_option linter.unusedSectionVars false in
/-- The actual p. 13 left-step raw tuple is measurable under the same fixed-base
edge-matrix measurability hypothesis as the explicit raw preimage tuple. -/
theorem measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) :
    Measurable
      (p13ProductCoordinateLeftStepRawTopologyTuple
        V Bv U₀ hU₀ CedgeBase) := by
  have hpre :
      Measurable
        (paperEndpointFixedBaseP13RawPreimageTuple
          V Bv U₀ hU₀ CedgeBase) :=
    measurable_paperEndpointFixedBaseP13RawPreimageTuple_of_measurable_edgeMatrix
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) hEdgeMatrix
  have hfun :
      p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase =
        paperEndpointFixedBaseP13RawPreimageTuple V Bv U₀ hU₀ CedgeBase := by
    funext xu
    exact
      p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) xu
  rw [hfun]
  exact hpre

set_option linter.unusedSectionVars false in
/-- A.e.-measurability form of
`measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix`. -/
theorem aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) :
    AEMeasurable
      (p13ProductCoordinateLeftStepRawTopologyTuple
        V Bv U₀ hU₀ CedgeBase) η :=
  (measurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
    (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
    (CedgeBase := CedgeBase) hEdgeMatrix).aemeasurable

set_option linter.unusedSectionVars false in
/-- Section-level p. 13 product-step measure identity.

If the actual p. 13 left-step raw tuple lands in the raw determinant chart
a.e., then the p. 13 raw-order target measure is the raw-order product-step
image of the actual left-step raw image measure.  This is only a
section-image identity; it does not assert that the left-step raw image
measure is full raw Haar measure on the raw determinant chart. -/
theorem
    map_p13RawOrderTuple_eq_map_leftStepRawOrder_image_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hraw_mem :
      ∀ᵐ xu ∂η,
        p13ProductCoordinateLeftStepRawTopologyTuple V Bv U₀ hU₀ CedgeBase xu ∈
          productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))) :
    Measure.map
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
        η =
      Measure.map
        (productReductionStepTopologyTupleToChartRawOrder
          (ρ := Fin (Module.finrank ℝ U₀))
          (π := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (μ := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (ν := throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀
              ((0 : Fin (M + 2)).castSucc)))
        (Measure.map
          (p13ProductCoordinateLeftStepRawTopologyTuple
            V Bv U₀ hU₀ CedgeBase)
          η) := by
  classical
  let raw :=
    p13ProductCoordinateLeftStepRawTopologyTuple
      V Bv U₀ hU₀ CedgeBase
  let pre :=
    paperEndpointFixedBaseP13RawPreimageTuple
      V Bv U₀ hU₀ CedgeBase
  let target :=
    paperEndpointFixedBaseP13RawOrderTuple
      V Bv U₀ hU₀ CedgeBase
  let S : Set (ProductReductionStepRawTopologyTuple
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))) :=
    productReductionStepRawDetChartSet
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))
  let Φ :=
    productReductionStepTopologyTupleToChartRawOrder
      (ρ := Fin (Module.finrank ℝ U₀))
      (π := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))
  have hraw :
      AEMeasurable raw η :=
    aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) hEdgeMatrix
  have hS_meas : MeasurableSet S := by
    simpa [S] using
      (isOpen_productReductionStepRawDetChartSet
        (ρ := Fin (Module.finrank ℝ U₀))
        (π := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀
            ((0 : Fin (M + 2)).castSucc))).measurableSet
  have hraw_mem' : ∀ᵐ xu ∂η, raw xu ∈ S := by
    simpa [raw, S] using hraw_mem
  have hraw_image_mem : ∀ᵐ z ∂Measure.map raw η, z ∈ S :=
    (ae_map_iff hraw hS_meas).2 hraw_mem'
  have hΦ_restrict :
      AEMeasurable Φ ((Measure.map raw η).restrict S) := by
    simpa [Φ, S] using
      aemeasurable_productReductionStepTopologyTupleToChartRawOrder_restrict_detChart
        (ρ := Fin (Module.finrank ℝ U₀))
        (π := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (μ := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (ν := throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))
        (Measure.map raw η)
  have hΦ : AEMeasurable Φ (Measure.map raw η) := by
    have hrestrict : (Measure.map raw η).restrict S = Measure.map raw η :=
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
    rwa [hrestrict] at hΦ_restrict
  have hmap_comp :
      Measure.map (fun xu => Φ (raw xu)) η =
        Measure.map Φ (Measure.map raw η) := by
    simpa [Φ, raw, Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := η) (g := Φ) (f := raw) hΦ hraw).symm
  have hCtop_ae :
      ∀ᵐ xu ∂η,
        IsUnit
          (AoyagiRegularBlockCoordinateIndex.ctopMatrix
            (fun c : AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex V) (reverseEdge V Bv) U₀ 0) => xu.2 c)).det := by
    filter_upwards [hraw_mem'] with xu hx
    have htuple : raw xu = pre xu :=
      p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) xu
    have hx_pre : pre xu ∈ S := by
      simpa [S, htuple] using hx
    simpa [pre, paperEndpointFixedBaseP13RawPreimageTuple,
      S, productReductionStepRawDetChartSet] using hx_pre.2
  have htarget :
      target =ᵐ[η] fun xu => Φ (raw xu) := by
    filter_upwards [hCtop_ae] with xu hCtop
    have htuple : raw xu = pre xu :=
      p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) xu
    symm
    rw [htuple]
    simpa [Φ, target, pre] using
      productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (xu := xu) hCtop
  calc
    Measure.map (paperEndpointFixedBaseP13RawOrderTuple V Bv U₀ hU₀ CedgeBase) η =
        Measure.map (fun xu => Φ (raw xu)) η := by
          simpa [target] using Measure.map_congr htarget
    _ =
        Measure.map Φ (Measure.map raw η) := hmap_comp

set_option linter.unusedSectionVars false in
/-- The constructed multi-edge p. 13 product-coordinate matrix family's
left-step target tuple is the explicit p. 13 raw-shaped target tuple. -/
theorem p13ProductCoordinateLeftStepRawOrderTargetTuple_eq_rawOrderTuple
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
    let G :=
      paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
        V Bv U₀ hU₀ CedgeBase xu
    let p0 : Fin (M + 2) := 0
    let j : Fin (M + 3) := Fin.last (M + 2)
    let F3 : Matrix
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ j)
        (Fin (Module.finrank ℝ U₀)) ℝ :=
      AoyagiRegularBlockCoordinateIndex.f3Matrix
        (fun c : AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ j)
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
    chartLocalSuffixStateStepRawOrderTargetTuple G p0
        (ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last) F3 =
      paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu := by
  classical
  let G :=
    paperEndpointFixedBaseP13ProductCoordinateMatrixFamily
      V Bv U₀ hU₀ CedgeBase xu
  let p0 : Fin (M + 2) := 0
  let j : Fin (M + 3) := Fin.last (M + 2)
  let F3 : Matrix
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ j)
      (Fin (Module.finrank ℝ U₀)) ℝ :=
    AoyagiRegularBlockCoordinateIndex.f3Matrix
      (fun c : AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ j)
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0) ↦ xu.2 c)
  have hraw :
      (ChartLocalSuffixState.stepRawCoordinates G p0
        (ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last) F3).topologyTuple =
      paperEndpointFixedBaseP13RawPreimageTuple
        V Bv U₀ hU₀ CedgeBase xu := by
    simpa [G, p0, j, F3] using
      p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) xu
  change productReductionStepTopologyTupleToChartRawOrder
      ((ChartLocalSuffixState.stepRawCoordinates G p0
        (ChartLocalSuffixState.suffixState G j p0.succ p0.succ.le_last) F3).topologyTuple) =
      paperEndpointFixedBaseP13RawOrderTuple
        V Bv U₀ hU₀ CedgeBase xu
  rw [hraw]
  exact
    productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (xu := xu) hCtop

set_option linter.unusedSectionVars false in
/-- Conditional p. 13 consumer of the raw product-step inverse-Jacobian
pushforward.

If the explicit p. 13 raw preimage tuple already pushes a source measure to
Haar measure restricted to the raw determinant chart, then the p. 13 raw-order
target tuple has the chart-side inverse-Jacobian density.  The source-side
pushforward is an explicit hypothesis. -/
theorem map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (m : Measure
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    [m.IsAddHaarMeasure]
    (hpre :
      AEMeasurable
        (paperEndpointFixedBaseP13RawPreimageTuple
          V Bv U₀ hU₀ CedgeBase)
        η)
    (hpre_map :
      Measure.map
          (paperEndpointFixedBaseP13RawPreimageTuple
            V Bv U₀ hU₀ CedgeBase) η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))) :
    Measure.map
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
        η =
      (m.restrict
        (productReductionStepRawDetChartSet
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀
              ((0 : Fin (M + 2)).castSucc)))).withDensity
        (fun y : ProductReductionStepRawTopologyTuple
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) =>
            ENNReal.ofReal
              (productReductionStepRawOrderInverseJacobianDensity y)) := by
  classical
  let pre :=
    paperEndpointFixedBaseP13RawPreimageTuple
      V Bv U₀ hU₀ CedgeBase
  let target :=
    paperEndpointFixedBaseP13RawOrderTuple
      V Bv U₀ hU₀ CedgeBase
  let Φ :=
    productReductionStepTopologyTupleToChartRawOrder
      (ρ := Fin (Module.finrank ℝ U₀))
      (π := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (μ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
      (ν := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))
  have hCtop_ae :=
    ae_isUnit_ctopMatrix_det_of_p13RawPreimage_map_eq_restrict_rawDetChart
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) (m := m)
      hpre hpre_map
  have htarget :
      target =ᵐ[η] fun xu => Φ (pre xu) := by
    filter_upwards [hCtop_ae] with xu hCtop
    symm
    simpa [target, pre, Φ] using
      productReductionStepTopologyTupleToChartRawOrder_paperEndpointFixedBaseP13RawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (xu := xu) hCtop
  calc
    Measure.map target η =
        Measure.map (fun xu => Φ (pre xu)) η := Measure.map_congr htarget
    _ =
      (m.restrict
        (productReductionStepRawDetChartSet
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀
              ((0 : Fin (M + 2)).castSucc)))).withDensity
        (fun y : ProductReductionStepRawTopologyTuple
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) =>
            ENNReal.ofReal
              (productReductionStepRawOrderInverseJacobianDensity y)) := by
        simpa [pre, Φ] using
          map_productReductionStepRawOrder_comp_eq_withDensity_inverseJacobian
            (η := η) (m := m)
            (pre := paperEndpointFixedBaseP13RawPreimageTuple
              V Bv U₀ hU₀ CedgeBase)
            hpre hpre_map

set_option linter.unusedSectionVars false in
/-- Conditional p. 13 consumer using the actual constructed left-step raw tuple.

If the actual left-endpoint raw suffix-step tuple of the constructed p. 13
product-coordinate matrix family pushes a source measure to Haar measure
restricted to the raw determinant chart, then the explicit p. 13 raw-order
target tuple has the chart-side inverse-Jacobian density. -/
theorem map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (m : Measure
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    [m.IsAddHaarMeasure]
    (hraw :
      AEMeasurable
        (p13ProductCoordinateLeftStepRawTopologyTuple
          V Bv U₀ hU₀ CedgeBase)
        η)
    (hraw_map :
      Measure.map
          (p13ProductCoordinateLeftStepRawTopologyTuple
            V Bv U₀ hU₀ CedgeBase) η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))) :
    Measure.map
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
        η =
      (m.restrict
        (productReductionStepRawDetChartSet
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀
              ((0 : Fin (M + 2)).castSucc)))).withDensity
        (fun y : ProductReductionStepRawTopologyTuple
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) =>
            ENNReal.ofReal
              (productReductionStepRawOrderInverseJacobianDensity y)) := by
  classical
  let raw :=
    p13ProductCoordinateLeftStepRawTopologyTuple
      V Bv U₀ hU₀ CedgeBase
  let pre :=
    paperEndpointFixedBaseP13RawPreimageTuple
      V Bv U₀ hU₀ CedgeBase
  have hraw_pre : raw =ᵐ[η] pre := by
    filter_upwards with xu
    simpa [raw, pre, p13ProductCoordinateLeftStepRawTopologyTuple] using
      p13ProductCoordinateLeftStepRawTopologyTuple_eq_rawPreimageTuple
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) xu
  have hpre : AEMeasurable pre η := hraw.congr hraw_pre
  have hmap_raw_pre : Measure.map raw η = Measure.map pre η :=
    Measure.map_congr hraw_pre
  have hpre_map :
      Measure.map pre η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))) := by
    rw [← hmap_raw_pre]
    exact hraw_map
  exact
    map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_rawPreimage_map
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) (m := m)
      hpre hpre_map

set_option linter.unusedSectionVars false in
/-- Conditional p. 13 consumer using the actual constructed left-step raw tuple,
with raw-tuple a.e.-measurability derived from measurable fixed-base edge
matrices.

The raw source pushforward remains an explicit hypothesis. -/
theorem
    map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map_of_measurable_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [MeasurableSpace α]
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (η : Measure (α × EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0))))
    (m : Measure
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc))))
    [BorelSpace
      (ProductReductionStepRawTopologyTuple
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))]
    [m.IsAddHaarMeasure]
    (hEdgeMatrix :
      Measurable (fun x : α =>
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) V Bv U₀ hU₀
          (fun p : Fin (M + 2) =>
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hraw_map :
      Measure.map
          (p13ProductCoordinateLeftStepRawTopologyTuple
            V Bv U₀ hU₀ CedgeBase) η =
        m.restrict
          (productReductionStepRawDetChartSet
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)))) :
    Measure.map
        (paperEndpointFixedBaseP13RawOrderTuple
          V Bv U₀ hU₀ CedgeBase)
        η =
      (m.restrict
        (productReductionStepRawDetChartSet
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀
              ((0 : Fin (M + 2)).castSucc)))).withDensity
        (fun y : ProductReductionStepRawTopologyTuple
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).succ))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ ((0 : Fin (M + 2)).castSucc)) =>
            ENNReal.ofReal
              (productReductionStepRawOrderInverseJacobianDensity y)) := by
  have hraw :
      AEMeasurable
        (p13ProductCoordinateLeftStepRawTopologyTuple
          V Bv U₀ hU₀ CedgeBase)
        η :=
    aemeasurable_p13ProductCoordinateLeftStepRawTopologyTuple_of_measurable_edgeMatrix
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) hEdgeMatrix
  exact
    map_p13RawOrderTuple_eq_withDensity_inverseJacobian_of_leftStepRaw_map
      (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
      (CedgeBase := CedgeBase) (η := η) (m := m)
      hraw hraw_map

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
