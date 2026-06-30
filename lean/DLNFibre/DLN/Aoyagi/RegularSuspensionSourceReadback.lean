import DLNFibre.DLN.Aoyagi.RegularSuspensionCoordinates
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinates

/-!
# Fixed-base product-coordinate source readback

This file connects the explicit fixed-base p.13 product-coordinate chart to
the retained-passive `sourceReadback` algebra.  It is pointwise finite block
algebra: no source-prior transport, source-image coverage, normal crossings,
pole order, or RLCT extraction is proved here.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

universe v

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Fieldwise source readback for the generic fixed-base source-dependent p.13
product-coordinate edge family.

The product chart keeps the decoded regular variables `Ctop`, first `F2`,
`F3`, and the residual blocks extracted from the base edge family.  Its
retained passive readback fields are the canonical values `A1passive = 1` and
`A3passive = 0`.  This is not a source-prior, coverage, normal-crossing, pole
order, or RLCT statement. -/
theorem paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
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
    (x : α)
    (u : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c ↦ u c)).det) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ := throughSubspaceEndpointComplementIndex
      (reverseVertex V) (reverseEdge V Bv) U₀
    let Coord :=
      AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let Ebase : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeBase x p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
    let Eprod : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
        (fun p ↦
          (CedgeProd (x, u) p :
            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
    let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
    let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
    let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
    let C : ∀ p : Fin (M + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ :=
      fun p ↦ ChartLocalSuffixState.residualBlock Ebase (Fin.last (M + 2)) p p.succ.le_last
    let data :=
      ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
        (K := ℝ) (ρ := ρ) (M := M + 1) (κ' := κ) Eprod
    data.A1passive = (fun _ : Fin (M + 1) ↦ 1) ∧
      data.F2 = Fin.cases F2 (fun _ : Fin (M + 1) ↦ 0) ∧
      data.A3passive = (fun _ : Fin (M + 1) ↦ 0) ∧
      data.C = C ∧
      data.Ctop = Ctop ∧
      data.F3 = F3 := by
  intro ρ κ Coord CedgeProd Ebase Eprod F2 F3 Ctop C data
  let G :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean
      V Bv U₀ u Ebase
  have hEMat : Eprod = G := by
    funext p
    simpa [Eprod, CedgeProd,
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean,
      Ebase, G] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_continuousReverseEdgeFamilyOfMatrices
        (K := ℝ) V Bv U₀ hU₀ G p
  have hLast :
      Eprod (Fin.last (M + 1)) =
        ChartLocalSuffixState.productCoordinateRightEndpointMatrix F3 (C (Fin.last (M + 1))) := by
    rw [hEMat]
    simp [G, F3, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean]
    rfl
  have hMid :
      ∀ p : Fin (M + 2), 0 < p.val → p.val < M + 1 →
        Eprod p =
          ChartLocalSuffixState.productCoordinateMiddleMatrix (ρ := ρ) (C p) := by
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
    rw [hEMat]
    simp [G, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast, hnotZero]
  have hLeft :
      let p0 : Fin (M + 2) := 0
      Eprod p0 = ChartLocalSuffixState.productCoordinateLeftEndpointMatrix F2 Ctop (C p0) := by
    have hnotLast : (0 : Fin (M + 2)) ≠ Fin.last (M + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp at hval
    rw [hEMat]
    simp [G, F2, Ctop, C, paperEndpointFixedBaseMultiEdgeProductCoordinateMatrixOfEuclidean,
      hnotLast]
    rfl
  have hfields :=
    ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback_productCoordinate_fields_succSucc
      (K := ℝ) (N := M) (ρ := ρ) (κ := κ)
      Eprod F2 F3 Ctop C hLast hMid hLeft
      (by simpa [Ctop] using hCtop)
  simpa [data] using hfields

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Generic fixed-base small-ball package for p.13 product-coordinate readouts.

After shrinking the regular Euclidean variable around `0`, one radius gives
the determinant-unit certificate, raw regular/residual coordinate readouts,
and source-readback field equalities for every base point.  This is only local
fixed-base coordinate algebra: no source-prior transport, source-image
coverage, normal crossings, pole order, or RLCT extraction is proved. -/
theorem exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_readout_package
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
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
      let CedgeProd :=
        paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
          V Bv U₀ hU₀ CedgeBase
      ∀ x : α, ∀ u : EuclideanSpace ℝ Coord,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
          IsUnit (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)).det ∧
          (paperEndpointFixedBaseRegularBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
                (fun c ↦ u c)) ∧
          (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) ∧
          let Ebase : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun p ↦
                (CedgeBase x p :
                  reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
          let Eprod : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun p ↦
                (CedgeProd (x, u) p :
                  reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
          let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
          let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
          let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
          let C : ∀ p : Fin (M + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ :=
            fun p ↦
              ChartLocalSuffixState.residualBlock Ebase (Fin.last (M + 2)) p p.succ.le_last
          let data :=
            ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := ρ) (M := M + 1) (κ' := κ) Eprod
          data.A1passive = (fun _ : Fin (M + 1) ↦ 1) ∧
            data.F2 = Fin.cases F2 (fun _ : Fin (M + 1) ↦ 0) ∧
            data.A3passive = (fun _ : Fin (M + 1) ↦ 0) ∧
            data.C = C ∧
            data.Ctop = Ctop ∧
            data.F3 = F3 := by
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
  intro ρ κ Coord CedgeProd x u hu
  have hCtop :
      IsUnit
        (AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)).det :=
    hunit u hu
  have hcoord :
      (paperEndpointFixedBaseRegularBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
            (fun c ↦ u c)) ∧
      (paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeProd (x, u) =
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x) := by
    simpa [ρ, κ, Coord, CedgeProd] using
      paperEndpointFixedBaseRegular_residualBlockCoordinateMap_eq_multiEdgeProductCoordinateEuclidean_baseEdgeFamily
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (CedgeBase := CedgeBase) (x := x) (u := u) hCtop
  constructor
  · exact hCtop
  constructor
  · exact hcoord.1
  constructor
  · exact hcoord.2
  · intro Ebase Eprod F2 F3 Ctop C data
    simpa [ρ, κ, Coord, CedgeProd, Ebase, Eprod, F2, F3, Ctop, C, data] using
      (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
        (M := M) V Bv U₀ hU₀ CedgeBase x u hCtop)

set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On a sufficiently small regular Euclidean ball, the generic fixed-base
source-dependent p.13 product-coordinate family has the stated source-readback
fields uniformly in the base point.

This only packages the `Ctop` determinant-unit hypothesis in
`paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields`
by shrinking around `u = 0`.  It is not a source-prior, coverage,
normal-crossing, pole-order, or RLCT statement. -/
theorem exists_pos_radius_le_forall_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
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
      let ρ := Fin (Module.finrank ℝ U₀)
      let κ := throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀
      let Coord :=
        AoyagiRegularBlockCoordinateIndex ρ (κ (Fin.last (M + 2))) (κ 0)
      ∀ x : α, ∀ u : EuclideanSpace ℝ Coord,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
          let CedgeProd :=
            paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
              V Bv U₀ hU₀ CedgeBase
          let Ebase : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun p ↦
                (CedgeBase x p :
                  reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
          let Eprod : ∀ p : Fin (M + 2), Matrix (ρ ⊕ κ p.succ) (ρ ⊕ κ p.castSucc) ℝ :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges V Bv U₀ hU₀
              (fun p ↦
                (CedgeProd (x, u) p :
                  reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))
          let F2 := AoyagiRegularBlockCoordinateIndex.f2Matrix (fun c : Coord ↦ u c)
          let F3 := AoyagiRegularBlockCoordinateIndex.f3Matrix (fun c : Coord ↦ u c)
          let Ctop := AoyagiRegularBlockCoordinateIndex.ctopMatrix (fun c : Coord ↦ u c)
          let C : ∀ p : Fin (M + 2), Matrix (κ p.succ) (κ p.castSucc) ℝ :=
            fun p ↦
              ChartLocalSuffixState.residualBlock Ebase (Fin.last (M + 2)) p p.succ.le_last
          let data :=
            ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.sourceReadback
              (K := ℝ) (ρ := ρ) (M := M + 1) (κ' := κ) Eprod
          data.A1passive = (fun _ : Fin (M + 1) ↦ 1) ∧
            data.F2 = Fin.cases F2 (fun _ : Fin (M + 1) ↦ 0) ∧
            data.A3passive = (fun _ : Fin (M + 1) ↦ 0) ∧
            data.C = C ∧
            data.Ctop = Ctop ∧
            data.F3 = F3 := by
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
  intro ρ κ Coord x u hu CedgeProd Ebase Eprod F2 F3 Ctop C data
  simpa [ρ, κ, Coord, CedgeProd, Ebase, Eprod, F2, F3, Ctop, C, data] using
    (paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_sourceReadback_fields
      (M := M) V Bv U₀ hU₀ CedgeBase x u (hunit u hu))

end Aoyagi
end DLN
end DLNFibre
