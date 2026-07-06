import DLNFibre.DLN.Aoyagi.EndpointLossComparison
import DLNFibre.DLN.Aoyagi.RegularSuspensionLocalMeasure

/-!
# Local finite-integral handoff for the original square-Frobenius loss

This file specializes the generic adapted-loss local-measure handoff to the
original `lossDLN` of a tuple built from chain-edge matrices in fixed bases.
The specialization uses only the finite endpoint basis comparison from
`EndpointLossComparison`.  It still assumes the p. 13 product-coordinate lower
bound, residual source hypotheses, and density hypotheses explicitly.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

set_option linter.style.longLine false

section OriginalLossLocalMeasure

universe v

variable {N : ℕ}
  (W : Fin (N + 1) → Type v) [∀ i, AddCommGroup (W i)]
  [∀ i, TopologicalSpace (W i)] [∀ i, IsTopologicalAddGroup (W i)]
  [∀ i, T2Space (W i)] [∀ i, Module ℝ (W i)]
  [∀ i, ContinuousSMul ℝ (W i)]
  (B : ∀ i : Fin N, W i.succ →ₗ[ℝ] W i.castSucc)

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

set_option linter.unusedSectionVars false in
/-- Pulling a locally positive continuous original density back along the
explicit self-base p.13 product-coordinate edge-family map preserves the
continuous-at and positive-at-base hypotheses required by the local
finite-integral sockets.

This is only a pointwise/topological density handoff.  It does not prove a
measure change-of-variables formula or original-prior transport through the
product-coordinate map. -/
theorem continuousAt_pos_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
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
    (u₀ : EuclideanSpace ℝ
      (AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)))
    (CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    {density :
      (∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ) → ℝ} :
    let Coord :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    ContinuousAt density (CedgeProd (x₀, u₀)) →
      0 < density (CedgeProd (x₀, u₀)) →
        ContinuousAt (fun z : α × EuclideanSpace ℝ Coord ↦ density (CedgeProd z)) (x₀, u₀) ∧
          0 < (fun z : α × EuclideanSpace ℝ Coord ↦ density (CedgeProd z)) (x₀, u₀) := by
  intro Coord CedgeProd hdensity_cont hdensity_pos
  have hCedgeProd : ContinuousAt CedgeProd (x₀, u₀) := by
    simpa [CedgeProd, Coord] using
      continuousAt_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀) (u₀ := u₀)
        (CedgeBase := CedgeBase) hCedgeBase hbase
  exact ⟨hdensity_cont.comp hCedgeProd, hdensity_pos⟩

set_option linter.unusedSectionVars false in
/-- Pulling a positive continuous original density back along the explicit
self-base p.13 product-coordinate edge-family map gives the local
nonnegativity and upper-bound hypotheses consumed by the local finite-integral
sockets, after shrinking the regular-coordinate radius below a supplied cap.

This is still only a pointwise/topological density bound.  It does not prove a
measure change-of-variables formula or original-prior transport through the
product-coordinate map. -/
theorem exists_pos_radius_le_eventually_nhdsWithin_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_bounds_of_continuousAt_pos
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
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    {source : Set α}
    {density :
      (∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ) → ℝ}
    {Rmax : ℝ} :
    let Coord :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    ContinuousAt density
      (CedgeProd (x₀, (0 : EuclideanSpace ℝ Coord))) →
      0 < density (CedgeProd (x₀, (0 : EuclideanSpace ℝ Coord))) →
        0 < Rmax →
          ∃ R C : ℝ, 0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧
            (∀ᶠ x in nhdsWithin x₀ source,
              ∀ u : EuclideanSpace ℝ Coord,
                u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
                  0 ≤ density (CedgeProd (x, u))) ∧
            (∀ᶠ x in nhdsWithin x₀ source,
              ∀ u : EuclideanSpace ℝ Coord,
                u ∈ Metric.ball (0 : EuclideanSpace ℝ Coord) R →
                  density (CedgeProd (x, u)) ≤ C) := by
  intro Coord CedgeProd hdensity_cont hdensity_pos hRmax
  rcases
      continuousAt_pos_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (u₀ := (0 : EuclideanSpace ℝ Coord))
        (CedgeBase := CedgeBase) hCedgeBase hbase
        (density := density) hdensity_cont hdensity_pos with
    ⟨hcomp_cont, hcomp_pos⟩
  simpa [CedgeProd, Coord] using
    exists_pos_radius_le_eventually_nhdsWithin_density_bounds_of_continuousAt_pos
      (α := α) (E := EuclideanSpace ℝ Coord)
      (density := fun z : α × EuclideanSpace ℝ Coord ↦ density (CedgeProd z))
      (x₀ := x₀) (s := source) (Rmax := Rmax)
      hcomp_cont hcomp_pos hRmax

set_option linter.unusedSectionVars false in
/-- Local-source p.13 finite-integral handoff for the original
square-Frobenius `lossDLN` of a chain-coordinate tuple.

The finite endpoint basis comparison supplies the adapted-to-original loss
comparison.  The local source set, residual source hypotheses, product-coordinate
adapted lower bound, and density bounds remain explicit. -/
theorem exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    {source : Set α} {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hsource_meas : MeasurableSet source)
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict source,
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase source μ t)
    (hadapted_lower :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u))
    (hdensity_nonneg :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            0 ≤ density (x, u))
    (hdensity_le :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) R →
            density (x, u) ≤ C) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) (reverseEdge W B)
          0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
      (∫⁻ z : α × EuclideanSpace ℝ ρ,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
            (fun u =>
              (lossDLN d target
                (chainMapMatrixTuple b
                  (fun p : Fin N =>
                    (CedgeProd (z.1, u) p :
                      reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) ^
                (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                density (z.1, u)) z.2) ∂
          (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let target : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N))
      (chainMap (reverseVertex W) (reverseEdge W B)
        0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  let originalLoss : α × EuclideanSpace ℝ ρ → ℝ :=
    fun z =>
      lossDLN d target
        (chainMapMatrixTuple b
          (fun p : Fin N =>
            (CedgeProd z p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W) (B := B) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  have hloss_cmp :
      ∀ᶠ x in nhdsWithin x₀ source,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤
              originalLoss (x, u) := by
    exact Filter.Eventually.of_forall fun x => by
      intro u _hu
      rw [← paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeProd) (x := (x, u))]
      simpa [originalLoss, target] using hcmp (x, u)
  simpa [ρ, target, originalLoss] using
    exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_const_mul_adaptedProductDifferenceSquareSum_le_loss
      (W := W) (B := B) sourceData
      (source := source) (μ := μ) (ν := ν)
      (CedgeProd := CedgeProd) (loss := originalLoss) (density := density)
      (t := t) (R := R) (c := c) (c0 := c0) (C := C)
      hR hc hc0 hC ht hsource_meas hpos_source
      (by simpa [residualNegPowerIntegrableOn] using hbase_source)
      (by simpa [ρ] using hadapted_lower)
      (by simpa [ρ] using hloss_cmp)
      (by simpa [ρ] using hdensity_nonneg)
      (by simpa [ρ] using hdensity_le)

set_option linter.unusedSectionVars false in
/-- Measurable-local-source continuation theorem for the original
square-Frobenius `lossDLN` along the explicit self-base multi-edge p.13
product-coordinate family.

The theorem constructs the measurable local source and product-family adapted
lower bound, then returns a continuation: once residual source hypotheses and
density bounds are supplied on that returned source, the local-source
original-loss finite-integral socket applies.  No signed-box chart,
pushforward, Jacobian/source-density identity, or monomial-unit data is
constructed here. -/
theorem exists_measurable_localSource_forall_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_multiEdgeProductCoordinateEdgeFamily_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ source sourceU : Set α, ∃ R c : ℝ,
      sourceU ∈ nhds x₀ ∧ IsOpen sourceU ∧ x₀ ∈ sourceU ∧
      source = sourceU ∩ sourceStratum ∧
      MeasurableSet source ∧ x₀ ∈ source ∧ source ⊆ sourceStratum ∧
      (∀ x, x ∈ source →
        PaperEndpointFixedBaseCanonicalProductDifferenceSourceRanks
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase r rEdge x) ∧
      nhdsWithin x₀ source = nhdsWithin x₀ sourceStratum ∧
      0 < R ∧ R ≤ Rmax ∧ 0 < c ∧
      ∀ {μ : Measure α} {ν : Measure (EuclideanSpace ℝ ρ)}
          {density : α × EuclideanSpace ℝ ρ → ℝ} {t C : ℝ},
        ν.IsAddHaarMeasure →
        0 ≤ C → 0 < t →
        (∀ᵐ x ∂ μ.restrict source,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x)) →
        residualNegPowerIntegrableOn
          (W := V) (B := Bv) (U₀ := U₀) (hU₀ := hU₀) CedgeBase source μ t →
        (∀ᶠ x in nhdsWithin x₀ source,
          ∀ u : EuclideanSpace ℝ ρ,
            u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
              0 ≤ density (x, u)) →
        (∀ᶠ x in nhdsWithin x₀ source,
          ∀ u : EuclideanSpace ℝ ρ,
            u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
              density (x, u) ≤ C) →
        ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
          (∫⁻ z : α × EuclideanSpace ℝ ρ,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
                (fun u =>
                  (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin (M + 2) =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
              (μ.restrict (U ∩ source)).prod ν) < ∞ := by
  classical
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let target : Matrix (Fin (d (Fin.last (M + 2)))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
      (chainMap (reverseVertex V) (reverseEdge V Bv)
        0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
  rcases
      exists_measurable_localSource_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ sourceData
        hCedgeBase hbase hEdgeMatrix hRmax with
    ⟨source, sourceU, R, c, hsourceU_nhds, hsourceU_open, hxsourceU,
      hsource_eq, hsource_meas, hxsource, hsource_subset, hsourceRanks,
      hnhds_source, hR, hR_le_Rmax, hc, hadapted_lower⟩
  have hcontinue :
      ∀ {μ : Measure α} {ν : Measure (EuclideanSpace ℝ ρ)}
          {density : α × EuclideanSpace ℝ ρ → ℝ} {t C : ℝ},
        ν.IsAddHaarMeasure →
        0 ≤ C → 0 < t →
        (∀ᵐ x ∂ μ.restrict source,
          0 < aoyagiCoordinateSquareSum
            (paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase x)) →
        residualNegPowerIntegrableOn
          (W := V) (B := Bv) (U₀ := U₀) (hU₀ := hU₀) CedgeBase source μ t →
        (∀ᶠ x in nhdsWithin x₀ source,
          ∀ u : EuclideanSpace ℝ ρ,
            u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
              0 ≤ density (x, u)) →
        (∀ᶠ x in nhdsWithin x₀ source,
          ∀ u : EuclideanSpace ℝ ρ,
            u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) R →
              density (x, u) ≤ C) →
        ∃ U : Set α, IsOpen U ∧ x₀ ∈ U ∧
          (∫⁻ z : α × EuclideanSpace ℝ ρ,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
                (fun u =>
                  (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin (M + 2) =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
              (μ.restrict (U ∩ source)).prod ν) < ∞ := by
    intro μ ν density t C hν hC ht hpos_source hbase_source hdensity_nonneg hdensity_le
    letI : ν.IsAddHaarMeasure := hν
    simpa [ρ, sourceStratum, CedgeProd, target] using
      exists_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_localSource_adaptedProductDifferenceSquareSum_lower
        (W := V) (B := Bv) sourceData b
        (source := source) (μ := μ) (ν := ν)
        (CedgeProd := CedgeProd) (density := density)
        (t := t) (R := R) (c := c) (C := C)
        hR hc hC ht hsource_meas hpos_source hbase_source
        (by simpa [ρ, CedgeProd] using hadapted_lower)
        (by simpa [ρ] using hdensity_nonneg)
        (by simpa [ρ] using hdensity_le)
  exact
    ⟨source, sourceU, R, c, hsourceU_nhds, hsourceU_open, hxsourceU,
      by simpa [sourceStratum] using hsource_eq,
      hsource_meas, hxsource, by simpa [sourceStratum] using hsource_subset,
      by simpa [sourceStratum] using hsourceRanks,
      by simpa [sourceStratum] using hnhds_source,
      hR, hR_le_Rmax, hc,
      by
        intro μ ν density t C hν hC ht hpos_source hbase_source
          hdensity_nonneg hdensity_le
        simpa [ρ, sourceStratum, CedgeProd, target] using
          hcontinue (μ := μ) (ν := ν) (density := density) (t := t) (C := C)
            hν hC ht hpos_source hbase_source hdensity_nonneg hdensity_le⟩

set_option linter.unusedSectionVars false in
/-- Radius-shrinking p.13 finite-integral handoff for the original
square-Frobenius `lossDLN` of a chain-coordinate tuple.

The finite endpoint basis comparison supplies the previously separate
`c0 * adapted <= loss` hypothesis for this specific original loss.  The
product-coordinate adapted lower bound, residual source hypotheses, and
positive continuous density hypothesis remain explicit inputs. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {CedgeBase : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c : ℝ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hsource_meas :
      MeasurableSet (paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge))
    (hpos_source :
      ∀ᵐ x ∂ μ.restrict
          (paperEndpointFixedBaseSourceRankStratum
            (K := ℝ) W B CedgeBase r rEdge),
        0 < aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ CedgeBase x))
    (hbase_source :
      residualNegPowerIntegrableOn
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀) CedgeBase
        (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge) μ t)
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B CedgeBase r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ CedgeBase x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B CedgeBase r rEdge
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) (reverseEdge W B)
          0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin N =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B CedgeBase r rEdge
  let target : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N))
      (chainMap (reverseVertex W) (reverseEdge W B)
        0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  let originalLoss : α × EuclideanSpace ℝ ρ → ℝ :=
    fun z =>
      lossDLN d target
        (chainMapMatrixTuple b
          (fun p : Fin N =>
            (CedgeProd z p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W) (B := B) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  have hloss_cmp :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤
              originalLoss (x, u) := by
    exact Filter.Eventually.of_forall fun x => by
      intro u _hu
      rw [← paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeProd) (x := (x, u))]
      simpa [originalLoss, target] using hcmp (x, u)
  simpa [ρ, sourceStratum, target, originalLoss] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν) (CedgeProd := CedgeProd)
      (loss := originalLoss) (density := density)
      (t := t) (Rmax := Rmax) (c := c) (c0 := c0)
      hRmax hc hc0 ht
      (by simpa [sourceStratum] using hsource_meas)
      (by simpa [sourceStratum] using hpos_source)
      (by simpa [residualNegPowerIntegrableOn, sourceStratum] using hbase_source)
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hadapted_lower)
      (by simpa [ρ, sourceStratum] using hloss_cmp)

set_option linter.unusedSectionVars false in
/-- Top measurable-edge-matrix signed-box finite-integral handoff for the
original square-Frobenius `lossDLN` of a chain-coordinate tuple.

This is the measurable-edge-matrix variant of the continuous-edge signed-box
front end.  The finite endpoint basis comparison proves the adapted-to-original
loss comparison; the signed-box chart, weighted pushforward, residual monomial
lower bound, density positivity, and product-coordinate adapted lower bound
remain explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) W B U₀ hU₀
          (fun p : Fin N ↦
            (Cedge x p : reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) (reverseEdge W B)
          0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin N =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  let target : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N))
      (chainMap (reverseVertex W) (reverseEdge W B)
        0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  let originalLoss : α × EuclideanSpace ℝ ρ → ℝ :=
    fun z =>
      lossDLN d target
        (chainMapMatrixTuple b
          (fun p : Fin N =>
            (CedgeProd z p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W) (B := B) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  have hloss_cmp :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤
              originalLoss (x, u) := by
    exact Filter.Eventually.of_forall fun x => by
      intro u _hu
      rw [← paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeProd) (x := (x, u))]
      simpa [originalLoss, target] using hcmp (x, u)
  simpa [ρ, sourceStratum, target, originalLoss] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν)
      (sourceChart := sourceChart) (sourceDensity := sourceDensity)
      (CedgeProd := CedgeProd) (loss := originalLoss) (density := density)
      (t := t) (Rmax := Rmax) (c := c) (c0 := c0)
      (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres)
      (kres := kres)
      hRmax hc hc0 ht hEdgeMatrix hsourceDensity_aemeas hsourceChart hmap
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hadapted_lower)
      (by simpa [ρ, sourceStratum] using hloss_cmp)

set_option linter.unusedSectionVars false in
/-- Top continuous-edge signed-box finite-integral handoff for the original
square-Frobenius `lossDLN` of a chain-coordinate tuple.

This specializes the existing continuous-edge signed-box adapted-loss front
end by proving the adapted-to-loss comparison from finite endpoint
basis-change.  The signed-box chart and pushforward, residual monomial lower
bound, density positivity, and product-coordinate adapted lower bound remain
explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
    [∀ j, FiniteDimensional ℝ (W j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    {U₀ : Submodule ℝ (reverseVertex W 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W B))}
    {Cedge : α → ∀ p : Fin N,
      reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin N → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W B U₀ hU₀ x₀ Cedge H r rEdge)
    {d : Fin (N + 1) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex W j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {CedgeProd :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ∀ p : Fin N,
        reverseVertex W p.castSucc →L[ℝ] reverseVertex W p.succ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W) (reverseEdge W B) U₀ 0)) → ℝ}
    {t Rmax c cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (hc : 0 < c) (ht : 0 < t)
    (hCedge : Continuous Cedge)
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W B U₀ hU₀ Cedge (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0))
    (hadapted_lower :
      ∀ᶠ x in
        nhdsWithin x₀ (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) W B Cedge r rEdge),
        ∀ u : EuclideanSpace ℝ
            (AoyagiRegularBlockCoordinateIndex
              (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W) (reverseEdge W B) U₀ 0)),
          u ∈ Metric.ball
              (0 : EuclideanSpace ℝ
                (AoyagiRegularBlockCoordinateIndex
                  (Fin (Module.finrank ℝ U₀))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
                  (throughSubspaceEndpointComplementIndex
                    (reverseVertex W) (reverseEdge W B) U₀ 0))) Rmax →
            c * (aoyagiCoordinateSquareSum
                (paperEndpointFixedBaseResidualBlockCoordinateMap
                  (K := ℝ) W B U₀ hU₀ Cedge x) +
              aoyagiCoordinateSquareSum (fun i => u i)) ≤
            paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
              (K := ℝ) W B U₀ hU₀ CedgeProd (x, u)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W) (reverseEdge W B) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W B Cedge r rEdge
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last N))
        (chainMap (reverseVertex W) (reverseEdge W B)
          0 (Fin.last N) (Fin.zero_le (Fin.last N)))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin N =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount N H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ (Fin.last N))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex W) (reverseEdge W B) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) W B Cedge r rEdge
  let target : Matrix (Fin (d (Fin.last N))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last N))
      (chainMap (reverseVertex W) (reverseEdge W B)
        0 (Fin.last N) (Fin.zero_le (Fin.last N)))
  let originalLoss : α × EuclideanSpace ℝ ρ → ℝ :=
    fun z =>
      lossDLN d target
        (chainMapMatrixTuple b
          (fun p : Fin N =>
            (CedgeProd z p :
              reverseVertex W p.castSucc →ₗ[ℝ] reverseVertex W p.succ)))
  rcases
      exists_pos_const_forall_adaptedProductDifferenceFrobeniusLoss_le_lossDLN_chainMapMatrixTuple
        (W := W) (B := B) b U₀ hU₀ CedgeProd with
    ⟨c0, hc0, hcmp⟩
  have hloss_cmp :
      ∀ᶠ x in nhdsWithin x₀ sourceStratum,
        ∀ u : EuclideanSpace ℝ ρ,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρ) Rmax →
            c0 *
              paperEndpointFixedBaseAdaptedProductDifferenceSquareSum
                (K := ℝ) W B U₀ hU₀ CedgeProd (x, u) ≤
              originalLoss (x, u) := by
    exact Filter.Eventually.of_forall fun x => by
      intro u _hu
      rw [← paperEndpointFixedBaseAdaptedProductDifferenceFrobeniusLoss_eq_squareSum
        (W := W) (B := B) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := CedgeProd) (x := (x, u))]
      simpa [originalLoss, target] using hcmp (x, u)
  simpa [ρ, sourceStratum, target, originalLoss] using
    exists_radius_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_const_mul_adaptedProductDifferenceSquareSum_le_loss_continuousAt_pos_density
      (W := W) (B := B) sourceData
      (μ := μ) (ν := ν)
      (sourceChart := sourceChart) (sourceDensity := sourceDensity)
      (CedgeProd := CedgeProd) (loss := originalLoss) (density := density)
      (t := t) (Rmax := Rmax) (c := c) (c0 := c0)
      (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres)
      (kres := kres)
      hRmax hc hc0 ht hCedge hsourceDensity_aemeas hsourceChart hmap
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensity_cont hdensity_pos
      (by simpa [ρ, sourceStratum] using hadapted_lower)
      (by simpa [ρ, sourceStratum] using hloss_cmp)

set_option linter.unusedSectionVars false in
/-- Top local finite-integral handoff for the original square-Frobenius
`lossDLN` along the explicit self-base multi-edge p.13 product-coordinate
family.

This removes the separate adapted product-difference lower-bound hypothesis
for this explicit product family.  The signed-box source chart, weighted
pushforward, residual monomial lower bound, source-density bound, and
transported density factor remain explicit hypotheses. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : Continuous CedgeBase)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let target : Matrix (Fin (d (Fin.last (M + 2)))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
      (chainMap (reverseVertex V) (reverseEdge V Bv)
        0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ CedgeBase
        hCedgeBase.continuousAt hbase (r := r) (rEdge := rEdge)
        (Rmax := Rmax) hRmax with
    ⟨Rprod, cprod, hRprod, hRprod_le_Rmax, hcprod, hadapted_lower⟩
  have hfin :
      let ρ :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
          (chainMap (reverseVertex V) (reverseEdge V Bv)
            0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
      ∃ R C : ℝ, ∃ U : Set α,
        0 < R ∧ R ≤ Rprod ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
          (∫⁻ z : α × EuclideanSpace ℝ ρ,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
                (fun u =>
                  (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin (M + 2) =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                      (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
              (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    simpa [ρ, sourceStratum, CedgeProd, target] using
      exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_continuousEdge_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
        (W := V) (B := Bv) sourceData b
        (μ := μ) (ν := ν)
        (sourceChart := sourceChart) (sourceDensity := sourceDensity)
        (CedgeProd := CedgeProd) (density := density)
        (t := t) (Rmax := Rprod) (c := cprod)
        (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres)
        (kres := kres)
        hRprod hcprod ht hCedgeBase
        hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres hRres hcrit
        (by simpa [sourceStratum] using hres_lower)
        hsourceDensity_nonneg hsourceDensity_le
        hdensity_cont hdensity_pos
        (by simpa [ρ, sourceStratum, CedgeProd] using hadapted_lower)
  rcases hfin with ⟨R, C, U, hR, hR_le_Rprod, hC, hUopen, hxU, hfinite⟩
  exact
    ⟨R, C, U, hR, hR_le_Rprod.trans hRprod_le_Rmax, hC, hUopen, hxU,
      by simpa [ρ, sourceStratum, CedgeProd, target] using hfinite⟩

set_option linter.unusedSectionVars false in
/-- Measurable-edge-matrix version of the local finite-integral handoff for
the original square-Frobenius `lossDLN` along the explicit self-base multi-edge
p.13 product-coordinate family.

Compared with
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density`,
this theorem assumes only `ContinuousAt CedgeBase x₀` for the local product
family and keeps the fixed-base edge-matrix measurability hypothesis explicit.
The signed-box chart, weighted pushforward, residual monomial lower bound,
source-density bound, and transported density factor remain supplied. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {density :
      α × EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)) → ℝ}
    {t Rmax cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ))
    (hdensity_cont : ContinuousAt density (x₀, 0))
    (hdensity_pos : 0 < density (x₀, 0)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let sourceStratum :=
    paperEndpointFixedBaseSourceRankStratum
      (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
  let CedgeProd :=
    paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
      V Bv U₀ hU₀ CedgeBase
  let target : Matrix (Fin (d (Fin.last (M + 2)))) (Fin (d 0)) ℝ :=
    LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
      (chainMap (reverseVertex V) (reverseEdge V Bv)
        0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
  rcases
      exists_pos_radius_pos_const_residual_add_regular_squareSum_eventually_le_adaptedProductDifferenceSquareSum_multiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase_nhdsWithin_source
        (V := V) (Bv := Bv) (x₀ := x₀) U₀ hU₀ CedgeBase
        hCedgeBase hbase (r := r) (rEdge := rEdge)
        (Rmax := Rmax) hRmax with
    ⟨Rprod, cprod, hRprod, hRprod_le_Rmax, hcprod, hadapted_lower⟩
  have hfin :
      let ρ :=
        AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)
      let sourceStratum :=
        paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
      let target :=
        LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
          (chainMap (reverseVertex V) (reverseEdge V Bv)
            0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
      ∃ R C : ℝ, ∃ U : Set α,
        0 < R ∧ R ≤ Rprod ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
          (∫⁻ z : α × EuclideanSpace ℝ ρ,
            ENNReal.ofReal
              ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
                (fun u =>
                  (lossDLN d target
                    (chainMapMatrixTuple b
                      (fun p : Fin (M + 2) =>
                        (CedgeProd (z.1, u) p :
                          reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                      (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                    density (z.1, u)) z.2) ∂
              (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    simpa [ρ, sourceStratum, CedgeProd, target] using
      exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_adaptedProductDifferenceSquareSum_lower_continuousAt_pos_density
        (W := V) (B := Bv) sourceData b
        (μ := μ) (ν := ν)
        (sourceChart := sourceChart) (sourceDensity := sourceDensity)
        (CedgeProd := CedgeProd) (density := density)
        (t := t) (Rmax := Rprod) (c := cprod)
        (cres := cres) (Cres := Cres) (Rres := Rres) (hres := hres)
        (kres := kres)
        hRprod hcprod ht hEdgeMatrix
        hsourceDensity_aemeas hsourceChart
        (by simpa [sourceStratum] using hmap)
        hcres hCres hRres hcrit
        (by simpa [sourceStratum] using hres_lower)
        hsourceDensity_nonneg hsourceDensity_le
        hdensity_cont hdensity_pos
        (by simpa [ρ, sourceStratum, CedgeProd] using hadapted_lower)
  rcases hfin with ⟨R, C, U, hR, hR_le_Rprod, hC, hUopen, hxU, hfinite⟩
  exact
    ⟨R, C, U, hR, hR_le_Rprod.trans hRprod_le_Rmax, hC, hUopen, hxU,
      by simpa [ρ, sourceStratum, CedgeProd, target] using hfinite⟩

set_option linter.unusedSectionVars false in
/-- Measurable-edge-matrix original-loss local finite-integral handoff for an
edge-family density pulled back along the explicit self-base p.13
product-coordinate family.

This removes only the abstract product-coordinate density
continuity/positivity hypotheses from
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density`.
The signed-box source chart, weighted pushforward, residual monomial lower
bound, source-density bounds, local product-family construction, and original
loss comparison through the fixed endpoint bases remain delegated to that
parent original-loss wrapper. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_edgeFamilyDensity_comp_multiEdgeProductCoordinateEdgeFamily_selfBase_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {edgeFamilyDensity :
      (∀ p : Fin (M + 2),
        reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ) → ℝ}
    {t Rmax cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ContinuousAt edgeFamilyDensity (CedgeProd (x₀, (0 : EuclideanSpace ℝ ρ))) →
      0 < edgeFamilyDensity (CedgeProd (x₀, (0 : EuclideanSpace ℝ ρ))) →
        ∃ R C : ℝ, ∃ U : Set α,
          0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
            (∫⁻ z : α × EuclideanSpace ℝ ρ,
              ENNReal.ofReal
                ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
                  (fun u =>
                    (lossDLN d target
                      (chainMapMatrixTuple b
                        (fun p : Fin (M + 2) =>
                          (CedgeProd (z.1, u) p :
                            reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                      (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                    edgeFamilyDensity (CedgeProd (z.1, u))) z.2) ∂
                (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro ρ sourceStratum CedgeProd target hdensity_cont hdensity_pos
  classical
  let densityProd : α × EuclideanSpace ℝ ρ → ℝ :=
    fun z ↦ edgeFamilyDensity (CedgeProd z)
  have hdensityProd :
      ContinuousAt densityProd (x₀, 0) ∧ 0 < densityProd (x₀, 0) := by
    simpa [densityProd, ρ, CedgeProd] using
      continuousAt_pos_density_comp_paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean_selfBase
        (V := V) (Bv := Bv) (U₀ := U₀) (hU₀ := hU₀)
        (u₀ := (0 : EuclideanSpace ℝ ρ))
        (CedgeBase := CedgeBase) hCedgeBase hbase
        (density := edgeFamilyDensity) hdensity_cont hdensity_pos
  simpa [densityProd, ρ, sourceStratum, CedgeProd, target] using
    exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
      (V := V) (Bv := Bv) U₀ hU₀ sourceData b
      (μ := μ) (ν := ν)
      (sourceChart := sourceChart) (sourceDensity := sourceDensity)
      (density := densityProd)
      (t := t) (Rmax := Rmax) (cres := cres) (Cres := Cres)
      (Rres := Rres) (hres := hres) (kres := kres)
      hRmax ht hCedgeBase hbase hEdgeMatrix
      hsourceDensity_aemeas hsourceChart hmap
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensityProd.1 hdensityProd.2

set_option linter.unusedSectionVars false in
/-- Measurable-edge-matrix version of the original-loss local finite-integral
handoff with the concrete chart-side inverse product-step Jacobian density.

This specializes
`exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density`
to the density
`productReductionStepRawOrderInverseJacobianDensity` composed with
`paperEndpointFixedBaseP13RawOrderTuple`.  It removes only the abstract
continuity/positivity hypotheses for the transported regular-fiber density.
The signed-box source chart, weighted pushforward, residual monomial lower
bound, source-density bounds, local product-family construction, and original
loss comparison remain supplied or delegated exactly as before. -/
theorem exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_productStepInverseJacobianDensity_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase
    {M : ℕ}
    (V : Fin (M + 3) → Type v) [∀ i, AddCommGroup (V i)]
    [∀ i, TopologicalSpace (V i)] [∀ i, IsTopologicalAddGroup (V i)]
    [∀ i, T2Space (V i)] [∀ i, Module ℝ (V i)]
    [∀ i, ContinuousSMul ℝ (V i)]
    (Bv : ∀ i : Fin (M + 2), V i.succ →ₗ[ℝ] V i.castSucc)
    [∀ j, FiniteDimensional ℝ (V j)]
    {α ι : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [Fintype ι] {x₀ : α}
    (U₀ : Submodule ℝ (reverseVertex V 0))
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap V Bv)))
    {CedgeBase : α → ∀ p : Fin (M + 2),
      reverseVertex V p.castSucc →L[ℝ] reverseVertex V p.succ}
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin (M + 2) → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) (N := M + 2) V Bv U₀ hU₀ x₀ CedgeBase H r rEdge)
    {d : Fin (M + 3) → ℕ}
    (b : ∀ j, Module.Basis (Fin (d j)) ℝ (reverseVertex V j))
    {μ : Measure α}
    {ν : Measure
      (EuclideanSpace ℝ
        (AoyagiRegularBlockCoordinateIndex
          (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex V) (reverseEdge V Bv) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {sourceChart : (ι → ℝ) → α} {sourceDensity : (ι → ℝ) → ℝ}
    {t Rmax cres Cres : ℝ}
    {Rres : ι → ℝ} {hres kres : ι → ℕ}
    (hRmax : 0 < Rmax) (ht : 0 < t)
    (hCedgeBase : ContinuousAt CedgeBase x₀)
    (hbase :
      CedgeBase x₀ =
        fun p : Fin (M + 2) ↦ LinearMap.toContinuousLinearMap (reverseEdge V Bv p))
    (hEdgeMatrix :
      Measurable (fun x : α ↦
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges
          (K := ℝ) (N := M + 2) V Bv U₀ hU₀
          (fun p : Fin (M + 2) ↦
            (CedgeBase x p :
              reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ))))
    (hsourceDensity_aemeas :
      AEMeasurable (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))
        (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hsourceChart : AEMeasurable sourceChart
      (Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))))
    (hmap :
      μ.restrict (paperEndpointFixedBaseSourceRankStratum
          (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge) =
        Measure.map sourceChart
          ((Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))).withDensity
            (fun y : ι → ℝ => ENNReal.ofReal (sourceDensity y))))
    (hcres : 0 < cres) (hCres : 0 ≤ Cres) (hRres : ∀ i, 0 < Rres i)
    (hcrit : ∀ i, 2 * t * (kres i : ℝ) < (hres i : ℝ) + 1)
    (hres_lower : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      cres * ∏ i, (|y i|) ^ (2 * (kres i : ℝ)) ≤
        aoyagiCoordinateSquareSum
          (paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) (N := M + 2) V Bv U₀ hU₀ CedgeBase (sourceChart y)))
    (hsourceDensity_nonneg : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      0 ≤ sourceDensity y)
    (hsourceDensity_le : ∀ᵐ y : ι → ℝ
      ∂Measure.pi (fun i : ι => volume.restrict (Set.Ioo (-(Rres i)) (Rres i))),
      sourceDensity y ≤ Cres * ∏ i, (|y i|) ^ (hres i : ℝ)) :
    let ρ :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex V) (reverseEdge V Bv) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) (N := M + 2) V Bv CedgeBase r rEdge
    let CedgeProd :=
      paperEndpointFixedBaseMultiEdgeProductCoordinateEdgeFamilyOfBaseEdgeFamilyEuclidean
        V Bv U₀ hU₀ CedgeBase
    let target :=
      LinearMap.toMatrix (b 0) (b (Fin.last (M + 2)))
        (chainMap (reverseVertex V) (reverseEdge V Bv)
          0 (Fin.last (M + 2)) (Fin.zero_le (Fin.last (M + 2))))
    ∃ R C : ℝ, ∃ U : Set α,
      0 < R ∧ R ≤ Rmax ∧ 0 ≤ C ∧ IsOpen U ∧ x₀ ∈ U ∧
        (∫⁻ z : α × EuclideanSpace ℝ ρ,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρ) R).indicator
              (fun u =>
                (lossDLN d target
                  (chainMapMatrixTuple b
                    (fun p : Fin (M + 2) =>
                      (CedgeProd (z.1, u) p :
                        reverseVertex V p.castSucc →ₗ[ℝ] reverseVertex V p.succ)))) ^
                    (-(t + (aoyagiTheorem2RegularVariableCount (M + 2) H r : ℝ) / 2)) *
                  productReductionStepRawOrderInverseJacobianDensity
                    (paperEndpointFixedBaseP13RawOrderTuple
                      V Bv U₀ hU₀ CedgeBase (z.1, u))) z.2) ∂
            (μ.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  classical
  let ρ :=
    AoyagiRegularBlockCoordinateIndex
      (Fin (Module.finrank ℝ U₀))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ (Fin.last (M + 2)))
      (throughSubspaceEndpointComplementIndex
        (reverseVertex V) (reverseEdge V Bv) U₀ 0)
  let density : α × EuclideanSpace ℝ ρ → ℝ :=
    fun xu ↦
      productReductionStepRawOrderInverseJacobianDensity
        (paperEndpointFixedBaseP13RawOrderTuple V Bv U₀ hU₀ CedgeBase xu)
  have hdensity_cont : ContinuousAt density (x₀, 0) := by
    simpa [density, ρ] using
      continuousAt_paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_selfBase
        (V := V) (Bv := Bv) U₀ hU₀ CedgeBase hCedgeBase hbase
  have hdensity_pos : 0 < density (x₀, 0) := by
    simpa [density, ρ] using
      paperEndpointFixedBaseP13RawOrderTuple_inverseJacobianDensity_pos_center
        (V := V) (Bv := Bv) U₀ hU₀ CedgeBase x₀
  simpa [density, ρ] using
    exists_radius_open_lintegral_ofReal_lossDLN_chainMapMatrixTuple_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_residualSource_signedBox_withDensity_monomialLower_edgeMatrix_multiEdgeProductCoordinateEdgeFamily_selfBase_continuousAt_pos_density
      (V := V) (Bv := Bv) U₀ hU₀ sourceData b
      (μ := μ) (ν := ν)
      (sourceChart := sourceChart) (sourceDensity := sourceDensity)
      (density := density)
      (t := t) (Rmax := Rmax) (cres := cres) (Cres := Cres)
      (Rres := Rres) (hres := hres) (kres := kres)
      hRmax ht hCedgeBase hbase hEdgeMatrix
      hsourceDensity_aemeas hsourceChart hmap
      hcres hCres hRres hcrit hres_lower
      hsourceDensity_nonneg hsourceDensity_le
      hdensity_cont hdensity_pos

end PaperEndpointFixedBaseRegularCoordinateSourceData

end OriginalLossLocalMeasure

end Aoyagi
end DLN
end DLNFibre

end
