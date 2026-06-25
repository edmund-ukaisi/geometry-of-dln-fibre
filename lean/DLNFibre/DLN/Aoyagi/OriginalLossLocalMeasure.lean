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

end PaperEndpointFixedBaseRegularCoordinateSourceData

end OriginalLossLocalMeasure

end Aoyagi
end DLN
end DLNFibre

end
