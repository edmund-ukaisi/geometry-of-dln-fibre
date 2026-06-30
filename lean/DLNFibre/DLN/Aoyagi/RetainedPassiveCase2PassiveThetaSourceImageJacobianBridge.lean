import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaJacobianMeasure

/-!
# Source-image density to Jacobian-measure bridge

This file consumes a density on the chart-produced passive-theta source image
and feeds it into the retained-passive residual-source finite-integral socket.
It is downstream of both the source-image/readback layer and the
theta-domain Jacobian-measure layer.

The result is only a consumer for chart-produced source-image measures.  It
does not identify an original DLN prior, prove Haar transport, prove
source-rank coverage, construct normal crossings, compute pole order, or
extract RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

private theorem map_withDensity_comp_of_aemeasurable
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {η : Measure α} {f : α → β} {g : β → ℝ≥0∞}
    (hf : AEMeasurable f η)
    (hg : AEMeasurable g (Measure.map f η)) :
    Measure.map f (η.withDensity (fun x ↦ g (f x))) =
      (Measure.map f η).withDensity g := by
  ext t ht
  have hf_density :
      AEMeasurable f (η.withDensity (fun x ↦ g (f x))) :=
    hf.mono_ac (withDensity_absolutelyContinuous _ _)
  have hpre : NullMeasurableSet (f ⁻¹' t) η :=
    hf.nullMeasurableSet_preimage ht
  rw [Measure.map_apply_of_aemeasurable hf_density ht,
    withDensity_apply _ ht, withDensity_apply₀ _ hpre]
  calc
    ∫⁻ x in f ⁻¹' t, g (f x) ∂η =
        ∫⁻ x, (f ⁻¹' t).indicator (fun x ↦ g (f x)) x ∂η := by
          rw [lintegral_indicator₀ hpre]
    _ = ∫⁻ x, (t.indicator g) (f x) ∂η := by
          rfl
    _ = ∫⁻ y, t.indicator g y ∂Measure.map f η := by
          exact (lintegral_map' (hg.indicator ht) hf).symm
    _ = ∫⁻ y in t, g y ∂Measure.map f η := by
          rw [lintegral_indicator ht]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- A locally bounded density on the chart-produced source-image base measure
feeds into the retained-passive residual-source hypotheses.

The measure consumed by the conclusion is
`(Measure.map sourceChart (baseJ.restrict W)).withDensity sourceImageDensity`.
The theorem assumes only the local a.e. bound for this source-image density,
plus the measurability needed to identify this source-image measure with the
pushforward of the theta-domain density `sourceImageDensity ∘ sourceChart`.
It does not construct or identify an original source prior, determinant-chart
Haar measure, raw-order Haar measure, source-rank coverage, normal crossings,
pole order, or RLCT. -/
theorem exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        let localSource :=
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  sourceImageMeasure.restrict localSource = sourceImageMeasure ∧
                    (∀ᵐ E ∂ sourceImageMeasure.restrict localSource,
                        0 < aoyagiCoordinateSquareSum
                          (paperEndpointFixedBaseResidualBlockCoordinateMap
                            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
                      residualNegPowerIntegrableOn
                        (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
                        (fun E : EdgeFamily ↦ E) localSource sourceImageMeasure t := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart
  let sourceDensity :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        ℝ≥0∞ :=
    fun z ↦ sourceImageDensity (sourceChart z)
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, sourceDensity] using
          exists_open_residualSourceHypotheses_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceDensity passiveMeasure hpassive_lt_top
            Rres ht hRres hcrit) with
    ⟨W, hWopen, hz₀W, hresidual⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure localSource hsourceChart
    hsourceImageDensity Csrc hsourceImageDensity_le hCsrc
  have hsourceDensity_le :
      ∀ᵐ z ∂ baseJ.restrict W, sourceDensity z ≤ Csrc := by
    exact ae_of_ae_map hsourceChart hsourceImageDensity_le
  let thetaSourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    baseJ.withDensity sourceDensity
  let thetaSourceImage : Measure EdgeFamily :=
    Measure.map sourceChart (thetaSourceMeasure.restrict W)
  have hmap_density : thetaSourceImage = sourceImageMeasure := by
    have hmap :
        Measure.map sourceChart
            ((baseJ.restrict W).withDensity
              (fun z ↦ sourceImageDensity (sourceChart z))) =
          (Measure.map sourceChart (baseJ.restrict W)).withDensity
            sourceImageDensity :=
      map_withDensity_comp_of_aemeasurable hsourceChart hsourceImageDensity
    calc
      thetaSourceImage =
          Measure.map sourceChart
            ((baseJ.restrict W).withDensity
              (fun z ↦ sourceImageDensity (sourceChart z))) := by
            simp [thetaSourceImage, thetaSourceMeasure, sourceDensity,
              restrict_withDensity hWopen.measurableSet]
      _ = sourceImageMeasure := by
            simpa [sourceImageBase, sourceImageMeasure] using hmap
  have hsocket :
      thetaSourceImage.restrict localSource = thetaSourceImage ∧
        (∀ᵐ E ∂ thetaSourceImage.restrict localSource,
            0 < aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) E)) ∧
          residualNegPowerIntegrableOn
            (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
            (fun E : EdgeFamily ↦ E) localSource thetaSourceImage t := by
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
      jacobianDensity, baseJ, sourceDensity, thetaSourceMeasure,
      thetaSourceImage, EdgeFamily, sourceChart, localSource] using
      hresidual (Csrc := Csrc) hsourceDensity_le hCsrc
  simpa [hmap_density] using hsocket

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-stratum finite-integral handoff for a bounded density on the
chart-produced source-image base measure.

This is the source-image analogue of the theta-domain bounded-density
finite-integral theorem.  The caller supplies a density on
`Measure.map sourceChart (baseJ.restrict W)`, an a.e. upper bound for that
density, and the measurability needed to rewrite the theta-domain pushforward.
It does not construct or identify an original source prior, determinant-chart
Haar measure, raw-order Haar measure, source-rank coverage, normal crossings,
pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss density :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c C : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (hC : 0 ≤ C) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          0 ≤ density (x, u)) →
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          density (x, u) ≤ C) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                      ENNReal.ofReal
                        ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                          (fun u ↦
                            (loss (z.1, u)) ^
                                (-(t +
                                  (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                              density (z.1, u)) z.2) ∂
                    (sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart base ρreg sourceStratum
    hloss hdensity_nonneg hdensity_le
  let sourceDensity :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        ℝ≥0∞ :=
    fun z ↦ sourceImageDensity (sourceChart z)
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, base, ρreg,
          sourceStratum, sourceDensity] using
          exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_puncturedSector_yNext_of_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (density := density) (t := t) (R := R)
            (c := c) (C := C)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceDensity passiveMeasure
            hpassive_lt_top Rres hR hc hC ht hRres hcrit hloss
            hdensity_nonneg hdensity_le) with
    ⟨W, hWopen, hz₀W, hfinite⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  have hsourceDensity_le :
      ∀ᵐ z ∂ baseJ.restrict W, sourceDensity z ≤ Csrc := by
    exact ae_of_ae_map hsourceChart hsourceImageDensity_le
  let thetaSourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    baseJ.withDensity sourceDensity
  let thetaSourceImage : Measure EdgeFamily :=
    Measure.map sourceChart (thetaSourceMeasure.restrict W)
  have hmap_density : thetaSourceImage = sourceImageMeasure := by
    have hmap :
        Measure.map sourceChart
            ((baseJ.restrict W).withDensity
              (fun z ↦ sourceImageDensity (sourceChart z))) =
          (Measure.map sourceChart (baseJ.restrict W)).withDensity
            sourceImageDensity :=
      map_withDensity_comp_of_aemeasurable hsourceChart hsourceImageDensity
    calc
      thetaSourceImage =
          Measure.map sourceChart
            ((baseJ.restrict W).withDensity
              (fun z ↦ sourceImageDensity (sourceChart z))) := by
            simp [thetaSourceImage, thetaSourceMeasure, sourceDensity,
              restrict_withDensity hWopen.measurableSet]
      _ = sourceImageMeasure := by
            simpa [sourceImageBase, sourceImageMeasure] using hmap
  have hfinite_theta :
      ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
        (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
          ENNReal.ofReal
            ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
              (fun u ↦
                (loss (z.1, u)) ^
                    (-(t +
                      (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)) *
                  density (z.1, u)) z.2) ∂
        (thetaSourceImage.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
      jacobianDensity, baseJ, sourceDensity, thetaSourceMeasure,
      thetaSourceImage, EdgeFamily, sourceChart, base, ρreg, sourceStratum] using
      hfinite (Csrc := Csrc) hsourceDensity_le hCsrc
  simpa [hmap_density] using hfinite_theta

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Full p.13 product-measure domination handoff for a source-image density.

The returned source-image p.13 product measure is
`(sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν`, so it includes the
regular variables, not only the passive-theta source image.  Any external
measure on this full product coordinate space dominated by a finite scalar
multiple of that product measure inherits the finite loss-power integral.

This theorem still does not prove that an original DLN prior has such a
domination, nor does it prove Haar transport, source-rank coverage, normal
crossings, pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    ∀ {externalProductMeasure :
                        Measure (EdgeFamily × EuclideanSpace ℝ ρreg)}
                      {Cext : ℝ≥0∞},
                      externalProductMeasure ≤
                          Cext •
                            (sourceImageMeasure.restrict
                              (U ∩ sourceStratum)).prod ν →
                        Cext < ∞ →
                          (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                            ENNReal.ofReal
                              ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                (fun u ↦
                                  (loss (z.1, u)) ^
                                    (-(t +
                                      (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) /
                                        2))) z.2) ∂
                          externalProductMeasure) < ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart base ρreg sourceStratum hloss
  let oneDensity : EdgeFamily × EuclideanSpace ℝ ρreg → ℝ := fun _ ↦ 1
  have hone_nonneg :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            0 ≤ oneDensity (x, u) := by
    exact Filter.Eventually.of_forall fun _ _ _ ↦ zero_le_one
  have hone_le :
      ∀ᶠ x in nhdsWithin base sourceStratum,
        ∀ u : EuclideanSpace ℝ ρreg,
          u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
            oneDensity (x, u) ≤ 1 := by
    exact Filter.Eventually.of_forall fun _ _ _ ↦ le_rfl
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, base, ρreg,
          sourceStratum, oneDensity] using
          exists_open_lintegral_ofReal_loss_rpow_neg_mul_density_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_ae_le_const_globalWithDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (density := oneDensity) (t := t) (R := R)
            (c := c) (C := 1)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top Rres hR hc zero_le_one ht hRres hcrit hloss
            hone_nonneg hone_le) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  rcases
      hsocket hsourceChart hsourceImageDensity
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  refine ⟨U, hUopen, hbaseU, ?_⟩
  intro externalProductMeasure Cext hdom hCext
  have hfinite_base :
      (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
        ENNReal.ofReal
          ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
            (fun u ↦
              (loss (z.1, u)) ^
                (-(t + (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) / 2)))
            z.2) ∂
        (sourceImageMeasure.restrict (U ∩ sourceStratum)).prod ν) < ∞ := by
    simpa [oneDensity] using hfinite
  exact lintegral_lt_top_of_measure_le_smul hdom hCext hfinite_base

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-level external-measure bounded-density handoff for the full p.13
product measure.

This theorem is the source-measure version of
`..._externalProductMeasure_le_smul_...`: instead of asking the caller for
domination of an arbitrary product measure, it accepts an explicit external
source measure whose restriction to the returned `U ∩ sourceStratum` is a
bounded-density perturbation of the chart-produced source-image measure.  The
product domination is then derived by measure theory.

The equality and density bound for `externalSourceMeasure` remain explicit.
The theorem does not identify an original DLN prior, prove source-rank
coverage, Haar transport, normal crossings, pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {externalSourceMeasure : Measure EdgeFamily}
                        {externalDensity : EdgeFamily → ℝ≥0∞} {Cext : ℝ≥0∞},
                        externalSourceMeasure.restrict sourceLocal =
                            (sourceImageMeasure.withDensity externalDensity).restrict
                              sourceLocal →
                          (∀ᵐ E ∂ sourceImageMeasure.restrict sourceLocal,
                            externalDensity E ≤ Cext) →
                          Cext < ∞ →
                            (∫⁻ z : EdgeFamily × EuclideanSpace ℝ ρreg,
                              ENNReal.ofReal
                                ((Metric.ball (0 : EuclideanSpace ℝ ρreg) R).indicator
                                  (fun u ↦
                                    (loss (z.1, u)) ^
                                      (-(t +
                                        (aoyagiTheorem2RegularVariableCount 2 H r : ℝ) /
                                          2))) z.2) ∂
                              (externalSourceMeasure.restrict sourceLocal).prod ν) < ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart base ρreg sourceStratum hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, base, ρreg,
          sourceStratum] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  rcases
      hsocket hsourceChart hsourceImageDensity
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  have hsourceStratum_meas : MeasurableSet sourceStratum := by
    dsimp [sourceStratum]
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W₂) (B := B₂) (Cedge := fun E : EdgeFamily ↦ E)
        (r := r) (rEdge := rEdge)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
  let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
  have hsourceLocal_meas : MeasurableSet sourceLocal := by
    exact hUopen.measurableSet.inter hsourceStratum_meas
  refine ⟨U, hUopen, hbaseU, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [sourceLocal]
  · intro externalSourceMeasure externalDensity Cext hsource_eq hdensity_le hCext
    have hsource_le :
        externalSourceMeasure.restrict sourceLocal ≤
          Cext • sourceImageMeasure.restrict sourceLocal := by
      rw [hsource_eq]
      exact
        restrict_withDensity_le_smul_restrict_of_ae_le
          (μ := sourceImageMeasure) (f := externalDensity)
          (s := sourceLocal) (c := Cext) hsourceLocal_meas hdensity_le
    have hprod_le :
        (externalSourceMeasure.restrict sourceLocal).prod ν ≤
          Cext • (sourceImageMeasure.restrict sourceLocal).prod ν :=
      prod_le_smul_prod_of_le_smul_left (η := ν) hsource_le
    exact
      (by
        simpa [sourceLocal] using
          hfinite
            (externalProductMeasure := (externalSourceMeasure.restrict sourceLocal).prod ν)
            (Cext := Cext) hprod_le hCext)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Chart-piece-restricted external-source bounded-density handoff for the
full p.13 product measure.

This is a localized variant of the source-level external-measure handoff: the
external source measure is compared with the chart-produced source-image
measure only on an arbitrary measurable piece contained in the returned
`sourceLocal = U ∩ sourceStratum`.  This is the socket needed for callers
working on a measurable chart image or subimage without proving that the chart
image equals the whole local source.

The equality and density bound on the chosen piece remain explicit.  The
theorem does not identify an original DLN prior, prove chart-image
measurability, source-rank coverage, source-image equality, Haar transport,
normal crossings, pole order, or RLCT. -/
theorem exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalSourceMeasure_restrict_chartPiece_eq_withDensity_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] [DecidableEq τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    {hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂))}
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta.PassiveFields
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀)
    {H : ℕ → ℕ} {r : ℕ} {rEdge : Fin 2 → ℕ}
    (sourceData :
      PaperEndpointFixedBaseRegularCoordinateSourceData
        (K := ℝ) W₂ B₂ U₀ hU₀
        ((fun p : Fin 2 ↦
          LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)) :
          ∀ p : Fin 2,
            reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
        (fun E :
            (∀ p : Fin 2,
              reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E)
        H r rEdge)
    (sourceImageDensity :
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
        ℝ≥0∞)
    (passiveMeasure :
      Measure
        (Case2PassiveTheta.PassiveFields
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {ν :
      Measure
        (EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)))}
    [ν.IsAddHaarMeasure] [SFinite ν]
    {loss :
      (∀ p : Fin 2,
        reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ×
        EuclideanSpace ℝ
          (AoyagiRegularBlockCoordinateIndex
            (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)) → ℝ}
    {t R c : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (hR : 0 < R) (hc : 0 < c) (ht : 0 < t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let signedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      Measure.pi
        (fun i : Case2PassiveTheta.Center n S J =>
          volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      signedBox.withDensity
        (fun y : Case2PassiveTheta.Center n S J → ℝ =>
          ENNReal.ofReal (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let passiveSource :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let jacobianDensity :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ℝ≥0∞ :=
      fun z ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) (Y z))
    let baseJ :
        Measure
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
      passiveSource.withDensity jacobianDensity
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      case2PassiveThetaEndpointSourceChart W₂ B₂ n hS hcont hnext hU₀ eNext e
    let base : EdgeFamily :=
      fun p : Fin 2 ↦ LinearMap.toContinuousLinearMap (reverseEdge W₂ B₂ p)
    let ρreg :=
      AoyagiRegularBlockCoordinateIndex
        (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0)
    let sourceStratum :=
      paperEndpointFixedBaseSourceRankStratum
        (K := ℝ) W₂ B₂ (fun E : EdgeFamily ↦ E) r rEdge
    (∀ᶠ x in nhdsWithin base sourceStratum,
      ∀ u : EuclideanSpace ℝ ρreg,
        u ∈ Metric.ball (0 : EuclideanSpace ℝ ρreg) R →
          c * (aoyagiCoordinateSquareSum
              (paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) x) +
            aoyagiCoordinateSquareSum (fun i ↦ u i)) ≤ loss (x, u)) →
    ∃ W :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen W ∧ z₀ ∈ W ∧
        let sourceImageBase : Measure EdgeFamily :=
          Measure.map sourceChart (baseJ.restrict W)
        let sourceImageMeasure : Measure EdgeFamily :=
          sourceImageBase.withDensity sourceImageDensity
        AEMeasurable sourceChart (baseJ.restrict W) →
          AEMeasurable sourceImageDensity sourceImageBase →
            ∀ {Csrc : ℝ≥0∞},
              (∀ᵐ E ∂ sourceImageBase, sourceImageDensity E ≤ Csrc) →
                Csrc < ∞ →
                  ∃ U : Set EdgeFamily, IsOpen U ∧ base ∈ U ∧
                    let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
                    MeasurableSet sourceLocal ∧
                      ∀ {chartPiece : Set EdgeFamily},
                        MeasurableSet chartPiece →
                          chartPiece ⊆ sourceLocal →
                            ∀ {externalSourceMeasure : Measure EdgeFamily}
                              {externalDensity : EdgeFamily → ℝ≥0∞} {Cext : ℝ≥0∞},
                              externalSourceMeasure.restrict chartPiece =
                                  (sourceImageMeasure.withDensity externalDensity).restrict
                                    chartPiece →
                                (∀ᵐ E ∂ sourceImageMeasure.restrict chartPiece,
                                  externalDensity E ≤ Cext) →
                                Cext < ∞ →
                                  (∫⁻ z :
                                    EdgeFamily × EuclideanSpace ℝ ρreg,
                                    ENNReal.ofReal
                                      ((Metric.ball
                                        (0 : EuclideanSpace ℝ ρreg) R).indicator
                                        (fun u ↦
                                          (loss (z.1, u)) ^
                                            (-(t +
                                              (aoyagiTheorem2RegularVariableCount
                                                  2 H r : ℝ) /
                                                2))) z.2) ∂
                                    (externalSourceMeasure.restrict chartPiece).prod ν) <
                                      ∞ := by
  intro center pivotNext signedBox weightedBox passiveSource Y jacobianDensity
    baseJ EdgeFamily sourceChart base ρreg sourceStratum hloss
  rcases
      (by
        simpa [center, pivotNext, signedBox, weightedBox, passiveSource, Y,
          jacobianDensity, baseJ, EdgeFamily, sourceChart, base, ρreg,
          sourceStratum] using
          exists_open_lintegral_ofReal_loss_rpow_neg_p13RegularCoordinates_lt_top_of_case2PassiveThetaEndpointSourceChart_sourceImage_withDensity_externalProductMeasure_le_smul_jacobian_passiveProductMeasure_finiteMass_sourceStratum_bounds
            (ν := ν) (loss := loss) (t := t) (R := R) (c := c)
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ sourceData sourceImageDensity passiveMeasure
            hpassive_lt_top Rres hR hc ht hRres hcrit hloss) with
    ⟨W, hWopen, hz₀W, hsocket⟩
  refine ⟨W, hWopen, hz₀W, ?_⟩
  intro sourceImageBase sourceImageMeasure hsourceChart hsourceImageDensity
    Csrc hsourceImageDensity_le hCsrc
  rcases
      hsocket hsourceChart hsourceImageDensity
        (Csrc := Csrc) hsourceImageDensity_le hCsrc with
    ⟨U, hUopen, hbaseU, hfinite⟩
  have hsourceStratum_meas : MeasurableSet sourceStratum := by
    dsimp [sourceStratum]
    exact
      measurableSet_paperEndpointFixedBaseSourceRankStratum_of_continuous
        (W := W₂) (B := B₂) (Cedge := fun E : EdgeFamily ↦ E)
        (r := r) (rEdge := rEdge)
        (by simpa [EdgeFamily] using
          (continuous_id : Continuous (fun E : EdgeFamily ↦ E)))
  let sourceLocal : Set EdgeFamily := U ∩ sourceStratum
  have hsourceLocal_meas : MeasurableSet sourceLocal := by
    exact hUopen.measurableSet.inter hsourceStratum_meas
  refine ⟨U, hUopen, hbaseU, ?_⟩
  refine ⟨?_, ?_⟩
  · simpa [sourceLocal]
  · intro chartPiece hchartPiece_meas hchartPiece_sub externalSourceMeasure
      externalDensity Cext hsource_eq hdensity_le hCext
    have hsource_le :
        externalSourceMeasure.restrict chartPiece ≤
          Cext • sourceImageMeasure.restrict sourceLocal := by
      rw [hsource_eq]
      exact
        restrict_withDensity_le_smul_restrict_of_ae_le_of_subset
          (μ := sourceImageMeasure) (f := externalDensity)
          (s := chartPiece) (t := sourceLocal) (c := Cext)
          hchartPiece_meas hchartPiece_sub hdensity_le
    have hprod_le :
        (externalSourceMeasure.restrict chartPiece).prod ν ≤
          Cext • (sourceImageMeasure.restrict sourceLocal).prod ν :=
      prod_le_smul_prod_of_le_smul_left (η := ν) hsource_le
    exact
      (by
        simpa [sourceLocal] using
          hfinite
            (externalProductMeasure := (externalSourceMeasure.restrict chartPiece).prod ν)
            (Cext := Cext) hprod_le hCext)

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre
