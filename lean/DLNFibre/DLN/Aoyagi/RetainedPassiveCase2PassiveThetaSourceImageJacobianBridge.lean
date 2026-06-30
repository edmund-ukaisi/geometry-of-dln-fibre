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

end PaperEndpointFixedBaseRegularCoordinateSourceData
end Aoyagi
end DLN
end DLNFibre
