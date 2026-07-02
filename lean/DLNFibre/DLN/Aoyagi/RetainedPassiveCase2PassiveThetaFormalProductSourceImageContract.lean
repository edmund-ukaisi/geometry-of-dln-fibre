import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage

/-!
# Case 2 formal-product/source-image contract

This file packages the A2 bounded-density socket for comparing Aoyagi's p.13
formal-product chart measure with the concrete Case 2 source-image reference.
It deliberately stores the density identity and density bound as fields.  The
file proves only the measure-theoretic consequences of those fields; it does
not prove the Jacobian calculation, source-image coverage, Haar transport,
normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

namespace DLNFibre
namespace DLN
namespace Aoyagi

open MeasureTheory
open scoped ENNReal

/-- A local A2 p.13 formal-product/source-image bounded-density contract.

The intended `sourceChart` is the concrete Case 2 passive-theta endpoint
source chart, and `formalProductMeasure` is the p.13 formal-product chart
measure on edge families.  The record only packages the local chart facts and
the supplied density identity/bound.  It does not assert that the density is
already computed from Aoyagi's Jacobian formula. -/
structure A2Case2FormalProductSourceImagePieceContract
    (Theta E : Type*) [MeasurableSpace Theta] [TopologicalSpace Theta]
    [MeasurableSpace E] [TopologicalSpace E] where
  sourceChart : Theta → E
  readback : E → Theta
  thetaReference : Measure Theta
  V : Set Theta
  chartPiece : Set E
  formalProductMeasure : Measure E
  density : E → ℝ≥0∞
  bound : ℝ≥0∞
  measurable_V : MeasurableSet V
  measurable_chartPiece : MeasurableSet chartPiece
  measurable_image : MeasurableSet (sourceChart '' V)
  chartPiece_subset_image : chartPiece ⊆ sourceChart '' V
  source_contOn : ContinuousOn sourceChart V
  source_injOn : Set.InjOn sourceChart V
  left_inv : ∀ theta ∈ V, readback (sourceChart theta) = theta
  formalProduct_eq_withDensity :
    formalProductMeasure.restrict chartPiece =
      ((Measure.map sourceChart (thetaReference.restrict V)).withDensity density).restrict
        chartPiece
  density_le_bound :
    ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict chartPiece,
      density E ≤ bound

namespace A2Case2FormalProductSourceImagePieceContract

variable {Theta E : Type*} [MeasurableSpace Theta] [TopologicalSpace Theta]
  [MeasurableSpace E] [TopologicalSpace E]

/-- The chart-produced source-image reference attached to the contract. -/
def sourceRef
    (C : A2Case2FormalProductSourceImagePieceContract Theta E) : Measure E :=
  Measure.map C.sourceChart (C.thetaReference.restrict C.V)

/-- The bounded-density contract gives the formal-product/source-image
domination required by the same-shrink original-volume bridge. -/
theorem formalProductMeasure_restrict_le_smul_sourceRef
    (C : A2Case2FormalProductSourceImagePieceContract Theta E) :
    C.formalProductMeasure.restrict C.chartPiece ≤ C.bound • C.sourceRef := by
  calc
    C.formalProductMeasure.restrict C.chartPiece =
        (C.sourceRef.withDensity C.density).restrict C.chartPiece := by
          simpa [sourceRef] using C.formalProduct_eq_withDensity
    _ ≤ C.bound • C.sourceRef := by
          exact restrict_withDensity_le_smul_of_ae_le (μ := C.sourceRef)
            (s := C.chartPiece) (f := C.density) (c := C.bound)
            C.measurable_chartPiece
            (by simpa [sourceRef] using C.density_le_bound)

set_option linter.style.longLine false in
/-- The same contract gives the readback domination used by p.13 readback
finite-integral sockets, after enlarging the theta restriction from `V` to any
containing set `W`. -/
theorem aemeasurable_readback_and_map_readback_restrict_le_smul_thetaReference_restrict
    [BorelSpace Theta] [PolishSpace Theta] [BorelSpace E] [T2Space E]
    (C : A2Case2FormalProductSourceImagePieceContract Theta E)
    {W : Set Theta} (hVW : C.V ⊆ W) :
    AEMeasurable C.readback (C.formalProductMeasure.restrict C.chartPiece) ∧
      Measure.map C.readback (C.formalProductMeasure.restrict C.chartPiece) ≤
        C.bound • C.thetaReference.restrict W := by
  exact
    aemeasurable_readback_and_measure_map_readback_restrict_piece_le_smul_restrict_superset_of_restrict_eq_withDensity_of_continuousOn_injOn
      C.sourceChart C.readback C.formalProductMeasure C.thetaReference C.V W
      C.chartPiece C.density C.bound C.measurable_V C.measurable_chartPiece
      hVW C.source_contOn C.source_injOn C.left_inv
      C.formalProduct_eq_withDensity C.density_le_bound

end A2Case2FormalProductSourceImagePieceContract

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The enlarged following-factor endpoint chart supplies all local
source-image fields of the A2 bounded-density contract.

The density identity and a.e. bound remain explicit hypotheses.  This theorem
only packages the local open set, readback left inverse, injectivity,
continuity, and measurable source-image facts from the enlarged source chart;
it does not prove a Jacobian formula, Haar transport, source-rank coverage,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart
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
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [T2Space
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z₀ :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z
    let readback : EdgeFamily →
        Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V, (retainedData z).detChart) ∧
          ∀ thetaReference :
            Measure
              (Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          ∀ formalProductMeasure : Measure EdgeFamily,
          ∀ chartPiece : Set EdgeFamily,
          ∀ density : EdgeFamily → ℝ≥0∞,
          ∀ bound : ℝ≥0∞,
            MeasurableSet chartPiece →
              chartPiece ⊆ sourceChart '' V →
                formalProductMeasure.restrict chartPiece =
                    ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
                      density).restrict chartPiece →
                  (∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
                      chartPiece, density E ≤ bound) →
                    ∃ C :
                      A2Case2FormalProductSourceImagePieceContract
                        (Case2PassiveThetaWithFollowingFactor
                          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
                        EdgeFamily,
                      C.sourceChart = sourceChart ∧
                        C.readback = readback ∧
                          C.thetaReference = thetaReference ∧
                            C.V = V ∧
                              C.chartPiece = chartPiece ∧
                                C.formalProductMeasure = formalProductMeasure ∧
                                  C.density = density ∧ C.bound = bound := by
  intro EdgeFamily retainedData sourceChart readback
  rcases
      exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hdetV, hleftV, hsource_inj, hsource_contOn,
      hsource_image⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_, ?_⟩
  · intro z hz
    simpa [retainedData] using hdetV z hz
  · intro thetaReference formalProductMeasure chartPiece density bound
      hchartPiece hchartPiece_sub heq hdensity_le
    let C :
        A2Case2FormalProductSourceImagePieceContract
          (Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
          EdgeFamily :=
      { sourceChart := sourceChart
        readback := readback
        thetaReference := thetaReference
        V := V
        chartPiece := chartPiece
        formalProductMeasure := formalProductMeasure
        density := density
        bound := bound
        measurable_V := hVopen.measurableSet
        measurable_chartPiece := hchartPiece
        measurable_image := hsource_image
        chartPiece_subset_image := hchartPiece_sub
        source_contOn := hsource_contOn
        source_injOn := hsource_inj
        left_inv := hleftV
        formalProduct_eq_withDensity := heq
        density_le_bound := hdensity_le }
    refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
