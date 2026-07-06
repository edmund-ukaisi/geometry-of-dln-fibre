import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaFormalProductSourceReference
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
open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

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

/-- Convert a theta-side weighted source-chart pushforward into the
edge-side `withDensity` equality expected by the contract.

This is measure bookkeeping only: the theta-side equality and the density are
still supplied hypotheses. -/
theorem formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity
    {Theta E : Type*} [MeasurableSpace Theta] [MeasurableSpace E]
    (sourceChart : Theta → E) (thetaReference : Measure Theta)
    (V : Set Theta) (targetPiece : Set E)
    (formalProductMeasure : Measure E) (density : E → ℝ≥0∞)
    (hV : MeasurableSet V)
    (hsourceChart :
      AEMeasurable sourceChart (thetaReference.restrict V))
    (hdensity :
      AEMeasurable density
        (Measure.map sourceChart (thetaReference.restrict V)))
    (heq :
      formalProductMeasure.restrict targetPiece =
        (Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ density (sourceChart theta))).restrict V)).restrict
          targetPiece) :
    formalProductMeasure.restrict targetPiece =
      (((Measure.map sourceChart (thetaReference.restrict V)).withDensity
        density).restrict targetPiece) := by
  have hfactor :
      ∀ᵐ theta ∂thetaReference.restrict V,
        (fun theta ↦ density (sourceChart theta)) theta =
          density (sourceChart theta) :=
    Filter.Eventually.of_forall fun _ ↦ rfl
  have hpush :
      Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ density (sourceChart theta))).restrict V) =
        (Measure.map sourceChart (thetaReference.restrict V)).withDensity
          density :=
    measure_map_restrict_withDensity_eq_withDensity_map_of_ae_eq
      (thetaMeasure := thetaReference) (V := V) (rawMap := sourceChart)
      (thetaDensity := fun theta ↦ density (sourceChart theta))
      (rawDensity := density) hV hsourceChart hdensity hfactor
  calc
    formalProductMeasure.restrict targetPiece =
        (Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ density (sourceChart theta))).restrict V)).restrict
          targetPiece := heq
    _ =
        (((Measure.map sourceChart (thetaReference.restrict V)).withDensity
          density).restrict targetPiece) := by
          rw [hpush]

variable {Theta E : Type*} [MeasurableSpace Theta] [TopologicalSpace Theta]
  [MeasurableSpace E] [TopologicalSpace E]

/-- The chart-produced source-image reference attached to the contract. -/
def sourceRef
    (C : A2Case2FormalProductSourceImagePieceContract Theta E) : Measure E :=
  Measure.map C.sourceChart (C.thetaReference.restrict C.V)

set_option linter.style.longLine false in
/-- Build the bounded-density contract from a theta-side weighted
source-chart pushforward identity.

This is the constructor form of
`formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity`.
The weighted identity and the density bound remain supplied hypotheses. -/
theorem exists_of_restrict_eq_map_sourceChart_withDensity
    (sourceChart : Theta → E) (readback : E → Theta)
    (thetaReference : Measure Theta) (V : Set Theta)
    (chartPiece : Set E) (formalProductMeasure : Measure E)
    (density : E → ℝ≥0∞) (bound : ℝ≥0∞)
    (hV : MeasurableSet V)
    (hchartPiece : MeasurableSet chartPiece)
    (himage : MeasurableSet (sourceChart '' V))
    (hchartPiece_sub : chartPiece ⊆ sourceChart '' V)
    (hsource_contOn : ContinuousOn sourceChart V)
    (hsource_injOn : Set.InjOn sourceChart V)
    (hleft : ∀ theta ∈ V, readback (sourceChart theta) = theta)
    (hsourceChart :
      AEMeasurable sourceChart (thetaReference.restrict V))
    (hdensity :
      AEMeasurable density
        (Measure.map sourceChart (thetaReference.restrict V)))
    (heq :
      formalProductMeasure.restrict chartPiece =
        (Measure.map sourceChart
          ((thetaReference.withDensity
            (fun theta ↦ density (sourceChart theta))).restrict V)).restrict
          chartPiece)
    (hdensity_le :
      ∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
        chartPiece, density E ≤ bound) :
    ∃ C : A2Case2FormalProductSourceImagePieceContract Theta E,
      C.sourceChart = sourceChart ∧
        C.readback = readback ∧
          C.thetaReference = thetaReference ∧
            C.V = V ∧
              C.chartPiece = chartPiece ∧
                C.formalProductMeasure = formalProductMeasure ∧
                  C.density = density ∧ C.bound = bound := by
  have hformal :
      formalProductMeasure.restrict chartPiece =
        (((Measure.map sourceChart (thetaReference.restrict V)).withDensity
          density).restrict chartPiece) :=
    formalProduct_restrict_eq_withDensity_of_restrict_eq_map_sourceChart_withDensity
      sourceChart thetaReference V chartPiece formalProductMeasure density
      hV hsourceChart hdensity heq
  let C : A2Case2FormalProductSourceImagePieceContract Theta E :=
    { sourceChart := sourceChart
      readback := readback
      thetaReference := thetaReference
      V := V
      chartPiece := chartPiece
      formalProductMeasure := formalProductMeasure
      density := density
      bound := bound
      measurable_V := hV
      measurable_chartPiece := hchartPiece
      measurable_image := himage
      chartPiece_subset_image := hchartPiece_sub
      source_contOn := hsource_contOn
      source_injOn := hsource_injOn
      left_inv := hleft
      formalProduct_eq_withDensity := hformal
      density_le_bound := hdensity_le }
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- The proof combines two large local Case 2 chart packages and unfolds their concrete p.13 interfaces.
/-- Conditional with-following A2 bounded-density contract from a raw-source
pushforward identity.

After one local shrink, if the enlarged passive-theta raw-order map pushes the
chosen theta reference to the raw-order source-recursive restriction of a raw
Haar measure, then the p.13 formal-product chart measure gives an
`A2Case2FormalProductSourceImagePieceContract` with constant density `1` and
bound `1`.

The raw-pushforward identity, chart-piece measurability, source-image
membership, and p.13 source-set membership remain explicit hypotheses.  This
does not prove raw Haar transport, source-image coverage, original-prior
transport, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource
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
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
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
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
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
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        ∀ thetaReference :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
        ∀ chartPiece : Set EdgeFamily,
          MeasurableSet chartPiece →
            chartPiece ⊆ sourceChart '' V →
              chartPiece ⊆ p13SourceSet →
                Measure.map rawMap (thetaReference.restrict V) =
                  rawHaar.restrict rawSourceSet →
                  let formalProductMeasure : Measure EdgeFamily :=
                    Measure.map
                      (fun z : RawTuple ↦
                        rawChart
                          (topologyTupleEdgeRawOrder
                            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                            (κ' := throughSubspaceEndpointComplementIndex
                              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                      ((rawHaar.restrict rawDetChart).withDensity
                        (fun z : RawTuple ↦
                          ENNReal.ofReal
                            (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                              (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                              (κ' := throughSubspaceEndpointComplementIndex
                                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                  let oneDensity : EdgeFamily → ℝ≥0∞ := fun _ ↦ 1
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
                                C.density = oneDensity ∧
                                  C.bound = (1 : ℝ≥0∞) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawDetChart rawSourceSet
    p13SourceSet rawChart
  rcases
      exists_open_subset_continuousOn_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V₀, hV₀open, hz₀V₀, hV₀G, _hdetV₀, hleftV₀, hsource_injV₀,
      hsource_contOnV₀, _hsource_imageV₀⟩
  rcases
      exists_open_subset_formalProductMeasure_restrict_chartPiece_eq_withDensity_one_sourceReference_of_case2PassiveThetaWithFollowingFactor_rawMap_eq_restrict_rawSource
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ V₀ hV₀open hz₀V₀ with
    ⟨V, hVopen, hz₀V, hVV₀, hformal⟩
  have hVG : V ⊆ G := fun z hz ↦ hV₀G (hVV₀ hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    exact hleftV₀ z (hVV₀ hz)
  have hsource_injV : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    exact hsource_injV₀ (hVV₀ hz) (hVV₀ hz') hsrc
  have hsource_contOnV : ContinuousOn sourceChart V :=
    hsource_contOnV₀.mono hVV₀
  have hsource_imageV : MeasurableSet (sourceChart '' V) :=
    hVopen.measurableSet.image_of_continuousOn_injOn
      hsource_contOnV hsource_injV
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_image hchartPiece_p13 hraw_push formalProductMeasure oneDensity
  have hformal' :
      formalProductMeasure.restrict chartPiece =
          ((Measure.map sourceChart (thetaReference.restrict V)).withDensity
            oneDensity).restrict chartPiece ∧
        (∀ᵐ E ∂(Measure.map sourceChart (thetaReference.restrict V)).restrict
          chartPiece, oneDensity E ≤ (1 : ℝ≥0∞)) := by
    simpa [RawTuple, EdgeFamily, sourceChart, rawMap, rawDetChart, rawSourceSet,
      p13SourceSet, rawChart, formalProductMeasure, oneDensity] using
      hformal thetaReference rawHaar chartPiece hchartPiece hchartPiece_p13
        hraw_push
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
      density := oneDensity
      bound := 1
      measurable_V := hVopen.measurableSet
      measurable_chartPiece := hchartPiece
      measurable_image := hsource_imageV
      chartPiece_subset_image := hchartPiece_image
      source_contOn := hsource_contOnV
      source_injOn := hsource_injV
      left_inv := hleftV
      formalProduct_eq_withDensity := hformal'.1
      density_le_bound := hformal'.2 }
  refine ⟨C, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- This same-shrink wrapper combines the with-following image equality with
-- the raw-map contract package.
/-- Conditional with-following A2 bounded-density contract from a raw-source
pushforward identity, with chart-piece support stated in p.13/readback form.

The returned neighborhood `V` carries both the raw-map source-reference
contract and the local image equality
`sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V`.  Thus callers may supply
`chartPiece ⊆ p13SourceSet` and `chartPiece ⊆ readback ⁻¹' V` instead of a
separate `chartPiece ⊆ sourceChart '' V` proof.

The raw-pushforward identity remains a hypothesis.  This does not prove raw
Haar transport, the raw-map Jacobian, source-prior transport, normal crossings,
pole order, or RLCT extraction. -/
theorem exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource_chartPiece_subset_p13_readback
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
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [BorelSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [MeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [OpensMeasurableSpace
      (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)]
    [BorelSpace
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
    let RawTuple :=
      TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
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
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RawTuple :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawDetChart : Set RawTuple :=
      topologyTupleDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
    let p13SourceSet : Set EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V ∧
          ∀ thetaReference :
            Measure
              (Case2PassiveThetaWithFollowingFactor
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
          ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
          ∀ chartPiece : Set EdgeFamily,
            MeasurableSet chartPiece →
              chartPiece ⊆ p13SourceSet →
                chartPiece ⊆ readback ⁻¹' V →
                  Measure.map rawMap (thetaReference.restrict V) =
                    rawHaar.restrict rawSourceSet →
                    let formalProductMeasure : Measure EdgeFamily :=
                      Measure.map
                        (fun z : RawTuple ↦
                          rawChart
                            (topologyTupleEdgeRawOrder
                              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                              (κ' := throughSubspaceEndpointComplementIndex
                                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z))
                        ((rawHaar.restrict rawDetChart).withDensity
                          (fun z : RawTuple ↦
                            ENNReal.ofReal
                              (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
                                (M := 1) (ρ := Fin (Module.finrank ℝ U₀))
                                (κ' := throughSubspaceEndpointComplementIndex
                                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) z)))
                    let oneDensity : EdgeFamily → ℝ≥0∞ := fun _ ↦ 1
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
                                  C.density = oneDensity ∧
                                    C.bound = (1 : ℝ≥0∞) := by
  intro RawTuple EdgeFamily sourceChart readback rawMap rawDetChart rawSourceSet
    p13SourceSet rawChart
  rcases
      (by
        simpa [EdgeFamily, sourceChart, readback, p13SourceSet] using
          exists_open_subset_measurableSet_case2PassiveThetaWithFollowingFactorEndpointSourceChart_image_eq_p13SourceEdgeFamilySet_inter_readback_preimage
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ G hGopen hz₀G) with
    ⟨W, hWopen, hz₀W, hWG, _hdetW, _hpivotW, hleftW, _hsource_injW,
      _hsource_contOnW, _hsource_imageW, himageW⟩
  rcases
      (by
        simpa [RawTuple, EdgeFamily, sourceChart, readback, rawMap,
          rawDetChart, rawSourceSet, p13SourceSet, rawChart] using
          exists_open_subset_a2FormalProductSourceImagePieceContract_case2PassiveThetaWithFollowingFactorEndpointSourceChart_of_rawMap_eq_restrict_rawSource
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            z₀ hdet₀ hpivot₀ W hWopen hz₀W) with
    ⟨V, hVopen, hz₀V, hVW, hcontract⟩
  have hVG : V ⊆ G := fun z hz ↦ hWG (hVW hz)
  have hleftW' : ∀ z ∈ W, readback (sourceChart z) = z := by
    intro z hz
    have hz_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ W := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleftW z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hz_fields
  have himageV : sourceChart '' V = p13SourceSet ∩ readback ⁻¹' V :=
    sourceChart_image_eq_p13_readback_preimage_of_subset
      (sourceChart := sourceChart) (readback := readback)
      (V := V) (W := W) (p13SourceSet := p13SourceSet)
      himageW hVW hleftW'
  refine ⟨V, hVopen, hz₀V, hVG, himageV, ?_⟩
  intro thetaReference rawHaar _instRawHaar chartPiece hchartPiece
    hchartPiece_p13 hchartPiece_readback hraw_push formalProductMeasure oneDensity
  have hchartPiece_image : chartPiece ⊆ sourceChart '' V :=
    chartPiece_subset_sourceChart_image_of_subset_p13_readback
      (sourceChart := sourceChart) (readback := readback)
      (V := V) (p13SourceSet := p13SourceSet)
      (chartPiece := chartPiece) himageV hchartPiece_p13 hchartPiece_readback
  exact
    hcontract thetaReference rawHaar chartPiece hchartPiece hchartPiece_image
      hchartPiece_p13 hraw_push

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
