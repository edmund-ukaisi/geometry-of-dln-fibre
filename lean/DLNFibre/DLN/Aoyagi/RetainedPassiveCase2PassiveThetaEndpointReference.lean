import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceMeasure

/-!
# Case 2 passive theta endpoint reference measure

This file names the concrete coordinate-product reference measure on the full
Case 2 passive-theta source.  It is only a reference-measure and support layer:
it does not prove the endpoint determinant-chart change of variables, Haar
normalization, source-prior transport, normal crossings, pole order, or RLCT
extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

/-- Coordinate-product Lebesgue reference measure on a real matrix type,
aligned with the Pi measurable-space instance on matrix entries. -/
noncomputable def matrixEntryReferenceMeasure
    (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℝ) :=
  Measure.pi (fun _ : m => Measure.pi (fun _ : n => volume))

set_option linter.style.longLine false in
/-- Coordinate-product reference measure on the passive fields suppressed by
the reduced selected-entry section in Aoyagi Case 2. -/
noncomputable def case2PassiveThetaPassiveFieldReferenceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ) :
    Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
  let A1Measure : Measure (Fin 1 → Matrix ρ ρ ℝ) :=
    Measure.pi
      (fun _ : Fin 1 => matrixEntryReferenceMeasure ρ ρ)
  let F2Measure :
      Measure
        (∀ p : Fin 2,
          Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ) :=
    Measure.pi
      (fun p : Fin 2 =>
        matrixEntryReferenceMeasure ρ
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc))
  let A3Measure :
      Measure
        (∀ p : Fin 1,
          Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ) :=
    Measure.pi
      (fun p : Fin 1 =>
        matrixEntryReferenceMeasure
          (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ)
  let CtopMeasure : Measure (Matrix ρ ρ ℝ) :=
    matrixEntryReferenceMeasure ρ ρ
  let F3Measure :
      Measure
        (Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ) :=
    matrixEntryReferenceMeasure
      (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ
  A1Measure.prod (F2Measure.prod (A3Measure.prod (CtopMeasure.prod F3Measure)))

set_option linter.style.longLine false in
/-- Selected-entry signed-box measure on the successor residual center
coordinates. -/
noncomputable def case2PassiveThetaCenterSignedBoxMeasure
    (n : ℕ → ℕ) {S J : ℕ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta.Center n S J → ℝ) :=
  Measure.pi
    (fun i : Case2PassiveTheta.Center n S J =>
      volume.restrict (Set.Ioo (-(Rres i)) (Rres i)))

set_option linter.style.longLine false in
/-- Weighted selected-entry signed-box measure on the successor residual
center coordinates. -/
noncomputable def case2PassiveThetaCenterWeightedBoxMeasure
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta.Center n S J → ℝ) :=
  (case2PassiveThetaCenterSignedBoxMeasure n Rres).withDensity
    (fun y : Case2PassiveTheta.Center n S J → ℝ =>
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity
          (case2PassiveThetaPivotNext n hS hnext) y))

set_option linter.style.longLine false in
/-- Concrete passive-theta product reference measure: coordinate-product
Lebesgue reference on passive fields times the weighted selected-entry
signed-box reference on the residual center coordinates. -/
noncomputable def case2PassiveThetaReferenceSourceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
  (case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J).prod
    (case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres)

set_option linter.style.longLine false in
/-- Endpoint topology-tuple image measure of the concrete passive-theta
reference source restricted to a chosen local set.

This names the correct image-measure target for the current passive-theta
domain.  It is not unrestricted Haar on the full retained-passive determinant
chart. -/
noncomputable def case2PassiveThetaEndpointReferenceImageMeasure
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)) :
    Measure (TopologyTuple ρ κ' ℝ) :=
  let referenceSource :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  Measure.map Y (referenceSource.restrict Ω)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete passive-theta reference source is supported on the
determinant chart after restricting to any measurable determinant-sector
localization.

This is support only.  It does not prove that the endpoint pushforward is Haar,
absolutely continuous with bounded density, or dominated by a determinant-chart
Haar measure. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet : Ω ⊆ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    let referenceSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    (Measure.map Y (referenceSource.restrict Ω)).restrict rawDetChart =
      Measure.map Y (referenceSource.restrict Ω) := by
  intro referenceSource Y rawDetChart
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  simpa [referenceSource, Y, rawDetChart] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
      referenceSource Ω hΩ hΩdet hY

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named endpoint reference image measure is supported on the determinant
chart after determinant-sector localization.

This is the same support statement as
`measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector`,
but stated for the named image measure rather than an unfolded `Measure.map`.
It is not unrestricted determinant-chart Haar. -/
theorem case2PassiveThetaEndpointReferenceImageMeasure_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet : Ω ⊆ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J) :
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    endpointReferenceImage.restrict rawDetChart = endpointReferenceImage := by
  intro endpointReferenceImage rawDetChart
  simpa [endpointReferenceImage, rawDetChart,
    case2PassiveThetaEndpointReferenceImageMeasure] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ hΩdet

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Passive-field domination by the concrete coordinate reference pushes
forward to domination by the named endpoint reference image measure.

This is the honest replacement for an unrestricted determinant-chart Haar
target at the passive-theta level.  It assumes only domain-side passive-field
domination and concludes domination by the actual endpoint image measure of
the concrete reference source. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_passiveSource_restrict_le_smul_endpointReferenceImage_of_passiveMeasure_le_smul_reference
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    {d : ℝ≥0∞}
    (hpassive :
      passiveMeasure ≤
        d • case2PassiveThetaPassiveFieldReferenceMeasure
          (ρ := ρ) (τ := τ) n S J) :
    let weightedBox : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
      case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
    let passiveSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      passiveMeasure.prod weightedBox
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    Measure.map Y (passiveSource.restrict Ω) ≤ d • endpointReferenceImage := by
  intro weightedBox passiveSource endpointReferenceImage Y
  let referencePassive :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let referenceSource :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    referencePassive.prod weightedBox
  haveI : SFinite weightedBox := by
    subst weightedBox
    dsimp [case2PassiveThetaCenterWeightedBoxMeasure,
      case2PassiveThetaCenterSignedBoxMeasure]
    infer_instance
  have hprod : passiveSource ≤ d • referenceSource := by
    change passiveMeasure.prod weightedBox ≤ d • referencePassive.prod weightedBox
    exact prod_le_smul_prod_of_le_smul_left (η := weightedBox) hpassive
  have hrestrict :
      passiveSource.restrict Ω ≤ d • referenceSource.restrict Ω := by
    calc
      passiveSource.restrict Ω ≤ (d • referenceSource).restrict Ω :=
        Measure.restrict_mono Set.Subset.rfl hprod
      _ = d • referenceSource.restrict Ω := by
        rw [Measure.restrict_smul]
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hmap :
      Measure.map Y (passiveSource.restrict Ω) ≤
        d • Measure.map Y (referenceSource.restrict Ω) :=
    map_le_smul_map_of_le_smul_aemeasurable hY hrestrict
  simpa [endpointReferenceImage, case2PassiveThetaEndpointReferenceImageMeasure,
    referenceSource, referencePassive, weightedBox, Y] using hmap

end Aoyagi
end DLN
end DLNFibre
