import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference

/-!
# Case 2 passive theta with-following endpoint reference measure

This file names the concrete coordinate-product reference measure on the
enlarged Case 2 passive-theta source with an independent following factor.  It
is only a reference-measure and support layer: it does not prove the endpoint
determinant-chart change of variables, Haar normalization, source-prior
transport, normal crossings, pole order, or RLCT extraction.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open ChartLocalSuffixState
open ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData

set_option linter.style.longLine false in
/-- Coordinate-product reference measure on the enlarged passive-theta source:
the existing passive-theta reference measure times coordinate-product Lebesgue
measure on the independent following-factor matrix. -/
noncomputable def case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
  (case2PassiveThetaReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres).prod
    (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- The enlarged reference source is definitionally the product of the
old passive-theta reference source and the independent following-factor
matrix-entry reference measure. -/
theorem case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_prod
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres =
      (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres).prod
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) :=
  rfl

set_option linter.style.longLine false in
/-- Projecting the enlarged reference source to its passive-theta component
recovers the old passive-theta reference source, scaled by the total mass of
the independent following-factor reference measure.

The scalar is kept explicit: no finiteness or probability normalization is
claimed here. -/
theorem measure_map_case2PassiveThetaWithFollowingFactor_theta_referenceSource_eq_smul_reference
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure.map
        (Case2PassiveThetaWithFollowingFactor.theta
          (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J))
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) =
      (matrixEntryReferenceMeasure
          (Case2ResidualColIndex n S (J + 1)) τ Set.univ) •
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres := by
  haveI :
      SFinite
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) :=
    sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  change
    Measure.map
        (Prod.fst :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ →
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
        ((case2PassiveThetaReferenceSourceMeasure
            (ρ := ρ) (τ := τ) n hS hnext Rres).prod
          (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)) =
      (matrixEntryReferenceMeasure
          (Case2ResidualColIndex n S (J + 1)) τ Set.univ) •
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres
  exact
    Measure.map_fst_prod
      (μ :=
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
      (ν := matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- Projection to the old passive-theta component is quasi-measure-preserving
from the enlarged product reference source to the old passive-theta reference
source.

This avoids any normalization assumption on the independent following-factor
reference measure. -/
theorem quasiMeasurePreserving_case2PassiveThetaWithFollowingFactor_theta_referenceSource
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure.QuasiMeasurePreserving
        (Case2PassiveThetaWithFollowingFactor.theta
          (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J))
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
        (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) := by
  change
    Measure.QuasiMeasurePreserving
        (Prod.fst :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ →
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
        ((case2PassiveThetaReferenceSourceMeasure
            (ρ := ρ) (τ := τ) n hS hnext Rres).prod
          (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ))
        (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
  exact
    Measure.quasiMeasurePreserving_fst
      (μ :=
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
      (ν := matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- Projecting the enlarged reference source to its following-factor component
recovers the following-factor matrix-entry reference measure, scaled by the
total mass of the old passive-theta reference source.

The scalar is kept explicit: no finiteness or probability normalization is
claimed here. -/
theorem measure_map_case2PassiveThetaWithFollowingFactor_followingFactor_referenceSource_eq_smul_reference
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure.map
        (Case2PassiveThetaWithFollowingFactor.followingFactor
          (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J))
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) =
      (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres Set.univ) •
        matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ := by
  haveI :
      SFinite
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) :=
    sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  change
    Measure.map
        (Prod.snd :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ →
          Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ)
        ((case2PassiveThetaReferenceSourceMeasure
            (ρ := ρ) (τ := τ) n hS hnext Rres).prod
          (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)) =
      (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres Set.univ) •
        matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  exact
    Measure.map_snd_prod
      (μ :=
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
      (ν := matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- Projection to the independent following-factor component is
quasi-measure-preserving from the enlarged product reference source to the
following-factor matrix reference source.

This avoids any normalization assumption on the old passive-theta reference
source. -/
theorem quasiMeasurePreserving_case2PassiveThetaWithFollowingFactor_followingFactor_referenceSource
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure.QuasiMeasurePreserving
        (Case2PassiveThetaWithFollowingFactor.followingFactor
          (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J))
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ) := by
  change
    Measure.QuasiMeasurePreserving
        (Prod.snd :
          Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
            Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ →
          Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ)
        ((case2PassiveThetaReferenceSourceMeasure
            (ρ := ρ) (τ := τ) n hS hnext Rres).prod
          (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ))
        (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)
  exact
    Measure.quasiMeasurePreserving_snd
      (μ :=
        case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres)
      (ν := matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- Endpoint topology-tuple image measure of the enlarged concrete
passive-theta reference source restricted to a chosen local set.

This names the correct image-measure target for the enlarged coordinate
domain.  It is not unrestricted Haar on the full retained-passive determinant
chart. -/
noncomputable def case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
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
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)) :
    Measure (TopologyTuple ρ κ' ℝ) :=
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  Measure.map Y (referenceSource.restrict Ω)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete enlarged passive-theta reference source is supported on the
determinant chart after restricting to any measurable determinant-sector
localization.

This is support only.  It does not prove that the endpoint pushforward is Haar,
absolutely continuous with bounded density, or dominated by a determinant-chart
Haar measure. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet :
      Ω ⊆ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := ρ) (τ := τ) n S J) :
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
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
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  simpa [referenceSource, Y, rawDetChart] using
    measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
      referenceSource Ω hΩ hΩdet hY

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named enlarged endpoint reference image measure is supported on the
determinant chart after determinant-sector localization.

This is the same support statement as
`measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector`,
but stated for the named image measure rather than an unfolded `Measure.map`.
It is not unrestricted determinant-chart Haar. -/
theorem case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet :
      Ω ⊆ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := ρ) (τ := τ) n S J) :
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    endpointReferenceImage.restrict rawDetChart = endpointReferenceImage := by
  intro endpointReferenceImage rawDetChart
  simpa [endpointReferenceImage, rawDetChart,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure] using
    measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_detChartSet_eq_self_of_subset_detSector
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ hΩdet

end Aoyagi
end DLN
end DLNFibre
