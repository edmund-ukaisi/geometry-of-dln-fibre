import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSector
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveSelectedEntrySourceMeasure

/-!
# Case 2 passive theta source-measure adapter

This file specializes the passive selected-entry source-measure support theorem
to the concrete full theta coordinate domain.  It proves support and residual
readout for chart-produced measures on a local punctured theta sector.  It does
not identify determinant-chart Haar measure, source-prior measure, normal
crossings, pole order, or RLCT.
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
/-- A restricted passive-theta endpoint topology-tuple pushforward is supported
on the corresponding endpoint sector image.

This is only image-support bookkeeping for the full passive-sector coordinate
map.  The sector measurability and map a.e.-measurability hypotheses are
explicit; the theorem does not prove exact sector Haar transport,
finite-scalar domination, bounded-density comparison, source-prior transport,
normal crossings, pole order, or RLCT extraction. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (thetaMeasure :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    (hY :
      AEMeasurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
        (thetaMeasure.restrict Ω)) :
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y (thetaMeasure.restrict Ω)).restrict sectorSet =
      Measure.map Y (thetaMeasure.restrict Ω) := by
  intro Y sectorSet
  have hmem :
      ∀ᵐ theta ∂ thetaMeasure.restrict Ω, Y theta ∈ sectorSet := by
    filter_upwards [ae_restrict_mem hΩ] with theta htheta
    exact ⟨theta, htheta, rfl⟩
  have hmap_mem :
      ∀ᵐ y ∂ Measure.map Y (thetaMeasure.restrict Ω), y ∈ sectorSet := by
    exact (ae_map_iff (f := Y) hY hsector).2 hmem
  exact Measure.restrict_eq_self_of_ae_mem hmap_mem

set_option linter.style.longLine false in
/-- If a localized full passive-theta source lies in the passive determinant
sector, then its endpoint topology-tuple pushforward is supported on the
retained-passive determinant-chart target.

This is only support bookkeeping.  It supplies the determinant-chart support
side of a future passive-reference theorem; it does not identify the
pushforward with determinant-chart Haar measure, prove a Jacobian formula,
construct a source prior, or extract an RLCT. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (thetaMeasure :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet : Ω ⊆ case2PassiveThetaDetSector (ρ := ρ) (τ := τ) n S J)
    (hY :
      AEMeasurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
        (thetaMeasure.restrict Ω)) :
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    (Measure.map Y (thetaMeasure.restrict Ω)).restrict rawDetChart =
      Measure.map Y (thetaMeasure.restrict Ω) := by
  intro Y rawDetChart
  have hdet_meas : MeasurableSet rawDetChart := by
    exact
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hmem :
      ∀ᵐ theta ∂ thetaMeasure.restrict Ω, Y theta ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hΩ] with theta htheta
    exact
      case2PassiveThetaEndpointTopologyTuple_mem_detChartSet
        (ρ := ρ) n hS hcont hnext theta eNext e (hΩdet htheta)
  have hmap_mem :
      ∀ᵐ y ∂ Measure.map Y (thetaMeasure.restrict Ω), y ∈ rawDetChart :=
    (ae_map_iff (f := Y) hY hdet_meas).2 hmem
  exact Measure.restrict_eq_self_of_ae_mem hmap_mem

set_option linter.style.longLine false in
/-- If a localized enlarged following-factor full passive-theta source lies in
the passive determinant sector, then its endpoint topology-tuple pushforward
is supported on the retained-passive determinant-chart target.

This is only support bookkeeping for the enlarged source.  It does not
identify determinant-chart Haar measure, prove the selected-entry
change-of-variables formula for `Y`, prove raw-map transport, construct a
source prior, or extract an RLCT. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_detChartSet_eq_self_of_subset_detSector
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [Fintype ρ] [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (thetaMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (Ω : Set
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩdet :
      Ω ⊆ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := ρ) (τ := τ) n S J)
    (hY :
      AEMeasurable
        (fun theta :
            Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
        (thetaMeasure.restrict Ω)) :
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let rawDetChart : Set (TopologyTuple ρ κ' ℝ) :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    (Measure.map Y (thetaMeasure.restrict Ω)).restrict rawDetChart =
      Measure.map Y (thetaMeasure.restrict Ω) := by
  intro Y rawDetChart
  have hdet_meas : MeasurableSet rawDetChart := by
    exact
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hmem :
      ∀ᵐ theta ∂ thetaMeasure.restrict Ω, Y theta ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hΩ] with theta htheta
    exact
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_mem_detChartSet
        (ρ := ρ) n hS hcont hnext theta eNext e (hΩdet htheta)
  have hmap_mem :
      ∀ᵐ y ∂ Measure.map Y (thetaMeasure.restrict Ω), y ∈ rawDetChart :=
    (ae_map_iff (f := Y) hY hdet_meas).2 hmem
  exact Measure.restrict_eq_self_of_ae_mem hmap_mem

set_option linter.style.longLine false in
/-- A restricted enlarged following-factor passive-theta endpoint
topology-tuple pushforward is supported on the corresponding endpoint sector
image.

This is only image-support bookkeeping for the enlarged source.  The sector
measurability and map a.e.-measurability hypotheses are explicit; the theorem
does not prove exact sector Haar transport, finite-scalar domination,
bounded-density comparison, source-prior transport, normal crossings, pole
order, or RLCT extraction. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (thetaMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaWithFollowingFactorEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    (hY :
      AEMeasurable
        (fun theta :
            Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
        (thetaMeasure.restrict Ω)) :
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y (thetaMeasure.restrict Ω)).restrict sectorSet =
      Measure.map Y (thetaMeasure.restrict Ω) := by
  intro Y sectorSet
  have hmem :
      ∀ᵐ theta ∂ thetaMeasure.restrict Ω, Y theta ∈ sectorSet := by
    filter_upwards [ae_restrict_mem hΩ] with theta htheta
    exact ⟨theta, htheta, rfl⟩
  have hmap_mem :
      ∀ᵐ y ∂ Measure.map Y (thetaMeasure.restrict Ω), y ∈ sectorSet :=
    (ae_map_iff (f := Y) hY hsector).2 hmem
  exact Measure.restrict_eq_self_of_ae_mem hmap_mem

set_option linter.style.longLine false in
/-- Finite-scalar domination of enlarged following-factor theta-domain
measures pushes forward to the corresponding endpoint topology-tuple sector
measures.

The conclusion is restricted to the named endpoint image sector on both sides.
This assumes the theta-domain domination explicitly; it does not identify
determinant-chart Haar measure, construct a source prior, prove a bounded
density, or extract an RLCT. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (sourceMeasure referenceMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaWithFollowingFactorEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    {c : ℝ≥0∞}
    (hY :
      Measurable
        (fun theta :
            Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e))
    (hdom : sourceMeasure.restrict Ω ≤ c • referenceMeasure.restrict Ω) :
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y (sourceMeasure.restrict Ω)).restrict sectorSet ≤
      c • (Measure.map Y (referenceMeasure.restrict Ω)).restrict sectorSet := by
  intro Y sectorSet
  have hsource_support :
      (Measure.map Y (sourceMeasure.restrict Ω)).restrict sectorSet =
        Measure.map Y (sourceMeasure.restrict Ω) := by
    simpa [Y, sectorSet] using
      measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        sourceMeasure Ω hΩ hsector hY.aemeasurable
  have href_support :
      (Measure.map Y (referenceMeasure.restrict Ω)).restrict sectorSet =
        Measure.map Y (referenceMeasure.restrict Ω) := by
    simpa [Y, sectorSet] using
      measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        referenceMeasure Ω hΩ hsector hY.aemeasurable
  rw [hsource_support, href_support]
  exact map_le_smul_map_of_le_smul hY hdom

set_option linter.style.longLine false in
/-- A local a.e. upper bound on an enlarged following-factor theta-domain
density gives finite-scalar domination after pushing forward to the named
endpoint sector.

This is a bounded-density corollary of
`measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_le_smul`.
The density bound is still an explicit hypothesis; the theorem does not
construct determinant-chart Haar comparison or source-prior density. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_withDensity_restrict_endpointSectorSet_le_smul_of_ae_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (baseMeasure :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaWithFollowingFactorEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    {density :
      Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J →
        ℝ≥0∞}
    {c : ℝ≥0∞}
    (hY :
      Measurable
        (fun theta :
            Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e))
    (hdensity_le :
      ∀ᵐ theta ∂ baseMeasure.restrict Ω, density theta ≤ c) :
    let Y :
        Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y ((baseMeasure.withDensity density).restrict Ω)).restrict sectorSet ≤
      c • (Measure.map Y (baseMeasure.restrict Ω)).restrict sectorSet := by
  intro Y sectorSet
  have hdom :
      (baseMeasure.withDensity density).restrict Ω ≤ c • baseMeasure.restrict Ω := by
    rw [restrict_withDensity hΩ]
    rw [← withDensity_const (μ := baseMeasure.restrict Ω) c]
    exact withDensity_mono hdensity_le
  simpa [Y, sectorSet] using
    measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
      (baseMeasure.withDensity density) baseMeasure Ω hΩ hsector hY hdom

set_option linter.style.longLine false in
/-- Finite-scalar domination of theta-domain measures pushes forward to the
corresponding endpoint topology-tuple sector measures.

The conclusion is restricted to the named endpoint image sector on both sides.
This is the consumer-facing domination direction needed by later finite
integral transfers.  It assumes the theta-domain domination explicitly; it
does not identify determinant-chart Haar measure, construct a source prior,
prove a bounded density, or extract an RLCT. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (sourceMeasure referenceMeasure :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    {c : ℝ≥0∞}
    (hY :
      Measurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e))
    (hdom : sourceMeasure.restrict Ω ≤ c • referenceMeasure.restrict Ω) :
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y (sourceMeasure.restrict Ω)).restrict sectorSet ≤
      c • (Measure.map Y (referenceMeasure.restrict Ω)).restrict sectorSet := by
  intro Y sectorSet
  have hsource_support :
      (Measure.map Y (sourceMeasure.restrict Ω)).restrict sectorSet =
        Measure.map Y (sourceMeasure.restrict Ω) := by
    simpa [Y, sectorSet] using
      measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        sourceMeasure Ω hΩ hsector hY.aemeasurable
  have href_support :
      (Measure.map Y (referenceMeasure.restrict Ω)).restrict sectorSet =
        Measure.map Y (referenceMeasure.restrict Ω) := by
    simpa [Y, sectorSet] using
      measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_eq_self
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        referenceMeasure Ω hΩ hsector hY.aemeasurable
  rw [hsource_support, href_support]
  exact map_le_smul_map_of_le_smul hY hdom

set_option linter.style.longLine false in
/-- A local a.e. upper bound on a theta-domain density gives
finite-scalar domination after pushing forward to the named endpoint sector.

This is a bounded-density corollary of
`measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul`.
The density bound is still an explicit hypothesis; the theorem does not
construct a passive-sector Haar comparison or source-prior density. -/
theorem measure_map_case2PassiveThetaEndpointTopologyTuple_withDensity_restrict_endpointSectorSet_le_smul_of_ae_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (baseMeasure : Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (Ω : Set (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hsector :
      MeasurableSet
        (case2PassiveThetaEndpointSectorSet
          (ρ := ρ) n hS hcont hnext eNext e Ω))
    {density :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → ℝ≥0∞}
    {c : ℝ≥0∞}
    (hY :
      Measurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e))
    (hdensity_le :
      ∀ᵐ theta ∂ baseMeasure.restrict Ω, density theta ≤ c) :
    let Y :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let sectorSet : Set (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaEndpointSectorSet
        (ρ := ρ) n hS hcont hnext eNext e Ω
    (Measure.map Y ((baseMeasure.withDensity density).restrict Ω)).restrict sectorSet ≤
      c • (Measure.map Y (baseMeasure.restrict Ω)).restrict sectorSet := by
  intro Y sectorSet
  have hdom :
      (baseMeasure.withDensity density).restrict Ω ≤ c • baseMeasure.restrict Ω := by
    rw [restrict_withDensity hΩ]
    rw [← withDensity_const (μ := baseMeasure.restrict Ω) c]
    exact withDensity_mono hdensity_le
  simpa [Y, sectorSet] using
    measure_map_case2PassiveThetaEndpointTopologyTuple_restrict_endpointSectorSet_le_smul
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
      (baseMeasure.withDensity density) baseMeasure Ω hΩ hsector hY hdom

namespace PaperEndpointFixedBaseRegularCoordinateSourceData

universe v

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base p.13 source edge-family chart attached to a concrete
Case 2 passive theta coordinate. -/
def case2PassiveThetaEndpointSourceChart
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    [DecidableEq (Fin (Module.finrank ℝ U₀))]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
    (case2PassiveThetaEndpointRetainedData
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The residual-block coordinate equivalence used by the concrete Case 2
passive theta endpoint source chart. -/
def case2PassiveThetaEndpointResidualCoordEquiv
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ}
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃
      Case2PassiveTheta.Center n S J :=
  case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
    n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The selected-entry inverse residual readout attached to the concrete
Case 2 passive theta endpoint source chart. -/
def case2PassiveThetaEndpointInverseReadout
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      Case2PassiveTheta.Center n S J → ℝ :=
  let residualCoordEquiv :=
    case2PassiveThetaEndpointResidualCoordEquiv W₂ B₂ n eNext e
  fun X ↦
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero
      (case2PassiveThetaPivotNext n hS hnext)
      (fun i : Case2PassiveTheta.Center n S J ↦
        paperEndpointFixedBaseResidualBlockCoordinateMap
          (K := ℝ) W₂ B₂ U₀ hU₀
          (fun E :
              ∀ p : Fin 2,
                reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ ↦ E)
          X (residualCoordEquiv.symm i))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Read a full passive theta coordinate back from an endpoint p.13 source
edge family.

The passive fields are read from `sourceReadback` and transported back through
the endpoint equivalences; the selected residual field is read by the
selected-entry inverse readout. -/
def case2PassiveThetaEndpointSourceChartReadback
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
  let ρ := Fin (Module.finrank ℝ U₀)
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  fun X : EdgeFamily ↦
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let data :=
      sourceReadback
        (K := ℝ) (ρ := ρ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E
    let rawData := data.endpointTransport (fun j ↦ (e j).symm)
    Case2PassiveTheta.mk
      (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      rawData.A1passive rawData.F2 rawData.A3passive rawData.Ctop rawData.F3
      (case2PassiveThetaEndpointInverseReadout
        W₂ B₂ n hS hnext hU₀ eNext e X)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The concrete source-family readback recovers a theta coordinate when
`sourceReadback` recovers the endpoint retained data and the selected-entry
readout recovers `yNext`.

This is pointwise finite coordinate algebra.  It does not assert local image
measurability or any measure transport theorem. -/
theorem case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
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
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
    (hread :
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      sourceReadback
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E =
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    (hinv :
      case2PassiveThetaEndpointInverseReadout
          W₂ B₂ n hS hnext hU₀ eNext e X =
        theta.yNext) :
    case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e X = theta := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let E :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
      (fun p : Fin 2 ↦
        (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
  let data :=
    sourceReadback
      (K := ℝ) (ρ := ρ)
      (κ' := throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E
  let rawData := data.endpointTransport (fun j ↦ (e j).symm)
  change
    Case2PassiveTheta.mk
        (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
        rawData.A1passive rawData.F2 rawData.A3passive rawData.Ctop rawData.F3
        (case2PassiveThetaEndpointInverseReadout
          W₂ B₂ n hS hnext hU₀ eNext e X) = theta
  rw [hinv]
  subst rawData
  subst data
  rw [hread]
  have htransport :
      (case2PassiveThetaEndpointRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext e).endpointTransport
            (fun j ↦ (e j).symm) =
        case2PassiveThetaRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext := by
    dsimp [case2PassiveThetaEndpointRetainedData]
    exact
      endpointTransport_symm_endpointTransport
        (K := ℝ) (ρ := ρ) e
        (case2PassiveThetaRetainedData
          (ρ := ρ) n hS hcont hnext theta eNext)
  rw [htransport]
  cases theta
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Compatibility-gated two-sided reconstruction for the concrete Case 2
passive-theta endpoint source chart.

The source edge family must already lie in the retained-passive determinant
source chart, and its `sourceReadback` and selected-entry inverse readout must
match the chosen passive-theta endpoint datum.  Under exactly those
compatibility hypotheses, the concrete passive-theta readback recovers
`theta`, and the concrete passive-theta source chart maps `theta` back to the
original source edge family.

This is not a source-rank coverage theorem, source-prior transport theorem,
Haar transport theorem, normal-crossing statement, pole-order computation, or
RLCT extraction. -/
theorem case2PassiveThetaEndpointSourceChart_readback_eq_and_rightInverse_of_sourceReadback_eq_retainedData
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
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (theta :
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
    (hsource :
      X ∈ paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilySet
        (K := ℝ) W₂ B₂ U₀ hU₀)
    (hread :
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      sourceReadback
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E =
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    (hinv :
      case2PassiveThetaEndpointInverseReadout
          W₂ B₂ n hS hnext hU₀ eNext e X =
        theta.yNext) :
    case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e X = theta ∧
      case2PassiveThetaEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e theta = X := by
  constructor
  · exact
      case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
        W₂ B₂ n hS hcont hnext hU₀ eNext e theta X hread hinv
  · let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    have hread' :
        sourceReadback
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E =
          case2PassiveThetaEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e := by
      simpa [E] using hread
    have hright :
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
            (K := ℝ) W₂ B₂ U₀ hU₀
            (sourceReadback
              (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
              (κ' := throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E) =
          X := by
      simpa [E] using
        (paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamily_openPartialHomeomorph
          (K := ℝ) W₂ B₂ U₀ hU₀).right_inv' hsource
    change
      paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ U₀ hU₀
          (case2PassiveThetaEndpointRetainedData
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e) = X
    rw [← hread']
    exact hright

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The fixed-base p.13 source edge-family chart attached to an enlarged
Case 2 passive-theta coordinate with an independent following factor. -/
def case2PassiveThetaWithFollowingFactorEndpointSourceChart
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    [DecidableEq (Fin (Module.finrank ℝ U₀))]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ :=
  paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData W₂ B₂ U₀ hU₀
    (case2PassiveThetaWithFollowingFactorEndpointRetainedData
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Read the successor selected-entry coordinates directly from the `C 1`
block of a retained-passive source-family readback.

This readout intentionally does not use the old product `C 1 * C 0`: in the
enlarged source the free following factor changes that product. -/
def case2PassiveThetaWithFollowingFactorEndpointCOneReadout
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      Case2PassiveTheta.Center n S J → ℝ :=
  let ρ := Fin (Module.finrank ℝ U₀)
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  fun X : EdgeFamily ↦
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let data :=
      sourceReadback
        (K := ℝ) (ρ := ρ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E
    let rawData := data.endpointTransport (fun j ↦ (e j).symm)
    SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
      (fun i : Case2PassiveTheta.Center n S J ↦
        AoyagiResidualBlockCoordinateIndex.value
          (show
            Matrix (Case2ResidualRowIndex n S (J + 1))
              (Case2ResidualColIndex n S (J + 1)) ℝ from
            by
              simpa [case2PostPivotTwoEdgeDomain] using rawData.C (1 : Fin 2))
          (residualCoordEquiv.symm i))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Read an enlarged passive theta coordinate back from an endpoint p.13
source edge family.

The passive fields are read from `sourceReadback`; `yNext` is read directly
from the transported `C 1` block; and the independent following factor is read
from the transported `C 0` block. -/
def case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q) :
    (∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) →
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
  let ρ := Fin (Module.finrank ℝ U₀)
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  fun X : EdgeFamily ↦
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    let data :=
      sourceReadback
        (K := ℝ) (ρ := ρ)
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E
    let rawData := data.endpointTransport (fun j ↦ (e j).symm)
    let yNext :=
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
        W₂ B₂ n hS hnext hU₀ e X
    let F :
        Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ :=
      show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
        by
          simpa [case2PostPivotTwoEdgeDomain] using rawData.C (0 : Fin 2)
    Case2PassiveThetaWithFollowingFactor.mk
      (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
      rawData.A1passive rawData.F2 rawData.A3passive rawData.Ctop rawData.F3
      yNext F

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The enlarged source-family readback recovers the enlarged theta coordinate
when `sourceReadback` recovers the endpoint retained data and the selected
pivot coordinate is nonzero.

This is pointwise finite coordinate algebra.  It does not assert local image
measurability or any measure transport theorem. -/
theorem case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
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
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
    (hread :
      let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      sourceReadback
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) E =
        case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    (hpivot :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1) :
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ e X = z := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let E :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
      (fun p : Fin 2 ↦
        (X p : reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
  let data :=
    sourceReadback (K := ℝ) (ρ := ρ) (κ' := κ') E
  let rawData := data.endpointTransport (fun j ↦ (e j).symm)
  have htransport :
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := ρ) n hS hcont hnext z eNext e).endpointTransport
            (fun j ↦ (e j).symm) =
        case2PassiveThetaWithFollowingFactorRetainedData
          (ρ := ρ) n hS hcont hnext z eNext := by
    dsimp [case2PassiveThetaWithFollowingFactorEndpointRetainedData]
    exact
      endpointTransport_symm_endpointTransport
        (K := ℝ) (ρ := ρ) e
        (case2PassiveThetaWithFollowingFactorRetainedData
          (ρ := ρ) n hS hcont hnext z eNext)
  have hraw :
      rawData =
        case2PassiveThetaWithFollowingFactorRetainedData
          (ρ := ρ) n hS hcont hnext z eNext := by
    subst rawData
    subst data
    rw [hread]
    exact htransport
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (Case2ResidualRowIndex n S (J + 1))
          (Case2ResidualColIndex n S (J + 1)) ≃
        Case2PassiveTheta.Center n S J :=
    case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
      n S (J + 1) (Equiv.refl _) (Equiv.refl _)
  have hy :
      case2PassiveThetaWithFollowingFactorEndpointCOneReadout
          W₂ B₂ n hS hnext hU₀ e X =
        z.1.yNext := by
    change
      SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
          (fun i : Case2PassiveTheta.Center n S J ↦
            AoyagiResidualBlockCoordinateIndex.value
              (show
                Matrix (Case2ResidualRowIndex n S (J + 1))
                  (Case2ResidualColIndex n S (J + 1)) ℝ from
                by
                  simpa [case2PostPivotTwoEdgeDomain] using rawData.C (1 : Fin 2))
              (residualCoordEquiv.symm i)) =
        z.1.yNext
    rw [hraw]
    have hvalue :
        (fun i : Case2PassiveTheta.Center n S J ↦
          AoyagiResidualBlockCoordinateIndex.value
            (show
              Matrix (Case2ResidualRowIndex n S (J + 1))
                (Case2ResidualColIndex n S (J + 1)) ℝ from
              by
                simpa [case2PostPivotTwoEdgeDomain] using
                  (case2PassiveThetaWithFollowingFactorRetainedData
                    (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2))
            (residualCoordEquiv.symm i)) =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext := by
      funext i
      let D :
          Matrix (Case2ResidualRowIndex n S (J + 1))
            (Case2ResidualColIndex n S (J + 1)) ℝ :=
        show
          Matrix (Case2ResidualRowIndex n S (J + 1))
            (Case2ResidualColIndex n S (J + 1)) ℝ from
          by
            simpa [case2PostPivotTwoEdgeDomain] using
              (case2PassiveThetaWithFollowingFactorRetainedData
                (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2)
      have hC1 :
          D =
            (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).submatrix
              id eNext.symm := by
        change
          case2DisplayedPostPivotResidualBlock n hS hcont
              (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext) =
            (case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext).submatrix
              id eNext.symm
        simp [case2SuccessorSelectedEntrySourceResidual,
          case2DisplayedPostPivotSourceResidualOfMatrix,
          case2DisplayedPostPivotResidualBlock_sourceResidualBlockExtension]
      let c :
          AoyagiResidualBlockCoordinateIndex
              (Case2ResidualRowIndex n S (J + 1))
              (Case2ResidualColIndex n S (J + 1)) :=
        residualCoordEquiv.symm i
      have hcoord :
          case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl (Case2ResidualRowIndex n S (J + 1))) eNext
              (c.1, eNext.symm c.2) = i := by
        apply Subtype.ext
        change (c.1.1, (eNext (eNext.symm c.2)).1) = i.1
        rw [Equiv.apply_symm_apply]
        exact congrArg Subtype.val (Equiv.apply_symm_apply residualCoordEquiv i)
      change AoyagiResidualBlockCoordinateIndex.value D (residualCoordEquiv.symm i) =
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
      rw [hC1]
      change
        case2SuccessorSelectedEntryMatrix n hS hnext z.1.yNext eNext
            (residualCoordEquiv.symm i).1 (eNext.symm (residualCoordEquiv.symm i).2) =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
      change
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
            (case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
              n S (J + 1) (Equiv.refl (Case2ResidualRowIndex n S (J + 1))) eNext
              (c.1, eNext.symm c.2)) =
          SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext i
      rw [hcoord]
    change
      SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
          (fun i : Case2PassiveTheta.Center n S J ↦
            AoyagiResidualBlockCoordinateIndex.value
              (show
                Matrix (Case2ResidualRowIndex n S (J + 1))
                  (Case2ResidualColIndex n S (J + 1)) ℝ from
                by
                  simpa [case2PostPivotTwoEdgeDomain] using
                    (case2PassiveThetaWithFollowingFactorRetainedData
                      (ρ := ρ) n hS hcont hnext z eNext).C (1 : Fin 2))
              (residualCoordEquiv.symm i)) =
        z.1.yNext
    rw [hvalue]
    exact
      SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero_chartMap
        pivotNext z.1.yNext hpivot
  have hF :
      (show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
        by
          simpa [case2PostPivotTwoEdgeDomain] using
            (case2PassiveThetaWithFollowingFactorRetainedData
              (ρ := ρ) n hS hcont hnext z eNext).C (0 : Fin 2)) =
        z.2 := by
    change
      case2DisplayedPostPivotFreeFollowingFactor n hS hcont
          (case2DisplayedPostPivotFreeCprimeOfFollowingFactor n hS hcont z.2) =
        z.2
    exact case2DisplayedPostPivotFreeFollowingFactor_freeCprimeOfFollowingFactor
      n hS hcont z.2
  change
    Case2PassiveThetaWithFollowingFactor.mk
        (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
        rawData.A1passive rawData.F2 rawData.A3passive rawData.Ctop rawData.F3
        (case2PassiveThetaWithFollowingFactorEndpointCOneReadout
          W₂ B₂ n hS hnext hU₀ e X)
        (show Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ from
          by
            simpa [case2PostPivotTwoEdgeDomain] using rawData.C (0 : Fin 2)) = z
  rw [hraw, hy]
  cases z with
  | mk theta F =>
    cases theta
    apply Prod.ext
    · rfl
    · simpa [case2PassiveThetaWithFollowingFactorRetainedData,
        case2PostPivotSelectedEntryRetainedPassiveDataWithPassiveFollowingFactor,
        Case2PassiveThetaWithFollowingFactor.mk] using hF

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Locally, the enlarged endpoint source chart has a left inverse on
following-factor Case 2 passive theta coordinates.

The local set is the retained-passive determinant-chart neighborhood
intersected with the nonzero selected-pivot condition.  The readback uses the
raw `C 1` block for `yNext` and raw `C 0` for the free following factor; it
does not use the old residual-product inverse. -/
theorem exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1) :
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ z ∈ V, readback (sourceChart z) = z := by
  intro EdgeFamily sourceChart readback
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let retainedData :
      Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := ρ) n hS hcont hnext z eNext e
  let Y :
      Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦ topologyTuple (retainedData z)
  have hYcont : Continuous Y := by
    exact
      (continuous_topologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp
        (continuous_case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := ρ) n hS hcont hnext eNext e)
  have hY₀ : Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    have hdet :
        (retainedData z₀).detChart := by
      simpa [retainedData, ρ, κ'] using
        case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
          (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
    simpa [Y] using
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z₀)).2 hdet
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let Udet :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    Y ⁻¹' detSet
  have hUdet_open : IsOpen Udet := by
    exact
      hYcont.isOpen_preimage detSet
        (by
          simpa [detSet] using
            (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')))
  have hz₀Udet : z₀ ∈ Udet := by
    simpa [Udet, detSet] using hY₀
  let pivotSet :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    {z | case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous
          (fun z :
              Case2PassiveThetaWithFollowingFactor
                (ρ := ρ) (τ := τ) n S J ↦
            z.1.yNext (case2PassiveThetaPivotNext n hS hnext)) := by
      simpa [Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd.comp
            (continuous_fst :
              Continuous
                (fun z :
                    Case2PassiveThetaWithFollowingFactor
                      (ρ := ρ) (τ := τ) n S J ↦ z.1))))
    simpa [pivotSet, case2PassiveThetaPivotNonzero] using
      (isOpen_ne.preimage hpivot_cont)
  let V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    Udet ∩ pivotSet
  have hVopen : IsOpen V := hUdet_open.inter hpivotSet_open
  have hz₀V : z₀ ∈ V := by
    exact ⟨hz₀Udet, by simpa [pivotSet] using hpivot₀⟩
  refine ⟨V, hVopen, hz₀V, ?_⟩
  intro z hzV
  have hYz : Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    simpa [V, Udet, detSet] using hzV.1
  have hdet : (retainedData z).detChart := by
    exact
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
        (by simpa [Y] using hYz)
  have hpivot :
      case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1 := by
    simpa [V, pivotSet] using hzV.2
  let E :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
      (fun p : Fin 2 ↦
        (sourceChart z p :
          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
  have hedge :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            ((fun E : EdgeFamily ↦ E) (sourceChart z) p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
        (retainedData z).edgeMatrix := by
    simpa [sourceChart, retainedData,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
        (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
  have hread :
      (let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z) := by
    simpa [E] using
      sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
        (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EdgeFamily ↦ E)
        (sourceChart z) (retainedData z) hdet hedge
  exact
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
      W₂ B₂ n hS hcont hnext hU₀ eNext e z (sourceChart z) hread hpivot

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The enlarged with-following endpoint source-chart readback local
neighborhood may be chosen inside the selected-entry nonzero-pivot locus.

This is the same determinant-chart/readback construction as
`exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse`,
with the pivot condition on the returned local set exposed for later
right-inverse and source-image coverage arguments.  It does not prove
source-image reverse inclusion, source-rank coverage, source-prior transport,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse_pivotNonzero
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1) :
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
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        (∀ z ∈ V,
          case2PassiveThetaPivotNonzero
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z.1) ∧
          ∀ z ∈ V, readback (sourceChart z) = z := by
  intro EdgeFamily sourceChart readback
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let retainedData :
      Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := ρ) n hS hcont hnext z eNext e
  let Y :
      Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦ topologyTuple (retainedData z)
  have hYcont : Continuous Y := by
    exact
      (continuous_topologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp
        (continuous_case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := ρ) n hS hcont hnext eNext e)
  have hY₀ : Y z₀ ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    have hdet :
        (retainedData z₀).detChart := by
      simpa [retainedData, ρ, κ'] using
        case2PassiveThetaWithFollowingFactorEndpointRetainedData_detChart
          (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
    simpa [Y] using
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z₀)).2 hdet
  let detSet : Set (TopologyTuple ρ κ' ℝ) :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let Udet :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    Y ⁻¹' detSet
  have hUdet_open : IsOpen Udet := by
    exact
      hYcont.isOpen_preimage detSet
        (by
          simpa [detSet] using
            (isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')))
  have hz₀Udet : z₀ ∈ Udet := by
    simpa [Udet, detSet] using hY₀
  let pivotSet :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    {z | case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous
          (fun z :
              Case2PassiveThetaWithFollowingFactor
                (ρ := ρ) (τ := τ) n S J ↦
            z.1.yNext (case2PassiveThetaPivotNext n hS hnext)) := by
      simpa [Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd.comp
            (continuous_fst :
              Continuous
                (fun z :
                    Case2PassiveThetaWithFollowingFactor
                      (ρ := ρ) (τ := τ) n S J ↦ z.1))))
    simpa [pivotSet, case2PassiveThetaPivotNonzero] using
      (isOpen_ne.preimage hpivot_cont)
  let V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := ρ) (τ := τ) n S J) :=
    Udet ∩ pivotSet
  have hVopen : IsOpen V := hUdet_open.inter hpivotSet_open
  have hz₀V : z₀ ∈ V := by
    exact ⟨hz₀Udet, by simpa [pivotSet] using hpivot₀⟩
  refine ⟨V, hVopen, hz₀V, ?_, ?_⟩
  · intro z hzV
    simpa [V, pivotSet] using hzV.2
  · intro z hzV
    have hYz : Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
      simpa [V, Udet, detSet] using hzV.1
    have hdet : (retainedData z).detChart := by
      exact
        (topologyTuple_mem_topologyTupleDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
          (by simpa [Y] using hYz)
    have hpivot :
        case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1 := by
      simpa [V, pivotSet] using hzV.2
    let E :=
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
        (fun p : Fin 2 ↦
          (sourceChart z p :
            reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
    have hedge :
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              ((fun E : EdgeFamily ↦ E) (sourceChart z) p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
          (retainedData z).edgeMatrix := by
      simpa [sourceChart, retainedData,
        case2PassiveThetaWithFollowingFactorEndpointSourceChart] using
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
    have hread :
        (let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z) := by
      simpa [E] using
        sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
          (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (Cedge := fun E : EdgeFamily ↦ E)
          (sourceChart z) (retainedData z) hdet hedge
    exact
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
        W₂ B₂ n hS hcont hnext hU₀ eNext e z (sourceChart z) hread hpivot

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-side product residual readout for enlarged following-factor
Case 2 passive-theta coordinates. -/
def case2PassiveThetaWithFollowingFactorProductResidualReadout
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
  fun ij ↦
    (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
      (ChartLocalSuffixState.residualFactorProduct
        (case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := ρ) n hS hcont hnext z eNext e).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
          (e (Fin.last 2)) (e 0)) ij.1 ij.2

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The source-side product-residual readout is continuous in the enlarged
following-factor theta coordinates. -/
theorem continuous_case2PassiveThetaWithFollowingFactorProductResidualReadout
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q) :
    Continuous
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaWithFollowingFactorProductResidualReadout
          (ρ := ρ) n hS hcont hnext z eNext e) := by
  let retainedData :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := ρ) κ' :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := ρ) n hS hcont hnext z eNext e
  have hdata : Continuous retainedData :=
    continuous_case2PassiveThetaWithFollowingFactorEndpointRetainedData
      (ρ := ρ) n hS hcont hnext eNext e
  have hres :
      Continuous
        (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
          ChartLocalSuffixState.residualFactorProduct
            (K := ℝ) (κ := κ') (retainedData z).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))) := by
    exact
      (ChartLocalSuffixState.RetainedPassiveNonredundantCoordinateData.continuous_residualFactorProduct_C
        (M := 1) (ρ := ρ) (K := ℝ) (κ' := κ') 0
        (Fin.zero_le (Fin.last 2))).comp hdata
  refine continuous_pi ?_
  intro ij
  simpa [case2PassiveThetaWithFollowingFactorProductResidualReadout,
    retainedData] using
    (hres.matrix_elem (e (Fin.last 2) ij.1) (e 0 ij.2))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The negative-power source-side product-residual integrand is measurable
on the enlarged following-factor theta coordinate space. -/
theorem measurable_case2PassiveThetaWithFollowingFactorProductResidualIntegrand
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*} [DecidableEq ρ]
    [∀ j, Fintype (κ' j)] [∀ j, DecidableEq (κ' j)]
    (n : ℕ → ℕ) {S J : ℕ}
    [MeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [Fintype τ]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    {t : ℝ} :
    Measurable
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        ENNReal.ofReal
          ((aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorProductResidualReadout
              (ρ := ρ) n hS hcont hnext z eNext e)) ^ (-t))) := by
  have hres :
      Measurable
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J ↦
          case2PassiveThetaWithFollowingFactorProductResidualReadout
            (ρ := ρ) n hS hcont hnext z eNext e) :=
    (continuous_case2PassiveThetaWithFollowingFactorProductResidualReadout
      (ρ := ρ) n hS hcont hnext eNext e).measurable
  have hsq :
      Measurable
        (fun z : Case2PassiveThetaWithFollowingFactor
            (ρ := ρ) (τ := τ) n S J ↦
          aoyagiCoordinateSquareSum
            (case2PassiveThetaWithFollowingFactorProductResidualReadout
              (ρ := ρ) n hS hcont hnext z eNext e)) :=
    measurable_aoyagiCoordinateSquareSum hres
  exact ENNReal.measurable_ofReal.comp (hsq.pow_const (-t))

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Edge-family product residual readout obtained by first applying the
enlarged endpoint source-chart readback. -/
def case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) :
    Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
  case2PassiveThetaWithFollowingFactorProductResidualReadout
    (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext
    (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
      W₂ B₂ n hS hnext hU₀ e X)
    eNext e

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- If the enlarged endpoint source-chart readback recovers `z`, then the
edge-family residual readout agrees with the source-side product residual. -/
theorem case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_eq_of_readback_eq
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ)
    (hreadback :
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
          W₂ B₂ n hS hnext hU₀ e X = z) :
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
        W₂ B₂ n hS hcont hnext hU₀ eNext e X =
      case2PassiveThetaWithFollowingFactorProductResidualReadout
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e := by
  subst z
  rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Under a pointwise source-chart left-inverse hypothesis, the edge-family
residual readout of `sourceChart z` is the source-side product residual of `z`. -/
theorem case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hleft :
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
          W₂ B₂ n hS hnext hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z) :
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
        W₂ B₂ n hS hcont hnext hU₀ eNext e
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z) =
      case2PassiveThetaWithFollowingFactorProductResidualReadout
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e := by
  exact
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_eq_of_readback_eq
      W₂ B₂ n hS hcont hnext hU₀ eNext e z
      (case2PassiveThetaWithFollowingFactorEndpointSourceChart
        W₂ B₂ n hS hcont hnext hU₀ eNext e z) hleft

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The square-sum integrand obtained from the edge-family residual readout
agrees with the source-side product residual square-sum under a pointwise
source-chart left-inverse hypothesis. -/
theorem aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hleft :
      case2PassiveThetaWithFollowingFactorEndpointSourceChartReadback
          W₂ B₂ n hS hnext hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z) = z) :
    aoyagiCoordinateSquareSum
        (case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout
          W₂ B₂ n hS hcont hnext hU₀ eNext e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z)) =
      aoyagiCoordinateSquareSum
        (case2PassiveThetaWithFollowingFactorProductResidualReadout
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e) := by
  rw [
    case2PassiveThetaWithFollowingFactorEndpointSourceChartReadbackProductResidualReadout_sourceChart_eq_of_leftInverse
      W₂ B₂ n hS hcont hnext hU₀ eNext e z hleft]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The raw fixed-base residual-block coordinate readout, reindexed to the
with-following Case 2 product-residual coordinates. -/
def case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ}
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (X :
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) :
    Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
  fun ij ↦
    paperEndpointFixedBaseResidualBlockCoordinateMap
      (K := ℝ) W₂ B₂ U₀ hU₀ (fun E :
        (∀ p : Fin 2,
          reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ) ↦ E) X
      (e (Fin.last 2) ij.1, e 0 ij.2)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On a determinant-chart source point, the raw fixed-base residual-block
coordinate readout of the endpoint source chart is the source-side
with-following product residual. -/
theorem case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout_sourceChart_eq_of_detChart
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet :
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e).detChart) :
    case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout
        W₂ B₂ n hU₀ e
        (case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e z) =
      case2PassiveThetaWithFollowingFactorProductResidualReadout
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e := by
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let EdgeFamily :=
    ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
  let retainedData :
      RetainedPassiveNonredundantCoordinateData
        (K := ℝ) (ρ := ρ) κ' :=
    case2PassiveThetaWithFollowingFactorEndpointRetainedData
      (ρ := ρ) n hS hcont hnext z eNext e
  let sourceChart : EdgeFamily :=
    case2PassiveThetaWithFollowingFactorEndpointSourceChart
      W₂ B₂ n hS hcont hnext hU₀ eNext e z
  have hedge :
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
        retainedData.edgeMatrix := by
    simpa [sourceChart, retainedData,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart] using
      paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
        (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) retainedData
  have hread :
      sourceReadback (K := ℝ) (ρ := ρ)
          (paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))) =
        retainedData := by
    exact
      sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
        (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
        (Cedge := fun E : EdgeFamily ↦ E) sourceChart retainedData hdet hedge
  funext ij
  have hcoord :=
    paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
      (K := ℝ) (W := W₂) (B := B₂) U₀ hU₀
      (fun E : EdgeFamily ↦ E) sourceChart
  have hcoord_ij := congrFun hcoord (e (Fin.last 2) ij.1, e 0 ij.2)
  simpa [
    sourceChart, retainedData, ρ, κ',
    case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout,
    case2PassiveThetaWithFollowingFactorProductResidualReadout, hread] using hcoord_ij

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Square-sum form of the raw fixed-base residual-block coordinate readout
identity for a determinant-chart source point. -/
theorem aoyagiCoordinateSquareSum_case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout_sourceChart_eq_of_detChart
    (W₂ : Fin 3 → Type v) [∀ i, AddCommGroup (W₂ i)]
    [∀ i, TopologicalSpace (W₂ i)] [∀ i, IsTopologicalAddGroup (W₂ i)]
    [∀ i, T2Space (W₂ i)] [∀ i, Module ℝ (W₂ i)]
    [∀ i, ContinuousSMul ℝ (W₂ i)]
    (B₂ : ∀ i : Fin 2, W₂ i.succ →ₗ[ℝ] W₂ i.castSucc)
    [∀ j, FiniteDimensional ℝ (W₂ j)]
    {τ : Type} [Fintype τ] (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    {U₀ : Submodule ℝ (reverseVertex W₂ 0)}
    (hU₀ : IsCompl U₀ (LinearMap.ker (paperTotalMap W₂ B₂)))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (z :
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet :
      (case2PassiveThetaWithFollowingFactorEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e).detChart) :
    aoyagiCoordinateSquareSum
        (case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout
          W₂ B₂ n hU₀ e
          (case2PassiveThetaWithFollowingFactorEndpointSourceChart
            W₂ B₂ n hS hcont hnext hU₀ eNext e z)) =
      aoyagiCoordinateSquareSum
        (case2PassiveThetaWithFollowingFactorProductResidualReadout
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e) := by
  rw [
    case2PassiveThetaWithFollowingFactorEndpointSourceChartRawEdgeProductResidualReadout_sourceChart_eq_of_detChart
      W₂ B₂ n hS hcont hnext hU₀ eNext e z hdet]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The raw-order two-stage proof composes several retained-passive local chart
-- normalizations and follows the existing non-following bridge's footprint.
/-- Relative local raw-order source-chart bridge for the enlarged
following-factor Case 2 passive theta coordinates.

Inside any prescribed open neighborhood of a determinant-sector,
nonzero-pivot base point, there is a smaller open neighborhood `V` on which
the raw-order p.13 source chart agrees with the direct enlarged endpoint
source chart.  Consequently the one-stage and two-stage raw-order
presentations of any restricted source-domain measure agree with the direct
source-chart pushforward.

This is only retained-passive source-chart bookkeeping.  It does not identify
raw Haar measure, prove a Jacobian or density formula for the enlarged
coordinate map, compare to the original source prior, prove source-image
coverage, construct normal crossings, compute pole order, or extract an RLCT.
-/
theorem exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
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
          RetainedPassiveNonredundantCoordinateData
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
    let rawMap :
        Case2PassiveThetaWithFollowingFactor
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun z ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext z eNext e)
    let rawChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        (∀ z ∈ V,
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext z eNext e ∈
              topologyTupleDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawMap z ∈
              topologyTupleRawOrderSourceRecursiveDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawChart (rawMap z) = sourceChart z ∧
            sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            readback (sourceChart z) = z) ∧
          ∀ [MeasurableSpace EdgeFamily] [BorelSpace EdgeFamily],
            ∀ sourceMeasure :
              Measure
                (Case2PassiveThetaWithFollowingFactor
                  (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
            let ν := sourceMeasure.restrict V
            let μ := Measure.map sourceChart ν
            let μrawComp :=
              Measure.map (fun z ↦ rawChart (rawMap z)) ν
            let μrawTwoStage :=
              Measure.map rawChart (Measure.map rawMap ν)
            μrawComp = μ ∧ μrawTwoStage = μ := by
  intro EdgeFamily retainedData sourceChart readback rawMap rawChart
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let RawTuple := TopologyTuple ρ κ' ℝ
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RawTuple :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  obtain ⟨Vread, hVread_open, hz₀Vread, hleft⟩ :=
    (by
      simpa [EdgeFamily, sourceChart, readback, ρ, κ'] using
        exists_open_case2PassiveThetaWithFollowingFactorEndpointSourceChart_readback_leftInverse
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let detSet : Set RawTuple :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  let D : Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    Y ⁻¹' detSet
  have hYcont : Continuous Y := by
    change Continuous
      (fun z : Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e)
    exact
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hDopen : IsOpen D :=
    hYcont.isOpen_preimage detSet
      (by
        simpa [detSet, ρ, κ'] using
          isOpen_topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ'))
  have hz₀D : z₀ ∈ D := by
    have hY₀ :
        Y z₀ ∈ detSet := by
      simpa [Y, detSet, ρ, κ'] using
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_mem_detChartSet
          (ρ := ρ) n hS hcont hnext z₀ eNext e hdet₀
    simpa [D] using hY₀
  let V : Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    G ∩ (Vread ∩ D)
  have hVopen : IsOpen V := hGopen.inter (hVread_open.inter hDopen)
  have hz₀V : z₀ ∈ V := ⟨hz₀G, ⟨hz₀Vread, hz₀D⟩⟩
  have hVG : V ⊆ G := Set.inter_subset_left
  have hdet_of_mem : ∀ z ∈ V, Y z ∈ detSet := by
    intro z hz
    have hzD : z ∈ D := hz.2.2
    simpa [D] using hzD
  have hdetV : ∀ z ∈ V, (retainedData z).detChart := by
    intro z hz
    exact
      (topologyTuple_mem_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z)).1
        (by simpa [Y, detSet, retainedData, κ'] using hdet_of_mem z hz)
  have hleftV : ∀ z ∈ V, readback (sourceChart z) = z := by
    intro z hz
    have hzread_fields :
        (Case2PassiveThetaWithFollowingFactor.mk
            (ρ := ρ) (τ := τ) (n := n) (S := S) (J := J)
            z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
            z.1.yNext z.2) ∈ Vread := by
      simpa [Case2PassiveThetaWithFollowingFactor.mk,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz.2.1
    simpa [sourceChart, readback,
      case2PassiveThetaWithFollowingFactorEndpointSourceChart,
      Case2PassiveThetaWithFollowingFactor.mk,
      Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
      hleft z.1.A1passive z.1.F2 z.1.A3passive z.1.Ctop z.1.F3
        z.1.yNext z.2 hzread_fields
  have hpoint :
      ∀ z ∈ V,
        Y z ∈ detSet ∧
          rawMap z ∈
            topologyTupleRawOrderSourceRecursiveDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ') ∧
          rawChart (rawMap z) = sourceChart z ∧
          sourceChart z ∈
            paperEndpointFixedBaseRetainedPassiveP13LocalSource
              W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
          (let E :=
            paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun p : Fin 2 ↦
                (sourceChart z p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
          sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z) ∧
          readback (sourceChart z) = z := by
    intro z hz
    have hYz : Y z ∈ detSet := hdet_of_mem z hz
    have hdet : (retainedData z).detChart := hdetV z hz
    have hrawMem :
        rawMap z ∈
          topologyTupleRawOrderSourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ') := by
      have hm :=
        mapsTo_topologyTupleEdgeRawOrder_detChartSet_rawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') hYz
      simpa [rawMap, Y, detSet, RawTuple, ρ, κ'] using hm
    have hrawEq : rawChart (rawMap z) = sourceChart z := by
      have h :=
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart_topologyTupleEdgeRawOrder_topologyTuple_eq_sourceEdgeFamilyOfData
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀)
          (data := retainedData z) hdet
      simpa [rawMap, rawChart, sourceChart, retainedData, Y,
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple, ρ, κ'] using h
    have hsource :
        sourceChart z ∈
          paperEndpointFixedBaseRetainedPassiveP13LocalSource
            W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) := by
      change
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) ∈
          sourceRecursiveDetChartSet
            (K := ℝ) (ρ := ρ) (κ' := κ')
      rw [show
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
              (fun p : Fin 2 ↦
                (sourceChart z p :
                  reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
            (retainedData z).edgeMatrix by
        simpa [sourceChart, retainedData,
          case2PassiveThetaWithFollowingFactorEndpointSourceChart] using
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
            (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)]
      exact
        (mem_sourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z).edgeMatrix).2
          (sourceRecursiveDetChart_edgeMatrix_of_detChart
            (K := ℝ) (ρ := ρ) (κ' := κ') (retainedData z) hdet)
    have hedge :
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ)) =
          (retainedData z).edgeMatrix := by
      simpa [sourceChart, retainedData,
        case2PassiveThetaWithFollowingFactorEndpointSourceChart] using
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges_retainedPassiveP13SourceEdgeFamilyOfData_eq
          (K := ℝ) W₂ B₂ (U₀ := U₀) (hU₀ := hU₀) (retainedData z)
    have hread :
        (let E :=
          paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
            (fun p : Fin 2 ↦
              (sourceChart z p :
                reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
        sourceReadback (K := ℝ) (ρ := ρ) E = retainedData z) := by
      simpa using
        sourceReadback_paperEndpointFixedBaseEdgeMatrix_eq_retainedPassiveData_of_edgeMatrix_eq
          (K := ℝ) (W := W₂) (B := B₂) (U₀ := U₀) (hU₀ := hU₀)
          (Cedge := fun E : EdgeFamily ↦ E) (sourceChart z) (retainedData z)
          hdet hedge
    exact ⟨hYz, hrawMem, hrawEq, hsource, hread, hleftV z hz⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_, ?_⟩
  · intro z hz
    have hzpoint := hpoint z hz
    exact
      ⟨by simpa [Y, detSet, ρ, κ'] using hzpoint.1,
        by simpa [rawMap, ρ, κ'] using hzpoint.2.1,
        by simpa [rawMap, rawChart, ρ, κ'] using hzpoint.2.2.1,
        hzpoint.2.2.2.1, hzpoint.2.2.2.2.1, hzpoint.2.2.2.2.2⟩
  · intro _ _ sourceMeasure ν μ μrawComp μrawTwoStage
    let T : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    have hrawMapContOn : ContinuousOn rawMap V := by
      rw [continuousOn_iff_continuous_restrict]
      let Sdet : Set RawTuple :=
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
      let toDetTuple : V → Sdet :=
        fun z ↦ ⟨Y z.1, by simpa [Sdet, detSet] using hdet_of_mem z.1 z.2⟩
      have hToDetTuple : Continuous toDetTuple := by
        have hamb : Continuous (fun z : V ↦ Y z.1) :=
          hYcont.comp continuous_subtype_val
        exact hamb.subtype_mk _
      have hrawDet :
          Continuous
            (fun y :
                topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
              topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
        continuous_topologyTupleEdgeRawOrder_detChart_subtype
          (K := ℝ) (ρ := ρ) (κ' := κ')
      simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
        hrawDet.comp hToDetTuple
    have hrawMap : AEMeasurable rawMap ν := by
      simpa [ν] using
        ContinuousOn.aemeasurable₀ hrawMapContOn
          hVopen.measurableSet.nullMeasurableSet
    have hraw_mem : ∀ᵐ z ∂ν, rawMap z ∈ T := by
      filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
      have hzpoint := hpoint z hz
      simpa [rawMap, T, RawTuple, ρ, κ'] using hzpoint.2.1
    have hT_meas : MeasurableSet T := by
      simpa [T, RawTuple, ρ, κ'] using
        (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
    have hraw_image_mem :
        ∀ᵐ y ∂Measure.map rawMap ν, y ∈ T :=
      (ae_map_iff hrawMap hT_meas).2 hraw_mem
    have hrawChartContOn : ContinuousOn rawChart T := by
      rw [continuousOn_iff_continuous_restrict]
      let toDetChart :
          T →
            {data :
              RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
              data.detChart} :=
        fun y ↦
          ⟨ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1),
            (mem_topologyTupleDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrderInverse
                (K := ℝ) (ρ := ρ) (κ' := κ') y.1)).1
              (topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
                (K := ℝ) (ρ := ρ) (κ' := κ') y.2)⟩
      have hInv :
          Continuous
            (fun y : T ↦
              topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
        continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
          (K := ℝ) (ρ := ρ) (κ' := κ')
      have hToDetChart : Continuous toDetChart := by
        have hamb :
            Continuous
              (fun y : T ↦
                ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
                  (topologyTupleEdgeRawOrderInverse
                    (K := ℝ) (ρ := ρ) (κ' := κ') y.1)) :=
          (continuous_ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp hInv
        exact hamb.subtype_mk _
      have hchart :
          Continuous
            (fun data :
                {data :
                  RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
                  data.detChart} ↦
              paperEndpointFixedBaseRetainedPassiveP13SourceChart W₂ B₂ U₀ hU₀ data) :=
        continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
          (K := ℝ) W₂ B₂ U₀ hU₀
      simpa [rawChart, T, RawTuple,
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart,
        paperEndpointFixedBaseRetainedPassiveP13SourceChart,
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData,
        toDetChart, ρ, κ'] using hchart.comp hToDetChart
    have hrawChart_restrict :
        AEMeasurable rawChart ((Measure.map rawMap ν).restrict T) :=
      ContinuousOn.aemeasurable₀ hrawChartContOn hT_meas.nullMeasurableSet
    have hraw_restrict_eq :
        (Measure.map rawMap ν).restrict T = Measure.map rawMap ν :=
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
    have hrawChart :
        AEMeasurable rawChart (Measure.map rawMap ν) := by
      simpa [hraw_restrict_eq] using hrawChart_restrict
    have hmap_assoc :
        Measure.map rawChart (Measure.map rawMap ν) =
          Measure.map (fun z ↦ rawChart (rawMap z)) ν := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable
          (μ := ν) (f := rawMap) (g := rawChart) hrawChart hrawMap)
    have hcomp :
        (fun z ↦ rawChart (rawMap z)) =ᵐ[ν] sourceChart := by
      filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
      have hzpoint := hpoint z hz
      simpa [rawMap, rawChart, ρ, κ'] using hzpoint.2.2.1
    have hcomp_map : μrawComp = μ := by
      simpa [ν, μ, μrawComp] using Measure.map_congr hcomp
    have htwo_stage : μrawTwoStage = μ := by
      calc
        μrawTwoStage =
            Measure.map (fun z ↦ rawChart (rawMap z)) ν := by
          simpa [μrawTwoStage] using hmap_assoc
        _ = μ := by
          simpa [ν, μ, μrawComp] using hcomp_map
    exact ⟨hcomp_map, htwo_stage⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The generic passive selected-entry source-measure theorem, specialized to
the concrete full `Case2PassiveTheta` coordinate domain.

The source-domain measure is arbitrary and is restricted to the local open
punctured determinant sector produced by the theorem.  The conclusion is only
support of the chart-produced source measure and exact recovery of the
selected residual `yNext` marginal.  It is not determinant-chart Haar
transport, source-prior transport, a passive-sector pushforward theorem,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_measure_map_case2PassiveThetaEndpointSourceChart_puncturedSector_inverseReadout_eq_yNext
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
    (sourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let pivotNext : center :=
      case2PassiveThetaPivotNext n hS hnext
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData
          W₂ B₂ U₀ hU₀ (retainedData theta)
    let residualCoordEquiv :
      AoyagiResidualBlockCoordinateIndex
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
      case2ResidualBlockCoordinateIndexEquivPivotEntriesOfEquivs
        n S (J + 1) (e (Fin.last 2)).symm ((e 0).symm.trans eNext)
    let inverseReadout : EdgeFamily → center → ℝ :=
      fun X ↦
        SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
          (fun i : center ↦
            paperEndpointFixedBaseResidualBlockCoordinateMap
              (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) X
              (residualCoordEquiv.symm i))
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        (∀ z ∈ V,
          sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            inverseReadout (sourceChart z) = z.yNext) ∧
        ∀ [MeasurableSpace EdgeFamily] [OpensMeasurableSpace EdgeFamily]
          [BorelSpace EdgeFamily],
            let μ := Measure.map sourceChart (sourceMeasure.restrict V)
            let localSource :=
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            μ.restrict localSource = μ ∧
              Measure.map inverseReadout μ =
                Measure.map Case2PassiveTheta.yNext (sourceMeasure.restrict V) := by
  intro center pivotNext EdgeFamily retainedData sourceChart residualCoordEquiv
    inverseReadout
  let ρ := Fin (Module.finrank ℝ U₀)
  let η : Type :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let A1passive : η → Fin 1 → Matrix ρ ρ ℝ := fun passive ↦ passive.1
  let F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
    fun passive ↦ passive.2.1
  let A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
    fun passive ↦ passive.2.2.1
  let Ctop : η → Matrix ρ ρ ℝ := fun passive ↦ passive.2.2.2.1
  let F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
    fun passive ↦ passive.2.2.2.2
  have hA1passive_cont : Continuous A1passive := by
    simpa [A1passive] using (continuous_fst : Continuous (fun passive : η ↦ passive.1))
  have hF2_cont : Continuous F2 := by
    simpa [F2] using
      (continuous_fst.comp continuous_snd :
        Continuous (fun passive : η ↦ passive.2.1))
  have hA3passive_cont : Continuous A3passive := by
    simpa [A3passive] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd) :
        Continuous (fun passive : η ↦ passive.2.2.1))
  have hCtop_cont : Continuous Ctop := by
    simpa [Ctop] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.1))
  have hF3_cont : Continuous F3 := by
    simpa [F3] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.2))
  have hdet₀' :
      IsUnit (z₀.Ctop.det) ∧
        ∀ p : Fin 1, IsUnit ((z₀.A1passive p).det) := by
    simpa [case2PassiveThetaDetSector] using hdet₀
  have hCtop₀ : IsUnit ((Ctop z₀.1).det) := by
    simpa [Ctop, Case2PassiveTheta.Ctop] using hdet₀'.1
  have hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det) := by
    intro p
    simpa [A1passive, Case2PassiveTheta.A1passive] using hdet₀'.2 p
  have hpivot₀' :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0 := by
    simpa [case2PassiveThetaPivotNonzero, case2PassiveThetaPivotNext,
      Case2PassiveTheta.yNext] using hpivot₀
  simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
    residualCoordEquiv, inverseReadout, case2PassiveThetaEndpointRetainedData,
    case2PassiveThetaRetainedData, Case2PassiveTheta.A1passive,
    Case2PassiveTheta.F2, Case2PassiveTheta.A3passive,
    Case2PassiveTheta.Ctop, Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_inverseReadout_eq_snd
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' sourceMeasure

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Locally, the concrete endpoint source chart has a left inverse on full
Case 2 passive theta coordinates.

This is a pointwise local coordinate theorem.  It intersects the determinant
source-readback neighborhood with the open nonzero-pivot condition, then uses
the selected-entry inverse readout.  It does not assert endpoint-sector
measurability, image equality, Haar transport, source-prior comparison, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let readback : EdgeFamily →
        Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
      case2PassiveThetaEndpointSourceChartReadback
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ z ∈ V, readback (sourceChart z) = z := by
  intro EdgeFamily sourceChart readback
  let ρ := Fin (Module.finrank ℝ U₀)
  let η : Type :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let A1passive : η → Fin 1 → Matrix ρ ρ ℝ := fun passive ↦ passive.1
  let F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
    fun passive ↦ passive.2.1
  let A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
    fun passive ↦ passive.2.2.1
  let Ctop : η → Matrix ρ ρ ℝ := fun passive ↦ passive.2.2.2.1
  let F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
    fun passive ↦ passive.2.2.2.2
  have hA1passive_cont : Continuous A1passive := by
    simpa [A1passive] using (continuous_fst : Continuous (fun passive : η ↦ passive.1))
  have hF2_cont : Continuous F2 := by
    simpa [F2] using
      (continuous_fst.comp continuous_snd :
        Continuous (fun passive : η ↦ passive.2.1))
  have hA3passive_cont : Continuous A3passive := by
    simpa [A3passive] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd) :
        Continuous (fun passive : η ↦ passive.2.2.1))
  have hCtop_cont : Continuous Ctop := by
    simpa [Ctop] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.1))
  have hF3_cont : Continuous F3 := by
    simpa [F3] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.2))
  have hdet₀' :
      IsUnit (z₀.Ctop.det) ∧
        ∀ p : Fin 1, IsUnit ((z₀.A1passive p).det) := by
    simpa [case2PassiveThetaDetSector] using hdet₀
  have hCtop₀ : IsUnit ((Ctop z₀.1).det) := by
    simpa [Ctop, Case2PassiveTheta.Ctop] using hdet₀'.1
  have hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det) := by
    intro p
    simpa [A1passive, Case2PassiveTheta.A1passive] using hdet₀'.2 p
  let center : Finset (ℕ × ℕ) :=
    case2ResidualBlockPivotEntries n S (J + 1)
  let pivotNext : center :=
    case2PassiveThetaPivotNext n hS hnext
  let retainedData :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        RetainedPassiveNonredundantCoordinateData
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
    fun theta ↦
      case2PassiveThetaEndpointRetainedData
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
  let residualCoordEquiv :
    AoyagiResidualBlockCoordinateIndex
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ (Fin.last 2))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ 0) ≃ center :=
    case2PassiveThetaEndpointResidualCoordEquiv W₂ B₂ n eNext e
  rcases
      (by
        simpa [center, pivotNext, EdgeFamily, retainedData, sourceChart,
          residualCoordEquiv, case2PassiveThetaEndpointSourceChart,
          case2PassiveThetaEndpointResidualCoordEquiv,
          case2PassiveThetaEndpointRetainedData, case2PassiveThetaRetainedData,
          Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
          Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
          Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
          A1passive, F2, A3passive, Ctop, F3, η, ρ] using
          exists_open_case2EndpointTransport_withPassive_detChart_sourceReadback_eq_preimageOfPivotNeZero_residualReadout_eq
            W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
            A1passive F2 A3passive Ctop F3
            hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
            z₀ hCtop₀ hA1passive₀) with
    ⟨Udet, hUdet_open, hz₀Udet, hUdet_raw⟩
  let pivotSet :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    {z | z.yNext (case2PassiveThetaPivotNext n hS hnext) ≠ 0}
  have hpivotSet_open : IsOpen pivotSet := by
    have hpivot_cont :
        Continuous
          (fun z :
              Case2PassiveTheta
                (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦
            z.yNext (case2PassiveThetaPivotNext n hS hnext)) := by
      simpa [Case2PassiveTheta.yNext] using
        ((continuous_apply (case2PassiveThetaPivotNext n hS hnext)).comp
          (continuous_snd :
            Continuous
              (fun z :
                  Case2PassiveTheta
                    (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J ↦ z.2)))
    simpa [pivotSet] using (isOpen_ne.preimage hpivot_cont)
  let V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    Udet ∩ pivotSet
  have hVopen : IsOpen V := hUdet_open.inter hpivotSet_open
  have hz₀V : z₀ ∈ V := by
    exact ⟨hz₀Udet, by simpa [pivotSet] using hpivot₀⟩
  refine ⟨V, hVopen, hz₀V, ?_⟩
  intro z hzV
  have hzUdet : z ∈ Udet := hzV.1
  have hzpivot :
      z.yNext (case2PassiveThetaPivotNext n hS hnext) ≠ 0 := by
    simpa [V, pivotSet] using hzV.2
  have hzUdet_fields :
      ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈ Udet := by
    simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
      Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
      Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hzUdet
  have hbase :=
    hUdet_raw z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext hzUdet_fields
  let E :=
    paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
      (fun p : Fin 2 ↦
        (sourceChart z p :
          reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
  have hread :
      (let E :=
        paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
          (fun p : Fin 2 ↦
            (sourceChart z p :
              reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
      sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
        retainedData z) := by
    simpa [E, retainedData, ρ] using hbase.2.1
  have hinv :
      case2PassiveThetaEndpointInverseReadout
          W₂ B₂ n hS hnext hU₀ eNext e (sourceChart z) =
        z.yNext := by
    have hcoord :
        (fun i : center ↦
          paperEndpointFixedBaseResidualBlockCoordinateMap
            (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
            (sourceChart z) (residualCoordEquiv.symm i)) =
          fun i : center ↦
            AoyagiResidualBlockCoordinateIndex.value
              (residualFactorProduct
                (sourceReadback (K := ℝ) (ρ := ρ) E).C
                (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
              (residualCoordEquiv.symm i) := by
      funext i
      have hmap :=
        paperEndpointFixedBaseResidualBlockCoordinateMap_eq_sourceReadback_residualFactorProduct
          (K := ℝ) (W := W₂) (B := B₂) U₀ hU₀
          (fun E : EdgeFamily ↦ E) (sourceChart z)
      simpa [E, ρ] using congrFun hmap (residualCoordEquiv.symm i)
    have hpre :
        SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
            (fun i : center ↦
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z) (residualCoordEquiv.symm i)) =
          SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
            (fun i : center ↦
              AoyagiResidualBlockCoordinateIndex.value
                (residualFactorProduct
                  (sourceReadback (K := ℝ) (ρ := ρ) E).C
                  (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
                (residualCoordEquiv.symm i)) := by
      exact congrArg
        (SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext) hcoord
    have hzpivot' : z.2 pivotNext ≠ 0 := by
      simpa [pivotNext, Case2PassiveTheta.yNext] using hzpivot
    calc
      case2PassiveThetaEndpointInverseReadout
          W₂ B₂ n hS hnext hU₀ eNext e (sourceChart z) =
          SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
            (fun i : center ↦
              paperEndpointFixedBaseResidualBlockCoordinateMap
                (K := ℝ) W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E)
                (sourceChart z) (residualCoordEquiv.symm i)) := by
        rfl
      _ =
          SelectedEntrySignedBox.CenterCoord.preimageOfPivotNeZero pivotNext
            (fun i : center ↦
              AoyagiResidualBlockCoordinateIndex.value
                (residualFactorProduct
                  (sourceReadback (K := ℝ) (ρ := ρ) E).C
                  (Fin.last 2) 0 (Fin.zero_le (Fin.last 2)))
                (residualCoordEquiv.symm i)) := hpre
      _ = z.yNext := by
        simpa [Case2PassiveTheta.yNext] using hbase.2.2 hzpivot'
  exact
    case2PassiveThetaEndpointSourceChartReadback_eq_of_sourceReadback_eq_retainedData
      W₂ B₂ n hS hcont hnext hU₀ eNext e z (sourceChart z) hread hinv

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- This is the pointwise, non-measure specialization of the generic passive
-- selected-entry raw-order bridge; the same large definitional `simpa` is
-- needed as in the measure wrapper below.
/-- The concrete passive-theta endpoint topology tuple locally gives the direct
p.13 source chart after raw-order reindexing.

This is the pointwise local chart bridge used for injectivity.  It does not
assert any measure pushforward, image measurability, Haar transport,
source-prior comparison, normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let inverseReadout : EdgeFamily → center → ℝ :=
      case2PassiveThetaEndpointInverseReadout
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        ∀ z ∈ V,
          case2PassiveThetaEndpointTopologyTuple
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext z eNext e ∈
              topologyTupleDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawMap z ∈
              topologyTupleRawOrderSourceRecursiveDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawChart (rawMap z) = sourceChart z ∧
            sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            inverseReadout (sourceChart z) = z.yNext := by
  intro center EdgeFamily retainedData sourceChart rawMap rawChart
    inverseReadout
  let ρ := Fin (Module.finrank ℝ U₀)
  let η : Type :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let A1passive : η → Fin 1 → Matrix ρ ρ ℝ := fun passive ↦ passive.1
  let F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
    fun passive ↦ passive.2.1
  let A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
    fun passive ↦ passive.2.2.1
  let Ctop : η → Matrix ρ ρ ℝ := fun passive ↦ passive.2.2.2.1
  let F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
    fun passive ↦ passive.2.2.2.2
  have hA1passive_cont : Continuous A1passive := by
    simpa [A1passive] using (continuous_fst : Continuous (fun passive : η ↦ passive.1))
  have hF2_cont : Continuous F2 := by
    simpa [F2] using
      (continuous_fst.comp continuous_snd :
        Continuous (fun passive : η ↦ passive.2.1))
  have hA3passive_cont : Continuous A3passive := by
    simpa [A3passive] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd) :
        Continuous (fun passive : η ↦ passive.2.2.1))
  have hCtop_cont : Continuous Ctop := by
    simpa [Ctop] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.1))
  have hF3_cont : Continuous F3 := by
    simpa [F3] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.2))
  have hdet₀' :
      IsUnit (z₀.Ctop.det) ∧
        ∀ p : Fin 1, IsUnit ((z₀.A1passive p).det) := by
    simpa [case2PassiveThetaDetSector] using hdet₀
  have hCtop₀ : IsUnit ((Ctop z₀.1).det) := by
    simpa [Ctop, Case2PassiveTheta.Ctop] using hdet₀'.1
  have hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det) := by
    intro p
    simpa [A1passive, Case2PassiveTheta.A1passive] using hdet₀'.2 p
  have hpivot₀' :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0 := by
    simpa [case2PassiveThetaPivotNonzero, case2PassiveThetaPivotNext,
      Case2PassiveTheta.yNext] using hpivot₀
  simpa [center, EdgeFamily, retainedData, sourceChart, rawMap,
    rawChart, inverseReadout, case2PassiveThetaEndpointSourceChart,
    case2PassiveThetaEndpointResidualCoordEquiv,
    case2PassiveThetaEndpointInverseReadout, case2PassiveThetaEndpointTopologyTuple,
    case2PassiveThetaEndpointRetainedData, case2PassiveThetaRetainedData,
    Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
    Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_open_case2EndpointTransport_withPassive_topologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀'

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Locally, both the concrete endpoint source chart and the endpoint topology
tuple map are injective on full Case 2 passive theta coordinates.

This is local coordinate injectivity only.  It does not assert image
measurability, image equality, Haar transport, source-prior comparison, normal
crossings, pole order, or RLCT extraction. -/
theorem exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀) :
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let Y :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun theta ↦
        case2PassiveThetaEndpointTopologyTuple
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        Set.InjOn sourceChart V ∧ Set.InjOn Y V := by
  intro EdgeFamily sourceChart Y
  let readback : EdgeFamily →
      Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J :=
    case2PassiveThetaEndpointSourceChartReadback
      W₂ B₂ n hS hnext hU₀ eNext e
  obtain ⟨Vread, hVread_open, hz₀_read, hleft⟩ :=
    (by
      simpa [EdgeFamily, sourceChart, readback] using
        exists_open_case2PassiveThetaEndpointSourceChart_readback_leftInverse
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let rawMap :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
    fun theta ↦
      topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
        (κ' := throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
        (Y theta)
  let rawChart :
      TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
        EdgeFamily :=
    paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
      (K := ℝ) W₂ B₂ U₀ hU₀
  obtain ⟨Vraw, hVraw_open, hz₀_raw, hraw⟩ :=
    (by
      simpa [EdgeFamily, sourceChart, Y, rawMap, rawChart,
        case2PassiveThetaEndpointTopologyTuple] using
        exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    Vread ∩ Vraw
  have hV_open : IsOpen V := hVread_open.inter hVraw_open
  have hz₀V : z₀ ∈ V := ⟨hz₀_read, hz₀_raw⟩
  have hsource_inj : Set.InjOn sourceChart V := by
    intro z hz z' hz' hsrc
    have hleft_z : readback (sourceChart z) = z := by
      have hzread_fields :
          ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
            Vread := by
        simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
          Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
          Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz.1
      simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
        hleft z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
          hzread_fields
    have hleft_z' : readback (sourceChart z') = z' := by
      have hzread_fields :
          ((z'.A1passive, z'.F2, z'.A3passive, z'.Ctop, z'.F3), z'.yNext) ∈
            Vread := by
        simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
          Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
          Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz'.1
      simpa [sourceChart, readback, case2PassiveThetaEndpointSourceChart,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using
        hleft z'.A1passive z'.F2 z'.A3passive z'.Ctop z'.F3 z'.yNext
          hzread_fields
    calc
      z = readback (sourceChart z) := by
        exact hleft_z.symm
      _ = readback (sourceChart z') := by
        rw [hsrc]
      _ = z' := hleft_z'
  have hY_inj : Set.InjOn Y V := by
    intro z hz z' hz' hYeq
    have hrawMap_eq : rawMap z = rawMap z' := by
      simpa [rawMap] using congrArg
        (fun y :
            TopologyTuple (Fin (Module.finrank ℝ U₀))
              (throughSubspaceEndpointComplementIndex
                (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ ↦
          topologyTupleEdgeRawOrder
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (κ' := throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) y) hYeq
    have hraw_eq : rawChart (rawMap z) = sourceChart z := by
      have hzraw_fields :
          ((z.A1passive, z.F2, z.A3passive, z.Ctop, z.F3), z.yNext) ∈
            Vraw := by
        simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
          Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
          Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz.2
      rcases
          hraw z.A1passive z.F2 z.A3passive z.Ctop z.F3 z.yNext
            hzraw_fields with
        ⟨_hYdet, _hrawMem, hraw_eq_raw, _hlocal, _hread, _hinv⟩
      simpa [sourceChart, rawMap, rawChart, Y,
        case2PassiveThetaEndpointSourceChart,
        case2PassiveThetaEndpointTopologyTuple,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hraw_eq_raw
    have hraw_eq' : rawChart (rawMap z') = sourceChart z' := by
      have hzraw_fields :
          ((z'.A1passive, z'.F2, z'.A3passive, z'.Ctop, z'.F3), z'.yNext) ∈
            Vraw := by
        simpa [Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
          Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
          Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hz'.2
      rcases
          hraw z'.A1passive z'.F2 z'.A3passive z'.Ctop z'.F3 z'.yNext
            hzraw_fields with
        ⟨_hYdet', _hrawMem', hraw_eq_raw, _hlocal', _hread', _hinv'⟩
      simpa [sourceChart, rawMap, rawChart, Y,
        case2PassiveThetaEndpointSourceChart,
        case2PassiveThetaEndpointTopologyTuple,
        Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
        Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
        Case2PassiveTheta.F3, Case2PassiveTheta.yNext] using hraw_eq_raw
    have hsrc : sourceChart z = sourceChart z' := by
      calc
        sourceChart z = rawChart (rawMap z) := hraw_eq.symm
        _ = rawChart (rawMap z') := by rw [hrawMap_eq]
        _ = sourceChart z' := hraw_eq'
    exact hsource_inj hz hz' hsrc
  exact ⟨V, hV_open, hz₀V, hsource_inj, hY_inj⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- There is a local endpoint theta sector whose image is measurable, under
the standard Polish/Borel hypotheses needed for Lusin-Souslin.

This only proves measurability of the local image sector.  It does not prove
global sector measurability, image equality beyond the definition of
`case2PassiveThetaEndpointSectorSet`, Haar transport, source-prior comparison,
normal crossings, pole order, or RLCT extraction. -/
theorem exists_open_measurableSet_case2PassiveThetaEndpointSectorSet
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
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
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀) :
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        MeasurableSet
          (case2PassiveThetaEndpointSectorSet
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext eNext e V) := by
  let Y :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
  obtain ⟨V, hVopen, hz₀V, _hsourceInj, hYinj⟩ :=
    (by
      simpa [Y] using
        exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hYcont : ContinuousOn Y V :=
    (continuous_case2PassiveThetaEndpointTopologyTuple
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext eNext e).continuousOn
  have himage : MeasurableSet (Y '' V) :=
    hVmeas.image_of_continuousOn_injOn hYcont hYinj
  refine ⟨V, hVopen, hz₀V, ?_⟩
  simpa [Y, case2PassiveThetaEndpointSectorSet] using himage

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Relative local endpoint image measurability: inside any prescribed open
neighborhood of a determinant-sector, nonzero-pivot base point, there is a
smaller open neighborhood whose endpoint theta sector image is measurable.

This is the local injectivity/Lusin-Souslin theorem with one additional
intersection.  It does not prove global endpoint-sector measurability, Haar
transport, source-prior comparison, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [OpensMeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    [T2Space
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        MeasurableSet
          (case2PassiveThetaEndpointSectorSet
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext eNext e V) := by
  let Y :
      Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
        TopologyTuple (Fin (Module.finrank ℝ U₀))
          (throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
  obtain ⟨V₀, hV₀open, hz₀V₀, _hsourceInj, hYinj⟩ :=
    (by
      simpa [Y] using
        exists_open_case2PassiveThetaEndpointTopologyTuple_sourceChart_injOn
          W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
          z₀ hdet₀ hpivot₀)
  let V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    G ∩ V₀
  have hVopen : IsOpen V := hGopen.inter hV₀open
  have hz₀V : z₀ ∈ V := ⟨hz₀G, hz₀V₀⟩
  have hVG : V ⊆ G := Set.inter_subset_left
  have hVmeas : MeasurableSet V := hVopen.measurableSet
  have hYcont : ContinuousOn Y V :=
    (continuous_case2PassiveThetaEndpointTopologyTuple
      (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext eNext e).continuousOn
  have hYinjV : Set.InjOn Y V := by
    intro z hz z' hz' hzz'
    exact hYinj hz.2 hz'.2 hzz'
  have himage : MeasurableSet (Y '' V) :=
    hVmeas.image_of_continuousOn_injOn hYcont hYinjV
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  simpa [Y, V, case2PassiveThetaEndpointSectorSet] using himage

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The final specialization is a large definitional `simpa` over the generic
-- passive selected-entry theorem and needs the same budget as that bridge.
/-- The concrete passive-theta endpoint topology tuple gives the direct p.13
source chart after local raw-order reindexing.

This is the `Case2PassiveTheta` specialization of the generic passive
selected-entry raw-order bridge.  It proves a local pointwise chart equality
and the corresponding restricted one-stage/two-stage pushforward identities;
it is not determinant-chart Haar transport, source-prior transport, a
Jacobian formula, source-image coverage, normal crossings, pole order, or RLCT
extraction. -/
theorem exists_open_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
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
    (sourceMeasure :
      Measure
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let inverseReadout : EdgeFamily → center → ℝ :=
      case2PassiveThetaEndpointInverseReadout
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧
        (∀ z ∈ V,
          rawMap z ∈
              topologyTupleRawOrderSourceRecursiveDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawChart (rawMap z) = sourceChart z ∧
            sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            inverseReadout (sourceChart z) = z.yNext) ∧
        ∀ [MeasurableSpace
              (TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
            [BorelSpace
              (TopologyTuple (Fin (Module.finrank ℝ U₀))
                (throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
            [MeasurableSpace EdgeFamily] [BorelSpace EdgeFamily],
            let ν := sourceMeasure.restrict V
            let μ := Measure.map sourceChart ν
            let μrawComp :=
              Measure.map (fun z ↦ rawChart (rawMap z)) ν
            let μrawTwoStage :=
              Measure.map rawChart (Measure.map rawMap ν)
            μrawComp = μ ∧ μrawTwoStage = μ := by
  intro center EdgeFamily retainedData sourceChart rawMap rawChart
    inverseReadout
  let ρ := Fin (Module.finrank ℝ U₀)
  let η : Type :=
    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J
  let A1passive : η → Fin 1 → Matrix ρ ρ ℝ := fun passive ↦ passive.1
  let F2 : η → ∀ p : Fin 2,
      Matrix ρ (case2PostPivotTwoEdgeDomain n S J τ p.castSucc) ℝ :=
    fun passive ↦ passive.2.1
  let A3passive : η → ∀ p : Fin 1,
      Matrix (case2PostPivotTwoEdgeDomain n S J τ p.castSucc.succ) ρ ℝ :=
    fun passive ↦ passive.2.2.1
  let Ctop : η → Matrix ρ ρ ℝ := fun passive ↦ passive.2.2.2.1
  let F3 : η →
      Matrix (case2PostPivotTwoEdgeDomain n S J τ (Fin.last 2)) ρ ℝ :=
    fun passive ↦ passive.2.2.2.2
  have hA1passive_cont : Continuous A1passive := by
    simpa [A1passive] using (continuous_fst : Continuous (fun passive : η ↦ passive.1))
  have hF2_cont : Continuous F2 := by
    simpa [F2] using
      (continuous_fst.comp continuous_snd :
        Continuous (fun passive : η ↦ passive.2.1))
  have hA3passive_cont : Continuous A3passive := by
    simpa [A3passive] using
      (continuous_fst.comp (continuous_snd.comp continuous_snd) :
        Continuous (fun passive : η ↦ passive.2.2.1))
  have hCtop_cont : Continuous Ctop := by
    simpa [Ctop] using
      (continuous_fst.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.1))
  have hF3_cont : Continuous F3 := by
    simpa [F3] using
      (continuous_snd.comp
        (continuous_snd.comp (continuous_snd.comp continuous_snd)) :
        Continuous (fun passive : η ↦ passive.2.2.2.2))
  have hdet₀' :
      IsUnit (z₀.Ctop.det) ∧
        ∀ p : Fin 1, IsUnit ((z₀.A1passive p).det) := by
    simpa [case2PassiveThetaDetSector] using hdet₀
  have hCtop₀ : IsUnit ((Ctop z₀.1).det) := by
    simpa [Ctop, Case2PassiveTheta.Ctop] using hdet₀'.1
  have hA1passive₀ : ∀ p : Fin 1, IsUnit ((A1passive z₀.1 p).det) := by
    intro p
    simpa [A1passive, Case2PassiveTheta.A1passive] using hdet₀'.2 p
  have hpivot₀' :
      z₀.2
        (⟨(J + 2, J + 2),
          case2_displayedPivot_mem_residualBlockPivotEntries_of_cont n hS hnext⟩ :
          {p : ℕ × ℕ // p ∈ case2ResidualBlockPivotEntries n S (J + 1)}) ≠ 0 := by
    simpa [case2PassiveThetaPivotNonzero, case2PassiveThetaPivotNext,
      Case2PassiveTheta.yNext] using hpivot₀
  simpa [center, EdgeFamily, retainedData, sourceChart, rawMap,
    rawChart, inverseReadout, case2PassiveThetaEndpointSourceChart,
    case2PassiveThetaEndpointResidualCoordEquiv,
    case2PassiveThetaEndpointInverseReadout, case2PassiveThetaEndpointTopologyTuple,
    case2PassiveThetaEndpointRetainedData, case2PassiveThetaRetainedData,
    Case2PassiveTheta.A1passive, Case2PassiveTheta.F2,
    Case2PassiveTheta.A3passive, Case2PassiveTheta.Ctop,
    Case2PassiveTheta.F3, Case2PassiveTheta.yNext,
    A1passive, F2, A3passive, Ctop, F3, η, ρ] using
    exists_open_measure_map_case2EndpointTransport_withPassive_puncturedSector_rawOrderMap_twoStage_eq_sourceChart_inverseReadout_eq_snd
      W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
      A1passive F2 A3passive Ctop F3
      hA1passive_cont hF2_cont hA3passive_cont hCtop_cont hF3_cont
      z₀ hCtop₀ hA1passive₀ hpivot₀' sourceMeasure

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The relative wrapper normalizes a large concrete passive-theta specialization
-- and rebuilds the local a.e. measurability package around the same shrink.
/-- Relative local endpoint sector and raw-order source-chart package.

Inside any prescribed open neighborhood `G` of a determinant-sector,
nonzero-pivot base theta point, there is a smaller open neighborhood `V`.
On this same `V`, the endpoint topology-tuple image is measurable, the
raw-order source chart agrees pointwise with the direct p.13 source chart, and
the one-stage and two-stage raw-order pushforward presentations agree with
the direct source-chart pushforward for any source measure restricted to `V`.

This is local chart-produced source bookkeeping.  It does not identify
determinant-chart Haar measure, raw-order Haar measure, an original source
prior, exact passive-sector pushforward, source-image equality, source-rank
coverage, normal crossings, pole order, or RLCT. -/
theorem exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
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
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [OpensMeasurableSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveTheta
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveTheta
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
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let center : Finset (ℕ × ℕ) :=
      case2ResidualBlockPivotEntries n S (J + 1)
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let retainedData :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          RetainedPassiveNonredundantCoordinateData
            (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) :=
      fun theta ↦
        case2PassiveThetaEndpointRetainedData
          (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e
    let sourceChart :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    let rawMap :
        Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J →
          TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
          (κ' := throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀)
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := Fin (Module.finrank ℝ U₀)) n hS hcont hnext theta eNext e)
    let rawChart :
        TopologyTuple (Fin (Module.finrank ℝ U₀))
            (throughSubspaceEndpointComplementIndex
              (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ →
          EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let inverseReadout : EdgeFamily → center → ℝ :=
      case2PassiveThetaEndpointInverseReadout
        W₂ B₂ n hS hnext hU₀ eNext e
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        MeasurableSet
          (case2PassiveThetaEndpointSectorSet
            (ρ := Fin (Module.finrank ℝ U₀))
            n hS hcont hnext eNext e V) ∧
        (∀ z ∈ V,
          case2PassiveThetaEndpointTopologyTuple
                (ρ := Fin (Module.finrank ℝ U₀))
                n hS hcont hnext z eNext e ∈
              topologyTupleDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawMap z ∈
              topologyTupleRawOrderSourceRecursiveDetChartSet
                (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                (κ' := throughSubspaceEndpointComplementIndex
                  (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
            rawChart (rawMap z) = sourceChart z ∧
            sourceChart z ∈
              paperEndpointFixedBaseRetainedPassiveP13LocalSource
                W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
            (let E :=
              paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                (fun p : Fin 2 ↦
                  (sourceChart z p :
                    reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
            sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
              retainedData z) ∧
            inverseReadout (sourceChart z) = z.yNext) ∧
          ∀ [MeasurableSpace EdgeFamily] [BorelSpace EdgeFamily],
            ∀ sourceMeasure :
              Measure
                (Case2PassiveTheta
                  (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
            let ν := sourceMeasure.restrict V
            let μ := Measure.map sourceChart ν
            let μrawComp :=
              Measure.map (fun z ↦ rawChart (rawMap z)) ν
            let μrawTwoStage :=
              Measure.map rawChart (Measure.map rawMap ν)
            μrawComp = μ ∧ μrawTwoStage = μ := by
  intro center EdgeFamily retainedData sourceChart rawMap rawChart inverseReadout
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
  let RawTuple := TopologyTuple ρ κ' ℝ
  have hraw_exists :
      ∃ Vraw :
        Set
          (Case2PassiveTheta
            (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
        IsOpen Vraw ∧ z₀ ∈ Vraw ∧
          ∀ z ∈ Vraw,
            case2PassiveThetaEndpointTopologyTuple
                  (ρ := Fin (Module.finrank ℝ U₀))
                  n hS hcont hnext z eNext e ∈
                topologyTupleDetChartSet
                  (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
              rawMap z ∈
                topologyTupleRawOrderSourceRecursiveDetChartSet
                  (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀))
                  (κ' := throughSubspaceEndpointComplementIndex
                    (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ∧
              rawChart (rawMap z) = sourceChart z ∧
              sourceChart z ∈
                paperEndpointFixedBaseRetainedPassiveP13LocalSource
                  W₂ B₂ U₀ hU₀ (fun E : EdgeFamily ↦ E) ∧
              (let E :=
                paperEndpointFixedBaseEdgeMatrixOfReverseEdges W₂ B₂ U₀ hU₀
                  (fun p : Fin 2 ↦
                    (sourceChart z p :
                      reverseVertex W₂ p.castSucc →ₗ[ℝ] reverseVertex W₂ p.succ))
              sourceReadback (K := ℝ) (ρ := Fin (Module.finrank ℝ U₀)) E =
                retainedData z) ∧
              inverseReadout (sourceChart z) = z.yNext := by
    simpa [center, EdgeFamily, retainedData, sourceChart, rawMap, rawChart,
      inverseReadout] using
      exists_open_case2PassiveThetaEndpointTopologyTuple_rawOrderSourceChart_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀
  rcases hraw_exists with
    ⟨Vraw, hVraw_open, hz₀Vraw, hraw⟩
  let Graw :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J) :=
    G ∩ Vraw
  have hGraw_open : IsOpen Graw := hGopen.inter hVraw_open
  have hz₀Graw : z₀ ∈ Graw := ⟨hz₀G, hz₀Vraw⟩
  rcases
      exists_open_subset_measurableSet_case2PassiveThetaEndpointSectorSet
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ Graw hGraw_open hz₀Graw with
    ⟨V, hVopen, hz₀V, hVGraw, hsector⟩
  have hVG : V ⊆ G := fun z hz ↦ (hVGraw hz).1
  have hVVraw : V ⊆ Vraw := fun z hz ↦ (hVGraw hz).2
  refine ⟨V, hVopen, hz₀V, hVG, hsector, ?_, ?_⟩
  · intro z hz
    have hpoint := hraw z (hVVraw hz)
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [ρ, κ'] using hpoint.1
    · simpa [rawMap, ρ, κ'] using hpoint.2.1
    · simpa [rawMap, rawChart, ρ, κ'] using hpoint.2.2.1
    · exact hpoint.2.2.2.1
    · exact hpoint.2.2.2.2.1
    · exact hpoint.2.2.2.2.2
  · intro _ _ sourceMeasure ν μ μrawComp μrawTwoStage
    let T : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    have hdet_of_mem :
        ∀ z ∈ V,
          case2PassiveThetaEndpointTopologyTuple
                (ρ := ρ) n hS hcont hnext z eNext e ∈
            topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
      intro z hz
      have hpoint := hraw z (hVVraw hz)
      simpa [ρ, κ'] using hpoint.1
    have hrawMapContOn : ContinuousOn rawMap V := by
      rw [continuousOn_iff_continuous_restrict]
      let S : Set RawTuple :=
        topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
      let toDetTuple : V → S :=
        fun z ↦
          ⟨case2PassiveThetaEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e,
            hdet_of_mem z.1 z.2⟩
      have hToDetTuple : Continuous toDetTuple := by
        have hamb :
            Continuous
              (fun z : V ↦
                case2PassiveThetaEndpointTopologyTuple
                  (ρ := ρ) n hS hcont hnext z.1 eNext e) :=
          (continuous_case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext eNext e).comp continuous_subtype_val
        exact hamb.subtype_mk _
      have hrawDet :
          Continuous
            (fun y :
                topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
              topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
        continuous_topologyTupleEdgeRawOrder_detChart_subtype
          (K := ℝ) (ρ := ρ) (κ' := κ')
      simpa [rawMap, toDetTuple, S, RawTuple, ρ, κ'] using hrawDet.comp hToDetTuple
    have hrawMap :
        AEMeasurable rawMap ν := by
      simpa [ν] using
        ContinuousOn.aemeasurable₀ hrawMapContOn
          hVopen.measurableSet.nullMeasurableSet
    have hraw_mem :
        ∀ᵐ z ∂ν, rawMap z ∈ T := by
      filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
      have hpoint := hraw z (hVVraw hz)
      simpa [rawMap, T, RawTuple, ρ, κ'] using hpoint.2.1
    have hT_meas : MeasurableSet T := by
      simpa [T, RawTuple, ρ, κ'] using
        (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
          (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
    have hraw_image_mem :
        ∀ᵐ y ∂Measure.map rawMap ν, y ∈ T :=
      (ae_map_iff hrawMap hT_meas).2 hraw_mem
    have hrawChartContOn : ContinuousOn rawChart T := by
      rw [continuousOn_iff_continuous_restrict]
      let toDetChart :
          T →
            {data :
              RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
              data.detChart} :=
        fun y ↦
          ⟨ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1),
            (mem_topologyTupleDetChartSet
              (K := ℝ) (ρ := ρ) (κ' := κ')
              (topologyTupleEdgeRawOrderInverse
                (K := ℝ) (ρ := ρ) (κ' := κ') y.1)).1
              (topologyTupleEdgeRawOrderInverse_mem_topologyTupleDetChartSet
                (K := ℝ) (ρ := ρ) (κ' := κ') y.2)⟩
      have hInv :
          Continuous
            (fun y : T ↦
              topologyTupleEdgeRawOrderInverse (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
        continuous_topologyTupleEdgeRawOrderInverse_rawOrderSourceRecursiveDetChart_subtype
          (K := ℝ) (ρ := ρ) (κ' := κ')
      have hToDetChart : Continuous toDetChart := by
        have hamb :
            Continuous
              (fun y : T ↦
                ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')
                  (topologyTupleEdgeRawOrderInverse
                    (K := ℝ) (ρ := ρ) (κ' := κ') y.1)) :=
          (continuous_ofTopologyTuple (K := ℝ) (ρ := ρ) (κ' := κ')).comp hInv
        exact hamb.subtype_mk _
      have hchart :
          Continuous
            (fun data :
                {data :
                  RetainedPassiveNonredundantCoordinateData (K := ℝ) (ρ := ρ) κ' //
                  data.detChart} ↦
              paperEndpointFixedBaseRetainedPassiveP13SourceChart W₂ B₂ U₀ hU₀ data) :=
        continuous_paperEndpointFixedBaseRetainedPassiveP13SourceChart
          (K := ℝ) W₂ B₂ U₀ hU₀
      simpa [rawChart, T, RawTuple,
        paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart,
        paperEndpointFixedBaseRetainedPassiveP13SourceChart,
        paperEndpointFixedBaseRetainedPassiveP13SourceEdgeFamilyOfData,
        toDetChart, ρ, κ'] using hchart.comp hToDetChart
    have hrawChart_restrict :
        AEMeasurable rawChart ((Measure.map rawMap ν).restrict T) :=
      ContinuousOn.aemeasurable₀ hrawChartContOn hT_meas.nullMeasurableSet
    have hraw_restrict_eq :
        (Measure.map rawMap ν).restrict T = Measure.map rawMap ν :=
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
    have hrawChart :
        AEMeasurable rawChart (Measure.map rawMap ν) := by
      simpa [hraw_restrict_eq] using hrawChart_restrict
    have hmap_assoc :
        Measure.map rawChart (Measure.map rawMap ν) =
          Measure.map (fun z ↦ rawChart (rawMap z)) ν := by
      simpa [Function.comp_def] using
        (AEMeasurable.map_map_of_aemeasurable
          (μ := ν) (f := rawMap) (g := rawChart) hrawChart hrawMap)
    have hcomp :
        (fun z ↦ rawChart (rawMap z)) =ᵐ[ν] sourceChart := by
      filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
      have hpoint := hraw z (hVVraw hz)
      simpa [rawMap, rawChart, ρ, κ'] using hpoint.2.2.1
    have hcomp_map : μrawComp = μ := by
      simpa [ν, μ, μrawComp] using Measure.map_congr hcomp
    have htwo_stage : μrawTwoStage = μ := by
      calc
        μrawTwoStage =
            Measure.map (fun z ↦ rawChart (rawMap z)) ν := by
          simpa [μrawTwoStage] using hmap_assoc
        _ = μ := by
          simpa [ν, μ, μrawComp] using hcomp_map
    exact ⟨hcomp_map, htwo_stage⟩

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
