import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaWithFollowingFactorEndpointReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCoordinatesJacobianMeasure

/-!
# Case 2 passive theta raw-order reference measure

This file names the raw-order image of the concrete passive-theta reference
source and proves its local raw-source support and finite-scalar domination
handoff.  It is an image-measure layer only: it does not identify the image
with raw Haar, determinant-chart Haar, source-prior measure, normal crossings,
pole order, or RLCT.
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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Raw-order image measure of the concrete Case 2 passive-theta reference
source restricted to a chosen local set.

This is the correct raw-order target at the passive-theta layer.  It is the
actual image measure of the selected-entry passive-theta source; it is not
unrestricted raw Haar on the retained-passive raw-order determinant chart. -/
noncomputable def case2PassiveThetaRawOrderReferenceImageMeasure
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    Measure
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
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
  let rawMap :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') (Y theta)
  Measure.map rawMap (referenceSource.restrict Ω)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Raw-order image measure of the enlarged Case 2 passive-theta reference
source with an independent following factor, restricted to a chosen local set.

This is the correct raw-order target at the with-following layer.  It is the
actual image measure of the enlarged selected-entry source; it is not
unrestricted raw Haar on the retained-passive raw-order determinant chart. -/
noncomputable def case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
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
    [MeasurableSpace
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ)]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    Measure
      (TopologyTuple (Fin (Module.finrank ℝ U₀))
        (throughSubspaceEndpointComplementIndex
          (reverseVertex W₂) (reverseEdge W₂ B₂) U₀) ℝ) :=
  let ρ := Fin (Module.finrank ℝ U₀)
  let κ' : Fin 3 → Type :=
    throughSubspaceEndpointComplementIndex
      (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
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
  let rawMap :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun theta ↦
      topologyTupleEdgeRawOrder
        (K := ℝ) (ρ := ρ) (κ' := κ') (Y theta)
  Measure.map rawMap (referenceSource.restrict Ω)

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- If the enlarged endpoint reference image is a weighted determinant-side
Haar patch, then the named raw-order reference image is Haar restricted to the
corresponding raw-order image patch. -/
theorem case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure_eq_restrict_image_of_endpointReferenceImageMeasure_eq_withDensity_formalProductAbsDet
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
    [OpensMeasurableSpace
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
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let Φ : RawTuple → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
    let Jprod : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') y)
    let endpointReferenceImage : Measure RawTuple :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres V
    let rawOrderReferenceImage : Measure RawTuple :=
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
        W₂ B₂ n hS hcont hnext eNext e Rres V
    ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
      ∀ {Ω : Set RawTuple},
        NullMeasurableSet Ω rawHaar →
          Ω ⊆ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') →
            endpointReferenceImage =
                (rawHaar.restrict Ω).withDensity Jprod →
              rawOrderReferenceImage =
                rawHaar.restrict (Φ '' Ω) := by
  intro ρ κ' RawTuple Φ Jprod endpointReferenceImage rawOrderReferenceImage
    rawHaar _instRawHaar Ω hΩ hΩdet hendpoint
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RawTuple :=
    fun theta ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  let rawMap :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RawTuple :=
    fun theta ↦ Φ (Y theta)
  have hY :
      AEMeasurable Y (referenceSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hΦ_restrict :
      AEMeasurable Φ (rawHaar.restrict Ω) := by
    refine ContinuousOn.aemeasurable₀ ?_ hΩ
    intro y hy
    exact
      (differentiableAt_topologyTupleEdgeRawOrder_of_mem_topologyTupleDetChartSet
        (ρ := ρ) (κ' := κ') y (hΩdet hy)).continuousAt.continuousWithinAt
  have hΦ_endpoint :
      AEMeasurable Φ endpointReferenceImage := by
    simpa [hendpoint, Jprod] using
      hΦ_restrict.mono_ac (withDensity_absolutelyContinuous _ _)
  have hmap_assoc :
      Measure.map Φ endpointReferenceImage =
        rawOrderReferenceImage := by
    simpa [endpointReferenceImage, rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, Y, rawMap, Φ, RawTuple, ρ, κ', Function.comp_def] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := referenceSource.restrict V) (f := Y) (g := Φ) hΦ_endpoint hY)
  have hcov :
      Measure.map Φ ((rawHaar.restrict Ω).withDensity Jprod) =
        rawHaar.restrict (Φ '' Ω) := by
    simpa [Φ, Jprod, RawTuple, ρ, κ'] using
      map_topologyTupleEdgeRawOrder_withDensity_formalProductAbsDet_eq_restrict_image_of_subset_detChart
        (M := 1) (ρ := ρ) (κ' := κ') rawHaar hΩ hΩdet
  calc
    rawOrderReferenceImage = Measure.map Φ endpointReferenceImage := hmap_assoc.symm
    _ = Measure.map Φ ((rawHaar.restrict Ω).withDensity Jprod) := by
          rw [hendpoint]
    _ = rawHaar.restrict (Φ '' Ω) := hcov

set_option maxRecDepth 2048 in
set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
/-- Post-composed form of
`case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure_eq_restrict_image_of_endpointReferenceImageMeasure_eq_withDensity_formalProductAbsDet`.
-/
theorem map_case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure_eq_map_restrict_image_of_endpointReferenceImageMeasure_eq_withDensity_formalProductAbsDet
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
    [OpensMeasurableSpace
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
    {β : Type*} [MeasurableSpace β]
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e :
      ∀ q : Fin 3,
        case2PostPivotTwoEdgeDomain n S J τ q ≃
          throughSubspaceEndpointComplementIndex
            (reverseVertex W₂) (reverseEdge W₂ B₂) U₀ q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let Φ : RawTuple → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
    let Jprod : RawTuple → ℝ≥0∞ :=
      fun y ↦
        ENNReal.ofReal
          (retainedPassiveFormalRawOrderJacobianProductAbsDetAt
            (M := 1) (ρ := ρ) (κ' := κ') y)
    let endpointReferenceImage : Measure RawTuple :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres V
    let rawOrderReferenceImage : Measure RawTuple :=
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
        W₂ B₂ n hS hcont hnext eNext e Rres V
    ∀ (rawHaar : Measure RawTuple) [rawHaar.IsAddHaarMeasure],
      ∀ {Ω : Set RawTuple} (ψ : RawTuple → β),
        NullMeasurableSet Ω rawHaar →
          Ω ⊆ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') →
            AEMeasurable ψ (rawHaar.restrict (Φ '' Ω)) →
              endpointReferenceImage =
                  (rawHaar.restrict Ω).withDensity Jprod →
                Measure.map ψ rawOrderReferenceImage =
                  Measure.map ψ (rawHaar.restrict (Φ '' Ω)) := by
  intro ρ κ' RawTuple Φ Jprod endpointReferenceImage rawOrderReferenceImage
    rawHaar _instRawHaar Ω ψ hΩ hΩdet _hψ hendpoint
  have hraw :
      rawOrderReferenceImage = rawHaar.restrict (Φ '' Ω) :=
    case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure_eq_restrict_image_of_endpointReferenceImageMeasure_eq_withDensity_formalProductAbsDet
      W₂ B₂ n hS hcont hnext eNext e Rres V
      rawHaar hΩ hΩdet hendpoint
  rw [hraw]

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The proof unfolds the concrete Case 2 passive-theta chart and raw-order interfaces.
/-- Local raw-source support and passive-field domination for the named
raw-order reference image measure.

After shrinking inside any prescribed open neighborhood of a determinant-sector
and nonzero-pivot base point, the concrete raw-order reference image is
supported on the retained-passive raw-order source-recursive determinant
chart.  On the same local set, passive-field scalar domination pushes forward
to domination by this named raw-order image measure.

This is not raw-Haar domination.  The target measure is the actual raw-order
image of the concrete passive-theta reference source. -/
theorem exists_open_subset_case2PassiveThetaRawOrderReferenceImageMeasure_support_and_domination
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
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let rawMap :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        let rawOrderReferenceImage : Measure RawTuple :=
          case2PassiveThetaRawOrderReferenceImageMeasure
            W₂ B₂ n hS hcont hnext eNext e Rres V
        rawOrderReferenceImage.restrict rawSourceSet =
            rawOrderReferenceImage ∧
          ∀ (passiveMeasure :
              Measure
                (Case2PassiveTheta.PassiveFields
                  (ρ := ρ) (τ := τ) n S J)) {d : ℝ≥0∞},
            passiveMeasure ≤
                d • case2PassiveThetaPassiveFieldReferenceMeasure
                  (ρ := ρ) (τ := τ) n S J →
              let weightedBox :
                  Measure (Case2PassiveTheta.Center n S J → ℝ) :=
                case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
              let passiveSource :
                  Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
                passiveMeasure.prod weightedBox
              Measure.map rawMap (passiveSource.restrict V) ≤
                d • rawOrderReferenceImage := by
  intro ρ κ' RawTuple rawMap rawSourceSet
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, _hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawOrderReferenceImage
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  have hdet_of_mem :
      ∀ z ∈ V, Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    intro z hz
    simpa [Y, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hrawMapContOn : ContinuousOn rawMap V := by
    rw [continuousOn_iff_continuous_restrict]
    let Sdet : Set RawTuple :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let toDetTuple : V → Sdet :=
      fun z ↦ ⟨Y z.1, hdet_of_mem z.1 z.2⟩
    have hToDetTuple : Continuous toDetTuple := by
      have hamb : Continuous (fun z : V ↦ Y z.1) := by
        change Continuous
          (fun z : V ↦
            case2PassiveThetaEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext eNext e).comp continuous_subtype_val
      exact hamb.subtype_mk _
    have hrawDet :
        Continuous
          (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
            topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrder_detChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
      hrawDet.comp hToDetTuple
  let referencePassive :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let referenceWeightedBox :
      Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
  let referenceSource :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    referencePassive.prod referenceWeightedBox
  have hrawMap_reference :
      AEMeasurable rawMap (referenceSource.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂referenceSource.restrict V, rawMap z ∈ rawSourceSet := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, rawSourceSet, RawTuple, ρ, κ'] using (hpoint z hz).2.1
  have hrawSourceSet_meas : MeasurableSet rawSourceSet := by
    simpa [rawSourceSet, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (referenceSource.restrict V),
        y ∈ rawSourceSet :=
    (ae_map_iff hrawMap_reference hrawSourceSet_meas).2 hraw_mem
  have hsupport :
      rawOrderReferenceImage.restrict rawSourceSet =
        rawOrderReferenceImage := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, referencePassive, referenceWeightedBox,
      rawMap, Y, rawSourceSet, RawTuple, ρ, κ'] using
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  refine ⟨hsupport, ?_⟩
  intro passiveMeasure d hpassive weightedBox passiveSource
  let referencePassive' :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let referenceSource' :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    referencePassive'.prod weightedBox
  haveI : SFinite weightedBox := by
    subst weightedBox
    dsimp [case2PassiveThetaCenterWeightedBoxMeasure,
      case2PassiveThetaCenterSignedBoxMeasure]
    infer_instance
  have hprod : passiveSource ≤ d • referenceSource' := by
    change passiveMeasure.prod weightedBox ≤
      d • referencePassive'.prod weightedBox
    exact prod_le_smul_prod_of_le_smul_left (η := weightedBox) hpassive
  have hrestrict :
      passiveSource.restrict V ≤ d • referenceSource'.restrict V := by
    calc
      passiveSource.restrict V ≤ (d • referenceSource').restrict V :=
        Measure.restrict_mono Set.Subset.rfl hprod
      _ = d • referenceSource'.restrict V := by
        rw [Measure.restrict_smul]
  have hrawMap_reference' :
      AEMeasurable rawMap (referenceSource'.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hmap :
      Measure.map rawMap (passiveSource.restrict V) ≤
        d • Measure.map rawMap (referenceSource'.restrict V) :=
    map_le_smul_map_of_le_smul_aemeasurable hrawMap_reference' hrestrict
  simpa [rawOrderReferenceImage,
    case2PassiveThetaRawOrderReferenceImageMeasure,
    case2PassiveThetaReferenceSourceMeasure,
    referenceSource', referencePassive', weightedBox,
    rawMap, Y, RawTuple, ρ, κ'] using hmap

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The proof uses the same concrete local raw-order/source-chart package as the support theorem.
/-- Local functorial handoff from endpoint reference image to raw-order and
p.13 source-chart reference images.

After the usual determinant/punctured-sector shrink, pushing the named
endpoint reference image through `topologyTupleEdgeRawOrder` gives the named
raw-order reference image.  Pushing that raw-order image through the p.13
raw-order source chart gives the direct p.13 source-chart image of the
theta-domain reference source.

This is a functorial image-measure identity.  It does not identify any of the
image measures with raw Haar, determinant-chart Haar, original volume, or an
original/source prior. -/
theorem exists_open_subset_case2PassiveThetaEndpointReferenceImage_rawOrder_sourceChart_handoff
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
    [MeasurableSpace
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
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let referenceSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let Phi : RawTuple → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceChart :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        let endpointReferenceImage : Measure RawTuple :=
          case2PassiveThetaEndpointReferenceImageMeasure
            (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres V
        let rawOrderReferenceImage : Measure RawTuple :=
          case2PassiveThetaRawOrderReferenceImageMeasure
            W₂ B₂ n hS hcont hnext eNext e Rres V
        Measure.map Phi endpointReferenceImage =
            rawOrderReferenceImage ∧
            Measure.map rawChart rawOrderReferenceImage =
            Measure.map sourceChart (referenceSource.restrict V) := by
  intro ρ κ' RawTuple EdgeFamily referenceSource Phi rawChart sourceChart
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  let rawMap :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
    fun theta ↦ Phi (Y theta)
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmaps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro endpointReferenceImage rawOrderReferenceImage
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  have hY :
      AEMeasurable Y (referenceSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hY_mem :
      ∀ᵐ z ∂referenceSource.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hendpoint_mem :
      ∀ᵐ y ∂Measure.map Y (referenceSource.restrict V), y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hPhiContOn : ContinuousOn Phi rawDetChart := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hPhi_restrict :
      AEMeasurable Phi
        ((Measure.map Y (referenceSource.restrict V)).restrict rawDetChart) :=
    ContinuousOn.aemeasurable₀ hPhiContOn hdet_meas.nullMeasurableSet
  have hendpoint_restrict :
      (Measure.map Y (referenceSource.restrict V)).restrict rawDetChart =
        Measure.map Y (referenceSource.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hendpoint_mem
  have hPhi :
      AEMeasurable Phi (Measure.map Y (referenceSource.restrict V)) := by
    simpa [hendpoint_restrict] using hPhi_restrict
  have hmap_assoc :
      Measure.map Phi (Measure.map Y (referenceSource.restrict V)) =
        Measure.map rawMap (referenceSource.restrict V) := by
    simpa [rawMap, Phi, Y, Function.comp_def, RawTuple, ρ, κ'] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := referenceSource.restrict V) (f := Y) (g := Phi) hPhi hY)
  have hfirst :
      Measure.map Phi endpointReferenceImage = rawOrderReferenceImage := by
    simpa [endpointReferenceImage, rawOrderReferenceImage,
      case2PassiveThetaEndpointReferenceImageMeasure,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, Y, Phi, rawMap, RawTuple, ρ, κ'] using hmap_assoc
  have htwo_stage :
      Measure.map rawChart (Measure.map rawMap (referenceSource.restrict V)) =
        Measure.map sourceChart (referenceSource.restrict V) := by
    have hmaps' := hmaps (sourceMeasure := referenceSource)
    simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart,
      Measure.map_map] using hmaps'.2
  have hsecond :
      Measure.map rawChart rawOrderReferenceImage =
        Measure.map sourceChart (referenceSource.restrict V) := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, Y, Phi, rawMap, rawChart, RawTuple, ρ, κ'] using
      htwo_stage
  exact ⟨hfirst, hsecond⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 900000 in
-- The proof specializes the generic raw-density transport to the named reference image.
/-- Local density transport from the named raw-order reference image to the
p.13 source-chart image.

After the usual determinant/punctured-sector shrink, any raw density that is
a.e. measurable for the named raw-order reference image transports through the
p.13 raw-order source chart to the direct source-chart image of the
theta-domain reference source weighted by the composed raw density.

This theorem is only a named image-measure density handoff.  It does not
identify the raw-order image with raw Haar, determinant-chart Haar, original
volume, or an original/source prior. -/
theorem exists_open_subset_case2PassiveThetaRawOrderReferenceImage_withDensity_sourceChart_handoff
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
    [MeasurableSpace
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
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let referenceSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let rawMap :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceChart :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        let rawOrderReferenceImage : Measure RawTuple :=
          case2PassiveThetaRawOrderReferenceImageMeasure
            W₂ B₂ n hS hcont hnext eNext e Rres V
        ∀ rawDensity : RawTuple → ℝ≥0∞,
          AEMeasurable rawDensity rawOrderReferenceImage →
            Measure.map rawChart
                (rawOrderReferenceImage.withDensity rawDensity) =
              Measure.map sourceChart
                ((referenceSource.withDensity
                  (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
  intro ρ κ' RawTuple EdgeFamily referenceSource rawMap rawChart sourceChart
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro rawOrderReferenceImage rawDensity hrawDensity
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  have hdet_of_mem :
      ∀ z ∈ V, Y z ∈ topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') := by
    intro z hz
    simpa [Y, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hrawMapContOn : ContinuousOn rawMap V := by
    rw [continuousOn_iff_continuous_restrict]
    let Sdet : Set RawTuple :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let toDetTuple : V → Sdet :=
      fun z ↦ ⟨Y z.1, hdet_of_mem z.1 z.2⟩
    have hToDetTuple : Continuous toDetTuple := by
      have hamb : Continuous (fun z : V ↦ Y z.1) := by
        change Continuous
          (fun z : V ↦
            case2PassiveThetaEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext eNext e).comp continuous_subtype_val
      exact hamb.subtype_mk _
    have hrawDet :
        Continuous
          (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
            topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrder_detChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
      hrawDet.comp hToDetTuple
  have hrawMap :
      AEMeasurable rawMap (referenceSource.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hrawDensity' :
      AEMeasurable rawDensity
        (Measure.map rawMap (referenceSource.restrict V)) := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, rawMap, Y, RawTuple, ρ, κ'] using hrawDensity
  have htwoStage :
      Measure.map rawChart
          (Measure.map rawMap
            ((referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V)) =
        Measure.map sourceChart
          ((referenceSource.withDensity
            (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
    have hmaps :=
      hmeasure_maps
        (sourceMeasure :=
          referenceSource.withDensity
            (fun theta ↦ rawDensity (rawMap theta)))
    simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart] using
      hmaps.2
  have htransport :
      Measure.map rawChart
          ((Measure.map rawMap (referenceSource.restrict V)).withDensity rawDensity) =
        Measure.map sourceChart
          ((referenceSource.withDensity
            (fun theta ↦ rawDensity (rawMap theta))).restrict V) :=
    DLNFibre.DLN.Aoyagi.measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
      (hV := hVopen.measurableSet) hrawMap hrawDensity' htwoStage
  simpa [rawOrderReferenceImage,
    case2PassiveThetaRawOrderReferenceImageMeasure,
    case2PassiveThetaReferenceSourceMeasure,
    referenceSource, rawMap, Y, rawChart, RawTuple, ρ, κ'] using htransport

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- This theorem deliberately packages all conclusions from one local shrink.
/-- Same-shrink package for the Case 2 passive-theta raw-order reference image.

After the usual determinant/punctured-sector shrink, a single local open set
`V` supports all raw-order reference image handoffs needed downstream: support
on the raw-order source-recursive determinant chart, passive-field domination,
endpoint-reference image composition, source-chart composition, and raw-density
transport.

This is only an image-measure bookkeeping package.  It does not identify the
named raw-order image with raw Haar, determinant-chart Haar, original volume,
or an original/source prior. -/
theorem exists_open_subset_case2PassiveThetaRawOrderReferenceImage_same_shrink_package
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
    [MeasurableSpace
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
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let referenceSource :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let rawMap :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let Phi : RawTuple → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceChart :
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → EdgeFamily :=
      fun theta ↦
        case2PassiveThetaEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    ∃ V :
      Set
        (Case2PassiveTheta
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        let endpointReferenceImage : Measure RawTuple :=
          case2PassiveThetaEndpointReferenceImageMeasure
            (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres V
        let rawOrderReferenceImage : Measure RawTuple :=
          case2PassiveThetaRawOrderReferenceImageMeasure
            W₂ B₂ n hS hcont hnext eNext e Rres V
        rawOrderReferenceImage.restrict rawSourceSet =
            rawOrderReferenceImage ∧
          (∀ (passiveMeasure :
              Measure
                (Case2PassiveTheta.PassiveFields
                  (ρ := ρ) (τ := τ) n S J)) {d : ℝ≥0∞},
            passiveMeasure ≤
                d • case2PassiveThetaPassiveFieldReferenceMeasure
                  (ρ := ρ) (τ := τ) n S J →
              let weightedBox :
                  Measure (Case2PassiveTheta.Center n S J → ℝ) :=
                case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
              let passiveSource :
                  Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
                passiveMeasure.prod weightedBox
              Measure.map rawMap (passiveSource.restrict V) ≤
                d • rawOrderReferenceImage) ∧
          Measure.map Phi endpointReferenceImage =
            rawOrderReferenceImage ∧
          Measure.map rawChart rawOrderReferenceImage =
            Measure.map sourceChart (referenceSource.restrict V) ∧
          ∀ rawDensity : RawTuple → ℝ≥0∞,
            AEMeasurable rawDensity rawOrderReferenceImage →
              Measure.map rawChart
                  (rawOrderReferenceImage.withDensity rawDensity) =
                Measure.map sourceChart
                  ((referenceSource.withDensity
                    (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
  intro ρ κ' RawTuple EdgeFamily referenceSource rawMap rawSourceSet Phi rawChart sourceChart
  let Y :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J → RawTuple :=
    fun theta ↦
      case2PassiveThetaEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  rcases
      exists_open_subset_measurableSet_measure_map_case2PassiveThetaEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_puncturedSector_inverseReadout_eq_yNext
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, _hsector, hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro endpointReferenceImage rawOrderReferenceImage
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  have hdet_of_mem :
      ∀ z ∈ V, Y z ∈ rawDetChart := by
    intro z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hrawMapContOn : ContinuousOn rawMap V := by
    rw [continuousOn_iff_continuous_restrict]
    let Sdet : Set RawTuple :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let toDetTuple : V → Sdet :=
      fun z ↦ ⟨Y z.1, by
        simpa [Sdet, rawDetChart] using hdet_of_mem z.1 z.2⟩
    have hToDetTuple : Continuous toDetTuple := by
      have hamb : Continuous (fun z : V ↦ Y z.1) := by
        change Continuous
          (fun z : V ↦
            case2PassiveThetaEndpointTopologyTuple
              (ρ := ρ) n hS hcont hnext z.1 eNext e)
        exact
          (continuous_case2PassiveThetaEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext eNext e).comp continuous_subtype_val
      exact hamb.subtype_mk _
    have hrawDet :
        Continuous
          (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
            topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrder_detChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
      hrawDet.comp hToDetTuple
  have hrawMap_reference :
      AEMeasurable rawMap (referenceSource.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂referenceSource.restrict V, rawMap z ∈ rawSourceSet := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, rawSourceSet, Y, rawDetChart, RawTuple, ρ, κ'] using
      (hpoint z hz).2.1
  have hrawSourceSet_meas : MeasurableSet rawSourceSet := by
    simpa [rawSourceSet, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (referenceSource.restrict V),
        y ∈ rawSourceSet :=
    (ae_map_iff hrawMap_reference hrawSourceSet_meas).2 hraw_mem
  have hsupport :
      rawOrderReferenceImage.restrict rawSourceSet =
        rawOrderReferenceImage := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, rawMap, Y, rawSourceSet, RawTuple, ρ, κ'] using
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  have hdomination :
      ∀ (passiveMeasure :
          Measure
            (Case2PassiveTheta.PassiveFields
              (ρ := ρ) (τ := τ) n S J)) {d : ℝ≥0∞},
        passiveMeasure ≤
            d • case2PassiveThetaPassiveFieldReferenceMeasure
              (ρ := ρ) (τ := τ) n S J →
          let weightedBox :
              Measure (Case2PassiveTheta.Center n S J → ℝ) :=
            case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
          let passiveSource :
              Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
            passiveMeasure.prod weightedBox
          Measure.map rawMap (passiveSource.restrict V) ≤
            d • rawOrderReferenceImage := by
    intro passiveMeasure d hpassive weightedBox passiveSource
    let referencePassive' :
        Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
    let referenceSource' :
        Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
      referencePassive'.prod weightedBox
    haveI : SFinite weightedBox := by
      subst weightedBox
      dsimp [case2PassiveThetaCenterWeightedBoxMeasure,
        case2PassiveThetaCenterSignedBoxMeasure]
      infer_instance
    have hprod : passiveSource ≤ d • referenceSource' := by
      change passiveMeasure.prod weightedBox ≤
        d • referencePassive'.prod weightedBox
      exact prod_le_smul_prod_of_le_smul_left (η := weightedBox) hpassive
    have hrestrict :
        passiveSource.restrict V ≤ d • referenceSource'.restrict V := by
      calc
        passiveSource.restrict V ≤ (d • referenceSource').restrict V :=
          Measure.restrict_mono Set.Subset.rfl hprod
        _ = d • referenceSource'.restrict V := by
          rw [Measure.restrict_smul]
    have hrawMap_reference' :
        AEMeasurable rawMap (referenceSource'.restrict V) :=
      ContinuousOn.aemeasurable₀ hrawMapContOn
        hVopen.measurableSet.nullMeasurableSet
    have hmap :
        Measure.map rawMap (passiveSource.restrict V) ≤
          d • Measure.map rawMap (referenceSource'.restrict V) :=
      map_le_smul_map_of_le_smul_aemeasurable hrawMap_reference' hrestrict
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource', referencePassive', weightedBox,
      rawMap, Y, RawTuple, ρ, κ'] using hmap
  have hY :
      AEMeasurable Y (referenceSource.restrict V) := by
    have hYcont : Continuous Y := by
      simpa [Y, RawTuple, ρ, κ'] using
        continuous_case2PassiveThetaEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hY_mem :
      ∀ᵐ z ∂referenceSource.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    exact hdet_of_mem z hz
  have hendpoint_mem :
      ∀ᵐ y ∂Measure.map Y (referenceSource.restrict V), y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hPhiContOn : ContinuousOn Phi rawDetChart := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hPhi_restrict :
      AEMeasurable Phi
        ((Measure.map Y (referenceSource.restrict V)).restrict rawDetChart) :=
    ContinuousOn.aemeasurable₀ hPhiContOn hdet_meas.nullMeasurableSet
  have hendpoint_restrict :
      (Measure.map Y (referenceSource.restrict V)).restrict rawDetChart =
        Measure.map Y (referenceSource.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hendpoint_mem
  have hPhi :
      AEMeasurable Phi (Measure.map Y (referenceSource.restrict V)) := by
    simpa [hendpoint_restrict] using hPhi_restrict
  have hmap_assoc :
      Measure.map Phi (Measure.map Y (referenceSource.restrict V)) =
        Measure.map rawMap (referenceSource.restrict V) := by
    simpa [rawMap, Phi, Y, Function.comp_def, RawTuple, ρ, κ'] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := referenceSource.restrict V) (f := Y) (g := Phi) hPhi hY)
  have hendpoint_raw :
      Measure.map Phi endpointReferenceImage = rawOrderReferenceImage := by
    simpa [endpointReferenceImage, rawOrderReferenceImage,
      case2PassiveThetaEndpointReferenceImageMeasure,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, Y, Phi, rawMap, RawTuple, ρ, κ'] using hmap_assoc
  have htwo_stage_unweighted :
      Measure.map rawChart (Measure.map rawMap (referenceSource.restrict V)) =
        Measure.map sourceChart (referenceSource.restrict V) := by
    have hmaps' := hmeasure_maps (sourceMeasure := referenceSource)
    simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart,
      Measure.map_map] using hmaps'.2
  have hraw_source :
      Measure.map rawChart rawOrderReferenceImage =
        Measure.map sourceChart (referenceSource.restrict V) := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, Y, rawMap, rawChart, RawTuple, ρ, κ'] using
      htwo_stage_unweighted
  have hdensity :
      ∀ rawDensity : RawTuple → ℝ≥0∞,
        AEMeasurable rawDensity rawOrderReferenceImage →
          Measure.map rawChart
              (rawOrderReferenceImage.withDensity rawDensity) =
            Measure.map sourceChart
              ((referenceSource.withDensity
                (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
    intro rawDensity hrawDensity
    have hrawDensity' :
        AEMeasurable rawDensity
          (Measure.map rawMap (referenceSource.restrict V)) := by
      simpa [rawOrderReferenceImage,
        case2PassiveThetaRawOrderReferenceImageMeasure,
        case2PassiveThetaReferenceSourceMeasure,
        referenceSource, rawMap, Y, RawTuple, ρ, κ'] using hrawDensity
    have htwoStage :
        Measure.map rawChart
            (Measure.map rawMap
              ((referenceSource.withDensity
                (fun theta ↦ rawDensity (rawMap theta))).restrict V)) =
          Measure.map sourceChart
            ((referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
      have hmaps :=
        hmeasure_maps
          (sourceMeasure :=
            referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta)))
      simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart] using
        hmaps.2
    have htransport :
        Measure.map rawChart
            ((Measure.map rawMap (referenceSource.restrict V)).withDensity rawDensity) =
          Measure.map sourceChart
            ((referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V) :=
      DLNFibre.DLN.Aoyagi.measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
        (hV := hVopen.measurableSet) hrawMap_reference hrawDensity' htwoStage
    simpa [rawOrderReferenceImage,
      case2PassiveThetaRawOrderReferenceImageMeasure,
      case2PassiveThetaReferenceSourceMeasure,
      referenceSource, rawMap, Y, rawChart, RawTuple, ρ, κ'] using htransport
  exact ⟨hsupport, hdomination, hendpoint_raw, hraw_source, hdensity⟩

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in
-- This theorem deliberately packages all conclusions from one local shrink.
/-- Same-shrink package for the enlarged Case 2 passive-theta raw-order
reference image with an independent following factor.

After the usual determinant/punctured-sector shrink, a single local open set
`V` supports all with-following raw-order reference image handoffs needed
downstream: support on the raw-order source-recursive determinant chart,
domination for source measures dominated by the enlarged reference source,
endpoint-reference image composition, source-chart composition, and raw-density
transport.

This is only an actual image-measure bookkeeping package.  It does not identify
the named raw-order image with raw Haar, determinant-chart Haar, original
volume, or an original/source prior. -/
theorem exists_open_subset_case2PassiveThetaWithFollowingFactorRawOrderReferenceImage_same_shrink_package
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
    [MeasurableSpace
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
      Case2PassiveThetaWithFollowingFactor
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hdet₀ :
      z₀ ∈ case2PassiveThetaWithFollowingFactorDetSector
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J)
    (hpivot₀ :
      case2PassiveThetaPivotNonzero
        (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n hS hnext z₀.1)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (G :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J))
    (hGopen : IsOpen G)
    (hz₀G : z₀ ∈ G) :
    let ρ := Fin (Module.finrank ℝ U₀)
    let κ' : Fin 3 → Type :=
      throughSubspaceEndpointComplementIndex
        (reverseVertex W₂) (reverseEdge W₂ B₂) U₀
    let RawTuple := TopologyTuple ρ κ' ℝ
    let EdgeFamily :=
      ∀ p : Fin 2, reverseVertex W₂ p.castSucc →L[ℝ] reverseVertex W₂ p.succ
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let rawMap :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J → RawTuple :=
      fun theta ↦
        topologyTupleEdgeRawOrder
          (K := ℝ) (ρ := ρ) (κ' := κ')
          (case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e)
    let rawSourceSet : Set RawTuple :=
      topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')
    let Phi : RawTuple → RawTuple :=
      fun y ↦ topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y
    let rawChart : RawTuple → EdgeFamily :=
      paperEndpointFixedBaseRetainedPassiveP13RawOrderSourceChart
        (K := ℝ) W₂ B₂ U₀ hU₀
    let sourceChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          EdgeFamily :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointSourceChart
          W₂ B₂ n hS hcont hnext hU₀ eNext e theta
    ∃ V :
      Set
        (Case2PassiveThetaWithFollowingFactor
          (ρ := Fin (Module.finrank ℝ U₀)) (τ := τ) n S J),
      IsOpen V ∧ z₀ ∈ V ∧ V ⊆ G ∧
        let endpointReferenceImage : Measure RawTuple :=
          case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
            (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres V
        let rawOrderReferenceImage : Measure RawTuple :=
          case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure
            W₂ B₂ n hS hcont hnext eNext e Rres V
        rawOrderReferenceImage.restrict rawSourceSet =
            rawOrderReferenceImage ∧
          (∀ (sourceMeasure :
              Measure
                (Case2PassiveThetaWithFollowingFactor
                  (ρ := ρ) (τ := τ) n S J)) {d : ℝ≥0∞},
            sourceMeasure ≤ d • referenceSource →
              Measure.map rawMap (sourceMeasure.restrict V) ≤
                d • rawOrderReferenceImage) ∧
          Measure.map Phi endpointReferenceImage =
            rawOrderReferenceImage ∧
          Measure.map rawChart rawOrderReferenceImage =
            Measure.map sourceChart (referenceSource.restrict V) ∧
          ∀ rawDensity : RawTuple → ℝ≥0∞,
            AEMeasurable rawDensity rawOrderReferenceImage →
              Measure.map rawChart
                  (rawOrderReferenceImage.withDensity rawDensity) =
                Measure.map sourceChart
                  ((referenceSource.withDensity
                    (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
  intro ρ κ' RawTuple EdgeFamily referenceSource rawMap rawSourceSet Phi rawChart sourceChart
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        RawTuple :=
    fun theta ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext theta eNext e
  rcases
      exists_open_subset_measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_rawOrderMap_twoStage_eq_sourceChart_readback_leftInverse
        W₂ B₂ n hS hcont hnext (U₀ := U₀) (hU₀ := hU₀) eNext e
        z₀ hdet₀ hpivot₀ G hGopen hz₀G with
    ⟨V, hVopen, hz₀V, hVG, hpoint, hmeasure_maps⟩
  refine ⟨V, hVopen, hz₀V, hVG, ?_⟩
  intro endpointReferenceImage rawOrderReferenceImage
  let rawDetChart : Set RawTuple :=
    topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
  have hYcont : Continuous Y := by
    change Continuous
      (fun theta :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e)
    exact
      continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e
  have hdet_of_mem :
      ∀ z ∈ V, Y z ∈ rawDetChart := by
    intro z hz
    simpa [Y, rawDetChart, RawTuple, ρ, κ'] using (hpoint z hz).1
  have hrawMapContOn : ContinuousOn rawMap V := by
    rw [continuousOn_iff_continuous_restrict]
    let Sdet : Set RawTuple :=
      topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ')
    let toDetTuple : V → Sdet :=
      fun z ↦ ⟨Y z.1, by
        simpa [Sdet, rawDetChart] using hdet_of_mem z.1 z.2⟩
    have hToDetTuple : Continuous toDetTuple := by
      have hamb : Continuous (fun z : V ↦ Y z.1) :=
        hYcont.comp continuous_subtype_val
      exact hamb.subtype_mk _
    have hrawDet :
        Continuous
          (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
            topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1) :=
      continuous_topologyTupleEdgeRawOrder_detChart_subtype
        (K := ℝ) (ρ := ρ) (κ' := κ')
    simpa [rawMap, Y, toDetTuple, Sdet, RawTuple, ρ, κ'] using
      hrawDet.comp hToDetTuple
  have hrawMap_reference :
      AEMeasurable rawMap (referenceSource.restrict V) :=
    ContinuousOn.aemeasurable₀ hrawMapContOn
      hVopen.measurableSet.nullMeasurableSet
  have hraw_mem :
      ∀ᵐ z ∂referenceSource.restrict V, rawMap z ∈ rawSourceSet := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    simpa [rawMap, rawSourceSet, Y, rawDetChart, RawTuple, ρ, κ'] using
      (hpoint z hz).2.1
  have hrawSourceSet_meas : MeasurableSet rawSourceSet := by
    simpa [rawSourceSet, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleRawOrderSourceRecursiveDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hraw_image_mem :
      ∀ᵐ y ∂Measure.map rawMap (referenceSource.restrict V),
        y ∈ rawSourceSet :=
    (ae_map_iff hrawMap_reference hrawSourceSet_meas).2 hraw_mem
  have hsupport :
      rawOrderReferenceImage.restrict rawSourceSet =
        rawOrderReferenceImage := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, rawMap, Y, rawSourceSet, RawTuple, ρ, κ'] using
      Measure.restrict_eq_self_of_ae_mem hraw_image_mem
  have hdomination :
      ∀ (sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J)) {d : ℝ≥0∞},
        sourceMeasure ≤ d • referenceSource →
          Measure.map rawMap (sourceMeasure.restrict V) ≤
            d • rawOrderReferenceImage := by
    intro sourceMeasure d hsource
    have hrestrict :
        sourceMeasure.restrict V ≤ d • referenceSource.restrict V := by
      calc
        sourceMeasure.restrict V ≤ (d • referenceSource).restrict V :=
          Measure.restrict_mono Set.Subset.rfl hsource
        _ = d • referenceSource.restrict V := by
          rw [Measure.restrict_smul]
    have hmap :
        Measure.map rawMap (sourceMeasure.restrict V) ≤
          d • Measure.map rawMap (referenceSource.restrict V) :=
      map_le_smul_map_of_le_smul_aemeasurable hrawMap_reference hrestrict
    simpa [rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, rawMap, Y, RawTuple, ρ, κ'] using hmap
  have hY :
      AEMeasurable Y (referenceSource.restrict V) :=
    hYcont.measurable.aemeasurable
  have hdet_meas : MeasurableSet rawDetChart := by
    simpa [rawDetChart, RawTuple, ρ, κ'] using
      (isOpen_topologyTupleDetChartSet
        (K := ℝ) (ρ := ρ) (κ' := κ')).measurableSet
  have hY_mem :
      ∀ᵐ z ∂referenceSource.restrict V, Y z ∈ rawDetChart := by
    filter_upwards [ae_restrict_mem hVopen.measurableSet] with z hz
    exact hdet_of_mem z hz
  have hendpoint_mem :
      ∀ᵐ y ∂Measure.map Y (referenceSource.restrict V), y ∈ rawDetChart :=
    (ae_map_iff hY hdet_meas).2 hY_mem
  have hPhiContOn : ContinuousOn Phi rawDetChart := by
    rw [continuousOn_iff_continuous_restrict]
    change Continuous
      (fun y : topologyTupleDetChartSet (K := ℝ) (ρ := ρ) (κ' := κ') ↦
        topologyTupleEdgeRawOrder (K := ℝ) (ρ := ρ) (κ' := κ') y.1)
    exact continuous_topologyTupleEdgeRawOrder_detChart_subtype
      (K := ℝ) (ρ := ρ) (κ' := κ')
  have hPhi_restrict :
      AEMeasurable Phi
        ((Measure.map Y (referenceSource.restrict V)).restrict rawDetChart) :=
    ContinuousOn.aemeasurable₀ hPhiContOn hdet_meas.nullMeasurableSet
  have hendpoint_restrict :
      (Measure.map Y (referenceSource.restrict V)).restrict rawDetChart =
        Measure.map Y (referenceSource.restrict V) :=
    Measure.restrict_eq_self_of_ae_mem hendpoint_mem
  have hPhi :
      AEMeasurable Phi (Measure.map Y (referenceSource.restrict V)) := by
    simpa [hendpoint_restrict] using hPhi_restrict
  have hmap_assoc :
      Measure.map Phi (Measure.map Y (referenceSource.restrict V)) =
        Measure.map rawMap (referenceSource.restrict V) := by
    simpa [rawMap, Phi, Y, Function.comp_def, RawTuple, ρ, κ'] using
      (AEMeasurable.map_map_of_aemeasurable
        (μ := referenceSource.restrict V) (f := Y) (g := Phi) hPhi hY)
  have hendpoint_raw :
      Measure.map Phi endpointReferenceImage = rawOrderReferenceImage := by
    simpa [endpointReferenceImage, rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, Y, Phi, rawMap, RawTuple, ρ, κ'] using hmap_assoc
  have htwo_stage_unweighted :
      Measure.map rawChart (Measure.map rawMap (referenceSource.restrict V)) =
        Measure.map sourceChart (referenceSource.restrict V) := by
    have hmaps' := hmeasure_maps (sourceMeasure := referenceSource)
    simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart,
      Measure.map_map] using hmaps'.2
  have hraw_source :
      Measure.map rawChart rawOrderReferenceImage =
        Measure.map sourceChart (referenceSource.restrict V) := by
    simpa [rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, Y, rawMap, rawChart, RawTuple, ρ, κ'] using
      htwo_stage_unweighted
  have hdensity :
      ∀ rawDensity : RawTuple → ℝ≥0∞,
        AEMeasurable rawDensity rawOrderReferenceImage →
          Measure.map rawChart
              (rawOrderReferenceImage.withDensity rawDensity) =
            Measure.map sourceChart
              ((referenceSource.withDensity
                (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
    intro rawDensity hrawDensity
    have hrawDensity' :
        AEMeasurable rawDensity
          (Measure.map rawMap (referenceSource.restrict V)) := by
      simpa [rawOrderReferenceImage,
        case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
        case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
        referenceSource, rawMap, Y, RawTuple, ρ, κ'] using hrawDensity
    have htwoStage :
        Measure.map rawChart
            (Measure.map rawMap
              ((referenceSource.withDensity
                (fun theta ↦ rawDensity (rawMap theta))).restrict V)) =
          Measure.map sourceChart
            ((referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V) := by
      have hmaps :=
        hmeasure_maps
          (sourceMeasure :=
            referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta)))
      simpa [RawTuple, EdgeFamily, referenceSource, sourceChart, rawMap, rawChart] using
        hmaps.2
    have htransport :
        Measure.map rawChart
            ((Measure.map rawMap (referenceSource.restrict V)).withDensity rawDensity) =
          Measure.map sourceChart
            ((referenceSource.withDensity
              (fun theta ↦ rawDensity (rawMap theta))).restrict V) :=
      DLNFibre.DLN.Aoyagi.measure_map_rawChart_restrict_withDensity_comp_eq_of_twoStage_restrict
        (hV := hVopen.measurableSet) hrawMap_reference hrawDensity' htwoStage
    simpa [rawOrderReferenceImage,
      case2PassiveThetaWithFollowingFactorRawOrderReferenceImageMeasure,
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure,
      referenceSource, rawMap, Y, rawChart, RawTuple, ρ, κ'] using htransport
  exact ⟨hsupport, hdomination, hendpoint_raw, hraw_source, hdensity⟩

end PaperEndpointFixedBaseRegularCoordinateSourceData

end Aoyagi
end DLN
end DLNFibre
