import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaEndpointReference
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaSourceImage
import DLNFibre.DLN.Aoyagi.RetainedPassiveCase2PassiveThetaCFieldReadout

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
/-- Unweighted coordinate-product measure on the enlarged Case 2
passive-theta source: passive fields, unsigned selected-entry center box, and
the independent following-factor matrix. -/
noncomputable def case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) (S J : ℕ)
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    Measure
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
  ((case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J).prod
    (case2PassiveThetaCenterSignedBoxMeasure n Rres)).prod
    (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)

set_option linter.style.longLine false in
/-- The selected-entry source-density factor on the enlarged Case 2
passive-theta source.  This is the `Y`-side Jacobian factor before composing
with the retained-passive raw-order map. -/
noncomputable def case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1)) :
    Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
      ℝ≥0∞ :=
  fun z ↦
    ENNReal.ofReal
      (SelectedEntrySignedBox.CenterCoord.sourceDensity
        (case2PassiveThetaPivotNext n hS hnext) z.1.yNext)

set_option linter.style.longLine false in
/-- The enlarged reference source is the unweighted coordinate-product source
with the selected-entry source-density factor.

This is the source-side selected-entry change-of-variables convention used by
the endpoint reference image.  It is not determinant-chart Haar transport and
does not include the retained-passive raw-order determinant factor. -/
theorem case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres =
      (case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
        (ρ := ρ) (τ := τ) n S J Rres).withDensity
        (case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
          (ρ := ρ) (τ := τ) n hS hnext) := by
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let passiveRef :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let signedBox :=
    case2PassiveThetaCenterSignedBoxMeasure n Rres
  let weightedBox :=
    case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres
  let followingRef :=
    matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  let centerDensity : (Case2PassiveTheta.Center n S J → ℝ) → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)
  haveI : SFinite signedBox := by
    dsimp [signedBox, case2PassiveThetaCenterSignedBoxMeasure]
    infer_instance
  haveI : SFinite followingRef :=
    sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  have hcenterDensity :
      AEMeasurable centerDensity signedBox := by
    simpa [centerDensity, signedBox, case2PassiveThetaCenterSignedBoxMeasure,
      pivotNext] using
      (SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
        pivotNext Rres).1
  have hthetaDensity :
      AEMeasurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          centerDensity theta.yNext)
        (passiveRef.prod signedBox) := by
    simpa [Case2PassiveTheta.yNext] using
      (hcenterDensity.comp_snd (μ := passiveRef))
  have hpassive :
      passiveRef.prod weightedBox =
        (passiveRef.prod signedBox).withDensity
          (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
            centerDensity theta.yNext) := by
    simpa [weightedBox, signedBox, centerDensity,
      case2PassiveThetaCenterWeightedBoxMeasure, Case2PassiveTheta.yNext] using
      (prod_withDensity_right₀ (μ := passiveRef) (ν := signedBox)
        hcenterDensity)
  calc
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres =
        (passiveRef.prod weightedBox).prod followingRef := by
          rfl
    _ =
        ((passiveRef.prod signedBox).prod followingRef).withDensity
          (fun z :
              Case2PassiveThetaWithFollowingFactor
                (ρ := ρ) (τ := τ) n S J ↦
            centerDensity z.1.yNext) := by
          rw [hpassive]
          simpa [Case2PassiveThetaWithFollowingFactor,
            Case2PassiveTheta.yNext] using
            (prod_withDensity_left₀
              (μ := passiveRef.prod signedBox) (ν := followingRef)
              hthetaDensity)
    _ =
        (case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
          (ρ := ρ) (τ := τ) n S J Rres).withDensity
          (case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
            (ρ := ρ) (τ := τ) n hS hnext) := by
          rfl

set_option linter.style.longLine false in
/-- The selected-entry source density is a.e. measurable for the unweighted
enlarged Case 2 source. -/
theorem aemeasurable_case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity_unweightedSource
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    AEMeasurable
      (case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
        (ρ := ρ) (τ := τ) n hS hnext)
      (case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
        (ρ := ρ) (τ := τ) n S J Rres) := by
  let pivotNext := case2PassiveThetaPivotNext n hS hnext
  let passiveRef :=
    case2PassiveThetaPassiveFieldReferenceMeasure
      (ρ := ρ) (τ := τ) n S J
  let signedBox :=
    case2PassiveThetaCenterSignedBoxMeasure n Rres
  let followingRef :=
    matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  let centerDensity : (Case2PassiveTheta.Center n S J → ℝ) → ℝ≥0∞ :=
    fun y ↦
      ENNReal.ofReal
        (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y)
  haveI : SFinite followingRef :=
    sFinite_matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ
  have hcenterDensity :
      AEMeasurable centerDensity signedBox := by
    simpa [centerDensity, signedBox, case2PassiveThetaCenterSignedBoxMeasure,
      pivotNext] using
      (SelectedEntrySignedBox.CenterCoord.monomialLower_sourceDensityBounds
        pivotNext Rres).1
  have hthetaDensity :
      AEMeasurable
        (fun theta : Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ↦
          centerDensity theta.yNext)
        (passiveRef.prod signedBox) := by
    simpa [Case2PassiveTheta.yNext] using
      (hcenterDensity.comp_snd (μ := passiveRef))
  have hsourceDensity :
      AEMeasurable
        (fun z :
            Case2PassiveThetaWithFollowingFactor
              (ρ := ρ) (τ := τ) n S J ↦
          centerDensity z.1.yNext)
        ((passiveRef.prod signedBox).prod followingRef) := by
    simpa [Case2PassiveThetaWithFollowingFactor,
      Case2PassiveTheta.yNext] using
      (hthetaDensity.comp_fst (ν := followingRef))
  simpa [case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure,
    case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity,
    centerDensity, passiveRef, signedBox, followingRef, pivotNext,
    Case2PassiveTheta.yNext] using hsourceDensity

set_option linter.style.longLine false in
/-- Adding a further source density to the enlarged reference source is the
same as adding the product of that density with the selected-entry density to
the unweighted source.

This is source-side density composition only.  It does not identify a raw-order
image with Haar measure and does not add the retained-passive raw-order
Jacobian factor unless `rawDensity` is instantiated with such a factor. -/
theorem case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_eq_unweighted_withDensity_selectedEntrySourceDensity_mul
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (rawDensity :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        ℝ≥0∞)
    (hrawDensity :
      AEMeasurable rawDensity
        (case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
          (ρ := ρ) (τ := τ) n S J Rres)) :
    (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres).withDensity rawDensity =
      (case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
        (ρ := ρ) (τ := τ) n S J Rres).withDensity
        (fun z ↦
          case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
            (ρ := ρ) (τ := τ) n hS hnext z * rawDensity z) := by
  let unweightedSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
      (ρ := ρ) (τ := τ) n S J Rres
  let selectedEntryDensity :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        ℝ≥0∞ :=
    case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
      (ρ := ρ) (τ := τ) n hS hnext
  have hsource :
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres =
        unweightedSource.withDensity selectedEntryDensity := by
    simpa [unweightedSource, selectedEntryDensity] using
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
        (ρ := ρ) (τ := τ) n hS hnext Rres
  have hselected :
      AEMeasurable selectedEntryDensity unweightedSource := by
    simpa [unweightedSource, selectedEntryDensity] using
      aemeasurable_case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity_unweightedSource
        (ρ := ρ) (τ := τ) n hS hnext Rres
  calc
    (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres).withDensity rawDensity =
        (unweightedSource.withDensity selectedEntryDensity).withDensity
          rawDensity := by
          rw [hsource]
    _ =
        unweightedSource.withDensity
          (fun z ↦ selectedEntryDensity z * rawDensity z) := by
          simpa [Pi.mul_apply] using
            (withDensity_mul₀ hselected hrawDensity).symm

set_option linter.style.longLine false in
/-- Local restricted version of
`case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_eq_unweighted_withDensity_selectedEntrySourceDensity_mul`.

This is the form used by local source-chart handoffs after shrinking to a
neighborhood `Ω`. -/
theorem case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_withDensity_restrict_eq_unweighted_withDensity_selectedEntrySourceDensity_mul_restrict
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (rawDensity :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        ℝ≥0∞)
    (hrawDensity :
      AEMeasurable rawDensity
        ((case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
          (ρ := ρ) (τ := τ) n S J Rres).restrict Ω)) :
    ((case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres).withDensity rawDensity).restrict Ω =
      ((case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
        (ρ := ρ) (τ := τ) n S J Rres).withDensity
        (fun z ↦
          case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
            (ρ := ρ) (τ := τ) n hS hnext z * rawDensity z)).restrict Ω := by
  let unweightedSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
      (ρ := ρ) (τ := τ) n S J Rres
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let selectedEntryDensity :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        ℝ≥0∞ :=
    case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
      (ρ := ρ) (τ := τ) n hS hnext
  have hsource :
      referenceSource = unweightedSource.withDensity selectedEntryDensity := by
    simpa [referenceSource, unweightedSource, selectedEntryDensity] using
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
        (ρ := ρ) (τ := τ) n hS hnext Rres
  have hselected :
      AEMeasurable selectedEntryDensity (unweightedSource.restrict Ω) := by
    exact
      (aemeasurable_case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity_unweightedSource
        (ρ := ρ) (τ := τ) n hS hnext Rres).restrict
  calc
    (referenceSource.withDensity rawDensity).restrict Ω =
        (referenceSource.restrict Ω).withDensity rawDensity := by
          rw [restrict_withDensity hΩ]
    _ =
        ((unweightedSource.withDensity selectedEntryDensity).restrict Ω).withDensity
          rawDensity := by
          rw [hsource]
    _ =
        ((unweightedSource.restrict Ω).withDensity selectedEntryDensity).withDensity
          rawDensity := by
          rw [restrict_withDensity hΩ]
    _ =
        (unweightedSource.restrict Ω).withDensity
          (fun z ↦ selectedEntryDensity z * rawDensity z) := by
          simpa [Pi.mul_apply] using
            (withDensity_mul₀ hselected
              (by simpa [unweightedSource] using hrawDensity)).symm
    _ =
        (unweightedSource.withDensity
          (fun z ↦ selectedEntryDensity z * rawDensity z)).restrict Ω := by
          rw [restrict_withDensity hΩ]
    _ =
        ((case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
          (ρ := ρ) (τ := τ) n S J Rres).withDensity
          (fun z ↦
            case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
              (ρ := ρ) (τ := τ) n hS hnext z * rawDensity z)).restrict Ω := by
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
/-- The enlarged reference source pushes through the selected-entry active
coordinate chart as the product of unchanged passive fields, Lebesgue measure
restricted to the selected-entry chart image, and unchanged following-factor
coordinates.

This is only a source-coordinate product change-of-variables statement.  It
does not identify the endpoint topology-tuple image with Haar measure and does
not assert any raw-map pushforward. -/
theorem measure_map_case2PassiveThetaWithFollowingFactor_activeSelectedEntryChart_referenceSource_eq_prod
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let passiveRef :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
    let followingRef :=
      matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ
    let activeChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      fun z ↦ ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.2), z.2)
    Measure.map activeChart
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) =
      ((passiveRef.prod
        ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod followingRef) := by
  intro pivotNext passiveRef followingRef activeChart
  haveI : SFinite passiveRef := by
    exact
      sFinite_case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
  haveI : SFinite followingRef :=
    sFinite_matrixEntryReferenceMeasure
      (Case2ResidualColIndex n S (J + 1)) τ
  let activeThetaChart :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J :=
    fun theta ↦
      (theta.1,
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext theta.2)
  have hactiveTheta_meas : Measurable activeThetaChart := by
    change Measurable
      (Prod.map id (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext))
    exact
      measurable_id.prodMap
        (SelectedEntrySignedBox.CenterCoord.measurable_chartMap pivotNext)
  have hactiveTheta :
      Measure.map activeThetaChart
        (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) =
        passiveRef.prod
          ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)) := by
    change
      Measure.map
          (fun z :
              Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
                (Case2PassiveTheta.Center n S J → ℝ) ↦
            (z.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.2))
          (passiveRef.prod
            (case2PassiveThetaCenterWeightedBoxMeasure n hS hnext Rres)) =
        passiveRef.prod
          ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
            (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
              SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))
    simpa [case2PassiveThetaCenterWeightedBoxMeasure,
      case2PassiveThetaCenterSignedBoxMeasure, passiveRef, pivotNext] using
      (SelectedEntrySignedBox.CenterCoord.map_prod_id_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_prod_restrict_image
        (β := Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)
        pivotNext Rres passiveRef)
  have hsource_sfinite :
      SFinite
        (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) := by
    exact
      sFinite_case2PassiveThetaReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
  letI :
      SFinite
        (case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) :=
    hsource_sfinite
  change
    Measure.map (Prod.map activeThetaChart id)
        ((case2PassiveThetaReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres).prod followingRef) =
      ((passiveRef.prod
        ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod followingRef)
  rw [← Measure.map_prod_map
    (case2PassiveThetaReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres)
    followingRef hactiveTheta_meas measurable_id]
  rw [hactiveTheta]
  simp

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Finite-side-mass active selected-entry integrability for the enlarged
with-following source coordinates.

The residual in this theorem is the active `C 1` selected-entry readout
`chartMap pivotNext z.1.yNext`; it is not the p.13 residual-factor product
`C 1 * C 0`.  Thus this theorem does not discharge the p.13
`residualNegPowerIntegrableOn` socket without a further comparison between the
full residual product and the active readout. -/
theorem case2PassiveThetaWithFollowingFactor_activeReadout_pos_ae_and_lintegral_rpow_neg_prod_finiteMass
    {ρ : Type*} {τ : Type} [Fintype ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (followingMeasure :
      Measure (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    [SFinite followingMeasure]
    (hfollowing_lt_top : followingMeasure Set.univ < ∞)
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
    let sourceMeasure :
        Measure (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      (passiveMeasure.prod weightedBox).prod followingMeasure
    let activeResidual :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveTheta.Center n S J → ℝ :=
      fun z ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
    (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (activeResidual z)) ∧
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (activeResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure activeResidual
  let thetaMeasure :
      Measure (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J) :=
    passiveMeasure.prod weightedBox
  let targetMeasure : Measure (Case2PassiveTheta.Center n S J → ℝ) :=
    (volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
      (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
        SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres)
  let thetaActive :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        Case2PassiveTheta.Center n S J → ℝ :=
    fun theta ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext theta.yNext
  have htarget :
      (∀ᵐ y ∂ targetMeasure, 0 < aoyagiCoordinateSquareSum y) ∧
        (∫⁻ y : Case2PassiveTheta.Center n S J → ℝ,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))
            ∂ targetMeasure) < ∞ := by
    simpa [center, pivotNext, targetMeasure] using
      SelectedEntrySignedBox.CenterCoord.aoyagiCoordinateSquareSum_pos_ae_and_lintegral_rpow_neg_restrict_chartMap_image
        pivotNext ht hRres hcrit
  have hchart_meas :
      Measurable (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext) :=
    SelectedEntrySignedBox.CenterCoord.measurable_chartMap pivotNext
  have hthetaActive : Measurable thetaActive := by
    change Measurable
      (fun theta :
          Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
            (Case2PassiveTheta.Center n S J → ℝ) ↦
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext theta.2)
    exact hchart_meas.comp measurable_snd
  have hactiveResidual : Measurable activeResidual := by
    change Measurable
      (fun z :
          (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
              (Case2PassiveTheta.Center n S J → ℝ)) ×
            Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ ↦
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.2)
    exact hthetaActive.comp measurable_fst
  have hmap_theta_snd :
      Measure.map
          (Prod.snd :
            Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
              (Case2PassiveTheta.Center n S J → ℝ) →
            Case2PassiveTheta.Center n S J → ℝ)
          thetaMeasure =
        passiveMeasure Set.univ • weightedBox := by
    simp [thetaMeasure]
  have hmap_theta :
      Measure.map thetaActive thetaMeasure =
        passiveMeasure Set.univ • targetMeasure := by
    calc
      Measure.map thetaActive thetaMeasure =
          Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
            (Measure.map
              (Prod.snd :
                Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
                  (Case2PassiveTheta.Center n S J → ℝ) →
                Case2PassiveTheta.Center n S J → ℝ)
              thetaMeasure) := by
            simpa [thetaActive, Function.comp_def] using
              (Measure.map_map
                (μ := thetaMeasure)
                (g := SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
                (f :=
                  (Prod.snd :
                    Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J ×
                      (Case2PassiveTheta.Center n S J → ℝ) →
                    Case2PassiveTheta.Center n S J → ℝ))
                hchart_meas measurable_snd).symm
      _ =
          Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
            (passiveMeasure Set.univ • weightedBox) := by
            rw [hmap_theta_snd]
      _ =
          passiveMeasure Set.univ •
            Measure.map (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
              weightedBox := by
            exact
              Measure.map_smul (passiveMeasure Set.univ) weightedBox
                (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext)
      _ = passiveMeasure Set.univ • targetMeasure := by
            rw [SelectedEntrySignedBox.CenterCoord.map_chartMap_signedBoxMeasure_withDensity_sourceDensity_eq_restrict_image]
  have hmap_fst :
      Measure.map
          (Prod.fst :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
              Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
          sourceMeasure =
        followingMeasure Set.univ • thetaMeasure := by
    change
      Measure.map
          (Prod.fst :
            (Case2PassiveTheta (ρ := ρ) (τ := τ) n S J ×
              Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ) →
              Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
          (thetaMeasure.prod followingMeasure) =
        followingMeasure Set.univ • thetaMeasure
    exact Measure.map_fst_prod (μ := thetaMeasure) (ν := followingMeasure)
  have hmap_active :
      Measure.map activeResidual sourceMeasure =
        followingMeasure Set.univ •
          (passiveMeasure Set.univ • targetMeasure) := by
    calc
      Measure.map activeResidual sourceMeasure =
          Measure.map thetaActive
            (Measure.map
              (Prod.fst :
                Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
                  Case2PassiveTheta (ρ := ρ) (τ := τ) n S J)
              sourceMeasure) := by
            simpa [activeResidual, thetaActive, Function.comp_def] using
              (Measure.map_map
                (μ := sourceMeasure)
                (g := thetaActive)
                (f :=
                  (Prod.fst :
                    Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
                      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J))
                hthetaActive measurable_fst).symm
      _ =
          Measure.map thetaActive (followingMeasure Set.univ • thetaMeasure) := by
            rw [hmap_fst]
      _ =
          followingMeasure Set.univ • Measure.map thetaActive thetaMeasure := by
            exact
              Measure.map_smul (followingMeasure Set.univ) thetaMeasure thetaActive
      _ =
          followingMeasure Set.univ •
            (passiveMeasure Set.univ • targetMeasure) := by
            rw [hmap_theta]
  have hpos_meas :
      MeasurableSet
        {y : Case2PassiveTheta.Center n S J → ℝ |
          0 < aoyagiCoordinateSquareSum y} := by
    have hsquare :
        Measurable
          (fun y : Case2PassiveTheta.Center n S J → ℝ ↦
            aoyagiCoordinateSquareSum y) :=
      measurable_aoyagiCoordinateSquareSum measurable_id
    simpa [Set.preimage] using hsquare measurableSet_Ioi
  have hpos_map :
      ∀ᵐ y ∂ Measure.map activeResidual sourceMeasure,
        0 < aoyagiCoordinateSquareSum y := by
    rw [hmap_active]
    exact
      Measure.ae_smul_measure
        (Measure.ae_smul_measure htarget.1 (passiveMeasure Set.univ))
        (followingMeasure Set.univ)
  have hpos_source :
      ∀ᵐ z ∂ sourceMeasure,
        0 < aoyagiCoordinateSquareSum (activeResidual z) :=
    (ae_map_iff hactiveResidual.aemeasurable hpos_meas).1 hpos_map
  have hpow_meas :
      Measurable
        (fun y : Case2PassiveTheta.Center n S J → ℝ ↦
          ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))) := by
    have hsquare :
        Measurable
          (fun y : Case2PassiveTheta.Center n S J → ℝ ↦
            aoyagiCoordinateSquareSum y) :=
      measurable_aoyagiCoordinateSquareSum measurable_id
    fun_prop
  have hfinite_map :
      (∫⁻ y : Case2PassiveTheta.Center n S J → ℝ,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum y) ^ (-t))
          ∂ Measure.map activeResidual sourceMeasure) < ∞ := by
    rw [hmap_active, lintegral_smul_measure, lintegral_smul_measure]
    exact
      ENNReal.mul_lt_top hfollowing_lt_top
        (ENNReal.mul_lt_top hpassive_lt_top htarget.2)
  have hfinite_source :
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (activeResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
    rw [← lintegral_map hpow_meas hactiveResidual]
    exact hfinite_map
  exact ⟨hpos_source, hfinite_source⟩

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Finite-side-mass p.13 product-residual integrability from an a.e. lower
comparison with the active selected-entry readout.

The comparison hypothesis is intentionally explicit: it is the local
following-factor nondegeneracy socket needed to pass from the active `C 1`
readout to the true two-edge residual product `C 1 * C 0`. -/
theorem case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_const_mul_activeReadout_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [Fintype τ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (followingMeasure :
      Measure (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    [SFinite followingMeasure]
    (hfollowing_lt_top : followingMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hcomp :
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
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        (passiveMeasure.prod weightedBox).prod followingMeasure
      let activeResidual :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
            Case2PassiveTheta.Center n S J → ℝ :=
        fun z ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
      let productResidual :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
            Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
        fun z ij ↦
          (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
            (ChartLocalSuffixState.residualFactorProduct
              (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                (ρ := ρ) n hS hcont hnext z eNext e).C
              (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                (e (Fin.last 2)) (e 0)) ij.1 ij.2
      ∃ c : ℝ, 0 < c ∧
        ∀ᵐ z ∂ sourceMeasure,
          c * aoyagiCoordinateSquareSum (activeResidual z) ≤
            aoyagiCoordinateSquareSum (productResidual z)) :
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
          ENNReal.ofReal
            (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      (passiveMeasure.prod weightedBox).prod followingMeasure
    let productResidual :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
      fun z ij ↦
        (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
          (ChartLocalSuffixState.residualFactorProduct
            (case2PassiveThetaWithFollowingFactorEndpointRetainedData
              (ρ := ρ) n hS hcont hnext z eNext e).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
              (e (Fin.last 2)) (e 0)) ij.1 ij.2
    (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure productResidual
  let activeResidual :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        Case2PassiveTheta.Center n S J → ℝ :=
    fun z ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
  have hactive :
      (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (activeResidual z)) ∧
        (∫⁻ z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
          ENNReal.ofReal ((aoyagiCoordinateSquareSum (activeResidual z)) ^ (-t))
            ∂ sourceMeasure) < ∞ := by
    simpa [center, pivotNext, signedBox, weightedBox, sourceMeasure,
      activeResidual] using
      case2PassiveThetaWithFollowingFactor_activeReadout_pos_ae_and_lintegral_rpow_neg_prod_finiteMass
        (ρ := ρ) (τ := τ) n hS hnext passiveMeasure hpassive_lt_top
        followingMeasure hfollowing_lt_top Rres ht hRres hcrit
  rcases hcomp with ⟨c, hc, hle⟩
  have hpos :
      ∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z) := by
    filter_upwards [hactive.1, hle] with z hzpos hzle
    exact lt_of_lt_of_le (mul_pos hc hzpos) hzle
  have hfinite :
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
    exact
      lintegral_ofReal_rpow_neg_lt_top_of_ae_pos_of_ae_const_mul_le
        (μ := sourceMeasure)
        (a := fun z ↦ aoyagiCoordinateSquareSum (activeResidual z))
        (b := fun z ↦ aoyagiCoordinateSquareSum (productResidual z))
        (c := c) (t := t) hc ht hactive.1 hle hactive.2
  exact ⟨hpos, hfinite⟩

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Finite-side-mass p.13 product-residual integrability under an a.e.
uniformly bounded right-inverse hypothesis for the following factor.

This packages the local nondegeneracy socket for the independent following
factor.  It does not construct such a patch or prove it from endpoint topology;
those remain separate local chart obligations. -/
theorem case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_followingFactor_rightInverse_squareSum_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [Fintype τ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (followingMeasure :
      Measure (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    [SFinite followingMeasure]
    (hfollowing_lt_top : followingMeasure Set.univ < ∞)
    {t K : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hright :
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
            ENNReal.ofReal
              (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
      let sourceMeasure :
          Measure
            (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
        (passiveMeasure.prod weightedBox).prod followingMeasure
      ∀ᵐ z ∂ sourceMeasure,
        ∃ G : Matrix τ (Case2ResidualColIndex n S (J + 1)) ℝ,
          z.2 * G =
            (1 :
              Matrix (Case2ResidualColIndex n S (J + 1))
                (Case2ResidualColIndex n S (J + 1)) ℝ) ∧
            aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) => G ij.1 ij.2) ≤ K) :
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
          ENNReal.ofReal
            (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      (passiveMeasure.prod weightedBox).prod followingMeasure
    let productResidual :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
      fun z ij ↦
        (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
          (ChartLocalSuffixState.residualFactorProduct
            (case2PassiveThetaWithFollowingFactorEndpointRetainedData
              (ρ := ρ) n hS hcont hnext z eNext e).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
              (e (Fin.last 2)) (e 0)) ij.1 ij.2
    (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure productResidual
  refine
    case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_const_mul_activeReadout_le
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
      passiveMeasure hpassive_lt_top followingMeasure hfollowing_lt_top
      Rres ht hRres hcrit eNext e ?_
  let activeResidual :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        Case2PassiveTheta.Center n S J → ℝ :=
    fun z ↦ SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext
  let rightInvertibleSet : Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ) :=
    {F | ∃ G : Matrix τ (Case2ResidualColIndex n S (J + 1)) ℝ,
      F * G =
        (1 :
          Matrix (Case2ResidualColIndex n S (J + 1))
            (Case2ResidualColIndex n S (J + 1)) ℝ) ∧
        aoyagiCoordinateSquareSum
          (fun ij : τ × Case2ResidualColIndex n S (J + 1) => G ij.1 ij.2) ≤ K}
  rcases
    exists_pos_const_forall_matrixCoordinateSquareSum_le_mul_right_of_forall_exists_rightInverse_squareSum_le
      (μ := Case2ResidualRowIndex n S (J + 1))
      (s := rightInvertibleSet) (K := K)
      (by
        intro F hF
        exact hF) with
    ⟨c, hc, hc_le⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [hright] with z hzright
  let D : Matrix (Case2ResidualRowIndex n S (J + 1))
      (Case2ResidualColIndex n S (J + 1)) ℝ :=
    case2DisplayedPostPivotResidualBlock n hS hcont
      (case2SuccessorSelectedEntrySourceResidual n hS hnext z.1.yNext eNext)
  let P : Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ :=
    show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
      (ChartLocalSuffixState.residualFactorProduct
        (case2PassiveThetaWithFollowingFactorEndpointRetainedData
          (ρ := ρ) n hS hcont hnext z eNext e).C
        (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
          (e (Fin.last 2)) (e 0)
  have hzmem : z.2 ∈ rightInvertibleSet := by
    simpa [rightInvertibleSet] using hzright
  have hcompare :
      c * aoyagiCoordinateSquareSum
          (fun ij :
              Case2ResidualRowIndex n S (J + 1) ×
                Case2ResidualColIndex n S (J + 1) => D ij.1 ij.2) ≤
        aoyagiCoordinateSquareSum
          (fun ij : Case2ResidualRowIndex n S (J + 1) × τ =>
            (D * z.2) ij.1 ij.2) := by
    simpa [D] using hc_le z.2 hzmem D
  have hactive_sq :
      aoyagiCoordinateSquareSum
          (fun ij :
              Case2ResidualRowIndex n S (J + 1) ×
                Case2ResidualColIndex n S (J + 1) => D ij.1 ij.2) =
        aoyagiCoordinateSquareSum (activeResidual z) := by
    simpa [D, activeResidual, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.displayedPostPivotResidualBlock_squareSum_eq_activeReadout_squareSum
        (ρ := ρ) n hS hcont hnext z eNext
  have hprod : P = D * z.2 := by
    simpa [P, D] using
      Case2PassiveThetaWithFollowingFactor.endpointRetainedData_residualFactorProduct_submatrix_eq_displayedPostPivotResidualBlock_mul_followingFactor
        (ρ := ρ) n hS hcont hnext z eNext e
  change
    c * aoyagiCoordinateSquareSum (activeResidual z) ≤
      aoyagiCoordinateSquareSum (productResidual z)
  rw [← hactive_sq]
  change
    c * aoyagiCoordinateSquareSum
        (fun ij :
            Case2ResidualRowIndex n S (J + 1) ×
              Case2ResidualColIndex n S (J + 1) => D ij.1 ij.2) ≤
      aoyagiCoordinateSquareSum
        (fun ij : Case2ResidualRowIndex n S (J + 1) × τ => P ij.1 ij.2)
  rw [hprod]
  exact hcompare

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Finite-side-mass p.13 product-residual integrability on a restricted
following-factor patch whose points have uniformly bounded right inverses.

This is the local-patch wrapper for the previous a.e. right-inverse theorem:
the patch supplies finite following mass and the right-inverse socket almost
everywhere after restriction. -/
theorem case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_rightInverse_squareSum_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [Fintype τ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (followingMeasure :
      Measure (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    [SFinite followingMeasure]
    {followingPatch : Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ)}
    (hfollowingPatch_meas : MeasurableSet followingPatch)
    (hfollowingPatch_lt_top : followingMeasure followingPatch < ∞)
    {t K : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hpatch_right :
      ∀ F ∈ followingPatch,
        ∃ G : Matrix τ (Case2ResidualColIndex n S (J + 1)) ℝ,
          F * G =
            (1 :
              Matrix (Case2ResidualColIndex n S (J + 1))
                (Case2ResidualColIndex n S (J + 1)) ℝ) ∧
            aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) => G ij.1 ij.2) ≤ K) :
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
          ENNReal.ofReal
            (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      (passiveMeasure.prod weightedBox).prod
        (followingMeasure.restrict followingPatch)
    let productResidual :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
      fun z ij ↦
        (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
          (ChartLocalSuffixState.residualFactorProduct
            (case2PassiveThetaWithFollowingFactorEndpointRetainedData
              (ρ := ρ) n hS hcont hnext z eNext e).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
              (e (Fin.last 2)) (e 0)) ij.1 ij.2
    (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
  intro center pivotNext signedBox weightedBox sourceMeasure productResidual
  haveI : SFinite (followingMeasure.restrict followingPatch) := inferInstance
  have hfollowing_restrict_lt_top :
      followingMeasure.restrict followingPatch Set.univ < ∞ := by
    simpa only [Measure.restrict_apply, MeasurableSet.univ, Set.univ_inter]
      using hfollowingPatch_lt_top
  refine
    case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_ae_followingFactor_rightInverse_squareSum_le
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
      passiveMeasure hpassive_lt_top (followingMeasure.restrict followingPatch)
      hfollowing_restrict_lt_top (t := t) (K := K) Rres ht hRres hcrit eNext e ?_
  have hfollowing_ae :
      ∀ᵐ F ∂ followingMeasure.restrict followingPatch,
        ∃ G : Matrix τ (Case2ResidualColIndex n S (J + 1)) ℝ,
          F * G =
            (1 :
              Matrix (Case2ResidualColIndex n S (J + 1))
                (Case2ResidualColIndex n S (J + 1)) ℝ) ∧
            aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) => G ij.1 ij.2) ≤ K := by
    exact
      (ae_restrict_mem hfollowingPatch_meas).mono
        (fun F hF => hpatch_right F hF)
  exact
    (Measure.quasiMeasurePreserving_snd
      (μ := passiveMeasure.prod weightedBox)
      (ν := followingMeasure.restrict followingPatch)).ae hfollowing_ae

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Finite-side-mass p.13 product-residual integrability on a restricted
following-factor patch whose square reindexing has unit determinant and
uniformly bounded inverse square-sum.

This is a determinant-chart instantiation of the previous right-inverse patch
theorem.  The equivalence `eNext` makes the following factor square; on that
square chart, `F.submatrix id eNext.symm` has inverse, and reindexing that
inverse supplies the required right inverse of `F`. -/
theorem case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_reindexed_det_isUnit_inverse_squareSum_le
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [Fintype τ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    (followingMeasure :
      Measure (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ))
    [SFinite followingMeasure]
    {followingPatch : Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ)}
    (hfollowingPatch_meas : MeasurableSet followingPatch)
    (hfollowingPatch_lt_top : followingMeasure followingPatch < ∞)
    {t K : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (hpatch_det :
      ∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det))
    (hpatch_inv_bound :
      ∀ F ∈ followingPatch,
        aoyagiCoordinateSquareSum
            (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
              (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id) ij.1 ij.2) ≤ K) :
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
          ENNReal.ofReal
            (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
    let sourceMeasure :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      (passiveMeasure.prod weightedBox).prod
        (followingMeasure.restrict followingPatch)
    let productResidual :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
      fun z ij ↦
        (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
          (ChartLocalSuffixState.residualFactorProduct
            (case2PassiveThetaWithFollowingFactorEndpointRetainedData
              (ρ := ρ) n hS hcont hnext z eNext e).C
            (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
              (e (Fin.last 2)) (e 0)) ij.1 ij.2
    (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
      (∫⁻ z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
        ENNReal.ofReal ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
          ∂ sourceMeasure) < ∞ := by
  refine
    case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_rightInverse_squareSum_le
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
      passiveMeasure hpassive_lt_top followingMeasure hfollowingPatch_meas
      hfollowingPatch_lt_top (t := t) (K := K) Rres ht hRres hcrit eNext e ?_
  intro F hF
  exact
    exists_rightInverse_squareSum_le_of_reindexed_det_isUnit_inverse_squareSum_le
      eNext (hpatch_det F hF) (hpatch_inv_bound F hF)

set_option linter.unusedFintypeInType false in
set_option linter.style.longLine false in
/-- Existential finite-side-mass p.13 product-residual integrability over a
locally constructed `matrixEntryReferenceMeasure` following-factor patch.

The extra input is a base following factor `F₀` whose reindexed square
following block has unit determinant.  The produced patch is finite for the
coordinate-product following-factor measure and satisfies the determinant and
uniform inverse-square-sum hypotheses consumed by the determinant-chart patch
wrapper above. -/
theorem exists_matrixEntryReference_followingPatch_case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_of_base_reindexed_det_isUnit
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [Fintype τ] [DecidableEq ρ]
    [∀ q, Fintype (κ' q)] [∀ q, DecidableEq (κ' q)]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    [MeasurableSpace
      (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J)]
    (passiveMeasure :
      Measure (Case2PassiveTheta.PassiveFields (ρ := ρ) (τ := τ) n S J))
    (hpassive_lt_top : passiveMeasure Set.univ < ∞)
    {t : ℝ}
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (ht : 0 ≤ t)
    (hRres : ∀ i, 0 < Rres i)
    (hcrit :
      2 * t <
        (((case2ResidualBlockPivotEntries n S (J + 1)).erase
          (J + 2, J + 2)).card : ℝ) + 1)
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (F₀ : Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ)
    (hF₀det : IsUnit ((F₀.submatrix id eNext.symm).det)) :
    ∃ followingPatch :
        Set (Matrix (Case2ResidualColIndex n S (J + 1)) τ ℝ), ∃ K : ℝ,
      0 < K ∧
        F₀ ∈ followingPatch ∧
        MeasurableSet followingPatch ∧
        matrixEntryReferenceMeasure
          (Case2ResidualColIndex n S (J + 1)) τ followingPatch < ∞ ∧
        (∀ F ∈ followingPatch, IsUnit ((F.submatrix id eNext.symm).det)) ∧
        (∀ F ∈ followingPatch,
          aoyagiCoordinateSquareSum
              (fun ij : τ × Case2ResidualColIndex n S (J + 1) =>
                (((F.submatrix id eNext.symm)⁻¹).submatrix eNext id)
                  ij.1 ij.2) ≤ K) ∧
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
              ENNReal.ofReal
                (SelectedEntrySignedBox.CenterCoord.sourceDensity pivotNext y))
        let sourceMeasure :
            Measure
              (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
          (passiveMeasure.prod weightedBox).prod
            ((matrixEntryReferenceMeasure
              (Case2ResidualColIndex n S (J + 1)) τ).restrict followingPatch)
        let productResidual :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
              Case2ResidualRowIndex n S (J + 1) × τ → ℝ :=
          fun z ij ↦
            (show Matrix (Case2ResidualRowIndex n S (J + 1)) τ ℝ from
              (ChartLocalSuffixState.residualFactorProduct
                (case2PassiveThetaWithFollowingFactorEndpointRetainedData
                  (ρ := ρ) n hS hcont hnext z eNext e).C
                (Fin.last 2) 0 (Fin.zero_le (Fin.last 2))).submatrix
                  (e (Fin.last 2)) (e 0)) ij.1 ij.2
        (∀ᵐ z ∂ sourceMeasure, 0 < aoyagiCoordinateSquareSum (productResidual z)) ∧
          (∫⁻ z :
              Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J,
            ENNReal.ofReal
              ((aoyagiCoordinateSquareSum (productResidual z)) ^ (-t))
              ∂ sourceMeasure) < ∞ := by
  classical
  rcases
      exists_matrixEntryReferenceMeasure_finite_followingPatch_of_reindexed_det_isUnit
        eNext F₀ hF₀det with
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_meas, hpatch_lt_top,
      hpatch_det, hpatch_inv_bound⟩
  haveI :
      SFinite (matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ) :=
    sFinite_matrixEntryReferenceMeasure
      (Case2ResidualColIndex n S (J + 1)) τ
  refine
    ⟨followingPatch, K, hK_pos, hF₀_mem, hpatch_meas, hpatch_lt_top,
      hpatch_det, hpatch_inv_bound, ?_⟩
  exact
    case2PassiveThetaWithFollowingFactor_productResidual_pos_ae_and_lintegral_rpow_neg_prod_restrict_followingPatch_of_forall_mem_reindexed_det_isUnit_inverse_squareSum_le
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext
      passiveMeasure hpassive_lt_top
      (matrixEntryReferenceMeasure (Case2ResidualColIndex n S (J + 1)) τ)
      hpatch_meas hpatch_lt_top (t := t) (K := K) Rres ht hRres hcrit
      eNext e hpatch_det hpatch_inv_bound

set_option linter.style.longLine false in
/-- Composing the endpoint topology tuple with the finite active-coordinate
readout gives the same reference-measure pushforward as the source-coordinate
active selected-entry chart.

This is still only a coordinate readout of the endpoint image.  It does not
identify the endpoint image measure with determinant-chart Haar measure and
does not assert any raw-map pushforward. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_activeReadout_comp_referenceSource_eq_prod
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ} (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let passiveRef :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
    let followingRef :=
      matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ
    let activeReadout :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout
        n e
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun z ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext z eNext e
    Measure.map (fun z ↦ activeReadout (Y z))
        (case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) =
      ((passiveRef.prod
        ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod followingRef) := by
  intro pivotNext passiveRef followingRef activeReadout Y
  have hfun :
      (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        activeReadout (Y z)) =
        (fun z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
          ((z.1.1,
            SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)) := by
    funext z
    simpa [activeReadout, Y, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
        (ρ := ρ) n hS hcont hnext z eNext e
  rw [hfun]
  simpa [pivotNext, passiveRef, followingRef] using
    measure_map_case2PassiveThetaWithFollowingFactor_activeSelectedEntryChart_referenceSource_eq_prod
      (ρ := ρ) (τ := τ) n hS hnext Rres

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
/-- The named enlarged endpoint reference image factors through the active
selected-entry chart and the finite active-coordinate writeback.

This is only a pushforward factorization of the endpoint image measure.  It
does not identify the endpoint image with determinant-chart Haar measure and
does not assert any raw-order change-of-variables statement. -/
theorem case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_eq_map_activeWriteback_activeSelectedEntryChart_restrict
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        Rres Ω
    let activeWriteback :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveWriteback
        n e
    let activeChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      fun z ↦ ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    endpointReferenceImage =
      Measure.map activeWriteback
        (Measure.map activeChart (referenceSource.restrict Ω)) := by
  intro pivotNext referenceSource endpointReferenceImage activeWriteback activeChart
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  let activeThetaChart :
      Case2PassiveTheta (ρ := ρ) (τ := τ) n S J →
        Case2PassiveTheta (ρ := ρ) (τ := τ) n S J :=
    fun theta ↦
      (theta.1, SelectedEntrySignedBox.CenterCoord.chartMap pivotNext theta.2)
  have hW : Measurable activeWriteback := by
    exact
      (Case2PassiveThetaWithFollowingFactor.continuous_endpointTopologyTupleActiveWriteback
        (ρ := ρ) (τ := τ) n e).measurable
  have hactiveTheta : Measurable activeThetaChart := by
    change Measurable
      (Prod.map id (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext))
    exact
      measurable_id.prodMap
        (SelectedEntrySignedBox.CenterCoord.measurable_chartMap pivotNext)
  have hactive : Measurable activeChart := by
    change Measurable (Prod.map activeThetaChart id)
    exact hactiveTheta.prodMap measurable_id
  have hfun :
      Y =
        (fun z :
            Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
          activeWriteback (activeChart z)) := by
    funext z
    simpa [Y, activeWriteback, activeChart, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_eq_activeWriteback_activeSelectedEntryChart
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext z eNext e
  calc
    endpointReferenceImage =
        Measure.map Y (referenceSource.restrict Ω) := by
          simp [endpointReferenceImage,
            case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
            referenceSource, Y]
    _ =
        Measure.map
          (fun z :
              Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
            activeWriteback (activeChart z))
          (referenceSource.restrict Ω) := by
          rw [hfun]
    _ =
        Measure.map activeWriteback
          (Measure.map activeChart (referenceSource.restrict Ω)) := by
          rw [Measure.map_map hW hactive]
          rfl

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-side selected-entry change of variables for the enlarged endpoint
reference image.

Pushing the unweighted enlarged coordinate-product source with density
`case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity` through the
endpoint topology tuple gives exactly the named endpoint reference image of
the same source restriction.  The target is the actual endpoint image measure,
not determinant-chart Haar; the retained-passive raw-order determinant enters
only after composing with `topologyTupleEdgeRawOrder`. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_unweighted_withDensity_selectedEntrySourceDensity_restrict_eq_endpointReferenceImageMeasure
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
    let unweightedSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorUnweightedSourceMeasure
        (ρ := ρ) (τ := τ) n S J Rres
    let selectedEntryDensity :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          ℝ≥0∞ :=
      case2PassiveThetaWithFollowingFactorSelectedEntrySourceDensity
        (ρ := ρ) (τ := τ) n hS hnext
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    Measure.map Y ((unweightedSource.withDensity selectedEntryDensity).restrict Ω) =
      endpointReferenceImage := by
  intro unweightedSource selectedEntryDensity Y endpointReferenceImage
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  have hsource :
      referenceSource = unweightedSource.withDensity selectedEntryDensity := by
    simpa [referenceSource, unweightedSource, selectedEntryDensity] using
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure_eq_unweighted_withDensity_selectedEntrySourceDensity
        (ρ := ρ) (τ := τ) n hS hnext Rres
  simpa [endpointReferenceImage,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
    referenceSource, Y] using
    congrArg (fun μ : Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) ↦
      Measure.map Y (μ.restrict Ω)) hsource.symm

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The named enlarged endpoint reference image measure is supported on the
actual image of the chosen source set.

This is support for the endpoint image measure only.  It is not determinant
chart Haar measure and does not assert a raw-map pushforward. -/
theorem case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
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
    (himage :
      MeasurableSet
        ((fun theta ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e) '' Ω)) :
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    endpointReferenceImage.restrict (Y '' Ω) = endpointReferenceImage := by
  intro Y endpointReferenceImage
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have himageY : MeasurableSet (Y '' Ω) := by
    simpa [Y] using himage
  simpa [endpointReferenceImage,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
    referenceSource, Y] using
    measure_map_restrict_image_eq_self_of_aemeasurable
      Y referenceSource Ω hΩ himageY hY

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The unfolded endpoint pushforward is the named endpoint reference image
measure restricted to the actual endpoint image.

The target measure is the named endpoint image of the same restricted source
reference; this is not determinant-chart Haar measure. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image
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
    (himage :
      MeasurableSet
        ((fun theta ↦
          case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
            (ρ := ρ) n hS hcont hnext theta eNext e) '' Ω)) :
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
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    Measure.map Y (referenceSource.restrict Ω) =
      endpointReferenceImage.restrict (Y '' Ω) := by
  intro referenceSource Y endpointReferenceImage
  have hsupp :=
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ himage
  symm
  simpa [endpointReferenceImage,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
    referenceSource, Y] using hsupp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On measurable selected-pivot-nonzero source sets, the named enlarged
endpoint reference image measure is supported on its actual image without a
separately supplied image-measurability hypothesis.

This is still only support for the endpoint image measure.  It is not
determinant-chart Haar measure and does not assert a raw-map pushforward. -/
theorem case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [T2Space (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩpivot :
      Ω ⊆ {z |
        case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}) :
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    endpointReferenceImage.restrict (Y '' Ω) = endpointReferenceImage := by
  intro Y endpointReferenceImage
  have himage :
      MeasurableSet (Y '' Ω) := by
    simpa [Y, case2PassiveThetaWithFollowingFactorEndpointSectorSet] using
      Case2PassiveThetaWithFollowingFactor.measurableSet_case2PassiveThetaWithFollowingFactorEndpointSectorSet_of_subset_pivotNonzero
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Ω hΩ hΩpivot
  exact
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ
      (by simpa [Y] using himage)

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- On measurable selected-pivot-nonzero source sets, the unfolded endpoint
pushforward is the named endpoint reference image measure restricted to the
actual endpoint image, with image measurability supplied by endpoint
injectivity.

The target measure is the named endpoint image of the same restricted source
reference; this is not determinant-chart Haar measure. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_referenceSource_restrict_eq_endpointReferenceImageMeasure_restrict_image_of_subset_pivotNonzero
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [PolishSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [MeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    [T2Space (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    (hΩ : MeasurableSet Ω)
    (hΩpivot :
      Ω ⊆ {z |
        case2PassiveThetaPivotNonzero (ρ := ρ) (τ := τ) n hS hnext z.1}) :
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
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    Measure.map Y (referenceSource.restrict Ω) =
      endpointReferenceImage.restrict (Y '' Ω) := by
  intro referenceSource Y endpointReferenceImage
  have hsupp :=
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_restrict_image_eq_self_of_subset_pivotNonzero
      (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω hΩ hΩpivot
  symm
  simpa [endpointReferenceImage,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
    referenceSource, Y] using hsupp

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- The active-coordinate marginal of the named enlarged endpoint reference
image is the product reference measure produced by the selected-entry active
chart.

This is a marginal/readout theorem for the endpoint image with `Ω = Set.univ`.
It does not identify the full endpoint image measure with determinant-chart
Haar measure and does not assert a raw-map pushforward. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_activeReadout_univ_eq_prod
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let passiveRef :=
      case2PassiveThetaPassiveFieldReferenceMeasure
        (ρ := ρ) (τ := τ) n S J
    let followingRef :=
      matrixEntryReferenceMeasure
        (Case2ResidualColIndex n S (J + 1)) τ
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        Rres Set.univ
    let activeReadout :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout
        n e
    Measure.map activeReadout endpointReferenceImage =
      ((passiveRef.prod
        ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod followingRef) := by
  intro pivotNext passiveRef followingRef endpointReferenceImage activeReadout
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  have hactive : Measurable activeReadout := by
    exact
      (Case2PassiveThetaWithFollowingFactor.continuous_endpointTopologyTupleActiveReadout
        (ρ := ρ) (τ := τ) n e).measurable
  have hY : Measurable Y := by
    exact
      (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e).measurable
  calc
    Measure.map activeReadout endpointReferenceImage =
        Measure.map activeReadout (Measure.map Y (referenceSource.restrict Set.univ)) := by
          simp [endpointReferenceImage,
            case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
            referenceSource, Y]
    _ = Measure.map (fun z ↦ activeReadout (Y z))
        (referenceSource.restrict Set.univ) := by
          rw [Measure.map_map hactive hY]
          rfl
    _ = Measure.map (fun z ↦ activeReadout (Y z)) referenceSource := by
          simp
    _ =
      ((passiveRef.prod
        ((volume : Measure (Case2PassiveTheta.Center n S J → ℝ)).restrict
          (SelectedEntrySignedBox.CenterCoord.chartMap pivotNext ''
            SelectedEntrySignedBox.CenterCoord.signedBoxSet Rres))).prod followingRef) := by
          simpa [activeReadout, Y, referenceSource, pivotNext, passiveRef, followingRef] using
            measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_activeReadout_comp_referenceSource_eq_prod
              (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- For an arbitrary source restriction, the active-coordinate marginal of the
named endpoint reference image is exactly the active selected-entry chart
pushforward of the same restricted source reference.

Unlike the `Set.univ` corollary, this does not identify the marginal with an
unrestricted product measure.  The right side keeps the restricted source set
visible. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure_activeReadout_eq_activeSelectedEntryChart_restrict
    {ρ : Type*} {τ : Type} {κ' : Fin 3 → Type*}
    [Fintype ρ] [DecidableEq ρ] [Fintype τ]
    (n : ℕ → ℕ) {S J : ℕ}
    [OpensMeasurableSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [BorelSpace
      (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)]
    [OpensMeasurableSpace (TopologyTuple ρ κ' ℝ)]
    [BorelSpace (TopologyTuple ρ κ' ℝ)]
    (hS : 1 ≤ S)
    (hcont : J + 1 ≤ prefixMinNat n (S + 1))
    (hnext : J + 2 ≤ prefixMinNat n (S + 1))
    (eNext : τ ≃ Case2ResidualColIndex n S (J + 1))
    (e : ∀ q : Fin 3, case2PostPivotTwoEdgeDomain n S J τ q ≃ κ' q)
    (Rres : Case2PassiveTheta.Center n S J → ℝ)
    (Ω :
      Set (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J)) :
    let pivotNext := case2PassiveThetaPivotNext n hS hnext
    let referenceSource :
        Measure
          (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
      case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
        (ρ := ρ) (τ := τ) n hS hnext Rres
    let endpointReferenceImage : Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e
        Rres Ω
    let activeReadout :
        TopologyTuple ρ κ' ℝ →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout
        n e
    let activeChart :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J :=
      fun z ↦ ((z.1.1,
        SelectedEntrySignedBox.CenterCoord.chartMap pivotNext z.1.yNext), z.2)
    Measure.map activeReadout endpointReferenceImage =
      Measure.map activeChart (referenceSource.restrict Ω) := by
  intro pivotNext referenceSource endpointReferenceImage activeReadout activeChart
  let Y :
      Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
        TopologyTuple ρ κ' ℝ :=
    fun z ↦
      case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext z eNext e
  have hactive : Measurable activeReadout := by
    exact
      (Case2PassiveThetaWithFollowingFactor.continuous_endpointTopologyTupleActiveReadout
        (ρ := ρ) (τ := τ) n e).measurable
  have hY : Measurable Y := by
    exact
      (continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
        (ρ := ρ) n hS hcont hnext eNext e).measurable
  have hfun :
      (fun z :
          Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J ↦
        activeReadout (Y z)) = activeChart := by
    funext z
    simpa [activeChart, activeReadout, Y, pivotNext] using
      Case2PassiveThetaWithFollowingFactor.endpointTopologyTupleActiveReadout_endpointTopologyTuple_eq_activeSelectedEntryChart
        (ρ := ρ) n hS hcont hnext z eNext e
  calc
    Measure.map activeReadout endpointReferenceImage =
        Measure.map activeReadout (Measure.map Y (referenceSource.restrict Ω)) := by
          simp [endpointReferenceImage,
            case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
            referenceSource, Y]
    _ = Measure.map (fun z ↦ activeReadout (Y z))
        (referenceSource.restrict Ω) := by
          rw [Measure.map_map hactive hY]
          rfl
    _ = Measure.map activeChart (referenceSource.restrict Ω) := by
          rw [hfun]

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

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedSectionVars false in
set_option linter.style.longLine false in
/-- Source-measure domination by the concrete enlarged coordinate reference
pushes forward to domination by the named endpoint reference image measure.

This is a source-to-endpoint image-measure domination theorem.  It targets the
actual endpoint image of the reference source, not determinant-chart Haar, and
it does not assert a raw-map pushforward. -/
theorem measure_map_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple_sourceMeasure_restrict_le_smul_endpointReferenceImage_of_sourceMeasure_le_smul_referenceSource
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
    (sourceMeasure :
      Measure (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J))
    {d : ℝ≥0∞}
    (hsource :
      sourceMeasure ≤
        d • case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
          (ρ := ρ) (τ := τ) n hS hnext Rres) :
    let endpointReferenceImage :
        Measure (TopologyTuple ρ κ' ℝ) :=
      case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure
        (ρ := ρ) (τ := τ) (κ' := κ') n hS hcont hnext eNext e Rres Ω
    let Y :
        Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J →
          TopologyTuple ρ κ' ℝ :=
      fun theta ↦
        case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext theta eNext e
    Measure.map Y (sourceMeasure.restrict Ω) ≤ d • endpointReferenceImage := by
  intro endpointReferenceImage Y
  let referenceSource :
      Measure
        (Case2PassiveThetaWithFollowingFactor (ρ := ρ) (τ := τ) n S J) :=
    case2PassiveThetaWithFollowingFactorReferenceSourceMeasure
      (ρ := ρ) (τ := τ) n hS hnext Rres
  have hrestrict :
      sourceMeasure.restrict Ω ≤ d • referenceSource.restrict Ω := by
    calc
      sourceMeasure.restrict Ω ≤ (d • referenceSource).restrict Ω :=
        Measure.restrict_mono Set.Subset.rfl hsource
      _ = d • referenceSource.restrict Ω := by
        rw [Measure.restrict_smul]
  have hY :
      AEMeasurable Y (referenceSource.restrict Ω) := by
    have hYcont : Continuous Y := by
      simpa [Y] using
        continuous_case2PassiveThetaWithFollowingFactorEndpointTopologyTuple
          (ρ := ρ) n hS hcont hnext eNext e
    exact hYcont.measurable.aemeasurable
  have hmap :
      Measure.map Y (sourceMeasure.restrict Ω) ≤
        d • Measure.map Y (referenceSource.restrict Ω) :=
    map_le_smul_map_of_le_smul_aemeasurable hY hrestrict
  simpa [endpointReferenceImage,
    case2PassiveThetaWithFollowingFactorEndpointReferenceImageMeasure,
    referenceSource, Y] using hmap

end Aoyagi
end DLN
end DLNFibre
