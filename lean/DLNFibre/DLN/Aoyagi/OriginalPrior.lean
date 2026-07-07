import DLNFibre.Core.OrbitCodim
import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import DLNFibre.DLN.Aoyagi.MatrixMeasurable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Original DLN coordinate prior

This file names the ambient coordinate Lebesgue measure and prior-weighted
variants on the flattened DLN parameter coordinates `RepCoord d → ℝ` and on
the actual matrix tuple space `Tuple (k := ℝ) d`.

These measures are independent of the retained-passive or selected-entry chart
pushforwards.  No theorem here transports them to an Aoyagi source chart,
identifies them with a chart-produced source-image measure, proves source-image
coverage, or extracts an RLCT.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DLNFibre
namespace DLN
namespace Aoyagi

open DLNFibre.Core

variable {N : ℕ}

/-- The canonical matrix-entry flattening is measurable. -/
theorem measurable_canonicalCoord
    (d : Fin (N + 1) → ℕ) :
    Measurable (canonicalCoord d : Tuple (k := ℝ) d → (RepCoord d → ℝ)) := by
  rw [measurable_pi_iff]
  intro x
  simpa [canonicalCoord_apply] using
    ((measurable_pi_apply x.2.2).comp
      ((measurable_pi_apply x.2.1).comp (measurable_pi_apply x.1)) :
      Measurable (fun A : Tuple (k := ℝ) d ↦ A x.1 x.2.1 x.2.2))

/-- The inverse of the canonical matrix-entry flattening is measurable. -/
theorem measurable_canonicalCoord_symm
    (d : Fin (N + 1) → ℕ) :
    Measurable ((canonicalCoord d).symm :
      (RepCoord d → ℝ) → Tuple (k := ℝ) d) := by
  rw [measurable_pi_iff]
  intro i
  change Measurable
    (fun x : RepCoord d → ℝ ↦
      (fun r : Fin (d i.succ) ↦
        fun c : Fin (d i.castSucc) ↦ (canonicalCoord d).symm x i r c))
  rw [measurable_pi_iff]
  intro r
  rw [measurable_pi_iff]
  intro c
  simpa [canonicalCoord] using
    (measurable_pi_apply (⟨i, r, c⟩ : RepCoord d) :
      Measurable (fun x : RepCoord d → ℝ ↦ x (⟨i, r, c⟩ : RepCoord d)))

/-- Ambient product Lebesgue measure on the flattened original DLN parameter
coordinates, one coordinate for every matrix entry of the tuple. -/
noncomputable abbrev originalCoordinateVolume
    (d : Fin (N + 1) → ℕ) : Measure (RepCoord d → ℝ) :=
  volume

/-- Ambient prior measure on flattened original DLN parameter coordinates,
with density written against product Lebesgue measure. -/
noncomputable def originalCoordinatePrior
    (d : Fin (N + 1) → ℕ) (density : (RepCoord d → ℝ) → ℝ) :
    Measure (RepCoord d → ℝ) :=
  (originalCoordinateVolume d).withDensity
    (fun x ↦ ENNReal.ofReal (density x))

/-- Ambient product Lebesgue measure on the original DLN matrix tuple space,
defined by transporting flattened coordinate Lebesgue measure through the
inverse of the canonical entry-flattening equivalence. -/
noncomputable def originalTupleVolume
    (d : Fin (N + 1) → ℕ) : Measure (Tuple (k := ℝ) d) :=
  Measure.map (canonicalCoord d).symm (originalCoordinateVolume d)

/-- Pushing the tuple-side original volume forward by the canonical
entry-flattening returns flattened coordinate volume. -/
theorem originalTupleVolume_map_canonicalCoord
    (d : Fin (N + 1) → ℕ) :
    Measure.map (canonicalCoord d) (originalTupleVolume d) =
      originalCoordinateVolume d := by
  rw [originalTupleVolume]
  rw [Measure.map_map]
  · simp
  · exact measurable_canonicalCoord d
  · exact measurable_canonicalCoord_symm d

/-- Ambient prior measure on the original DLN matrix tuple space, with density
written against tuple-side original coordinate volume. -/
noncomputable def originalTuplePrior
    (d : Fin (N + 1) → ℕ) (density : Tuple (k := ℝ) d → ℝ) :
    Measure (Tuple (k := ℝ) d) :=
  (originalTupleVolume d).withDensity
    (fun A ↦ ENNReal.ofReal (density A))

set_option linter.style.longLine false in
/-- Transporting a restricted original coordinate prior through the inverse
canonical entry-flattening gives the corresponding restricted tuple prior.

This is only finite-dimensional coordinate/tuple prior transport.  It does
not identify an Aoyagi source-chart image measure, compute a retained-passive
Jacobian, prove source-rank coverage, construct normal crossings, compute a
pole order, or extract an RLCT. -/
theorem map_canonicalCoord_symm_originalCoordinatePrior_restrict_eq_originalTuplePrior_restrict_image
    (d : Fin (N + 1) → ℕ)
    {density : (RepCoord d → ℝ) → ℝ}
    {S : Set (RepCoord d → ℝ)}
    (hS : MeasurableSet S)
    (hdensity :
      AEMeasurable
        (fun A : Tuple (k := ℝ) d ↦
          ENNReal.ofReal (density (canonicalCoord d A)))
        (Measure.map (canonicalCoord d).symm
          ((originalCoordinateVolume d).restrict S))) :
    Measure.map (canonicalCoord d).symm
        ((originalCoordinatePrior d density).restrict S) =
      (originalTuplePrior d (fun A ↦ density (canonicalCoord d A))).restrict
        ((canonicalCoord d).symm '' S) := by
  let T : (RepCoord d → ℝ) ≃ᵐ Tuple (k := ℝ) d :=
    { toEquiv := (canonicalCoord d).symm
      measurable_toFun := measurable_canonicalCoord_symm d
      measurable_invFun := measurable_canonicalCoord d }
  let tupleDensity : Tuple (k := ℝ) d → ℝ≥0∞ :=
    fun A ↦ ENNReal.ofReal (density (canonicalCoord d A))
  have hS_image : MeasurableSet (T '' S) :=
    (T.measurableSet_image).2 hS
  have hcomp_density :
      (fun x : RepCoord d → ℝ ↦ tupleDensity (T x)) =
        fun x ↦ ENNReal.ofReal (density x) := by
    funext x
    simp [tupleDensity, T]
  have hleft :
      (originalCoordinatePrior d density).restrict S =
        ((originalCoordinateVolume d).restrict S).withDensity
          (fun x ↦ tupleDensity (T x)) := by
    rw [originalCoordinatePrior, restrict_withDensity hS]
    rw [hcomp_density]
  have hright :
      (originalTuplePrior d (fun A ↦ density (canonicalCoord d A))).restrict
          (T '' S) =
        ((originalTupleVolume d).restrict (T '' S)).withDensity
          tupleDensity := by
    rw [originalTuplePrior, restrict_withDensity hS_image]
  have hT_meas :
      AEMeasurable T ((originalCoordinateVolume d).restrict S) :=
    T.measurable.aemeasurable
  have hweighted :
      Measure.map T
          (((originalCoordinateVolume d).restrict S).withDensity
            (fun x ↦ tupleDensity (T x))) =
        (Measure.map T ((originalCoordinateVolume d).restrict S)).withDensity
          tupleDensity := by
    exact
      measure_map_withDensity_comp_of_aemeasurable
        (η := (originalCoordinateVolume d).restrict S)
        (f := T) (g := tupleDensity) hT_meas hdensity
  have hvolume :
      Measure.map T ((originalCoordinateVolume d).restrict S) =
        (originalTupleVolume d).restrict (T '' S) := by
    have hrestrict :=
      (T.restrict_map (originalCoordinateVolume d) (T '' S)).symm
    have hpre : T ⁻¹' (T '' S) = S :=
      Set.preimage_image_eq S T.injective
    simpa [hpre, originalTupleVolume, T] using hrestrict
  calc
    Measure.map (canonicalCoord d).symm
        ((originalCoordinatePrior d density).restrict S) =
        Measure.map T
          (((originalCoordinateVolume d).restrict S).withDensity
            (fun x ↦ tupleDensity (T x))) := by
          rw [hleft]
          rfl
    _ = (Measure.map T ((originalCoordinateVolume d).restrict S)).withDensity
          tupleDensity := hweighted
    _ = ((originalTupleVolume d).restrict (T '' S)).withDensity
          tupleDensity := by rw [hvolume]
    _ = (originalTuplePrior d (fun A ↦ density (canonicalCoord d A))).restrict
          ((canonicalCoord d).symm '' S) := by
          simpa [T, tupleDensity] using hright.symm

/-- A local upper bound on the original coordinate prior density gives local
domination by restricted coordinate Lebesgue measure.  Finiteness of the
bound, when needed for later integrability transfer, is a downstream
hypothesis. -/
theorem originalCoordinatePrior_restrict_le_smul_of_ae_le
    (d : Fin (N + 1) → ℕ) {density : (RepCoord d → ℝ) → ℝ}
    {s : Set (RepCoord d → ℝ)} {K : ℝ}
    (hs : MeasurableSet s)
    (hdensity :
      ∀ᵐ x ∂(originalCoordinateVolume d).restrict s, density x ≤ K) :
    (originalCoordinatePrior d density).restrict s ≤
      ENNReal.ofReal K • (originalCoordinateVolume d).restrict s :=
  restrict_withDensity_le_smul_restrict_of_ae_le hs
    (hdensity.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

/-- A local upper bound on the original tuple prior density gives local
domination by restricted tuple-side original coordinate volume.  This is only
bounded-density bookkeeping on the ambient tuple space; it does not transport
the measure through any Aoyagi chart. -/
theorem originalTuplePrior_restrict_le_smul_of_ae_le
    (d : Fin (N + 1) → ℕ) {density : Tuple (k := ℝ) d → ℝ}
    {s : Set (Tuple (k := ℝ) d)} {K : ℝ}
    (hs : MeasurableSet s)
    (hdensity :
      ∀ᵐ A ∂(originalTupleVolume d).restrict s, density A ≤ K) :
    (originalTuplePrior d density).restrict s ≤
      ENNReal.ofReal K • (originalTupleVolume d).restrict s :=
  restrict_withDensity_le_smul_restrict_of_ae_le hs
    (hdensity.mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)

end Aoyagi
end DLN
end DLNFibre

end
