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
