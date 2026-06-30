import DLNFibre.Core.OrbitCodim
import DLNFibre.DLN.Aoyagi.LocalMeasureHandoff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Original DLN coordinate prior

This file names the ambient coordinate Lebesgue measure and a prior-weighted
variant on the flattened DLN parameter coordinates `RepCoord d → ℝ`.

The measure is independent of the retained-passive or selected-entry chart
pushforwards.  No theorem here transports it to an Aoyagi source chart,
identifies it with a chart-produced source-image measure, proves source-image
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

end Aoyagi
end DLN
end DLNFibre

end
