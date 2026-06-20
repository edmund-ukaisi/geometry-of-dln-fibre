import DLNFibre.DLN.RLCT.Foundations.Rlct
import DLNFibre.DLN.RLCT.Foundations.ParamsFlat
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1Transport` — S1.1 weighted-threshold transport

The S1.1 linchpin (`weightedThreshold_transport`): the weighted RLCT threshold `θ(F, φ; {w*})` is
invariant under a proper a.e.-analytic diffeo `π`, with the Jacobian `|det Dπ|` entering as a
weight. Proven standalone here (Foundations), to be wired into the goal skeleton. Feeds D1/L2, R1.
-/

namespace DLNFibre.DLN.RLCT

open MeasureTheory Set

/-- **S1.1 (weighted-threshold transport).** For a proper map `π` on a finite-dim real space with
additive-Haar `volume`, injective and differentiable off a null measurable set `E` (Jacobian `Dπ`),
the weighted threshold transports with the Jacobian weight: `θ(F, φ; {w*}) = θ(F∘π, (φ∘π)·|det Dπ|;
π⁻¹{w*})`. -/
theorem weightedThreshold_transport
    {M : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [MeasureSpace M] [BorelSpace M]
    [FiniteDimensional ℝ M] [(volume : Measure M).IsAddHaarMeasure]
    (F φ : M → ℝ) (wstar : M)
    (π : M → M) (Dπ : M → (M →L[ℝ] M)) (E : Set M)
    (hproper : IsProperMap π)
    (hE_meas : MeasurableSet E)
    (hE_null : volume E = 0)
    (hinj : Set.InjOn π Eᶜ)
    (hderiv : ∀ m ∈ Eᶜ, HasFDerivAt π (Dπ m) m) :
    weightedThreshold F φ {wstar}
      = weightedThreshold (F ∘ π) (fun m => φ (π m) * |(Dπ m).det|) (π ⁻¹' {wstar}) := by
  sorry

end DLNFibre.DLN.RLCT
