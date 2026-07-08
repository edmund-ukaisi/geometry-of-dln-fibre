import DLNFibre.DLN.RLCT.Validate.D1GeChart
import DLNFibre.DLN.RLCT.Foundations.S1InverseDerivEquiv

/-!
# `DLNFibre.DLN.RLCT.Validate.D1GeChartGlobal` — invertible derivative from a LEFT inverse (rung 8)

The general-`L` chart's globalisation needs an invertible derivative at the base point. The L = 2
route (`derivEquiv_of_eventual_inverse`, `S1InverseDerivEquiv`) used BOTH inverse germs `Ψ∘Φ =ᶠ id`
and `Φ∘Ψ =ᶠ id`. Here we observe that the LEFT inverse alone suffices in finite dimensions: from
`Ψ∘Φ =ᶠ id` the chain rule gives `DΨ ∘ DΦ = id`, so `DΦ` is injective, hence (finite-dimensional
`injective_iff_surjective`) bijective — a `ContinuousLinearEquiv`. This avoids proving the reverse
`Ψ∘Φ =ᶠ id` the chain rule gives `DΨ ∘ DΦ = id`, so `DΦ` is injective, hence (finite-dim
`Ψ∘Φ = id` is already established (`schurChartRawInvGen_schurChartRawGen`).
-/

open Filter
open scoped Topology

namespace DLNFibre.DLN.RLCT

/-- **An invertible chart derivative from a LEFT inverse germ** (finite-dim). If `Φ, Ψ : E → E` have
named derivatives `A` at `wstar`, `Bd` at `Φ wstar`, and `Ψ ∘ Φ =ᶠ id` near `wstar`, then `A`
underlies a continuous linear equivalence with `HasFDerivAt Φ (f' : E →L[ℝ] E) wstar`. The
finite-dimensional strengthening of `derivEquiv_of_eventual_inverse` needing only the left germ
(`Bd ∘ A = id` ⟹ `A` injective ⟹ bijective). -/
theorem derivEquiv_of_left_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ Ψ : E → E) (wstar : E) (A Bd : E →L[ℝ] E)
    (hΦ' : HasFDerivAt Φ A wstar) (hΨ' : HasFDerivAt Ψ Bd (Φ wstar))
    (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 wstar] id) :
    ∃ f' : E ≃L[ℝ] E, HasFDerivAt Φ (f' : E →L[ℝ] E) wstar := by
  -- `Bd ∘ A = id` from `Ψ ∘ Φ =ᶠ id`.
  have hcomp1 : HasFDerivAt (Ψ ∘ Φ) (Bd.comp A) wstar := hΨ'.comp wstar hΦ'
  have hid1 : HasFDerivAt (Ψ ∘ Φ) (ContinuousLinearMap.id ℝ E) wstar :=
    (hasFDerivAt_id (𝕜 := ℝ) wstar).congr_of_eventuallyEq hΨΦ
  have hBA : Bd.comp A = ContinuousLinearMap.id ℝ E := hcomp1.unique hid1
  -- `A` injective (left inverse `Bd`), hence bijective in finite dimensions.
  have hinj : Function.Injective (A : E →ₗ[ℝ] E) := by
    have hL : Function.LeftInverse Bd A := fun x => by
      have := ContinuousLinearMap.ext_iff.mp hBA x; simpa using this
    exact hL.injective
  have hbij : Function.Bijective (A : E →ₗ[ℝ] E) :=
    ⟨hinj, (LinearMap.injective_iff_surjective).mp hinj⟩
  refine ⟨(LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv, ?_⟩
  have hcoe : ((LinearEquiv.ofBijective (A : E →ₗ[ℝ] E) hbij).toContinuousLinearEquiv
      : E →L[ℝ] E) = A := by ext x; rfl
  rw [hcoe]; exact hΦ'

end DLNFibre.DLN.RLCT
