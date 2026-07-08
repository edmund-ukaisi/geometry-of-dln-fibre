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

/-! ## Rung 7 prep — ContDiff of the partial products -/

/-- **Each `partProd` entry is `ContDiff`** in the parameter, given each layer entry is. Induction on
`k`, peeling the last factor with the banked entrywise matrix-mult `ContDiff`
(`SchurChartC2.contDiff_matrix_mul_entry`). The core of the chart's smoothness: `schurChartRawGen`'s
output blocks are `+`/`∗`/`⁻¹` combinations of `partProd` entries. -/
theorem contDiff_partProd_entry {𝕏 : Type*} [NormedAddCommGroup 𝕏] [NormedSpace ℝ 𝕏]
    {r₀ : ℕ} {n : ℕ → ℕ}
    (C : 𝕏 → (s : ℕ) → Matrix (Fin r₀ ⊕ Fin (n s)) (Fin r₀ ⊕ Fin (n (s + 1))) ℝ)
    (hC : ∀ s i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => C x s i j)) :
    ∀ (k : ℕ) (i j), ContDiff ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k) i j) := by
  intro k
  induction k with
  | zero => intro i j; simp only [partProd]; exact contDiff_const
  | succ k ih =>
      intro i j
      change ContDiff ℝ (⊤ : ℕ∞) (fun x => (partProd (C x) k * C x k) i j)
      exact SchurChartC2.contDiff_matrix_mul_entry (fun a b => ih a b) (fun a b => hC k a b) i j

end DLNFibre.DLN.RLCT
