import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `DLNFibre.DLN.RLCT.Foundations.S1InverseDerivEquiv` — an invertible chart derivative from a
two-sided inverse germ

The invertibility leg for the L = 2 D1 explicit corner-elimination chart (`genm-phiexpl`): the chart
transfer `rlctAtOn_eq_of_contDiff_chart` needs an INVERTIBLE derivative `f' : E ≃L[ℝ] E` at the
base point, with `HasFDerivAt Φ (f' : E →L E) wstar`. Rather than computing `det (DΦ) ≠ 0`
(the general-width block Jacobian `± det X · det(M11)³`), we exhibit an EXPLICIT smooth two-sided
inverse `Ψ` (rational in the pivot determinants) and read off the invertibility for free:

* `Ψ ∘ Φ =ᶠ id` near `wstar` and the chain rule + derivative uniqueness give `DΨ ∘ DΦ = id`;
* `Φ ∘ Ψ =ᶠ id` near `Φ wstar` gives `DΦ ∘ DΨ = id`;
* so `DΦ` is a `ContinuousLinearEquiv` (`LinearEquiv.ofLinear … |>.toContinuousLinearEquiv`, finite-dim
  making continuity automatic), whose underlying CLM is `DΦ` itself.

Network-free; only the two germ identities (matrix-algebra, from the explicit rational inverse) and the
two named derivatives are the use-site's obligation. This is the leanest route to the `f'` slot
(Codex xhigh, `genm-phiexpl` design consult): the determinant computation is avoided entirely.
-/

open Filter
open scoped Topology

namespace DLNFibre.DLN.RLCT

/-- **An invertible chart derivative from a two-sided inverse germ.** If `Φ, Ψ : E → E` (`E` a
finite-dimensional real normed space) have named derivatives `A` at `wstar` and `Bd` at `Φ wstar`,
and are mutually inverse near the base point (`Ψ ∘ Φ =ᶠ id` near `wstar`, `Φ ∘ Ψ =ᶠ id` near
`Φ wstar`), then `A` underlies a continuous linear equivalence: there is `f' : E ≃L[ℝ] E` with
`HasFDerivAt Φ (f' : E →L[ℝ] E) wstar` — exactly the invertible-derivative slot
`rlctAtOn_eq_of_contDiff_chart` consumes. -/
theorem derivEquiv_of_eventual_inverse {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (Φ Ψ : E → E) (wstar : E) (A Bd : E →L[ℝ] E)
    (hΦ' : HasFDerivAt Φ A wstar) (hΨ' : HasFDerivAt Ψ Bd (Φ wstar))
    (hΨΦ : (Ψ ∘ Φ) =ᶠ[𝓝 wstar] id)
    (hΦΨ : (Φ ∘ Ψ) =ᶠ[𝓝 (Φ wstar)] id) :
    ∃ f' : E ≃L[ℝ] E, HasFDerivAt Φ (f' : E →L[ℝ] E) wstar := by
  -- `Bd ∘ A = id` from `Ψ ∘ Φ =ᶠ id`.
  have hcomp1 : HasFDerivAt (Ψ ∘ Φ) (Bd.comp A) wstar := hΨ'.comp wstar hΦ'
  have hid1 : HasFDerivAt (Ψ ∘ Φ) (ContinuousLinearMap.id ℝ E) wstar :=
    (hasFDerivAt_id (𝕜 := ℝ) wstar).congr_of_eventuallyEq hΨΦ
  have hBA : Bd.comp A = ContinuousLinearMap.id ℝ E := hcomp1.unique hid1
  -- `A ∘ Bd = id` from `Φ ∘ Ψ =ᶠ id`. The chain rule needs `Φ`'s derivative at `Ψ (Φ wstar) = wstar`.
  have hpt : Ψ (Φ wstar) = wstar := hΨΦ.eq_of_nhds
  have hΦ'' : HasFDerivAt Φ A (Ψ (Φ wstar)) := by rw [hpt]; exact hΦ'
  have hcomp2 : HasFDerivAt (Φ ∘ Ψ) (A.comp Bd) (Φ wstar) := hΦ''.comp (Φ wstar) hΨ'
  have hid2 : HasFDerivAt (Φ ∘ Ψ) (ContinuousLinearMap.id ℝ E) (Φ wstar) :=
    (hasFDerivAt_id (𝕜 := ℝ) (Φ wstar)).congr_of_eventuallyEq hΦΨ
  have hAB : A.comp Bd = ContinuousLinearMap.id ℝ E := hcomp2.unique hid2
  -- the linear-map inverse identities.
  have h₁ : A.toLinearMap.comp Bd.toLinearMap = LinearMap.id := by
    ext x; simpa using ContinuousLinearMap.ext_iff.mp hAB x
  have h₂ : Bd.toLinearMap.comp A.toLinearMap = LinearMap.id := by
    ext x; simpa using ContinuousLinearMap.ext_iff.mp hBA x
  -- the coe of `(ofLinear A.toLinearMap …).toContinuousLinearEquiv` to `E →L[ℝ] E` is
  -- definitionally `A` (same underlying linear map; continuity proof is proof-irrelevant).
  refine ⟨(LinearEquiv.ofLinear A.toLinearMap Bd.toLinearMap h₁ h₂).toContinuousLinearEquiv, ?_⟩
  have hcoe : ((LinearEquiv.ofLinear A.toLinearMap Bd.toLinearMap h₁ h₂).toContinuousLinearEquiv
      : E →L[ℝ] E) = A := by
    ext x; rfl
  rw [hcoe]; exact hΦ'

end DLNFibre.DLN.RLCT
