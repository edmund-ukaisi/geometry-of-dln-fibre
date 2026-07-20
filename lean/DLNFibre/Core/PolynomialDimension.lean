import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.NoetherNormalization
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Basic

/-!
# Krull dimension of a polynomial-ring quotient via the Noether-normalization rank

For `R = MvPolynomial (Fin n) k` (`k` any field — `IsAlgClosed` is *not* needed) and a prime `p`:

* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
  rank `s` of `R ⧸ p` (the number of algebraically-independent generators of the polynomial subring
  `k[y₁..y_s]` over which `R ⧸ p` is integral). Proved from Noether normalization
  (`exists_integral_inj_algHom_of_quotient`) + the integral-extension dimension invariance
  `ringKrullDim_eq_of_integral_injective` (`Core.Dimension.Integral`) + the polynomial dimension
  `ringKrullDim_mvPolynomial_fin_field` (`Core.Dimension.Basic`).

This is the Noether-*rank* fact (a dimension-invariance corollary), kept apart from the catenary
content `height p + dim (R ⧸ p) = n` in `Core.Dimension.Catenary`. It is consumed by the
finite-type-domain trdeg bridge (`Core.AffineNoetherRank`).
-/

open Order PrimeSpectrum

namespace DLNFibre.Core

open Dimension

/-! ### L5.5 — `dim (R ⧸ p)` equals the Noether-normalization rank -/

/-- **L5.5.** For a prime `p` of `R = k[x₁,…,xₙ]` (`k` a field), the Krull dimension of `R ⧸ p`
equals the Noether-normalization rank `s ≤ n`: there is an injective integral `k`-algebra map
`k[y₁,…,y_s] →ₐ[k] (R ⧸ p)`, and `dim (R ⧸ p) = s`. -/
theorem ringKrullDim_quotient_eq_noetherRank
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    ∃ s ≤ n, (∃ g : (MvPolynomial (Fin s) k) →ₐ[k] ((MvPolynomial (Fin n) k) ⧸ p),
      Function.Injective g ∧ g.IsIntegral) ∧
      ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p) = (s : WithBot ℕ∞) := by
  obtain ⟨s, hsn, g, hg_inj, hg_int⟩ :=
    exists_integral_inj_algHom_of_quotient p (Ideal.IsPrime.ne_top ‹_›)
  refine ⟨s, hsn, ⟨g, hg_inj, hg_int⟩, ?_⟩
  rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
    ringKrullDim_mvPolynomial_fin_field]

/-! ### Non-vacuity witness -/

/-- Witness for `ringKrullDim_quotient_eq_noetherRank`: for the zero prime of `k[x]` the Noether
rank `s` it produces is `1` (not the degenerate `0`), since `dim (k[x] ⧸ ⊥) = dim k[x] = 1`. -/
example (k : Type*) [Field k] :
    ∃ s : ℕ, (s : WithBot ℕ∞) = (1 : WithBot ℕ∞) ∧
      ringKrullDim ((MvPolynomial (Fin 1) k) ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) k)))
        = (s : WithBot ℕ∞) := by
  obtain ⟨s, _, _, hdim⟩ := ringKrullDim_quotient_eq_noetherRank k 1 ⊥
  refine ⟨s, ?_, hdim⟩
  rw [← hdim, ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _),
    ringKrullDim_mvPolynomial_fin_field, Nat.cast_one]

end DLNFibre.Core
