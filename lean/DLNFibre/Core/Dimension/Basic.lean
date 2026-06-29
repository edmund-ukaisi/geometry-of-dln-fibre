import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Basic Krull-dimension facts for the dimension stack

Two general commutative-algebra facts used throughout the affine dimension stack, kept apart from
the integral-extension content (`DLNFibre.Core.Dimension.Integral`):

* **Polynomial ring over a field** — `dim k[x₁,…,xₙ] = n`
  (`ringKrullDim_mvPolynomial_field`, and its `Fin n` specialisation), a field-specialisation of
  Mathlib's `MvPolynomial.ringKrullDim_of_isNoetherianRing`.
* **Quotient / coheight** — `dim (R ⧸ p) = coheight p` for a prime `p`
  (`ringKrullDim_quotient_eq_coheight`), via the order isomorphism `Spec (R ⧸ p) ≃o Set.Ici p`.

These mirror the eventual Mathlib homes
`Mathlib.RingTheory.KrullDimension.{Polynomial,Field,Basic}`. All statements are at the natural
generality (any field `k`, any commutative ring `R`).
-/

open Order PrimeSpectrum

namespace DLNFibre.Core.Dimension

variable {R : Type*}

/-! ### Polynomial ring over a field -/

/-- The Krull dimension of `k[xᵢ]ᵢ` over a field `k` is the number of variables. -/
theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (ι : Type*) [Finite ι] :
    ringKrullDim (MvPolynomial ι k) = Nat.card ι := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k, zero_add]

/-- Specialisation of `ringKrullDim_mvPolynomial_field` to `Fin n`: `dim k[x₁,…,xₙ] = n`. -/
theorem ringKrullDim_mvPolynomial_fin_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [ringKrullDim_mvPolynomial_field k (Fin n), Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### Quotient and coheight -/

/-- For a prime `p`, the closed subscheme `Spec (R ⧸ p)` is order-isomorphic to `Set.Ici p`: the
primes of `R ⧸ p` correspond to the primes of `R` containing `p`. -/
noncomputable def primeSpectrumQuotientOrderIsoIci [CommRing R] (p : PrimeSpectrum R) :
    PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p :=
  (p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus).trans
    (OrderIso.setCongr _ _ (by
      ext x
      rw [Set.mem_Ici, mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]
      rfl))

/-- The Krull dimension of `R ⧸ p` equals the coheight of `p` in `Spec R` (the length of the longest
chain of primes above `p`). -/
theorem ringKrullDim_quotient_eq_coheight [CommRing R] (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
    ← coheight_eq_krullDim_Ici]

/-- Non-vacuity witness for `ringKrullDim_mvPolynomial_fin_field`: `dim ℚ[x] = 1`, a nonzero finite
value. -/
example : ringKrullDim (MvPolynomial (Fin 1) ℚ) = 1 := by
  rw [ringKrullDim_mvPolynomial_fin_field ℚ 1, Nat.cast_one]

end DLNFibre.Core.Dimension
