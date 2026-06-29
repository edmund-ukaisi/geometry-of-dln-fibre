import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Basic

/-!
# Dimension data of primes in a polynomial ring over a field (network-free engine)

The L5.5–L5.7 layer of the dimension-formula ladder, built on the integral-extension
dimension-invariance headline `ringKrullDim_eq_of_integral_injective` (L5.4) and the polynomial
dimension `ringKrullDim_mvPolynomial_fin_field` (L5.0).

For `R = MvPolynomial (Fin n) k` (`k` any field — `IsAlgClosed` is *not* needed for these pure
dimension facts) and a prime `p`:

* **L5.5** `ringKrullDim_quotient_eq_noetherRank` — `dim (R ⧸ p)` equals the Noether-normalization
  rank `s` of `R ⧸ p` (the number of algebraically-independent generators of the polynomial subring
  `k[y₁..y_s]` over which `R ⧸ p` is integral). Proved from Noether normalization
  (`exists_integral_inj_algHom_of_quotient`) + L5.4 + L5.0.

* **L5.7 (`≤` direction)** `height_add_coheight_le` — `height p + coheight p ≤ n`, equivalently
  `Ideal.primeHeight p + dim (R ⧸ p) ≤ n`. Chain concatenation, via
  `Order.krullDim_eq_iSup_height_add_coheight_of_nonempty` and the polynomial dimension `= n`.

* **The polynomial-tower additive brick** `height_eq_height_under_add_height_map_quotient` — for the
  *one-variable* extension `A → A[X]` (`A` Noetherian, flat hence going-down) and a prime `P` of
  `A[X]`, `height P = height (P.under A) + height (P / (P.under A)·A[X])`. This is the load-bearing
  additive half of the catenary content (the `≥` direction), proved unconditionally from the flat
  going-down instance and `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`.

**The full equality is closed downstream.** This module proves only the `≤` half
(`primeHeight_add_ringKrullDim_quotient_le`). The catenary `≥` direction `height p ≥ n − dim(R/p)`
and the full headline equality `height p + dim (R ⧸ p) = n` are closed in
`Core.NoetherMonicPositioning` (`height_add_ringKrullDim_quotient_eq`), which imports this module
and reuses its additive tower brick above. Its standard proof inducts on `n`, peeling one variable
via that brick after a *monic-coordinate-positioning* step — a `k`-algebra coordinate change making
a nonzero element of `p` monic in the top variable, so `(A[X] ⧸ P)` is integral over `(A ⧸ q)` and
the quotient dimension is preserved. That positioning is Mathlib's Noether-normalization `T`
argument, `private` in `RingTheory.NoetherNormalization`; `Core.NoetherMonicPositioning` re-derives
the one public consequence it needs (`exists_algEquiv_finSuccEquiv_leadingCoeff_isUnit`), over any
field.
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

/-! ### L5.7 (`≤` direction) — `height p + coheight p ≤ n` -/

/-- **L5.7, easy half.** For a prime `p` of `R = k[x₁,…,xₙ]`, the height plus the coheight of `p`
is at most `n`: a chain below `p` spliced with a chain above `p` is a chain in `Spec R`, whose
dimension is `n`. (Order level, on the spectrum point.) -/
theorem height_add_coheight_le
    (k : Type*) [Field k] (n : ℕ) (p : PrimeSpectrum (MvPolynomial (Fin n) k)) :
    (Order.height p : ℕ∞) + Order.coheight p ≤ (n : ℕ∞) := by
  have hk : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k)) = (n : WithBot ℕ∞) :=
    ringKrullDim_mvPolynomial_fin_field k n
  have hsup : Order.krullDim (PrimeSpectrum (MvPolynomial (Fin n) k))
      = ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
          Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) :=
    Order.krullDim_eq_iSup_height_add_coheight_of_nonempty
  have hmem : (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a :=
    le_iSup (fun a ↦ Order.height a + Order.coheight a) p
  have hcoe : ((⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k),
        Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) = (n : WithBot ℕ∞) :=
    hsup ▸ hk
  calc (Order.height p + Order.coheight p : ℕ∞)
      ≤ ⨆ a : PrimeSpectrum (MvPolynomial (Fin n) k), Order.height a + Order.coheight a := hmem
    _ = (n : ℕ∞) := by exact_mod_cast hcoe

/-- **L5.7, easy half (ideal form).** For a prime `p` of `R = k[x₁,…,xₙ]`,
`Ideal.primeHeight p + dim (R ⧸ p) ≤ n`. -/
theorem primeHeight_add_ringKrullDim_quotient_le
    (k : Type*) [Field k] (n : ℕ) (p : Ideal (MvPolynomial (Fin n) k)) [p.IsPrime] :
    (Ideal.primeHeight p : WithBot ℕ∞) + ringKrullDim ((MvPolynomial (Fin n) k) ⧸ p)
      ≤ (n : WithBot ℕ∞) := by
  rw [ringKrullDim_quotient_eq_coheight ⟨p, ‹_›⟩]
  have h := height_add_coheight_le k n ⟨p, ‹_›⟩
  rw [Ideal.primeHeight]
  exact_mod_cast h

/-! ### The polynomial-tower additive brick (the `≥`/catenary additive half) -/

/-- **Additive height law on the one-variable tower.** For `A` Noetherian and a prime `P` of `A[X]`
lying over `q = P.under A`, `height P = height q + height (image of P in (A ⧸ q)[X])`. The
extension `A → A[X]` is free hence flat, so it satisfies going-down
(`Algebra.HasGoingDown.of_flat`), and the equality is
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown`. This is the load-bearing additive half of
the catenary content for polynomial rings. -/
theorem height_eq_height_under_add_height_map_quotient
    {A : Type*} [CommRing A] [IsNoetherianRing A]
    (P : Ideal (Polynomial A)) [P.IsPrime] :
    P.height = (P.under A).height +
      (P.map (Ideal.Quotient.mk ((P.under A).map (algebraMap A (Polynomial A))))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (P.under A) P

/-! ### Non-vacuity witnesses -/

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

/-- Witness that the additive tower law is non-vacuous: `ℤ[X]` is Noetherian, the law applies to its
prime `(X)`. -/
example : (Ideal.span {Polynomial.X} : Ideal (Polynomial ℤ)).IsPrime := by
  rw [Ideal.span_singleton_prime Polynomial.X_ne_zero]; exact Polynomial.prime_X

end DLNFibre.Core
