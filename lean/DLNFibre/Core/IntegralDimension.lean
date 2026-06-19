import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Krull dimension of integral extensions (network-free engine)

General commutative-algebra bedrock for the L5 dimension-formula ladder: the Krull dimension is
invariant under an integral injective ring extension. The route is the integral-extension
(trdeg-light) one — strict-mono `comap` for going-up (`≤` one way) and lying-over surjectivity for
going-up the other way (`≤` the other way) — assembled into the dimension-invariance headline
`ringKrullDim_eq_of_integral_injective`. Two supporting general facts are also recorded:
`MvPolynomial` dimension over a field (`ringKrullDim_mvPolynomial_field`) and the quotient/coheight
identity (`ringKrullDim_quotient_eq_coheight`).

All statements are at `RingHom` / `Algebra` generality (commutative rings); `IsDomain` / `Field`
appear only where genuinely needed. No new cited interfaces — every step is a proved Mathlib lemma.
-/

open Order PrimeSpectrum

namespace DLNFibre.Core

variable {R S A : Type*}

/-! ### L5.0 — dimension of a polynomial ring over a field -/

/-- The Krull dimension of `k[x₁,…,xₙ]` over a field `k` is `n`. -/
theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (ι : Type*) [Finite ι] :
    ringKrullDim (MvPolynomial ι k) = Nat.card ι := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field k, zero_add]

/-- Specialisation of `ringKrullDim_mvPolynomial_field` to `Fin n`: `dim k[x₁,…,xₙ] = n`. -/
theorem ringKrullDim_mvPolynomial_fin_field (k : Type*) [Field k] (n : ℕ) :
    ringKrullDim (MvPolynomial (Fin n) k) = n := by
  rw [ringKrullDim_mvPolynomial_field k (Fin n), Nat.card_eq_fintype_card, Fintype.card_fin]

/-! ### L5.1 — `dim (R ⧸ p) = coheight p` -/

/-- For a prime `p`, the closed subscheme `Spec (R ⧸ p)` is order-isomorphic to `Set.Ici p`. -/
noncomputable def primeSpectrumQuotientOrderIsoIci [CommRing R] (p : PrimeSpectrum R) :
    PrimeSpectrum (R ⧸ p.asIdeal) ≃o Set.Ici p :=
  (p.asIdeal.primeSpectrumQuotientOrderIsoZeroLocus).trans
    (OrderIso.setCongr _ _ (by
      ext x
      rw [Set.mem_Ici, mem_zeroLocus, ← PrimeSpectrum.asIdeal_le_asIdeal]
      rfl))

/-- The Krull dimension of `R ⧸ p` equals the coheight of `p` in `Spec R`. -/
theorem ringKrullDim_quotient_eq_coheight [CommRing R] (p : PrimeSpectrum R) :
    ringKrullDim (R ⧸ p.asIdeal) = (coheight p : WithBot ℕ∞) := by
  rw [ringKrullDim, Order.krullDim_eq_of_orderIso (primeSpectrumQuotientOrderIsoIci p),
    ← coheight_eq_krullDim_Ici]

/-! ### L5.2 / L5.3 — the two inequalities for an integral injective extension -/

/-- For an integral extension, `comap` of the algebra map is strictly monotone on primes. -/
theorem strictMono_comap_of_isIntegral [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    StrictMono (comap (algebraMap R S)) := by
  intro a b hab
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hab ⊢
  obtain ⟨hle, x, hxb, hxa⟩ := SetLike.lt_iff_le_and_exists.mp hab
  simpa only [comap_asIdeal] using
    Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxb, hxa⟩ (Algebra.IsIntegral.isIntegral x)

/-- Integral extension: `dim S ≤ dim A` (going-up via strict-mono `comap`; injectivity unneeded). -/
theorem ringKrullDim_le_of_integral [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim A := by
  algebraize [f]
  exact krullDim_le_of_strictMono _ strictMono_comap_of_isIntegral

/-- Going-up chain lift: an integral extension lifts any prime chain in `A` to a prime chain in `S`
of the same length, with matching last element. -/
theorem exists_ltSeries_comap_last_of_isIntegral [CommRing A] [CommRing S] [Algebra A S]
    [Algebra.IsIntegral A S] (hinj : Function.Injective (algebraMap A S))
    (p : LTSeries (PrimeSpectrum A)) :
    ∃ q : LTSeries (PrimeSpectrum S), q.length = p.length ∧
      comap (algebraMap A S) q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton x =>
    obtain ⟨Q, _, hQ, hcomap⟩ := Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal ⊥
      (by rw [Ideal.comap_bot_of_injective (algebraMap A S) hinj]; exact bot_le)
    refine ⟨RelSeries.singleton _ ⟨Q, hQ⟩, rfl, ?_⟩
    apply PrimeSpectrum.ext
    simpa only [comap_asIdeal] using hcomap
  | snoc p x hx hp =>
    obtain ⟨q, hlen, hlast⟩ := hp
    have hle : (q.last.asIdeal.comap (algebraMap A S)) ≤ x.asIdeal := by
      rw [show q.last.asIdeal.comap (algebraMap A S) = (comap (algebraMap A S) q.last).asIdeal from
        rfl, hlast]
      exact (PrimeSpectrum.asIdeal_lt_asIdeal _ _).mpr hx |>.le
    obtain ⟨Q, hQge, hQ, hcomap⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral x.asIdeal q.last.asIdeal hle
    have hlt : q.last < ⟨Q, hQ⟩ := by
      rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
      refine lt_of_le_of_ne hQge fun heq ↦ ?_
      have : (comap (algebraMap A S) q.last).asIdeal = x.asIdeal := by
        rw [comap_asIdeal, heq]; exact hcomap
      rw [hlast] at this
      exact absurd (PrimeSpectrum.ext this) (ne_of_lt hx)
    refine ⟨q.snoc ⟨Q, hQ⟩ hlt, by simp [hlen], ?_⟩
    apply PrimeSpectrum.ext
    simpa only [RelSeries.last_snoc, comap_asIdeal] using hcomap

/-- Integral injective extension: `dim A ≤ dim S` (going-up chain lift). -/
theorem ringKrullDim_ge_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A ≤ ringKrullDim S := by
  algebraize [f]
  rw [ringKrullDim, ringKrullDim, krullDim, iSup_le_iff]
  intro p
  obtain ⟨q, hlen, _⟩ := exists_ltSeries_comap_last_of_isIntegral (S := S) hinj p
  rw [← hlen]
  exact q.length_le_krullDim

/-! ### L5.4 — the headline: dimension invariance -/

/-- Krull dimension is invariant under an integral injective ring extension. -/
theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim A :=
  le_antisymm (ringKrullDim_le_of_integral hf)
    (ringKrullDim_ge_of_integral_injective hf hinj)

/-! ### Non-vacuity witnesses -/

/-- Witness for `ringKrullDim_mvPolynomial_fin_field`: `dim ℚ[x] = 1` (a nonzero, finite value). -/
example : ringKrullDim (MvPolynomial (Fin 1) ℚ) = 1 := by
  rw [ringKrullDim_mvPolynomial_fin_field ℚ 1, Nat.cast_one]

/-- Witness that the headline's hypothesis bundle is inhabited and its conclusion fires: the
identity ring hom is integral and injective, recovering `dim R = dim R`. (The substantive content —
that an integral injective extension can change the *ring* without changing the dimension — is
exercised downstream where Noether normalization is applied.) -/
example (R : Type*) [CommRing R] : ringKrullDim R = ringKrullDim R :=
  ringKrullDim_eq_of_integral_injective
    (RingHom.isIntegral_of_surjective (RingHom.id R) Function.surjective_id)
    Function.injective_id

end DLNFibre.Core
