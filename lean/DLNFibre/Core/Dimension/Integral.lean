import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Krull dimension of an integral ring extension

The Krull dimension is invariant under an **integral injective** ring extension
(`ringKrullDim_eq_of_integral_injective`, [Stacks, Tag 00OK]). The two inequalities are established
by the standard going-up route, each at the weakest hypotheses that suffice:

* `dim S ≤ dim R` needs only integrality — the comap on prime spectra is *strictly* monotone for an
  integral extension (`strictMono_comap_of_isIntegral`, the incomparability theorem
  [Stacks, Tag 00GT]), so it cannot collapse a chain.
* `dim R ≤ dim S` needs integrality **and** injectivity — the going-up theorem
  ([Stacks, Tag 00GU]) lifts any prime chain in `R` to a chain of equal length in `S`
  (`exists_ltSeries_comap_last_of_isIntegral`), with injectivity supplying the bottom of the chain
  via lying-over over `⊥`.

The companion transcendence-degree fact `trdeg_eq_of_integral_injective` — an integral injective
`k[Fin s] →ₐ[k] B` into a `k`-domain forces `trdeg k B = s` — also lives here: it is the
"integral ⟹ trdeg" twin of the dimension invariance, and a low-level fact importing only the
Mathlib trdeg + integral API (no Kähler, no orbit machinery), so both the dimension stack
(`Dimension.Localization`) and the orbit specialisation (`AffineNoetherRank`) consume it without
pulling in heavier modules.

This file mirrors the eventual Mathlib home `Mathlib.RingTheory.KrullDimension.Integral`; all
statements are at `RingHom` / `Algebra` generality over commutative rings. No new interface is
assumed — every step is a proved Mathlib lemma.
-/

open Order PrimeSpectrum

namespace DLNFibre.Core.Dimension

universe u

variable {R S A : Type*}

/-- For an integral extension, the comap of the algebra map on prime spectra is **strictly**
monotone: an integral element witnessing one prime's strict containment over another descends to a
strict containment of the contractions. (Equivalently, the incomparability theorem
[Stacks, Tag 00GT] forbids comap from collapsing a strict inclusion.) -/
theorem strictMono_comap_of_isIntegral [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] :
    StrictMono (comap (algebraMap R S)) := by
  intro a b hab
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal] at hab ⊢
  obtain ⟨hle, x, hxb, hxa⟩ := SetLike.lt_iff_le_and_exists.mp hab
  simpa only [comap_asIdeal] using
    Ideal.comap_lt_comap_of_integral_mem_sdiff hle ⟨hxb, hxa⟩ (Algebra.IsIntegral.isIntegral x)

/-- An integral extension does not raise the Krull dimension: `dim S ≤ dim R`. Only integrality is
needed (injectivity is not), via the strict monotonicity of `comap`. This is the
dimension-inequality conjunct of [Stacks, Tag 00OJ] (and one half of the invariance
[Stacks, Tag 00OK]). -/
@[stacks 00OJ "the dimension inequality `dim S ≤ dim R`"]
theorem ringKrullDim_le_of_integral [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) :
    ringKrullDim S ≤ ringKrullDim A := by
  algebraize [f]
  exact krullDim_le_of_strictMono _ strictMono_comap_of_isIntegral

/-- Going-up chain lift ([Stacks, Tag 00GU]): for an **integral injective** extension, every prime
chain in `A` lifts to a prime chain in `S` of the **same length** whose last term contracts back to
the chain's last term. Injectivity is used only to start the lift, lying over `⊥`. -/
@[stacks 00GU "iterated going-up: the chain-lift corollary"]
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

/-- An integral injective extension does not lower the Krull dimension: `dim A ≤ dim S`, via the
going-up chain lift `exists_ltSeries_comap_last_of_isIntegral`. One half of [Stacks, Tag 00OK]. -/
theorem ringKrullDim_ge_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim A ≤ ringKrullDim S := by
  algebraize [f]
  rw [ringKrullDim, ringKrullDim, krullDim, iSup_le_iff]
  intro p
  obtain ⟨q, hlen, _⟩ := exists_ltSeries_comap_last_of_isIntegral (S := S) hinj p
  rw [← hlen]
  exact q.length_le_krullDim

/-- **Krull dimension is invariant under an integral injective ring extension**:
`dim S = dim A` ([Stacks, Tag 00OK]). The headline of the file, assembled from the two going-up
inequalities. -/
@[stacks 00OK]
theorem ringKrullDim_eq_of_integral_injective [CommRing A] [CommRing S] {f : A →+* S}
    (hf : f.IsIntegral) (hinj : Function.Injective f) :
    ringKrullDim S = ringKrullDim A :=
  le_antisymm (ringKrullDim_le_of_integral hf)
    (ringKrullDim_ge_of_integral_injective hf hinj)

/-- Non-vacuity / hypothesis-bundle witness: the identity ring hom is integral and injective, and
the headline recovers `dim R = dim R`. The substantive content — an integral injective extension
that changes the *ring* without changing the dimension — is exercised downstream where Noether
normalization supplies a genuine integral extension `k[x₁,…,x_d] ↪ R`. -/
example (R : Type*) [CommRing R] : ringKrullDim R = ringKrullDim R :=
  ringKrullDim_eq_of_integral_injective
    (RingHom.isIntegral_of_surjective (RingHom.id R) Function.surjective_id)
    Function.injective_id

/-! ## The transcendence-degree twin: integral injective ⟹ `trdeg = s` -/

/-- An integral injective `k`-algebra map from a polynomial ring `k[Fin s]` into a `k`-domain `B`
forces `trdeg k B = s`: `B` is algebraic over the image of `k[Fin s]`, so by tower additivity
`trdeg_add_eq` the degree splits as `trdeg_k k[Fin s] + trdeg_{k[Fin s]} B = s + 0`.

The "integral ⟹ trdeg" twin of `ringKrullDim_eq_of_integral_injective`; together they give
`dim = trdeg` for an affine domain after Noether normalization. Char-free. -/
theorem trdeg_eq_of_integral_injective {k : Type u} [Field k] {s : ℕ} {B : Type u} [CommRing B]
    [IsDomain B] [Algebra k B] (g : MvPolynomial (Fin s) k →ₐ[k] B) (hinj : Function.Injective g)
    (hint : g.IsIntegral) :
    Algebra.trdeg k B = (s : Cardinal) := by
  letI : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  haveI : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective ..).mpr hinj
  haveI : Algebra.IsIntegral (MvPolynomial (Fin s) k) B :=
    (Algebra.isIntegral_def).mpr (fun b ↦ hint b)
  haveI : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B := inferInstance
  have h : Algebra.trdeg k (MvPolynomial (Fin s) k) + Algebra.trdeg (MvPolynomial (Fin s) k) B
      = Algebra.trdeg k B := trdeg_add_eq k (MvPolynomial (Fin s) k)
  rw [MvPolynomial.trdeg_of_isDomain, trdeg_eq_zero, add_zero, Cardinal.mk_fin,
    Cardinal.lift_natCast] at h
  exact h.symm

end DLNFibre.Core.Dimension
