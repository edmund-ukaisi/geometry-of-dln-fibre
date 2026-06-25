import DLNFibre.Core.AffineNoetherRank
import DLNFibre.Core.IntegralDimension
import DLNFibre.Core.LocalizationKrullDim
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Localization.Integral

/-!
# `DLNFibre.Core.AffineLocalizationNoDrop` — localization preserves dim for an affine domain

The one genuinely-new sub-lemma shared by the route-(c) step-4 (source) and step-5 (poly-extension)
no-drops: inverting a **nonzero** element of a finitely-generated `k`-domain `D` does not change the
Krull dimension.

> `ringKrullDim (Localization.Away g D) = ringKrullDim D`  for `D` an f.g. `k`-domain, `g ≠ 0`.

Route (validated update-7): `dim = trdeg` for affine domains (`ringKrullDim_eq_trdeg_of_fg_domain`,
via Noether normalization + `trdeg_eq_of_integral_injective`), and `trdeg` is invariant under
localization because `D` and `D[1/g]` share the fraction field `Frac D` (both are algebraic over the
fraction field's base, so `trdeg_add_eq` collapses the relative degree to `0`). Char-free.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra

universe u

variable {k : Type u} [Field k]

/-! ## `dim = trdeg` for a finitely-generated affine domain -/

/-- **`dim = trdeg` for an f.g. affine domain.** For a finitely-generated `k`-domain `A`,
`ringKrullDim A = (Algebra.trdeg k A).toNat`. Noether-normalize to an integral injective
`g : k[Fin s] →ₐ[k] A`; then `ringKrullDim A = s` (`ringKrullDim_eq_of_integral_injective` +
`ringKrullDim_mvPolynomial_fin_field`) and `trdeg k A = s` (`trdeg_eq_of_integral_injective`). -/
theorem ringKrullDim_eq_trdeg_of_fg_domain (A : Type u) [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] :
    ringKrullDim A = ((Algebra.trdeg k A).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg_inj, hg_int⟩ := exists_integral_inj_algHom_of_fg k A
  have hdim : ringKrullDim A = (s : WithBot ℕ∞) := by
    rw [ringKrullDim_eq_of_integral_injective (f := g.toRingHom) hg_int hg_inj,
      ringKrullDim_mvPolynomial_fin_field]
  have htr : Algebra.trdeg k A = (s : Cardinal) :=
    trdeg_eq_of_integral_injective g hg_inj hg_int
  rw [hdim, htr, Cardinal.toNat_natCast]

/-! ## trdeg is invariant under localization (sandwiched in the fraction field) -/

/-- **`trdeg k S = trdeg k D` for a localization of a domain at nonzero elements.** For a `k`-domain
`D` and a `k`-algebra localization `S = M⁻¹D` at `M ≤ D∖0` (so the structure map `D → S` makes `S`
sit between `D` and `Frac D`), the transcendence degrees over `k` agree. `S` is algebraic over `D`
(`S ↪ Frac D`, algebraic over `D`; `IsAlgebraic.tower_bot_of_injective`), so `trdeg D S = 0` and the
tower additivity `trdeg_add_eq` over `k ⊆ D ⊆ S` collapses to `trdeg k D`. -/
theorem trdeg_localization_eq (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
    (M : Submonoid D) (hM : M ≤ nonZeroDivisors D)
    (S : Type u) [CommRing S] [Algebra k S] [Algebra D S] [IsScalarTower k D S]
    [IsLocalization M S] :
    Algebra.trdeg k S = Algebra.trdeg k D := by
  haveI : IsDomain S := IsLocalization.isDomain_of_le_nonZeroDivisors S hM
  -- the canonical algebra `S → Frac D` and the scalar tower `D → S → Frac D`
  letI : Algebra S (FractionRing D) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe S (FractionRing D) M (nonZeroDivisors D) hM
  haveI : IsScalarTower D S (FractionRing D) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le S (FractionRing D) M
      (nonZeroDivisors D) hM
  -- `Frac D` is a fraction ring of `S` too, so `S ↪ Frac D` is injective.
  haveI : IsFractionRing S (FractionRing D) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (M := M) S (FractionRing D)
  -- `S` is algebraic over `D`: `S ↪ Frac D`, which is algebraic over `D`.
  haveI : Algebra.IsAlgebraic D (FractionRing D) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := D) (K := FractionRing D)
      (C := FractionRing D)).mpr inferInstance
  haveI : Algebra.IsAlgebraic D S :=
    Algebra.IsAlgebraic.tower_bot_of_injective (R := D) (S := S) (A := FractionRing D)
      (IsFractionRing.injective S (FractionRing D))
  -- tower additivity `k ⊆ D ⊆ S` with the relative degree `trdeg D S = 0`.
  haveI : FaithfulSMul k D := (faithfulSMul_iff_algebraMap_injective k D).2
    (FaithfulSMul.algebraMap_injective k D)
  haveI : FaithfulSMul D S := (faithfulSMul_iff_algebraMap_injective D S).2
    (IsLocalization.injective S hM)
  have h := trdeg_add_eq k D (A := S)
  rw [trdeg_eq_zero (R := D) (A := S), add_zero] at h
  exact h.symm

/-! ## The headline no-drop -/

/-- **Localization at a nonzero element preserves dim, for an f.g. affine domain.** For a
finitely-generated `k`-domain `D` and `0 ≠ g`,
`ringKrullDim (Localization.Away g D) = ringKrullDim D`. `D[1/g]` is again a finite-type `k`-domain
(`Localization.Away` is finite-type; a localization of a domain at a non-zero element is a domain)
sitting between `D` and `Frac D`, so `dim = trdeg` on both and `trdeg` is localization-invariant. -/
theorem ringKrullDim_localizationAway_eq_of_fg_domain (D : Type u) [CommRing D] [IsDomain D]
    [Algebra k D] [Algebra.FiniteType k D] (g : D) (hg : g ≠ 0) :
    ringKrullDim (Localization.Away g) = ringKrullDim D := by
  -- the localizing submonoid `powers g` sits inside the non-zero-divisors of the domain `D`
  have hpow : Submonoid.powers g ≤ nonZeroDivisors D :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hg
  set S := Localization.Away g with hS
  haveI : IsDomain S := IsLocalization.isDomain_localization hpow
  -- both `dim = trdeg`, and the two trdegs agree by localization-invariance
  rw [ringKrullDim_eq_trdeg_of_fg_domain (k := k) S, ringKrullDim_eq_trdeg_of_fg_domain (k := k) D,
    trdeg_localization_eq (k := k) D (Submonoid.powers g) hpow S]

/-! ## The shared abstract no-drop over a (possibly reducible) f.g. `k`-algebra -/

/-- **Inverting an element that avoids a top-dimensional component does not drop the dimension.**
For a finitely-generated `k`-algebra `R` (Noetherian, finite Krull dimension) and `g : R`, if `g`
avoids a *top-dimensional* minimal prime `p₀` of `R` (`ringKrullDim (R ⧸ p₀) = ringKrullDim R` and
`g ∉ p₀`), then `ringKrullDim (Localization.Away g R) = ringKrullDim R`.

The `≤` direction is the always-true `ringKrullDim_localization_le`. For `≥`: the away-localization
`R[1/g] ↠ (R ⧸ p₀)[1/ḡ]` is surjective (`Localization.awayMap` of the quotient, surjective because
the quotient map is), so its target has `≤` dimension; and `R ⧸ p₀` is a f.g. `k`-domain with
`ḡ ≠ 0` (since `g ∉ p₀`), so `dim ((R ⧸ p₀)[1/ḡ]) = dim (R ⧸ p₀) = dim R` by the affine-domain
no-drop. This is the shared lemma feeding route-(c) step-4 (source, `g = detΔ`) and step-5
(poly-extension, `g = detSchurS`); the two differ only in the avoidance witness `p₀`. -/
theorem ringKrullDim_localizationAway_eq_of_avoids_top_minimalPrime (R : Type u) [CommRing R]
    [IsNoetherianRing R] [Algebra k R] [Algebra.FiniteType k R] (g : R) (p₀ : Ideal R)
    (hp₀ : p₀ ∈ minimalPrimes R) (htop : ringKrullDim (R ⧸ p₀) = ringKrullDim R) (hg : g ∉ p₀) :
    ringKrullDim (Localization.Away g) = ringKrullDim R := by
  haveI : p₀.IsPrime := hp₀.1.1
  -- `R ⧸ p₀` is a f.g. `k`-domain
  haveI : IsDomain (R ⧸ p₀) := Ideal.Quotient.isDomain p₀
  haveI : Algebra.FiniteType k (R ⧸ p₀) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k p₀) (Ideal.Quotient.mkₐ_surjective k p₀)
  -- the image `ḡ` of `g` in the domain `R ⧸ p₀` is nonzero (`g ∉ p₀`)
  have hgbar : (Ideal.Quotient.mk p₀) g ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  -- the away-localization map `R[1/g] ↠ (R ⧸ p₀)[1/ḡ]` is surjective (the quotient map is)
  have hsurj : Function.Surjective
      (Localization.awayMap (Ideal.Quotient.mk p₀) g) := by
    rw [Localization.awayMap_surjective_iff]
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨b, 0, by simp⟩
  refine le_antisymm (ringKrullDim_localization_le (Submonoid.powers g) (Localization.Away g)) ?_
  -- `dim R = dim (R⧸p₀) = dim ((R⧸p₀)[1/ḡ]) ≤ dim (R[1/g])`.
  calc ringKrullDim R = ringKrullDim (R ⧸ p₀) := htop.symm
    _ = ringKrullDim (Localization.Away (Ideal.Quotient.mk p₀ g)) :=
        (ringKrullDim_localizationAway_eq_of_fg_domain (k := k) (R ⧸ p₀)
          (Ideal.Quotient.mk p₀ g) hgbar).symm
    _ ≤ ringKrullDim (Localization.Away g) :=
        ringKrullDim_le_of_surjective _ hsurj

end DLNFibre.Core
