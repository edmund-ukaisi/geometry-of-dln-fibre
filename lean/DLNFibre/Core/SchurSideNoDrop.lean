import DLNFibre.Core.Dimension.Localization
import DLNFibre.Core.RadicalCatenary
import Mathlib.RingTheory.Polynomial.Quotient

/-!
# `DLNFibre.Core.SchurSideNoDrop` — the schur-side no-drop (route-β step-3 obligation hP)

The step-5 / schur-side input to the localized poly-extension wrapper
(`Core.ChartLocalizedPolyDim`): inverting a polynomial `gfib` with a **unit `k`-coefficient** does
not drop the dimension of `P = MvPolynomial ι A` (`A` a possibly-reducible f.g. `k`-algebra). The
avoidance witness is `Ideal.map C q₀` for a top-dimensional prime `q₀` of `A`: it is prime (the
quotient `P ⧸ map C q₀ ≅ MvPolynomial ι (A ⧸ q₀)` is a domain), top-dimensional (the equiv adds
`card ι` to both sides), and `gfib ∉ map C q₀` because `gfib`'s image in the domain
`MvPolynomial ι (A ⧸ q₀)` is the nonzero polynomial obtained by pushing `gfib`'s `k`-coefficients
through the injection `k ↪ A ⧸ q₀`.

This discharges the `hP` hypothesis of `ringKrullDim_eq_of_localized_polyExtensionAlgEquiv` for the
schur side, given a top-dimensional prime of the fibre ring and the unit-`k`-coefficient witness.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Dimension

universe u

variable {k : Type u} [Field k]

/-- **`Ideal.map C q` is prime when `q` is.** For an `MvPolynomial ι A` over a commutative ring `A`
and a prime `q` of `A`, the extension `Ideal.map C q` is prime: the quotient
`MvPolynomial ι A ⧸ map C q ≅ MvPolynomial ι (A ⧸ q)` (`quotientEquivQuotientMvPolynomial`) is a
domain (a polynomial ring over the domain `A ⧸ q`). -/
theorem isPrime_map_C_of_isPrime {ι : Type*} {A : Type u} [CommRing A] (q : Ideal A) [q.IsPrime] :
    (Ideal.map (C : A →+* MvPolynomial ι A) q).IsPrime := by
  haveI : IsDomain (A ⧸ q) := Ideal.Quotient.isDomain q
  haveI : IsDomain (MvPolynomial ι (A ⧸ q)) := inferInstance
  rw [← Ideal.Quotient.isDomain_iff_prime]
  exact (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) q).symm.toRingEquiv.isDomain _

/-- **The schur-side no-drop.** For `P = MvPolynomial ι A` over a finitely-generated `k`-algebra `A`
(`ι` finite, Noetherian), a top-dimensional prime `q₀` of `A`
(`ringKrullDim (A ⧸ q₀) = ringKrullDim A`), and a localizing element
`gfib = map (algebraMap k A) g₀` with `g₀ ≠ 0` a `k`-polynomial, inverting `gfib` does not drop the
dimension:

> `ringKrullDim (Localization.Away gfib) = ringKrullDim (MvPolynomial ι A)`.

The avoidance witness is `p₀ = Ideal.map C q₀`: prime (`isPrime_map_C_of_isPrime`), top-dimensional
(the quotient equiv adds `card ι` to both `A ⧸ q₀` and `A`, so `dim (P ⧸ p₀) = dim (A ⧸ q₀) + card ι
= dim A + card ι = dim P`), and `gfib ∉ p₀` because `gfib`'s image in the domain
`MvPolynomial ι (A ⧸ q₀)` is `map (algebraMap k (A ⧸ q₀)) g₀`, nonzero (the `k`-coefficient
injection `k ↪ A ⧸ q₀` keeps `g₀ ≠ 0`). Discharges the `hP` hypothesis of the route-β wrapper. -/
theorem ringKrullDim_localizationAway_eq_of_schurSide {ι : Type u} [Finite ι] {A : Type u}
    [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    (q₀ : Ideal A) [q₀.IsPrime] (htop : ringKrullDim (A ⧸ q₀) = ringKrullDim A)
    (g₀ : MvPolynomial ι k) (hg₀ : g₀ ≠ 0) :
    ringKrullDim (Localization.Away (MvPolynomial.map (algebraMap k A) g₀))
      = ringKrullDim (MvPolynomial ι A) := by
  set gfib : MvPolynomial ι A := MvPolynomial.map (algebraMap k A) g₀ with hgfib
  set p₀ : Ideal (MvPolynomial ι A) := Ideal.map (C : A →+* _) q₀ with hp₀
  haveI : p₀.IsPrime := isPrime_map_C_of_isPrime q₀
  -- the quotient equiv `MvPolynomial ι (A ⧸ q₀) ≃ₐ[A] (MvPolynomial ι A) ⧸ p₀`
  let e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := ι) (R := A) q₀
  -- (2) top-dimensionality of `p₀`: `dim (P ⧸ p₀) = dim P`.
  have htopP : ringKrullDim (MvPolynomial ι A ⧸ p₀) = ringKrullDim (MvPolynomial ι A) := by
    rw [ringKrullDim_eq_of_ringEquiv e.symm.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, htop,
      MvPolynomial.ringKrullDim_of_isNoetherianRing]
  -- (3) avoidance: `gfib ∉ p₀`. The reduction `map (mk q₀) : P → MvPolynomial ι (A ⧸ q₀)` kills
  -- `p₀ = map C q₀` (each `C a`, `a ∈ q₀`, goes to `C (mk a) = 0`), so `p₀ ≤ ker`; `map (mk q₀)`
  -- sends `gfib = map (algebraMap k A) g₀` to `map (algebraMap k (A ⧸ q₀)) g₀`, nonzero (the
  -- `k`-coefficient injection `k ↪ A ⧸ q₀` keeps `g₀ ≠ 0`). Hence `gfib ∉ p₀`.
  set red : MvPolynomial ι A →+* MvPolynomial ι (A ⧸ q₀) :=
    MvPolynomial.map (Ideal.Quotient.mk q₀) with hred
  have hple : p₀ ≤ RingHom.ker red := by
    rw [hp₀, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, hred, MvPolynomial.map_C,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  have hcomp : (Ideal.Quotient.mk q₀).comp (algebraMap k A) = algebraMap k (A ⧸ q₀) :=
    (IsScalarTower.algebraMap_eq k A (A ⧸ q₀)).symm
  have hredgfib : red gfib = MvPolynomial.map (algebraMap k (A ⧸ q₀)) g₀ := by
    rw [hred, hgfib, MvPolynomial.map_map, hcomp]
  have hredne : red gfib ≠ 0 := by
    rw [hredgfib, Ne, ← map_zero (MvPolynomial.map (algebraMap k (A ⧸ q₀)))]
    exact fun h ↦ hg₀ (MvPolynomial.map_injective _ (algebraMap k (A ⧸ q₀)).injective h)
  have hgmem : gfib ∉ p₀ := fun h ↦ hredne (RingHom.mem_ker.mp (hple h))
  exact ringKrullDim_localizationAway_eq_of_avoids_top_prime (k := k)
    (MvPolynomial ι A) gfib p₀ htopP hgmem

end DLNFibre.Core
