/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Module.SpanRankOperations
import DLNFibre.Core.Dimension.Smooth

/-!
# `Dimension.Regular` — smooth point ⟹ regular local ring (entry-2 capstone)

For `A` a finite-type algebra over a **perfect** field `k` and `m` a maximal ideal at which `A` is
smooth, the local ring `R = Localization.AtPrime m` is a regular local ring
(`smooth_point_isRegularLocalRing`, `@[stacks 00TV]` — the smooth ⟹ regular direction). This is the
entry-2 capstone of the affine dimension stack: it sits on the non-circular local Krull-dimension
bridge `ringKrullDim_localizationAtPrime_eq_of_isSmoothAt` (`Core.Dimension.Smooth`), so the
regularity is *derived*, not assumed.

## The cotangent comparison

The local Krull dimension `dim R = n` is supplied by the dimension bridge (the
étale-over-affine-space route, **not** the cotangent/tangent identity — this is what keeps the
capstone non-circular). The cotangent space is then squeezed against it:

* the conormal map `m/m² → κ(m) ⊗_R Ω[R⁄k]` is `KaehlerDifferential.kerCotangentToTensor k R κ` (its
  source `(ker (R → κ)).Cotangent` is `(maximalIdeal R).Cotangent = CotangentSpace R`);
* it is **injective** because `R` is formally smooth over `k` (this *is* `IsSmoothAt`) and the
  residue field `κ` is formally smooth over `k` (perfect base field, via
  `Algebra.FormallySmooth.of_perfectField`), so `Algebra.H1Cotangent k κ` is subsingleton
  (`FormallySmooth.kerCotangentToTensor_injective_iff`);
* hence `finrank κ (m/m²) ≤ finrank κ (κ ⊗_R Ω[R⁄k]) = finrank R Ω[R⁄k] = n`, with `Ω[R⁄k]` free of
  rank `n` (the localization of the standard-smooth chart's free `Ω[S⁄k]`, transported by
  `Module.finrank_of_isLocalizedModule_of_free`);
* combined with `dim R = n` (the bridge) and the universal Krull bound `dim ≤ spanFinrank =
  finrank cotangent`, equality holds and `R` is regular
  (`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`).

## Hypotheses

The base field needs only **`[PerfectField k]`** — algebraic closedness is **not** used. The single
field-theoretic input is the residue field's formal smoothness over `k`
(`Algebra.FormallySmooth.of_perfectField`, which needs `[PerfectField k]` + essential finite type),
not the residue-field-is-`k` form of the Nullstellensatz; every other step is pure
commutative/local-ring algebra. `ℝ` (and any field of characteristic zero) qualifies, since
`CharZero ⟹ PerfectField`. The smoothness *hypothesis* `[IsSmoothAt k m]` is consumed, not produced,
so the smooth-locus density (`dense_smoothLocus_of_perfectField`, used by callers to *establish*
smoothness) never enters this chain.

This file mirrors the eventual Mathlib home `Mathlib.RingTheory.Smooth.Regular` / the regular-local-
ring namespace `Mathlib.RingTheory.RegularLocalRing.*`. It builds on entry 1–E1
(`Core.Dimension.Smooth`, the local-dimension bridge) as a black box.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open Algebra IsLocalRing TensorProduct

namespace DLNFibre.Core.Dimension

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-! ### Injectivity transport for cotangent spaces of equal ideals -/

/-- Injectivity of a conormal map transports along an equality of the defining ideal: if `I = J`
then a `J.Cotangent`-domain map cast from an injective `I.Cotangent`-domain map stays injective. -/
theorem injective_cotangent_cast {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J)
    {X : Type*} [AddCommGroup X] [Module R X]
    (f : I.Cotangent →ₗ[R] X) (hf : Function.Injective f) :
    Function.Injective (h ▸ f : J.Cotangent →ₗ[R] X) := by
  subst h; exact hf

/-! ### The local relative-dimension rank at a smooth point -/

/-- On the standard-smooth chart `S = A[1/f]`, `Ω[S⁄k]` is free of finite rank equal to the relative
dimension `n` (read off from `Module.rank Ω = n`). -/
theorem finrank_kaehler_chart_eq {S : Type*} [CommRing S] [Algebra k S] [Nontrivial S]
    [Algebra.FiniteType k S] {n : ℕ} [IsStandardSmoothOfRelativeDimension n k S]
    (hrank : Module.rank S (Ω[S⁄k]) = (n : Cardinal)) :
    Module.finrank S (Ω[S⁄k]) = n := by
  haveI : EssFiniteType k S := EssFiniteType.of_finiteType k S
  haveI : Module.Finite S (Ω[S⁄k]) := KaehlerDifferential.finite k S
  rw [Module.finrank, hrank]; simp

/-! ### The cotangent comparison -/

/-- At a smooth closed point of a finite-type algebra over a perfect
field, the cotangent space `m/m²` has `κ(m)`-dimension at most the local relative dimension `n`: the
conormal map `m/m² → κ(m) ⊗ Ω[R⁄k]` is injective (formal smoothness of `R` and of `κ(m)`), and the
target has `κ(m)`-dimension `n` (base change of the rank-`n` free module `Ω[R⁄k]`). -/
theorem finrank_cotangentSpace_le_of_isSmoothAt [PerfectField k]
    (m : Ideal A) [hm : m.IsMaximal] [IsSmoothAt k m] {n : ℕ}
    (hΩ : Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n) :
    Module.finrank (ResidueField (Localization.AtPrime m))
      (CotangentSpace (Localization.AtPrime m)) ≤ n := by
  set R := Localization.AtPrime m with hR
  haveI : m.IsPrime := hm.isPrime
  haveI : Algebra.FormallySmooth k R := ‹IsSmoothAt k m›
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : Module.Finite R (Ω[R⁄k]) := by
    haveI : EssFiniteType k R := by
      haveI : EssFiniteType A R := .of_isLocalization _ m.primeCompl
      exact .comp _ A _
    exact KaehlerDifferential.finite k R
  -- `Ω[R⁄k]` is free (projective over a local ring): smoothness gives projectivity.
  haveI : Module.Projective R (Ω[R⁄k]) := FormallySmooth.projective_kaehlerDifferential
  haveI : Module.Free R (Ω[R⁄k]) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Finite (ResidueField R) ((ResidueField R) ⊗[R] Ω[R⁄k]) :=
    Module.Finite.base_change R (ResidueField R) (Ω[R⁄k])
  -- residue field of `R` is formally smooth over `k` (perfect base field, ess. finite type)
  haveI : EssFiniteType k (ResidueField R) := by
    haveI : EssFiniteType R (ResidueField R) := inferInstance
    exact .comp _ R _
  haveI : Algebra.FormallySmooth k (ResidueField R) := inferInstance
  -- the conormal map `m/m² → κ ⊗ Ω` is injective
  have hsurj : Function.Surjective (algebraMap R (ResidueField R)) := by
    rw [ResidueField.algebraMap_eq]; exact residue_surjective
  have hker : RingHom.ker (algebraMap R (ResidueField R)) = maximalIdeal R := by
    rw [ResidueField.algebraMap_eq]; exact ker_residue
  have hinj : Function.Injective
      (KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)) := by
    rw [Algebra.FormallySmooth.kerCotangentToTensor_injective_iff
        (R := k) (P := R) (A := ResidueField R) hsurj]
    exact Algebra.FormallySmooth.subsingleton_h1Cotangent
  -- transport the injective conormal map to domain `(maximalIdeal R).Cotangent = CotangentSpace R`
  let g : (maximalIdeal R).Cotangent →ₗ[R] (ResidueField R) ⊗[R] Ω[R⁄k] :=
    hker ▸ KaehlerDifferential.kerCotangentToTensor k R (ResidueField R)
  have hginj : Function.Injective g := injective_cotangent_cast hker _ hinj
  -- read the `κ`-dimension bound from the injection; the target has `κ`-dimension `n`
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := g.extendScalarsOfSurjective hsurj) hginj
  have htgt : Module.finrank (ResidueField R) ((ResidueField R) ⊗[R] Ω[R⁄k]) = n :=
    (Module.finrank_baseChange).trans hΩ
  rw [htgt] at hle
  exact hle

/-! ### The Kähler rank transport from the chart to the local ring -/

/-- The local relative dimension at a smooth point: `Ω[Localization.AtPrime m⁄k]` is free of rank
`n`, the rank of the standard-smooth chart `Ω[A[1/f]⁄k]`, transported along `A[1/f] → A_m`. -/
theorem finrank_kaehler_localizationAtPrime_eq
    (m : Ideal A) [hm : m.IsMaximal] {n : ℕ} {f : A} (hf : f ∉ m)
    [Nontrivial (Localization.Away f)]
    [IsStandardSmoothOfRelativeDimension n k (Localization.Away f)]
    (hrank : Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal)) :
    Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n := by
  haveI hp : m.IsPrime := hm.isPrime
  haveI : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  haveI : Algebra.FiniteType k (Localization.Away f) :=
    Algebra.FiniteType.trans (R := k) (S := A) (A := Localization.Away f) inferInstance
      inferInstance
  haveI : IsStandardSmooth k (Localization.Away f) :=
    IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n)
  haveI : Module.Free (Localization.Away f) (Ω[Localization.Away f⁄k]) :=
    IsStandardSmooth.free_kaehlerDifferential
  have hle : Submonoid.powers f ≤ m.primeCompl := by
    intro x hx; obtain ⟨j, rfl⟩ := hx; exact fun h => hf (hp.mem_of_pow_mem j h)
  letI : Algebra (Localization.Away f) (Localization.AtPrime m) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization.Away f) (Localization.AtPrime m)
      (Submonoid.powers f) m.primeCompl hle
  haveI : IsScalarTower A (Localization.Away f) (Localization.AtPrime m) :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _
      (Submonoid.powers f) m.primeCompl hle
  haveI : IsLocalization (m.primeCompl.map (algebraMap A (Localization.Away f)))
      (Localization.AtPrime m) :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away f) (Localization.AtPrime m)
      (Submonoid.powers f) m.primeCompl hle
  haveI : IsScalarTower k (Localization.Away f) (Localization.AtPrime m) := by
    apply IsScalarTower.of_algebraMap_eq'
    rw [IsScalarTower.algebraMap_eq k A (Localization.Away f),
      IsScalarTower.algebraMap_eq k A (Localization.AtPrime m), ← RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A (Localization.Away f) (Localization.AtPrime m)]
  rw [Module.finrank_of_isLocalizedModule_of_free (Localization.AtPrime m)
    (m.primeCompl.map (algebraMap A (Localization.Away f)))
    (KaehlerDifferential.map k k (Localization.Away f) (Localization.AtPrime m))]
  exact finrank_kaehler_chart_eq hrank

/-! ### Smooth point ⟹ regular local ring -/

/-- **Smooth point ⟹ regular local ring** (`@[stacks 00TV]`, the smooth ⟹ regular direction). For
`A` finite type over a perfect field `k` and `m` maximal at which `A` is smooth,
`Localization.AtPrime m` is a regular local ring. The local Krull dimension is supplied by the
non-circular dimension bridge (`Core.Dimension.Smooth`), and the cotangent space is squeezed against
it via the conormal sequence (residue-field formal smoothness over the perfect base field). -/
@[stacks 00TV "the smooth ⟹ regular direction (perfect base field gives separable residue fields)"]
theorem smooth_point_isRegularLocalRing [PerfectField k]
    (m : Ideal A) [hm : m.IsMaximal] [IsSmoothAt k m] :
    IsRegularLocalRing (Localization.AtPrime m) := by
  haveI : m.IsPrime := hm.isPrime
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  haveI : IsNoetherianRing (Localization.AtPrime m) :=
    IsLocalization.isNoetherianRing m.primeCompl (Localization.AtPrime m) inferInstance
  obtain ⟨n, f, hf, hss, hrank, hdim⟩ := ringKrullDim_localizationAtPrime_eq_of_isSmoothAt
    (k := k) (A := A) m
  haveI : IsStandardSmoothOfRelativeDimension n k (Localization.Away f) := hss
  -- the chart is nontrivial: `m` survives in `A[1/f]` (it is maximal there since `f ∉ m`).
  haveI : (m.map (algebraMap A (Localization.Away f))).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint (S := Localization.Away f) f m hm hf
  haveI : Nontrivial (Localization.Away f) :=
    nontrivial_of_ne (0 : Localization.Away f) 1 fun h ↦
      (‹(m.map (algebraMap A (Localization.Away f))).IsMaximal›).ne_top
        (Ideal.eq_top_of_isUnit_mem _ (h ▸ (m.map (algebraMap A (Localization.Away f))).zero_mem)
          isUnit_one)
  have hΩ : Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n :=
    finrank_kaehler_localizationAtPrime_eq m hf hrank
  have hcot : Module.finrank (ResidueField (Localization.AtPrime m))
      (CotangentSpace (Localization.AtPrime m)) ≤ n :=
    finrank_cotangentSpace_le_of_isSmoothAt m hΩ
  -- regularity from `spanFinrank ≤ dim`: `spanFinrank = finrank cotangent ≤ n = ringKrullDim`.
  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le (Localization.AtPrime m) ?_
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hdim]
  exact_mod_cast hcot

/-- The companion equality: at a smooth closed point, `finrank κ(m) (m/m²)` equals the local
relative dimension `n = ringKrullDim (AtPrime m)`. -/
theorem finrank_cotangentSpace_eq_of_isSmoothAt [PerfectField k]
    (m : Ideal A) [m.IsMaximal] [IsSmoothAt k m] {n : ℕ}
    (hdim : ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞)) :
    Module.finrank (ResidueField (Localization.AtPrime m))
      (CotangentSpace (Localization.AtPrime m)) = n := by
  haveI hreg := smooth_point_isRegularLocalRing (k := k) (A := A) m
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime m)).1 hreg
  rw [hdim] at h
  exact_mod_cast h

/-! ### Non-vacuity witness -/

/-- The capstone fires concretely: the affine line `A = MvPolynomial (Fin 1) ℚ` is finite type over
the perfect field `ℚ` and smooth at every maximal ideal `m` (its smooth locus is everything), so
`Localization.AtPrime m` is a regular local ring. This exhibits the full antecedent bundle
`[PerfectField k] [IsSmoothAt k m] [FiniteType k A]` satisfied on a concrete nonzero target. -/
example (m : Ideal (MvPolynomial (Fin 1) ℚ)) [hm : m.IsMaximal] :
    IsRegularLocalRing (Localization.AtPrime m) := by
  haveI : m.IsPrime := hm.isPrime
  haveI : IsSmoothAt ℚ m := by
    have h : smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) = Set.univ := smoothLocus_eq_univ
    have : (⟨m, ‹_›⟩ : PrimeSpectrum _) ∈ smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) := by
      rw [h]; trivial
    exact this
  exact smooth_point_isRegularLocalRing (k := ℚ) (A := MvPolynomial (Fin 1) ℚ) m

end DLNFibre.Core.Dimension
