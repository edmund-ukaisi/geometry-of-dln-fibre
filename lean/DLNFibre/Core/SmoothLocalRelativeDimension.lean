/-
The dimension bridge: at a closed point where a finite-type algebra over a field is smooth,
the local Krull dimension equals the local relative dimension (the rank of Kähler differentials
on a standard-smooth chart), computed by the étale-over-affine-space route.

For `A` a finite-type `k`-algebra (`k` a field) and `m` a maximal ideal at which `A` is smooth,
there is a basic-open chart `S = A[1/f]` (`f ∉ m`) on which `A` is standard smooth of some relative
dimension `n`, with `Ω[S⁄k]` free of rank `n`, and the local ring `Localization.AtPrime m` has
Krull dimension `n`. The dimension is computed **without** the cotangent/tangent identity (so the
result is available to *prove* smooth ⟹ regular non-circularly):

* the standard-smooth chart `S` is étale over `B = k[x₁,…,xₙ]` (Mathlib's
  `exists_etale_mvPolynomial`); étale preserves height (M1 `height_eq_under_of_etale`);
* the contracted prime `p = q.under B` has `B/p` of dimension `0` (it embeds, finitely, into the
  field `S/q` — Zariski's lemma), so `p.height = n` by the affine-space catenary equality
  (L5 `height_add_ringKrullDim_quotient_eq`);
* heights transport down the localization `A → A[1/f]` (`IsLocalization.height_map_of_disjoint`) and
  `ringKrullDim` of a localization at a prime is that prime's height
  (`IsLocalization.AtPrime.ringKrullDim_eq_height`).

`k` need only be a field — algebraic closedness is not used (the closed-point maximality goes through
Zariski's lemma, not the residue-field-is-`k` form of the Nullstellensatz).
-/
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DLNFibre.Core.FlatQuasiFiniteHeight
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.NoetherMonicPositioning

open Algebra

namespace DLNFibre.Core

open Dimension

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-! ### The relative-dimension rank of a standard-smooth chart -/

/-- On a standard-smooth chart `S`, `Ω[S⁄k]` is free of finite rank, so its `Module.rank` is the
natural number `Module.finrank S Ω[S⁄k]`. -/
theorem rank_kaehler_eq_finrank (S : Type*) [CommRing S] [Algebra k S] [Nontrivial S]
    [IsStandardSmooth k S] :
    Module.rank S (Ω[S⁄k]) = (Module.finrank S (Ω[S⁄k]) : Cardinal) := by
  haveI : EssFiniteType k S := EssFiniteType.of_finiteType k S
  haveI : Module.Finite S (Ω[S⁄k]) := KaehlerDifferential.finite k S
  exact (Module.finrank_eq_rank S (Ω[S⁄k])).symm

/-- A standard-smooth chart is standard smooth of the relative dimension `finrank S Ω[S⁄k]`. -/
theorem isStandardSmoothOfRelativeDimension_finrank (S : Type*) [CommRing S] [Algebra k S]
    [Nontrivial S] [IsStandardSmooth k S] :
    IsStandardSmoothOfRelativeDimension (Module.finrank S (Ω[S⁄k])) k S :=
  (IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth
    (R := k) (S := S) (Module.finrank S (Ω[S⁄k]))).2 (rank_kaehler_eq_finrank S)

/-! ### The closed-point fibre over affine space is zero-dimensional -/

/-- If `g : B = k[x₁,…,xₙ] → S` is étale and `q` is a maximal ideal of `S`, then the contracted
prime `q.comap g` has zero-dimensional quotient: `B/(q.comap g)` embeds finitely (Zariski's lemma)
into the residue field `S/q`, and dimension is invariant under such an integral injective map. -/
theorem ringKrullDim_quotient_comap_etale_eq_zero {n : ℕ} {S : Type*} [CommRing S] [Algebra k S]
    (g : MvPolynomial (Fin n) k →+* S) (hg : g.Etale) (q : Ideal S) [hq : q.IsMaximal] :
    ringKrullDim ((MvPolynomial (Fin n) k) ⧸ q.comap g) = 0 := by
  haveI : q.IsPrime := hq.isPrime
  letI : Field (S ⧸ q) := Ideal.Quotient.field q
  letI := g.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) k) S := RingHom.etale_algebraMap.mp hg
  haveI : Algebra.FiniteType (MvPolynomial (Fin n) k) S := inferInstance
  -- `h = mk q ∘ g : B → S/q` is finite type, hence module-finite (Zariski), hence integral.
  have hgFT : g.FiniteType := RingHom.finiteType_algebraMap.mpr ‹_›
  have hhFT : ((Ideal.Quotient.mk q).comp g).FiniteType :=
    RingHom.FiniteType.comp_surjective (g := Ideal.Quotient.mk q) hgFT Ideal.Quotient.mk_surjective
  letI : Algebra (MvPolynomial (Fin n) k) (S ⧸ q) := ((Ideal.Quotient.mk q).comp g).toAlgebra
  haveI : Algebra.FiniteType (MvPolynomial (Fin n) k) (S ⧸ q) := by
    rw [← RingHom.FiniteType]; exact hhFT
  haveI : Module.Finite (MvPolynomial (Fin n) k) (S ⧸ q) :=
    finite_of_finite_type_of_isJacobsonRing (MvPolynomial (Fin n) k) (S ⧸ q)
  have hint : ((Ideal.Quotient.mk q).comp g).IsIntegral := by
    have : (algebraMap (MvPolynomial (Fin n) k) (S ⧸ q)).IsIntegral :=
      (RingHom.finite_algebraMap.mpr ‹_›).to_isIntegral
    rwa [RingHom.algebraMap_toAlgebra] at this
  -- the induced quotient map `B/(q.comap g) → S/q` is integral injective, `S/q` a field of dim 0.
  have hqmint : (Ideal.quotientMap q g le_rfl).IsIntegral := (isIntegral_quotientMap_iff g).mpr hint
  have hdim : ringKrullDim (S ⧸ q) = ringKrullDim ((MvPolynomial (Fin n) k) ⧸ q.comap g) :=
    ringKrullDim_eq_of_integral_injective hqmint Ideal.quotientMap_injective
  rw [← hdim, ringKrullDim_eq_zero_of_isField (Field.toIsField (S ⧸ q))]

/-- The contracted prime `q.comap g` of a maximal ideal under an étale map `g : k[x₁,…,xₙ] → S` has
height exactly `n`: `B/(q.comap g)` is zero-dimensional, so the affine-space catenary equality
(L5) gives `(q.comap g).height = n`. -/
theorem height_comap_etale_eq {n : ℕ} {S : Type*} [CommRing S] [Algebra k S]
    (g : MvPolynomial (Fin n) k →+* S) (hg : g.Etale) (q : Ideal S) [hq : q.IsMaximal] :
    (q.comap g).height = (n : ℕ∞) := by
  haveI : q.IsPrime := hq.isPrime
  haveI : (q.comap g).IsPrime := Ideal.comap_isPrime g q
  have hL5 := height_add_ringKrullDim_quotient_eq k n (q.comap g)
  rw [ringKrullDim_quotient_comap_etale_eq_zero g hg q, add_zero] at hL5
  exact_mod_cast hL5

/-! ### The dimension bridge -/

/-- **Dimension bridge (étale route, non-circular).** Let `A` be a finite-type algebra over a field
`k`, and `m` a maximal ideal at which `A` is smooth. Then there is a basic-open chart `S = A[1/f]`
(`f ∉ m`) on which `A` is standard smooth of relative dimension `n := finrank S Ω[S⁄k]`, with
`Ω[S⁄k]` free of rank `n`, and the local ring `Localization.AtPrime m` has Krull dimension `n`. The
Krull dimension is computed via the étale-over-affine-space route, *not* via the cotangent/tangent
identity, so this is available to prove smooth ⟹ regular without circularity. -/
theorem ringKrullDim_localizationAtPrime_eq_of_isSmoothAt
    (m : Ideal A) [hm : m.IsMaximal] [IsSmoothAt k m] :
    ∃ (n : ℕ) (f : A), f ∉ m ∧
      IsStandardSmoothOfRelativeDimension n k (Localization.Away f) ∧
      Module.rank (Localization.Away f) (Ω[Localization.Away f⁄k]) = (n : Cardinal) ∧
      ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  haveI : m.IsPrime := hm.isPrime
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  -- Step A: a standard-smooth chart `S = A[1/f]`.
  obtain ⟨f, hf, hss⟩ := IsSmoothAt.exists_notMem_isStandardSmooth k m
  set S := Localization.Away f with hS
  -- `q := m·S` is maximal in `S` (m maximal, f ∉ m), so `S` is nontrivial.
  haveI hqmax : (m.map (algebraMap A S)).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint (S := S) f m hm hf
  set q : Ideal S := m.map (algebraMap A S) with hq
  haveI : q.IsPrime := hqmax.isPrime
  haveI : Nontrivial S :=
    nontrivial_of_ne (0 : S) 1 fun h ↦ hqmax.ne_top (Ideal.eq_top_of_isUnit_mem q (h ▸ q.zero_mem)
      isUnit_one)
  -- Step C: the relative dimension `n := finrank S Ω`, with `rank Ω = n` and the chart standard
  -- smooth of relative dimension `n`.
  set n : ℕ := Module.finrank S (Ω[S⁄k]) with hn
  haveI hssrd : IsStandardSmoothOfRelativeDimension n k S :=
    isStandardSmoothOfRelativeDimension_finrank S
  refine ⟨n, f, hf, hssrd, rank_kaehler_eq_finrank S, ?_⟩
  -- Step D: an étale presentation `g : B = k[x₁,…,xₙ] → S`.
  obtain ⟨g, hg⟩ := IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial n k S
  -- Step E/F: `(q.comap g).height = n`; Step G via M1 `q.height = (q.under B).height`.
  letI := (g : MvPolynomial (Fin n) k →+* S).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) k) S := RingHom.etale_algebraMap.mp hg
  haveI : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  -- `q.under B = q.comap g` (definitionally `g`).
  have hunder : q.under (MvPolynomial (Fin n) k) = q.comap (g : MvPolynomial (Fin n) k →+* S) := by
    rw [Ideal.under_def]; rfl
  -- M1: étale ⟹ `q.height = (q.under B).height`; combine with `(q.comap g).height = n`.
  have hM1 : q.height = (q.under (MvPolynomial (Fin n) k)).height :=
    Ideal.height_eq_under_of_etale q
  have hpheight : (q.comap (g : MvPolynomial (Fin n) k →+* S)).height = (n : ℕ∞) :=
    height_comap_etale_eq (g : MvPolynomial (Fin n) k →+* S) hg q
  have hqheight : q.height = (n : ℕ∞) := by rw [hM1, hunder, hpheight]
  -- Step B: transport the height down `A → S`, then read `ringKrullDim (AtPrime m) = m.height`.
  have hqm : q.height = m.height :=
    IsLocalization.height_map_of_disjoint (Submonoid.powers f) m
      ((Ideal.disjoint_powers_iff_notMem f ‹m.IsPrime›.isRadical).2 hf)
  have hmheight : m.height = (n : ℕ∞) := by rw [← hqm, hqheight]
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m), hmheight]
  norm_cast

/-! ### Non-vacuity witnesses -/

/-- The smooth instance for affine space `MvPolynomial (Fin d) k`: formally smooth and finitely
presented over any commutative ring. -/
instance smooth_mvPolynomial (R : Type*) [CommRing R] (d : ℕ) :
    Algebra.Smooth R (MvPolynomial (Fin d) R) where
  formallySmooth := inferInstance
  finitePresentation := inferInstance

/-- The hypothesis bundle of the dimension bridge is satisfiable: affine space
`A = MvPolynomial (Fin 1) ℚ` is finite type over `ℚ`, has a maximal ideal `m`, and is smooth at it
(its smooth locus is everything). -/
example : ∃ (m : Ideal (MvPolynomial (Fin 1) ℚ)), ∃ (_ : m.IsMaximal),
    IsSmoothAt ℚ m := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (MvPolynomial (Fin 1) ℚ)
  haveI := hm
  haveI : m.IsPrime := hm.isPrime
  refine ⟨m, hm, ?_⟩
  have h : smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) = Set.univ := smoothLocus_eq_univ
  have : (⟨m, ‹_›⟩ : PrimeSpectrum _) ∈ smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) := by
    rw [h]; trivial
  exact this

/-- The dimension bridge fires concretely: at any maximal ideal `m` of affine space
`A = MvPolynomial (Fin 1) ℚ` (smooth at `m`), there is a chart of relative dimension `n` with
`ringKrullDim (Localization.AtPrime m) = n`. (Here `n = 1`, the dimension of the affine line, though
the witness records only that some such `n` is produced.) -/
example (m : Ideal (MvPolynomial (Fin 1) ℚ)) [m.IsMaximal] :
    ∃ (n : ℕ) (f : MvPolynomial (Fin 1) ℚ), f ∉ m ∧
      IsStandardSmoothOfRelativeDimension n ℚ (Localization.Away f) ∧
      Module.rank (Localization.Away f) (Ω[Localization.Away f⁄ℚ]) = (n : Cardinal) ∧
      ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  haveI : m.IsPrime := ‹m.IsMaximal›.isPrime
  haveI : IsSmoothAt ℚ m := by
    have h : smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) = Set.univ := smoothLocus_eq_univ
    have : (⟨m, ‹_›⟩ : PrimeSpectrum _) ∈ smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) := by
      rw [h]; trivial
    exact this
  exact ringKrullDim_localizationAtPrime_eq_of_isSmoothAt m

end DLNFibre.Core
