import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import DLNFibre.Core.Dimension.Integral
import DLNFibre.Core.Dimension.Catenary

/-!
# `Dimension.Smooth` — étale height-preservation + the smooth-point local-dimension bridge

This file collects the two reusable commutative-algebra facts on the étale route from **smoothness**
to **regular local ring** — the height-preservation brick and the local Krull-dimension bridge —
both at the weakest hypotheses that suffice and **without** the cotangent/tangent identity, so that
the bridge is available to *prove* "smooth ⟹ regular" non-circularly (the smooth ⟹ regular headline
itself lives in `DLNFibre.Core.Dimension.Regular`, the entry-2 capstone).

## Contents

1. **Étale (more generally flat + quasi-finite) preserves height.** For a flat, Noetherian
   `R`-algebra `S` that is `R`-quasi-finite at a prime `Q`, the height of `Q` equals the height of
   the prime `Q.under R` it lies over (`Ideal.height_eq_under_of_flat_quasiFiniteAt`); étale ⟹ flat
   and quasi-finite, so an étale Noetherian `R`-algebra preserves the height of *every* prime
   (`Ideal.height_eq_under_of_etale`). The fibre contributes nothing because quasi-finiteness forces
   `Q` to be minimal in its fibre (`fibre_height_eq_zero_of_quasiFiniteAt`).

2. **The smooth-point local-dimension bridge.** For `A` a finite-type algebra over a field `k` and
   `m` a maximal ideal at which `A` is smooth, the local ring `Localization.AtPrime m` has Krull
   dimension `n := finrank S Ω[S⁄k]` on a basic-open chart `S = A[1/f]`
   (`ringKrullDim_localizationAtPrime_eq_of_isSmoothAt`). The dimension is computed via the
   **étale-over-affine-space** route — the chart `S` is étale over `B = k[x₁,…,xₙ]`, height is
   preserved down to `B` by (1), and the affine-space catenary equality (entry 1,
   `Core.Dimension.Catenary`) reads off `n` from the zero-dimensional closed-point fibre — *not* via
   the cotangent/tangent identity, keeping the result available to prove smooth ⟹ regular without
   circularity.

## Hypotheses

The height-preservation brick is at `RingHom`/`Algebra` generality over Noetherian rings.
The dimension bridge needs only **`[Field k]`** — algebraic closedness is **not** used: the
closed-point maximality goes through Zariski's lemma, not the residue-field-is-`k` form of the
Nullstellensatz. (The `[IsAlgClosed] → [PerfectField]` generalisation is exclusively an entry-2
concern — the smooth ⟹ regular headline's residue-field formal-smoothness step — and never touches
this file, which is already field-general.) `Algebra.QuasiFiniteAt R Q` is Mathlib's finite-fibre-
dimension condition (`κ(p) ⊗ S` finite over `κ(p)`), *weaker* than the Stacks 00PL "finite type +
isolated in its fibre" notion; the two coincide for finite-type `S` and the height brick holds in
this weaker generality.

This file mirrors the eventual Mathlib home `Mathlib.RingTheory.Smooth.Regular` (the regular-local-
ring consequence of smoothness); the standalone étale height-preservation brick would naturally sit
near `Mathlib.RingTheory.Etale.QuasiFinite` / a `Mathlib.RingTheory.Etale.Height`. It builds on
entry 1 — `Core.Dimension.Integral` (integral-extension dimension invariance) and
`Core.Dimension.Catenary` (the polynomial-ring catenary equality) — as black boxes.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

open Algebra

namespace DLNFibre.Core.Dimension

/-! ### Étale (flat + quasi-finite) preserves height -/

section HeightPreservation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The image of `Q` in the fibre `S ⧸ (Q.under R)S` has height `0` when `S` is `R`-quasi-finite
at `Q`: any prime below it pulls back to a prime of `S` with the same contraction to `R`, hence
equal to `Q` by quasi-finiteness. -/
theorem fibre_height_eq_zero_of_quasiFiniteAt (Q : Ideal S) [Q.IsPrime]
    [Algebra.QuasiFiniteAt R Q] :
    (Q.map (Ideal.Quotient.mk ((Q.under R).map (algebraMap R S)))).height = 0 := by
  -- Abbreviations: `pS = (Q.under R) S`, `f = quotient map onto the fibre`.
  set pS : Ideal S := (Q.under R).map (algebraMap R S) with hpS
  set f : S →+* S ⧸ pS := Ideal.Quotient.mk pS with hf
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hkerf : RingHom.ker f = pS := Ideal.mk_ker
  -- `comap f ⊥ = pS` (the kernel of the quotient map), in usable form.
  have hbot : (⊥ : Ideal (S ⧸ pS)).comap f = pS := by
    rw [← RingHom.ker_eq_comap_bot]; exact hkerf
  -- `pS ≤ Q`, since `Q` lies over `Q.under R`.
  have hpSQ : pS ≤ Q := hpS.trans_le Ideal.map_comap_le
  -- `J := Q.map f` is prime and pulls back to `Q`.
  have hJprime : (Q.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (hkerf.trans_le hpSQ)
  have hJcomap : (Q.map f).comap f = Q := by
    rw [Ideal.comap_map_of_surjective f hsurj, hbot, sup_eq_left.mpr hpSQ]
  -- height = primeHeight = 0 ⟺ minimal prime.
  rw [Ideal.height_eq_primeHeight, Ideal.primeHeight_eq_zero_iff]
  refine ⟨⟨hJprime, bot_le⟩, ?_⟩
  -- Minimality: any prime `K ≤ J` equals `J`.
  rintro K ⟨hKprime, -⟩ hKJ
  -- `K' := K.comap f`, with `pS ≤ K' ≤ Q`.
  have hK'prime : (K.comap f).IsPrime := hKprime.comap f
  have hpSK' : pS ≤ K.comap f := (le_of_eq hkerf.symm).trans (Ideal.ker_le_comap f)
  have hK'Q : K.comap f ≤ Q := by rw [← hJcomap]; exact Ideal.comap_mono hKJ
  -- `K'.under R = Q.under R`: both equal `Q.under R`.
  have hunder : (K.comap f).under R = Q.under R := by
    refine le_antisymm (Ideal.comap_mono hK'Q) ?_
    have h1 : Q.under R ≤ pS.comap (algebraMap R S) := hpS.symm ▸ Ideal.le_comap_map
    exact h1.trans (Ideal.comap_mono hpSK')
  -- Quasi-finiteness: `K' = Q`, hence `K = K'.map f = Q.map f = J`, so `J ≤ K`.
  have hK'Q' : K.comap f = Q := QuasiFiniteAt.eq_of_le_of_under_eq hK'Q hunder
  have hKJ' : K = Q.map f :=
    calc K = (K.comap f).map f := (Ideal.map_comap_of_surjective f hsurj K).symm
      _ = Q.map f := by rw [hK'Q']
  exact hKJ'.ge

/-- For a flat, Noetherian `R`-algebra `S` quasi-finite at a prime `Q`, the height of `Q`
equals the height of the prime `Q.under R` it lies over. -/
theorem Ideal.height_eq_under_of_flat_quasiFiniteAt
    [IsNoetherianRing R] [IsNoetherianRing S] [Module.Flat R S]
    (Q : Ideal S) [Q.IsPrime] [Algebra.QuasiFiniteAt R Q] :
    Q.height = (Q.under R).height := by
  have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (Q.under R) Q
  rw [fibre_height_eq_zero_of_quasiFiniteAt Q, add_zero] at this
  exact this

/-- Étale algebras are flat and quasi-finite, so an étale Noetherian `R`-algebra `S` preserves
the height of every prime: `Q.height = (Q.under R).height`. -/
theorem Ideal.height_eq_under_of_etale
    [IsNoetherianRing R] [IsNoetherianRing S] [Algebra.Etale R S]
    (Q : Ideal S) [Q.IsPrime] :
    Q.height = (Q.under R).height :=
  Ideal.height_eq_under_of_flat_quasiFiniteAt Q

/-- Non-vacuity: the hypotheses hold for the identity algebra `R = S` (flat and module-finite over
itself), where the statement reduces to `Q.height = Q.height`. -/
example [IsNoetherianRing R] (Q : Ideal R) [Q.IsPrime] :
    Q.height = (Q.under R).height :=
  Ideal.height_eq_under_of_flat_quasiFiniteAt (R := R) (S := R) Q

end HeightPreservation

/-! ### The relative-dimension rank of a standard-smooth chart -/

section DimensionBridge

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

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
gives `(q.comap g).height = n`. -/
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
  -- Step E/F: `(q.comap g).height = n`; Step G via the étale height-preservation brick
  -- `q.height = (q.under B).height`.
  letI := (g : MvPolynomial (Fin n) k →+* S).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin n) k) S := RingHom.etale_algebraMap.mp hg
  haveI : IsNoetherianRing (MvPolynomial (Fin n) k) := inferInstance
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing (Submonoid.powers f) S inferInstance
  -- `q.under B = q.comap g` (definitionally `g`).
  have hunder : q.under (MvPolynomial (Fin n) k) = q.comap (g : MvPolynomial (Fin n) k →+* S) := by
    rw [Ideal.under_def]; rfl
  -- Étale ⟹ `q.height = (q.under B).height`; combine with `(q.comap g).height = n`.
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

end DimensionBridge

end DLNFibre.Core.Dimension
