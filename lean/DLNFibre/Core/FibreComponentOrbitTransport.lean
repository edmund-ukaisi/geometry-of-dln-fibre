/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreComponentOrbit
import DLNFibre.Core.FibreGenericSmooth
import DLNFibre.Core.OrbitSmooth

/-!
# `DLNFibre.Core.FibreComponentOrbitTransport` — fully-unconditional fibre top-component smoothness
(thread 20, task #128)

This module discharges the **last** open input of generic smoothness — the C2(a) fact — and lands
the **fully unconditional** headline: the reduced fibre ring `sweepFibreRing` is `Algebra.IsSmoothAt
k I` at the generic point of every irreducible component `I`, with no open hypothesis.

## The route — no variety iso `e` needed

The thread-17 reduction asked for an iso `sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M`; thread-20 found
that target is dimensionally impossible (the fibre component is the orbit closure **times** affine
factor). But smoothness needs no such iso: a **fibre top component `sweepFibreRing ⧸ I` is itself a
finitely-presented DOMAIN over the algebraically-closed (perfect) field `k`**, and *any* such domain
is generically smooth (`Scheme.Hom.dense_smoothLocus_of_perfectField` — the same generic-smoothness
machinery `OrbitSmooth` used for the orbit ring). So `sweepFibreRing ⧸ I` is smooth at its generic
point `⊥`, and the C1 bridge
(`LocalizationAtComponent.isSmoothAt_minimalPrime_of_isSmoothAt_quotient`)
lifts that to `Algebra.IsSmoothAt k I` of the (reducible) `sweepFibreRing`.

The subtlety thread-16/17 navigated was the **reducibility** of `sweepFibreRing`: generic smoothness
of the whole reducible ring gives a dense smooth open that need not meet a given component's generic
point. Quotienting to the component `I` (a domain) removes the obstruction — generic smoothness
applies to the domain directly.

## Main results

* `mem_smoothLocus_iff_isSmoothAt` — the abstract scheme↔ring smooth-point dictionary for any fp
  `k`-algebra (the `OrbitSmooth` proof, freed of the orbit ring).
* `isSmoothAt_bot_of_finitePresentation_domain` — a fp domain over alg-closed `k` is `IsSmoothAt ⊥`.
* `isSmoothAt_sweepFibre_component` — **FULLY UNCONDITIONAL**: `sweepFibreRing` is `IsSmoothAt k I`
  at every minimal prime `I`; `isSmoothAt_sweepFibre_topComponent` is the top-dim specialisation.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial Matrix Algebra AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k]

/-! ## The abstract scheme↔ring smooth-point dictionary

Lifted verbatim from `OrbitSmooth.{comap_algebraMap_eq_bot, localRingHom_formallySmooth_iff,
orbitScheme_mem_smoothLocus_iff_isSmoothAt}`, with the orbit ring replaced by an arbitrary
`k`-algebra `A`. Only `k` being a field is used. -/

section Dictionary

variable (A : Type u) [CommRing A] [Algebra k A]

/-- The prime of `k` under the structure map of `Spec A` is `⊥` (`k` is a field). -/
theorem comap_algebraMap_specHom_eq_bot (p : PrimeSpectrum A) :
    (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal = ⊥ := by
  rcases Ideal.eq_bot_or_top
      (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal with h | h
  · exact h
  · exact absurd h (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).2.ne_top

variable {A} in
/-- The localized structure map at `p` is formally smooth iff `A` is formally smooth at `p` over `k`
(its source `AtPrime ⊥ ≃ k`, `k` a field). -/
theorem specHom_localRingHom_formallySmooth_iff (p : PrimeSpectrum A) :
    (Localization.localRingHom
        (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal
        p.asIdeal (algebraMap k A) rfl).FormallySmooth ↔
      Algebra.IsSmoothAt k p.asIdeal := by
  haveI hqp : (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal.IsPrime :=
    (PrimeSpectrum.comap _ p).2
  have hunits : (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal.primeCompl
        ≤ IsUnit.submonoid k := by
    intro x hx
    rw [Ideal.primeCompl, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_compl_iff,
      SetLike.mem_coe, comap_algebraMap_specHom_eq_bot A p, Ideal.mem_bot] at hx
    simp only [IsUnit.mem_submonoid_iff]
    exact isUnit_iff_ne_zero.mpr hx
  let e : k ≃ₐ[k] Localization.AtPrime
      (PrimeSpectrum.comap (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal :=
    IsLocalization.atUnits k _ hunits
  have harrow : Arrow.mk (CommRingCat.ofHom (Localization.localRingHom (PrimeSpectrum.comap
        (CommRingCat.ofHom (algebraMap k A)).hom p).asIdeal p.asIdeal (algebraMap k A) rfl))
      ≅ Arrow.mk (CommRingCat.ofHom (algebraMap k (Localization.AtPrime p.asIdeal))) :=
    Arrow.isoMk (e.symm.toRingEquiv.toCommRingCatIso) (Iso.refl _) (by
      refine CommRingCat.hom_ext (RingHom.ext (fun z ↦ ?_))
      obtain ⟨y, rfl⟩ : ∃ y : k, e y = z := ⟨e.symm z, e.apply_symm_apply z⟩
      change (algebraMap k (Localization.AtPrime p.asIdeal)) (e.symm (e y))
        = Localization.localRingHom _ p.asIdeal (algebraMap k A) rfl (e y)
      rw [AlgEquiv.symm_apply_apply]
      have hey : e y = algebraMap k (Localization.AtPrime
          (Ideal.comap (algebraMap k A) p.asIdeal)) y := rfl
      rw [hey, Localization.localRingHom_to_map,
        ← IsScalarTower.algebraMap_apply k A (Localization.AtPrime p.asIdeal) y])
  have hbridge := RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff harrow
  simp only [CommRingCat.hom_ofHom] at hbridge ⊢
  rw [hbridge, RingHom.formallySmooth_algebraMap]

variable {A} [Algebra.FinitePresentation k A] in
/-- **The abstract scheme↔ring smooth-point dictionary.** A point `p` of `Spec A` lies in the smooth
locus of the structure morphism `Spec.map (algebraMap k A)` iff `A` is `Algebra.IsSmoothAt k p`.
(The `OrbitSmooth` dictionary, freed of the orbit ring — only `k` a field is used; `[fp]` makes
the structure morphism locally of finite presentation so `smoothLocus` is defined.) -/
theorem mem_smoothLocus_iff_isSmoothAt (p : PrimeSpectrum A) :
    haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
      rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
      change (algebraMap k A).FinitePresentation
      rw [RingHom.finitePresentation_algebraMap]; infer_instance
    (p : Spec (.of A)) ∈ (Spec.map (CommRingCat.ofHom (algebraMap k A))).smoothLocus ↔
      Algebra.IsSmoothAt k p.asIdeal := by
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k A))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap k A).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]; infer_instance
  rw [show ((p : Spec (.of A)) ∈ (Spec.map (CommRingCat.ofHom (algebraMap k A))).smoothLocus)
      = ((Spec.map (CommRingCat.ofHom (algebraMap k A))).stalkMap
          (p : Spec (.of A))).hom.FormallySmooth from propext Scheme.Hom.mem_smoothLocus]
  rw [RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
    (Scheme.arrowStalkMapSpecIso (CommRingCat.ofHom (algebraMap k A)) p)]
  exact specHom_localRingHom_formallySmooth_iff p

end Dictionary

/-! ## A finitely-presented domain over an algebraically closed field is generically smooth -/

/-- **A fp domain over an algebraically-closed field is `IsSmoothAt k ⊥`** (smooth at its generic
point). `Spec D` is reduced (a domain) and the structure morphism is locally of finite presentation
+ finite type, so the smooth locus is dense (`dense_smoothLocus_of_perfectField`, `k` perfect),
hence nonempty: some prime `m` is `IsSmoothAt k m`; the basic-open bridge
(`isSmoothAt_bot_of_isSmoothAt`, `D` a domain) drops it to `⊥`. -/
theorem isSmoothAt_bot_of_finitePresentation_domain [IsAlgClosed k]
    (D : Type u) [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FinitePresentation k D] :
    Algebra.IsSmoothAt k (⊥ : Ideal D) := by
  haveI : LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap k D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    change (algebraMap k D).FinitePresentation
    rw [RingHom.finitePresentation_algebraMap]; infer_instance
  haveI : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap k D))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change (algebraMap k D).FiniteType
    rw [RingHom.finiteType_algebraMap]; infer_instance
  -- a smooth point exists (dense smooth locus over the perfect field `k`).
  obtain ⟨x, hx⟩ :=
    (Scheme.Hom.dense_smoothLocus_of_perfectField
      (Spec.map (CommRingCat.ofHom (algebraMap k D)))).nonempty
  have hsm : Algebra.IsSmoothAt k x.asIdeal := (mem_smoothLocus_iff_isSmoothAt x).mp hx
  haveI : x.asIdeal.IsPrime := x.2
  -- drop the smooth point to the generic point `⊥` (the domain `D` is fp).
  exact isSmoothAt_bot_of_isSmoothAt k x.asIdeal hsm

/-! ## The fully-unconditional fibre top-component smoothness headline -/

variable {N : ℕ}

/-- **FULLY UNCONDITIONAL — the reduced fibre ring is smooth at the generic point of EVERY
irreducible component.** For any minimal prime `I` of `sweepFibreRing` (an irreducible component of
the reduced fibre — *no top-dimensionality needed*), `Algebra.IsSmoothAt k I`, with **no open
hypothesis** (no orbit iso, no chart, no Lemma 4.6 bundle).

The component ring `sweepFibreRing ⧸ I` is a finitely-presented `k`-algebra **domain** (`I` prime,
`sweepFibreRing` fp); over the algebraically-closed (⟹ perfect) field `k` it is generically smooth
(`isSmoothAt_bot_of_finitePresentation_domain` — the standard "reduced finite type over a perfect
field is generically smooth on every component"), so it is `IsSmoothAt k ⊥` at its generic point.
The C1 bridge `isSmoothAt_minimalPrime_of_isSmoothAt_quotient` (`sweepFibreRing` reduced/Noetherian)
lifts that to `Algebra.IsSmoothAt k I` of the reducible `sweepFibreRing` (at the generic point `I`,
the other components — distinct minimal primes, incomparable to `I` — do not meet, so the local ring
at `I` is the component's local ring). -/
theorem isSmoothAt_sweepFibre_component [IsAlgClosed k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq)) :
    haveI : I.IsPrime := hImin.1.1
    Algebra.IsSmoothAt k I := by
  haveI : I.IsPrime := hImin.1.1
  -- the component ring is a fp domain.
  haveI : IsDomain (sweepFibreRing k d r hp hq ⧸ I) := Ideal.Quotient.isDomain I
  haveI : Algebra.FinitePresentation k (sweepFibreRing k d r hp hq ⧸ I) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian I)
  -- it is `IsSmoothAt k ⊥` (generic smoothness of a domain over alg-closed `k`).
  have hbot : Algebra.IsSmoothAt k (⊥ : Ideal (sweepFibreRing k d r hp hq ⧸ I)) :=
    isSmoothAt_bot_of_finitePresentation_domain (sweepFibreRing k d r hp hq ⧸ I)
  -- the C1 bridge lifts smoothness at `⊥ = I.map (mk I)` to `IsSmoothAt k I` of `sweepFibreRing`.
  haveI hmapprime : (I.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (le_refl I)
  refine isSmoothAt_minimalPrime_of_isSmoothAt_quotient k I hImin ?_
  exact isSmoothAt_of_ideal_eq k (Ideal.map_quotient_self I).symm hbot

/-- **The top-dimensional-component headline (the C2(a) deliverable).** Specialisation of
`isSmoothAt_sweepFibre_component` to a *top-dimensional* minimal prime `I` (a top-dim irreducible
component of the reduced fibre, `I ∈ TopDimMinPrimes`): `Algebra.IsSmoothAt k I`, fully
unconditionally. This is what thread-17's `isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre` /
generic-smoothness chain consumed as its one open input (C2(a)) — now discharged. -/
theorem isSmoothAt_sweepFibre_topComponent [IsAlgClosed k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    haveI : I.IsPrime := isPrime_of_mem_topDimMinPrimes hI
    Algebra.IsSmoothAt k I :=
  isSmoothAt_sweepFibre_component d r hp hq I hI.1

/-- **The source pivot chart is smooth on a basic open, FULLY UNCONDITIONALLY.** Composing the
now-discharged C2(a) input (`isSmoothAt_sweepFibre_topComponent` at a top-component prime `I`) with
the thread-17 chart transport `isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre`: there is a chart
element `h : Away (chartDsig …)` with `Algebra.IsSmoothAt k p` at every chart prime `p` off `h`. No
open hypothesis remains — generic smoothness of the source pivot chart is unconditional. -/
theorem exists_isSmoothAt_chartDsig_unconditional [IsAlgClosed k] [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    ∃ h : Localization.Away (chartDsig k d r hp hq),
      ∀ (p : Ideal (Localization.Away (chartDsig k d r hp hq))) [p.IsPrime],
        h ∉ p → Algebra.IsSmoothAt k p := by
  haveI : I.IsPrime := isPrime_of_mem_topDimMinPrimes hI
  exact isSmoothAt_chartDsig_of_isSmoothAt_sweepFibre d r hp hq I
    (isSmoothAt_sweepFibre_topComponent d r hp hq I hI)

end DLNFibre.Core
