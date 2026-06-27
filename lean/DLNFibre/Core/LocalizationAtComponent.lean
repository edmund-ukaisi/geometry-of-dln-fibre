/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.RingHom.Surjective
import Mathlib.RingTheory.Smooth.Locus

/-!
# `DLNFibre.Core.LocalizationAtComponent` — localizing a reduced ring recovers one component

The conceptual core of "a reducible variety is smooth at a generic point of a component **iff** that
component is smooth there": for a **reduced** ring `R`, localizing at a prime `q` that meets exactly
one irreducible component (`q` contains the minimal prime `I` of that component and no other minimal
prime) recovers the local ring of that component:

> `Localization.AtPrime R q  ≃ₐ[k]  Localization.AtPrime (R ⧸ I) (q.map (Quotient.mk I))`.

The mechanism (Codex-confirmed): in a reduced ring `⋂ⱼ Iⱼ = nilradical = ⊥`. For `x ∈ I` choose, for
each *other* minimal prime `J`, an element `s_J ∈ J \ q`; the product `s = ∏_J s_J` lies in every
other component but not in `q` (a unit in the localization), and `s · x ∈ ⋂ⱼ Iⱼ = ⊥`, so `x ↦ 0` in
`Localization.AtPrime R q`. Thus the kernel `I` of `R → R ⧸ I` dies in the localization, and the
induced `Localization.localAlgHom` is an iso (injective by the kernel-death, surjective because the
quotient map is surjective).

This is pure commutative algebra — no DLN content — reusable wherever a component's local ring is
extracted from a reducible reduced ring at a generic point. **Dependency rule:** `Core` only.
-/

namespace DLNFibre.Core

universe u

variable {R : Type u} [CommRing R]

/-! ## The component-killing lemma -/

/-- **A minimal prime dies in the localization at a generic point of its component.** For a reduced
ring `R` and a prime `q` containing the minimal prime `I` but *no other* minimal prime, the image of
`I` in `Localization.AtPrime R q` is `⊥`. The intersection `T = ⨅` of the *other* minimal primes is
not `≤ q` (else, `q` prime, some other `J ≤ q`, contradicting uniqueness), so pick `s ∈ T \ q`. For
`x ∈ I`, `x·s` lies in every minimal prime (in `I` since `x ∈ I`; in each other `J` since `s ∈ T ≤
J`), hence in `sInf (minimalPrimes R) = radical ⊥ = ⊥` (reduced); `s ∉ q` gives `x ↦ 0` via
`IsLocalization.map_eq_zero_iff`. -/
theorem map_eq_bot_localizationAtPrime_of_unique_minimalPrime_le [IsReduced R]
    [IsNoetherianRing R] (I q : Ideal R) [q.IsPrime] (hImin : I ∈ minimalPrimes R) (hIq : I ≤ q)
    (huniq : ∀ J ∈ minimalPrimes R, J ≤ q → J = I) :
    I.map (algebraMap R (Localization.AtPrime q)) = ⊥ := by
  classical
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro x hx
  -- The other minimal primes, as a finite set, and their intersection ideal `T`.
  set others : Finset (Ideal R) :=
    (minimalPrimes.finite_of_isNoetherianRing R).toFinset.filter (· ≠ I) with hothers
  set T : Ideal R := others.inf id with hT
  -- `T ⊄ q`: else (q prime) some other `J ≤ q`, forcing `J = I`, contradiction.
  have hTq : ¬ T ≤ q := by
    intro hle
    obtain ⟨J, hJothers, hJq⟩ := (Ideal.IsPrime.inf_le' (inferInstance)).mp hle
    rw [hothers, Finset.mem_filter, Set.Finite.mem_toFinset] at hJothers
    exact hJothers.2 (huniq J hJothers.1 hJq)
  -- pick `s ∈ T \ q`.
  obtain ⟨s, hsT, hsq⟩ := Set.not_subset.mp hTq
  -- `x·s` lies in every minimal prime, hence in `sInf minimalPrimes = ⊥` (reduced).
  have hxs : x * s = 0 := by
    rw [← Ideal.mem_bot, ← (Ideal.radical_eq_iff.mpr (Ideal.isRadical_bot (R := R))),
      ← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
    intro J hJ
    by_cases hJI : J = I
    · subst hJI; exact J.mul_mem_right s hx
    · -- `s ∈ T ≤ J` since `J` is one of the others.
      have hJin : J ∈ others := by
        rw [hothers, Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hJ, hJI⟩
      have hTJ : T ≤ J := by rw [hT]; exact Finset.inf_le hJin
      exact J.mul_mem_left x (hTJ hsT)
  -- so `x ↦ 0` in `Localization.AtPrime q`, since `s ∉ q`.
  rw [RingHom.mem_ker, IsLocalization.map_eq_zero_iff q.primeCompl]
  exact ⟨⟨s, hsq⟩, by rw [mul_comm]; exact hxs⟩

/-! ## The localization-quotient ring equivalence -/

variable (k : Type u) [Field k] [Algebra k R]

/-- **C1 — localizing at a generic point of one component recovers that component's local ring.**
For a reduced Noetherian ring `R` and a prime `q` meeting exactly one irreducible component (`q`
contains the minimal prime `I` and no other), the quotient map `π : R → R ⧸ I` induces a `k`-algebra
isomorphism on localizations:

> `Localization.AtPrime R q  ≃ₐ[k]  Localization.AtPrime (R ⧸ I) (q.map π)`.

It is `Localization.localAlgHom q (q.map π) (Quotient.mkₐ k I) hcomap`, bijective: **surjective**
since `π` is surjective (lift `mk' (π a) (π b)`), and **injective** since its
kernel is the image of `ker π = I`, which dies in `Localization.AtPrime R q`
(`map_eq_bot_localizationAtPrime_of_unique_minimalPrime_le`). -/
noncomputable def localizationAtPrimeQuotientAlgEquiv [IsReduced R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (hImin : I ∈ minimalPrimes R) (hIq : I ≤ q)
    (huniq : ∀ J ∈ minimalPrimes R, J ≤ q → J = I) :
    haveI : (q.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hIq
    Localization.AtPrime q ≃ₐ[k]
      Localization.AtPrime (q.map (Ideal.Quotient.mk I)) := by
  haveI hqbar : (q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIq
  -- `q = (q.map π).comap π` (kernel `I ≤ q`).
  have hcomap : q = (q.map (Ideal.Quotient.mk I)).comap (Ideal.Quotient.mk I) :=
    (Ideal.comap_map_mk hIq).symm
  -- the `k`-algebra hom on localizations induced by the quotient algebra map.
  refine AlgEquiv.ofBijective
    (Localization.localAlgHom (R := k) q (q.map (Ideal.Quotient.mk I))
      (Ideal.Quotient.mkₐ k I) hcomap) ⟨?_, ?_⟩
  · -- injective: kernel is the image of `ker (mkₐ) = I`, which is `⊥` after localizing.
    rw [injective_iff_map_eq_zero]
    intro z hz
    -- `z = mk' x s`; the map sends it to `mk' (π x) (π s)`, zero iff `x ∈ I` after localizing.
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    rw [Localization.localAlgHom_apply, Localization.localRingHom_mk',
      IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨⟨c, hc⟩, hceq⟩ := hz
    -- `c ∈ (q.map π).primeCompl` lifts to `c₀ ∉ q`; the relation `c·(π x) = 0` lifts to `c₀·x ∈ I`.
    obtain ⟨c₀, rfl⟩ := Ideal.Quotient.mk_surjective c
    have hmemI : c₀ * x ∈ I := by
      simp only [Ideal.Quotient.mkₐ_toRingHom] at hceq
      rw [← map_mul] at hceq; rwa [Ideal.Quotient.eq_zero_iff_mem] at hceq
    have hc₀q : c₀ ∉ q := fun h ↦ hc (Ideal.mem_map_of_mem _ h)
    -- `c₀ * x ∈ I` and `I.map = ⊥` gives `algebraMap (c₀*x) = 0`; cancel the unit `algebraMap c₀`.
    have hkill := map_eq_bot_localizationAtPrime_of_unique_minimalPrime_le I q hImin hIq huniq
    have h0 : algebraMap R (Localization.AtPrime q) (c₀ * x) = 0 := by
      rw [← Ideal.mem_bot, ← hkill]; exact Ideal.mem_map_of_mem _ hmemI
    -- so `algebraMap x = 0`, hence `mk' x s = 0`.
    have hxzero : algebraMap R (Localization.AtPrime q) x = 0 := by
      have hcu : IsUnit (algebraMap R (Localization.AtPrime q) c₀) :=
        IsLocalization.map_units _ (⟨c₀, Ideal.mem_primeCompl_iff.mpr hc₀q⟩ : q.primeCompl)
      rw [map_mul] at h0
      exact hcu.mul_left_cancel (by rw [h0, mul_zero])
    rw [IsLocalization.mk'_eq_zero_iff]
    rw [IsLocalization.map_eq_zero_iff q.primeCompl] at hxzero
    obtain ⟨m, hm⟩ := hxzero
    exact ⟨m, hm⟩
  · -- surjective: every `mk' y t` in `AtPrime q'` lifts (`π` surjective; `t ∉ q' ⟹ b ∉ q`).
    intro w
    obtain ⟨⟨y, t, ht⟩, rfl⟩ := IsLocalization.mk'_surjective
      (q.map (Ideal.Quotient.mk I)).primeCompl w
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective t
    -- `b ∉ q` since `mk b ∉ q' = q.map π`.
    have hbq : b ∉ q := fun h ↦ ht (Ideal.mem_map_of_mem _ h)
    refine ⟨IsLocalization.mk' (Localization.AtPrime q) a
      (⟨b, Ideal.mem_primeCompl_iff.mpr hbq⟩ : q.primeCompl), ?_⟩
    rw [Localization.localAlgHom_apply, Localization.localRingHom_mk']
    simp only [Ideal.Quotient.mkₐ_toRingHom]

/-! ## The unconditional smoothness bridge -/

/-- **C1 smoothness bridge — a reducible reduced variety is smooth at a generic point of a component
iff that component is.** For a reduced Noetherian `k`-algebra `R` and a prime `q` meeting exactly
one minimal prime `I`, the localizations of `R` and of the component ring `R ⧸ I` at `q` are
`k`-algebra isomorphic (`localizationAtPrimeQuotientAlgEquiv`), so `Algebra.IsSmoothAt k q` of `R`
transfers from `Algebra.IsSmoothAt k (q.map (Quotient.mk I))` of the component ring `R ⧸ I` (a
domain, where the orbit-closure machinery applies) via `Algebra.FormallySmooth.iff_of_equiv`.

This is the precise bridge turning "the component (a domain) is smooth at its generic point" into
"the reducible reduced variety is smooth at that generic point", discharging the LEAD route's
sub-wall (a) — the quotient-by-intersection localization comparison — flagged in thread 16. -/
theorem isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime [IsReduced R] [IsNoetherianRing R]
    (I q : Ideal R) [q.IsPrime] (hImin : I ∈ minimalPrimes R) (hIq : I ≤ q)
    (huniq : ∀ J ∈ minimalPrimes R, J ≤ q → J = I)
    (hsm : haveI : (q.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime hIq
      Algebra.IsSmoothAt k (q.map (Ideal.Quotient.mk I))) :
    Algebra.IsSmoothAt k q := by
  haveI : (q.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hIq
  exact (Algebra.FormallySmooth.iff_of_equiv
    (localizationAtPrimeQuotientAlgEquiv k I q hImin hIq huniq)).mpr hsm

/-- **The generic-point specialization (`q = I`, the component's own generic point).** A minimal
prime `I` of a reduced Noetherian `k`-algebra `R` is its own generic point; the "meets exactly one
minimal prime" hypothesis is then **free** (minimal primes are incomparable: `J ≤ I` with both
minimal forces `J = I`). So `R` is `IsSmoothAt k I` whenever the component ring `R ⧸ I` is
`IsSmoothAt k (I.map (Quotient.mk I))` — i.e. at *its* generic point `⊥`. -/
theorem isSmoothAt_minimalPrime_of_isSmoothAt_quotient [IsReduced R] [IsNoetherianRing R]
    (I : Ideal R) (hImin : I ∈ minimalPrimes R)
    (hIp : haveI : I.IsPrime := hImin.1.1
      haveI : (I.map (Ideal.Quotient.mk I)).IsPrime :=
        Ideal.isPrime_map_quotientMk_of_isPrime (le_refl I)
      Algebra.IsSmoothAt k (I.map (Ideal.Quotient.mk I))) :
    haveI : I.IsPrime := hImin.1.1
    Algebra.IsSmoothAt k I := by
  haveI : I.IsPrime := hImin.1.1
  refine isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime k I I hImin le_rfl ?_ hIp
  -- `huniq`: a minimal prime `J ≤ I` (both minimal) is `I` by incomparability.
  intro J hJ hJI
  exact le_antisymm hJI (hImin.2 ⟨hJ.1.1, bot_le⟩ hJI)

/-! ## A domain is smooth at its generic point if smooth anywhere -/

/-- **A domain smooth at *some* point is smooth at its generic point `⊥`.** If a finitely-presented
`k`-algebra domain `D` is `IsSmoothAt k m` at some prime `m`, then it is `IsSmoothAt k ⊥`: the
smooth locus is open and nonempty (`IsSmoothAt.exists_notMem_smooth` gives `g ∉ m` with
`Smooth k (Away g)`), and `g ≠ 0` (a nonzero divisor in the domain, as `g ∉ m ⊇ ⊥`), so `⊥` lies in
the basic open `{g ≠ 0}`; the basic-open bridge gives `IsSmoothAt k ⊥`. The generic point of an
irreducible `Spec` is smooth iff the smooth locus is nonempty. -/
theorem isSmoothAt_bot_of_isSmoothAt [IsDomain R] [Algebra.FinitePresentation k R]
    (m : Ideal R) [m.IsPrime] (hm : Algebra.IsSmoothAt k m) :
    Algebra.IsSmoothAt k (⊥ : Ideal R) := by
  obtain ⟨g, hgm, hg_smooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k m
  -- `g ≠ 0`: `g ∈ ⊥ = {0}` would give `g ∈ m` (since `⊥ ≤ m`), contradicting `g ∉ m`.
  have hg0 : g ∉ (⊥ : Ideal R) := fun h ↦ hgm ((bot_le : (⊥ : Ideal R) ≤ m) h)
  -- the basic-open bridge: `Smooth k (Away g)` + `g ∉ ⊥` ⟹ `IsSmoothAt k ⊥`.
  exact (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := k) (A := R) (f := g)).mpr hg_smooth
    (show (⟨(⊥ : Ideal R), inferInstance⟩ : PrimeSpectrum R) ∈ PrimeSpectrum.basicOpen g from hg0)

/-! ## `IsSmoothAt` transport across a `k`-algebra equivalence -/

/-- **`IsSmoothAt` transports across a `k`-algebra equivalence** `e : A ≃ₐ[k] B` by `comap`: a
smooth prime `m` of `B` pulls back to a smooth prime `m.comap e` of `A`. The localizations
`AtPrime (m.comap e)` and `AtPrime m` are `k`-algebra isomorphic (`ringEquivOfRingEquiv` along `e`,
which carries `(m.comap e).primeCompl` onto `m.primeCompl`), and
`Algebra.FormallySmooth.iff_of_equiv` transfers formal smoothness. -/
theorem isSmoothAt_comap_of_algEquiv {A B : Type u} [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] (e : A ≃ₐ[k] B) (m : Ideal B) [m.IsPrime]
    (hm : Algebra.IsSmoothAt k m) :
    haveI : (m.comap (e : A →+* B)).IsPrime := m.comap_isPrime (e : A →+* B)
    Algebra.IsSmoothAt k (m.comap (e : A →+* B)) := by
  haveI : (m.comap (e : A →+* B)).IsPrime := m.comap_isPrime (e : A →+* B)
  -- `e` carries `(m.comap e).primeCompl` onto `m.primeCompl`.
  have hmap : Submonoid.map (e : A ≃+* B).toMonoidHom (m.comap (e : A →+* B)).primeCompl
      = m.primeCompl := by
    ext y
    simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, Ideal.mem_comap]
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨e.symm y, by simpa using hy, by simp⟩
  refine (Algebra.FormallySmooth.iff_of_equiv
    (AlgEquiv.ofRingEquiv (f := IsLocalization.ringEquivOfRingEquiv
      (Localization.AtPrime (m.comap (e : A →+* B))) (Localization.AtPrime m)
      (e : A ≃+* B) hmap) (fun r ↦ ?_))).mpr hm
  rw [show (algebraMap k (Localization.AtPrime (m.comap (e : A →+* B)))) r
      = algebraMap A (Localization.AtPrime (m.comap (e : A →+* B)))
        (algebraMap k A r) from (IsScalarTower.algebraMap_apply k A _ r),
    IsLocalization.ringEquivOfRingEquiv_eq, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes,
    ← IsScalarTower.algebraMap_apply k B _ r]

/-- `Algebra.IsSmoothAt` depends only on the ideal: a smooth prime stays smooth under an ideal
equality (transport `FormallySmooth` along the localization equiv induced by the identity, sidestep
the prime-instance `▸`-motive obstruction). -/
theorem isSmoothAt_of_ideal_eq {A : Type u} [CommRing A] [Algebra k A]
    {p q : Ideal A} [p.IsPrime] [q.IsPrime] (h : p = q) (hp : Algebra.IsSmoothAt k p) :
    Algebra.IsSmoothAt k q := by
  subst h; exact hp

/-- **`Smooth (Localization.Away ·)` transports across a `k`-algebra equivalence** `e : C ≃ₐ[k] T`:
if `Localization.Away t` (`t : T`) is smooth, so is `Localization.Away (e.symm t)` (`e.symm t : C`),
via the localized equiv `Away (e.symm t) ≃ₐ[k] Away (e (e.symm t)) = Away t`
(`IsLocalization.algEquivOfAlgEquiv` along `e`, `Submonoid.map_powers`) and `Smooth.of_equiv`.
Stated abstractly so the heavy concrete chart ring is instantiated **once** at the call site
(avoiding a `whnf` blowup). -/
theorem smooth_localizationAway_symm_of_smooth_localizationAway {C T : Type u}
    [CommRing C] [CommRing T] [Algebra k C] [Algebra k T] (e : C ≃ₐ[k] T) (t : T)
    (ht : Algebra.Smooth k (Localization.Away t)) :
    Algebra.Smooth k (Localization.Away (e.symm t)) := by
  haveI : Algebra.Smooth k (Localization.Away (e (e.symm t))) := by
    rw [AlgEquiv.apply_symm_apply]; exact ht
  have hHpow : Submonoid.map (e : C ≃+* T).toMonoidHom (Submonoid.powers (e.symm t))
      = Submonoid.powers (e (e.symm t)) := by rw [Submonoid.map_powers]; rfl
  exact Algebra.Smooth.of_equiv
    (IsLocalization.algEquivOfAlgEquiv
      (Localization.Away (e.symm t)) (Localization.Away (e (e.symm t))) e hHpow).symm

/-! ## The packaged C1+C2 component bridge (abstract, single-instantiation) -/

/-- **The packaged bridge: a component isomorphic to a smooth domain ⟹ smooth at that component's
generic point.** For a reduced Noetherian `k`-algebra `R`, a minimal prime `I`, and a `k`-algebra
iso `e : R ⧸ I ≃ₐ[k] D` to a finitely-presented `k`-algebra **domain** `D` that is `IsSmoothAt k m`
at *some* prime `m`, the reducible ring `R` is `Algebra.IsSmoothAt k I` at the component `I`.

Packages the whole chain over abstract `R`/`D` (so the application instantiates the heavy concrete
ring **once**, avoiding repeated `whnf` on it): `D` smooth somewhere ⟹ smooth at its generic point
`⊥` (`isSmoothAt_bot_of_isSmoothAt`, `D` a domain); transport `⊥` across `e` to `⊥` of `R ⧸ I`
(`isSmoothAt_comap_of_algEquiv`, `⊥.comap e = ⊥` by injectivity); the C1 bridge
(`isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime`, `q := I`, `huniq` free by incomparability,
`I.map (mk I) = ⊥`) lifts to `IsSmoothAt k I` of `R`. -/
theorem isSmoothAt_minimalPrime_of_componentEquiv_domain [IsReduced R] [IsNoetherianRing R]
    (I : Ideal R) [I.IsPrime] (hImin : I ∈ minimalPrimes R)
    {D : Type u} [CommRing D] [IsDomain D] [Algebra k D] [Algebra.FinitePresentation k D]
    (e : (R ⧸ I) ≃ₐ[k] D) (m : Ideal D) [m.IsPrime] (hm : Algebra.IsSmoothAt k m) :
    Algebra.IsSmoothAt k I := by
  -- `D` is smooth at its generic point `⊥`; transport across `e` to `⊥.comap e` of `R ⧸ I`.
  have hbotD : Algebra.IsSmoothAt k (⊥ : Ideal D) := isSmoothAt_bot_of_isSmoothAt k m hm
  have hbotA : Algebra.IsSmoothAt k ((⊥ : Ideal D).comap (e : (R ⧸ I) →+* D)) :=
    isSmoothAt_comap_of_algEquiv k e (⊥ : Ideal D) hbotD
  -- the C1 bridge: `IsSmoothAt k (I.map (mk I))` of `R ⧸ I` ⟹ `IsSmoothAt k I` of `R`.
  haveI hmapprime : (I.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime (le_refl I)
  refine isSmoothAt_of_isSmoothAt_quotient_unique_minimalPrime k I I hImin le_rfl
    (fun J hJ hJI ↦ le_antisymm hJI (hImin.2 ⟨hJ.1.1, bot_le⟩ hJI)) ?_
  -- `⊥.comap e = ⊥ = I.map (mk I)`; transport `hbotA` along the ideal equality.
  refine isSmoothAt_of_ideal_eq k
    ((Ideal.comap_bot_of_injective (e : (R ⧸ I) →+* D) e.injective).trans
      (Ideal.map_quotient_self I).symm) hbotA

end DLNFibre.Core
