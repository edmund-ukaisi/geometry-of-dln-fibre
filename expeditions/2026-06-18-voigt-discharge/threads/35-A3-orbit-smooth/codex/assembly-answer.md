1. **Affine Bookkeeping**

Use the carrier defeq. For your abbrev

```lean
abbrev orbitScheme M := Spec (.of (orbitRing M))
```

Lean accepts both directions:

```lean
(p : PrimeSpectrum (orbitRing M)) : orbitScheme M
(x : orbitScheme M) : PrimeSpectrum (orbitRing M)
```

`Spec.topObj_forget` is the known simp lemma behind this, but in this file the cast is usually enough.

For `formallySmooth_stalkMap_iff` at `⊤, ⊤`, use this shape:

```lean
set_option backward.isDefEq.respectTransparency false in
private lemma mem_schemeSmooth_iff_mem_GammaSmooth
    (M : Tuple (k := k) d) (p : PrimeSpectrum (orbitRing M)) :
    (p : orbitScheme M) ∈ (orbitSchemeHom M).smoothLocus ↔
      letI := ((orbitSchemeHom M).appLE
        (⊤ : (Spec (.of k)).Opens) (⊤ : (orbitScheme M).Opens)
        (by intro _ _; trivial)).hom.toAlgebra
      (isAffineOpen_top (orbitScheme M)).primeIdealOf
          ⟨(p : orbitScheme M), trivial⟩ ∈
        Algebra.smoothLocus Γ(Spec (.of k), ⊤) Γ(orbitScheme M, ⊤) := by
  change ((orbitSchemeHom M).stalkMap (p : orbitScheme M)).hom.FormallySmooth ↔ _
  simpa using
    (formallySmooth_stalkMap_iff
      (f := orbitSchemeHom M) (x := (p : orbitScheme M))
      (U := (⊤ : (Spec (.of k)).Opens))
      (V := (⊤ : (orbitScheme M).Opens))
      (isAffineOpen_top (Spec (.of k)))
      (isAffineOpen_top (orbitScheme M))
      (by intro _ _; trivial) trivial)
```

There is no known `IsAffineOpen.primeIdealOf_top` lemma at this pin. The clean local helper is:

```lean
private lemma primeIdealOf_top_orbitScheme
    (M : Tuple (k := k) d) (p : PrimeSpectrum (orbitRing M)) :
    (isAffineOpen_top (orbitScheme M)).primeIdealOf
        ⟨(p : orbitScheme M), trivial⟩ =
      PrimeSpectrum.comap
        (Scheme.ΓSpecIso (.of (orbitRing M))).hom.hom p := by
  dsimp [IsAffineOpen.primeIdealOf, IsAffineOpen.isoSpec_hom]
  rw [Scheme.Opens.toSpecΓ_top]
  change ((⊤ : (Spec (.of (orbitRing M))).Opens).ι ≫
      (Spec (.of (orbitRing M))).toSpecΓ) ⟨p, trivial⟩ =
    Spec.map (Scheme.ΓSpecIso (.of (orbitRing M))).hom p
  simp only [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  rw [SpecMap_ΓSpecIso_hom]
```

Then put the remaining `ΓSpecIso` transport in one helper:

```lean
private lemma orbitScheme_mem_smoothLocus_iff_isSmoothAt
    (M : Tuple (k := k) d) (p : PrimeSpectrum (orbitRing M)) :
    (p : orbitScheme M) ∈ (orbitSchemeHom M).smoothLocus ↔
      Algebra.IsSmoothAt k p.asIdeal := by
  -- Use:
  -- * mem_schemeSmooth_iff_mem_GammaSmooth
  -- * primeIdealOf_top_orbitScheme
  -- * Scheme.ΓSpecIso_naturality for compatibility of Γ maps
  -- * IsLocalization.ringEquivOfRingEquiv for localizations at transported primes
  -- * RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff
  -- or equivalently Algebra.FormallySmooth.iff_of_equiv after base/target transport.
  sorry
```

I would not hand-roll this inside the main proof. I also did not find a packaged affine dictionary lemma of the form
`x ∈ f.smoothLocus ↔ p ∈ Algebra.smoothLocus k A` in v4.29.

2. **Shorter Route**

Yes: avoid `closedPoints` entirely. Since `orbitSpecSet M` is already the set of orbit point ideals, and those ideals are maximal by your landed instance, you do not need `nonempty_inter_closedPoints`.

Use:

```lean
(dense_orbitSpecSet M).inter_open_nonempty _
  (orbitSchemeHom M).smoothLocus.2
  hSmDense.nonempty
```

where

```lean
hSmDense :
  Dense (((orbitSchemeHom M).smoothLocus : Set (orbitScheme M))) :=
    Scheme.Hom.dense_smoothLocus_of_perfectField (orbitSchemeHom M)
```

Ring-side generic smoothness density appears absent at v4.29. What exists is ring-side openness:

```lean
Algebra.isOpen_smoothLocus
Algebra.basicOpen_subset_smoothLocus_iff
Algebra.basicOpen_subset_smoothLocus_iff_smooth
```

but I found no `Algebra.dense_smoothLocus_of_perfectField` analogue. So use the scheme theorem and bridge one point.

3. **Skeleton**

This main proof elaborates modulo the one affine dictionary helper above:

```lean
private lemma exists_orbitPointIdeal_isSmoothAt
    (M : Tuple (k := k) d) :
    ∃ P : BaseChangeGroup (k := k) d,
      Algebra.IsSmoothAt k (orbitPointIdeal M P) := by
  have hSmDense :
      Dense (((orbitSchemeHom M).smoothLocus : Set (orbitScheme M))) :=
    Scheme.Hom.dense_smoothLocus_of_perfectField (orbitSchemeHom M)

  have hInt :
      ((((orbitSchemeHom M).smoothLocus : Set (orbitScheme M)) ∩
          orbitSpecSet M).Nonempty) := by
    exact (dense_orbitSpecSet M).inter_open_nonempty _
      (orbitSchemeHom M).smoothLocus.2
      hSmDense.nonempty

  rcases hInt with ⟨p, hpSmooth, hpOrbit⟩
  rcases hpOrbit with ⟨P, hp_eq⟩
  refine ⟨P, ?_⟩

  have hpSmoothRing : Algebra.IsSmoothAt k p.asIdeal :=
    (orbitScheme_mem_smoothLocus_iff_isSmoothAt M p).mp hpSmooth

  simpa [hp_eq] using hpSmoothRing

theorem normalFormIdeal_isSmoothAt
    (M : Tuple (k := k) d) :
    Algebra.IsSmoothAt k (normalFormIdeal M) := by
  obtain ⟨P, hP⟩ := exists_orbitPointIdeal_isSmoothAt (k := k) M
  exact (isSmoothAt_orbitPointIdeal_iff M P).mp hP
```

Likely defeq-sensitive spots: the helper around `formallySmooth_stalkMap_iff`, the `letI` algebra from `appLE ⊤ ⊤`, and rewriting `⊤.toSpecΓ` via `Scheme.Opens.toSpecΓ_top`. Put `set_option backward.isDefEq.respectTransparency false` on the helper, not the final intersection proof.