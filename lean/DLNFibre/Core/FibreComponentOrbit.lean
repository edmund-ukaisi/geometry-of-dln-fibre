/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreGenericSmoothUncond
import DLNFibre.Core.OrbitSmooth
import DLNFibre.Core.TopDimMinPrimesW0
import DLNFibre.Core.CCodimCornerMono
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# `DLNFibre.Core.FibreComponentOrbit` — the C2(a) dimension finding + the sigma-side labeling
(thread 20, task #119)

Thread 17 reduced unconditional generic smoothness to a single open input C2(a): a `k`-algebra iso
`sweepFibreRing ⧸ I ≃ₐ[k] orbitRing M` per top-dimensional minimal prime `I`. **That target is
dimensionally impossible.** The chart identity (`ChartSweepWiring.sweep_of_localizedChartAlgEquiv`)
records `dim Σ^r = dim F + δ`, `δ = r·(d_last + d_0 − r)`; a fibre top component has the fibre
dimension `dim F`, while a *shifted* orbit closure `Ō_M` over `d − r` has dimension `dim F − δ`. The
fibre top component is the orbit closure **times an affine factor `A^δ`** (the C-part), so a bare
`orbitRing M` cannot be the coordinate ring.

⚠ **The whole orbit-iso route to C2(a) is SUPERSEDED.** Generic smoothness of the reduced fibre is
**fully unconditional** with *no* orbit iso, by the direct domain argument
`Core.FibreComponentOrbitTransport.isSmoothAt_sweepFibre_topComponent` (a fibre component is a fp
domain over the perfect field `k`, hence generically smooth). And the dimension-corrected consumer
`isSmoothAt_sweepFibre_of_component_orbitPolyEquiv` below — `e : sweepFibreRing ⧸ I ≃ₐ[k]
MvPolynomial η (orbitRing M)` (shifted orbit) — also takes a **globally-false / unreachable**
hypothesis (thread-24): the only chart-supported variety iso is *localized* with the polynomial
wrapper on the FIBRE side and the FULL-`d` orbit. So that consumer is **historical scaffolding**
(see its ⚠ docstring); it discharges nothing in practice.

**What this module genuinely contributes** (unconditional, live): the **sigma-side component ↔
orbit-closure labeling** `exists_sigma_topComponent_orbitRingEquiv` — every top-dim component of
`O(Σ̄^r)` IS `orbitRing (realizerD m)` exactly — and the reusable smooth-fp-domain ingredients. The
two `…_of_component_*` consumers are kept only for the honest record.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Ideal (TopDimMinPrimes mem_topDimMinPrimes isPrime_of_mem_topDimMinPrimes
  comap_mem_topDimMinPrimes bijOn_comap_topDimMinPrimes topDimMinPrimes_ncard_eq_of_ringEquiv
  quotTopDimSet bijOn_comap_quotTopDimSet)

open MvPolynomial Matrix Algebra
open scoped TensorProduct

universe u

variable {k : Type u} [Field k]

/-! ## Abstract: a polynomial extension of a smooth-at-a-point fp domain is smooth at `⊥`

Stated over an abstract `k`-algebra `A` so the heavy concrete `orbitRing M` abbrev is instantiated
**once** at the call site (avoiding the `whnf` blowup the thread-16/17 C3 keystones hit). -/

/-- **`Smooth k (Localization.Away (C g))` for a smooth `Away g`.** For a `k`-algebra `A`, an
element `g : A` with `Algebra.Smooth k (Localization.Away g)`, the polynomial extension localized at
the
constant `C g` is smooth: `MvPolynomial (Fin n) k ⊗_k Away g` is smooth (tensor of two smooth
`k`-algebras), `≃ₐ[k] Away (1 ⊗ g)` (C3 keystone `schurTensorAwayAlgEquiv`), carried to
`Away (algebraMap A (MvPolynomial (Fin n) A) g) = Away (C g)` across
`S ⊗_k A ≃ₐ[k] MvPolynomial (Fin n) A`. -/
theorem smooth_localizationAway_C_of_smooth_localizationAway {A : Type u} [CommRing A]
    [Algebra k A] (g : A) (n : ℕ)
    (hg : Algebra.Smooth k (Localization.Away g)) :
    Algebra.Smooth k
      (Localization.Away (algebraMap A (MvPolynomial (Fin n) A) g)) := by
  let S := MvPolynomial (Fin n) k
  -- `Smooth k (S ⊗_k Away g)`: tensor of two smooth `k`-algebras.
  haveI hgloc : Algebra.Smooth k (Localization.Away g) := hg
  haveI hSsmooth : Algebra.Smooth k S := ⟨inferInstance, inferInstance⟩
  haveI hSAg : Algebra.Smooth S (S ⊗[k] Localization.Away g) :=
    Algebra.Smooth.baseChange k (Localization.Away g) S
  haveI hkSAg : Algebra.Smooth k (S ⊗[k] Localization.Away g) :=
    Algebra.Smooth.comp k S (S ⊗[k] Localization.Away g)
  -- `Smooth k (Away (1 ⊗ g))` in `S ⊗_k A` (the C3 keystone `schurTensorAwayAlgEquiv`).
  haveI hAway1g : Algebra.Smooth k (Localization.Away
      (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g)) :=
    Algebra.Smooth.of_equiv (schurTensorAwayAlgEquiv (S := S) g)
  -- `S ⊗_k A ≃ₐ[k] MvPolynomial (Fin n) A` (comm to `A ⊗_k S`, then `algebraTensorAlgEquiv`).
  let e₁ : S ⊗[k] A ≃ₐ[k] MvPolynomial (Fin n) A :=
    (Algebra.TensorProduct.comm k S A).trans
      ((algebraTensorAlgEquiv k A (σ := Fin n)).restrictScalars k)
  -- the localized element `1 ⊗ g` carries to `C g = algebraMap A (MvPolynomial (Fin n) A) g`.
  have hval : e₁ (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g)
      = algebraMap A (MvPolynomial (Fin n) A) g := by
    change (algebraTensorAlgEquiv k A (σ := Fin n))
        ((Algebra.TensorProduct.comm k S A) (Algebra.TensorProduct.includeRight g)) = _
    rw [Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.comm_tmul,
      algebraTensorAlgEquiv_tmul, map_one, Algebra.smul_def, mul_one]
  -- transport `Smooth k (Away (1 ⊗ g))` across `e₁` (banked C3 transport, `e := e₁.symm`).
  rw [← hval]
  exact smooth_localizationAway_symm_of_smooth_localizationAway k e₁.symm
    (Algebra.TensorProduct.includeRight (R := k) (A := S) (B := A) g) hAway1g

/-- **A polynomial extension of an fp domain smooth at a prime is smooth at `⊥`.** For a
finitely-presented `k`-algebra **domain** `A` that is `Algebra.IsSmoothAt k m₀` at some prime, the
polynomial ring `MvPolynomial (Fin n) A` (a domain, fp over `k`) is `Algebra.IsSmoothAt k ⊥`: a
smooth basic open `Away g` of `A` (`IsSmoothAt.exists_notMem_smooth`, `g ≠ 0`) localizes the
polynomial ring at `C g ≠ 0` to a smooth ring
(`smooth_localizationAway_C_of_smooth_localizationAway`); `⊥` lies in the basic open of `C g`, so
the basic-open bridge gives `IsSmoothAt k ⊥`. -/
theorem isSmoothAt_bot_mvPolynomial_of_isSmoothAt {A : Type u} [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FinitePresentation k A] (n : ℕ)
    (m₀ : Ideal A) [m₀.IsPrime] (hm₀ : Algebra.IsSmoothAt k m₀) :
    haveI : Algebra.FinitePresentation k (MvPolynomial (Fin n) A) :=
      Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := k) (A := A) (Fin n)
    Algebra.IsSmoothAt k (⊥ : Ideal (MvPolynomial (Fin n) A)) := by
  haveI : Algebra.IsSmoothAt k m₀ := hm₀
  haveI : Algebra.FinitePresentation k (MvPolynomial (Fin n) A) :=
    Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := k) (A := A) (Fin n)
  -- a smooth basic open `Away g` of `A`, `g ∉ m₀` ⟹ `g ≠ 0` (the domain `A`, `⊥ ≤ m₀`).
  obtain ⟨g, hg_mem, hg_smooth⟩ := Algebra.IsSmoothAt.exists_notMem_smooth k m₀
  have hg0 : g ≠ 0 := fun h ↦ hg_mem (h ▸ m₀.zero_mem)
  -- `Smooth k (Away (C g))`.
  have hsmoothCg : Algebra.Smooth k
      (Localization.Away (algebraMap A (MvPolynomial (Fin n) A) g)) :=
    smooth_localizationAway_C_of_smooth_localizationAway g n hg_smooth
  -- `C g ≠ 0` in the domain `MvPolynomial (Fin n) A`.
  have hCg0 : algebraMap A (MvPolynomial (Fin n) A) g ≠ 0 := by
    rw [MvPolynomial.algebraMap_eq]
    exact fun h ↦ hg0 (MvPolynomial.C_injective (Fin n) A (by rw [h, map_zero]))
  -- `⊥` lies in the basic open of `C g`; the basic-open bridge gives `⊥ ∈ smoothLocus`, i.e.
  -- `IsSmoothAt k ⊥`.
  have hmem : (⟨(⊥ : Ideal (MvPolynomial (Fin n) A)), inferInstance⟩ : PrimeSpectrum _)
      ∈ Algebra.smoothLocus k (MvPolynomial (Fin n) A) := by
    refine (Algebra.basicOpen_subset_smoothLocus_iff_smooth (R := k)
      (A := MvPolynomial (Fin n) A) (f := algebraMap A (MvPolynomial (Fin n) A) g)).mpr
      hsmoothCg ?_
    simp only [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen]
    exact fun h ↦ hCg0 (by simpa [Ideal.mem_bot] using h)
  exact hmem

/-! ## The orbit-times-affine coordinate ring is a smooth fp domain -/

variable {N : ℕ}

/-- `MvPolynomial η (orbitRing M)` is a **domain** (`η` arbitrary): `orbitRing M` is a domain over
an algebraically closed field, and a polynomial ring over a domain is a domain. -/
instance isDomain_mvPolynomial_orbitRing [IsAlgClosed k] {d' : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d') (η : Type u) :
    IsDomain (MvPolynomial η (orbitRing M)) :=
  inferInstance

/-- `MvPolynomial (Fin n) (orbitRing M)` is **finitely presented** over `k`: `orbitRing M` is fp
over `k` (`orbitRing_finitePresentation`) and `MvPolynomial (Fin n)` is fp over its base
(`mvPolynomial_of_finitePresentation`). -/
instance finitePresentation_mvPolynomial_orbitRing {d' : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d') (n : ℕ) :
    Algebra.FinitePresentation k (MvPolynomial (Fin n) (orbitRing M)) :=
  Algebra.FinitePresentation.mvPolynomial_of_finitePresentation (R := k) (A := orbitRing M) (Fin n)

/-- **The orbit-times-affine ring is smooth at a prime.** `MvPolynomial (Fin n) (orbitRing M)` is
`Algebra.IsSmoothAt k ⊥` (its generic point): the orbit ring is an fp domain smooth at its
normal-form point (`isSmoothAt_normalFormIdeal`), and the abstract polynomial-extension lemma
`isSmoothAt_bot_mvPolynomial_of_isSmoothAt` lifts that to smoothness at the generic point of the
polynomial extension (one heavy-ring instantiation). -/
theorem exists_isSmoothAt_mvPolynomial_orbitRing [IsAlgClosed k] {d' : Fin (N + 1) → ℕ}
    (M : Tuple (k := k) d') (n : ℕ) :
    ∃ (m : Ideal (MvPolynomial (Fin n) (orbitRing M))) (_ : m.IsPrime),
      Algebra.IsSmoothAt k m :=
  ⟨⊥, inferInstance,
    isSmoothAt_bot_mvPolynomial_of_isSmoothAt n (normalFormIdeal M) (isSmoothAt_normalFormIdeal M)⟩

/-! ## The dimension-correct C2(a) consumer -/

/-- ⚠ **HISTORICAL SCAFFOLDING — do NOT use as a reduction.** This was the dimension-CORRECTED C2(a)
shape (fixing the dimensionally-impossible bare-`orbitRing` consumer
`isSmoothAt_sweepFibre_of_component_orbitSmooth`), taking
`e : sweepFibreRing ⧸ I ≃ₐ[k] MvPolynomial (Fin n) (orbitRing M)` with `M` a *shifted* orbit over
`d − r`. But that iso is **globally false / unreachable in this shape** (thread-24 finding,
Codex-confirmed): the only chart-supported identification is *localized* and puts the polynomial
wrapper on the FIBRE side with the FULL-`d` orbit, not the shifted orbit on the orbit side; the
shifted-orbit product form `(A) ≅ (C) × A^δ` would need a separate denominator-free fibre
normal-form theorem (cancellation `R[x] ≅ S[y] ⇏ R ≅ S[…]` is invalid). So the hypothesis `e` is
unsatisfiable in this shape; the theorem is **valid but vacuous in practice**.

**SUPERSEDED** by the direct domain argument
`Core.FibreComponentOrbitTransport.isSmoothAt_sweepFibre_topComponent`: smoothness is **fully
unconditional** with no `e`. The genuine reachable variety identification (LOCALIZED) is
`Core.FibreComponentOrbitIso.schurComponent_chartQuotientEquiv` and its documented residual. Kept
for the honest record; do not build a reduction to this. -/
@[deprecated "superseded by isSmoothAt_sweepFibre_topComponent (direct fp-domain route); \
hypothesis iso is globally unsatisfiable — historical scaffolding, do not use"
  (since := "2026-06-26")]
theorem isSmoothAt_sweepFibre_of_component_orbitPolyEquiv [IsAlgClosed k]
    {d' : Fin (N + 1) → ℕ} (d : Fin (N + 2) → ℕ) (r : ℕ)
    (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq)) [I.IsPrime]
    (hImin : I ∈ minimalPrimes (sweepFibreRing k d r hp hq))
    (M : Tuple (k := k) d') (n : ℕ)
    (e : (sweepFibreRing k d r hp hq ⧸ I) ≃ₐ[k] MvPolynomial (Fin n) (orbitRing M)) :
    Algebra.IsSmoothAt k I := by
  obtain ⟨m, _, hm⟩ := exists_isSmoothAt_mvPolynomial_orbitRing M n
  exact isSmoothAt_minimalPrime_of_componentEquiv_domain k I hImin e m hm

/-! ## The sigma-side labeled component ↔ orbit-closure iso (UNCONDITIONAL)

The first genuine "label a component by an orbit": at the **sigma** end of the count chain (the
closed locus `Σ̄^r`, ambient `RepCoord d`), a top-dimensional component IS the coordinate ring of a
Kostant orbit closure — *with no affine factor*, because the C-part `δ` lives only on the fibre side
of the chart, not on `Σ̄^r`. This is the labeled target the eventual fibre→sigma transport lands in;
it is built here unconditionally (the θ-count chain's labeled sigma facts already exist), and it
confirms the dimension story: sigma component `≅ orbitRing M` (exact), fibre component
`≅ MvPolynomial η (orbitRing M)` (orbit `×` `A^δ`). -/

/-- On a Kostant partition, `partitionIdeal d r m = orbitIdeal (realizerD m)` — the realizer's
rank-locus vanishing ideal equals its orbit vanishing ideal
(`vanishingIdeal_orbitRankLocus_eq_orbitSet`). So the partition ideal quotient is `orbitRing
(realizerD m)` after this rewrite. -/
theorem partitionIdeal_eq_orbitIdeal_realizerD [Infinite k] {d : Fin (N + 1) → ℕ} {r : ℕ}
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    partitionIdeal (k := k) d r m = orbitIdeal (realizerD (k := k) hm) := by
  rw [partitionIdeal_of_mem hm, orbitIdeal, vanishingIdeal_orbitRankLocus_eq_orbitSet]

/-- **The sigma-component ↔ orbit-closure `k`-algebra iso (UNCONDITIONAL).** For a top-dimensional
minimal prime `q` of the `Σ̄^r` coordinate ring
`O(Σ̄^r) = MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r`, there is a **corner-`r` Kostant
partition** `m` and a `k`-algebra isomorphism

> `(MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r) ⧸ q  ≃ₐ[k]  orbitRing (realizerD m)`.

Built from the labeled sigma facts of the θ-count chain (all unconditional): `q` comaps to a
`quotTopDimSet (sigmaIdeal)` member (`bijOn_comap_quotTopDimSet`), which is a `topComponents` member
(`quotTopDimSet_sigma_eq_topComponents`), recovered as `partitionIdeal d r m` for a corner-`r`
Kostant `m` (`exists_kostantPartition_partitionIdeal_eq_of`, `cCodim_zero_strict`); the third
isomorphism theorem (`quotQuotEquivQuotOfLEₐ`) identifies the double quotient with
`R ⧸ (q.comap (mk)) = R ⧸ partitionIdeal m`, and `partitionIdeal m = orbitIdeal (realizerD m)`
(`partitionIdeal_eq_orbitIdeal_realizerD`) makes that `orbitRing (realizerD m)`.

**No affine factor here** — the sigma component is exactly an orbit ring, unlike the fibre component
(`isSmoothAt_sweepFibre_of_component_orbitPolyEquiv`'s `MvPolynomial η (orbitRing M)`). -/
theorem exists_sigma_topComponent_orbitRingEquiv [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty)
    (q : Ideal (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r))
    (hq : q ∈ TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)) :
    ∃ (m : Fin (N + 1) × Fin (N + 1) → ℕ) (hm : m ∈ kostantPartitions d r),
      Nonempty (((MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r) ⧸ q)
        ≃ₐ[k] orbitRing (realizerD (k := k) hm)) := by
  -- `q` comaps to a `quotTopDimSet (sigmaIdeal) = topComponents` member.
  have hqmem : q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))
      ∈ quotTopDimSet (sigmaIdeal (k := k) d r) :=
    (bijOn_comap_quotTopDimSet (sigmaIdeal (k := k) d r)).1 hq
  have hqtop : q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))
      ∈ topComponents (k := k) d r h := by
    rw [← quotTopDimSet_sigma_eq_topComponents d r h]; exact hqmem
  -- recover `comap q = partitionIdeal m` for a corner-`r` Kostant partition `m`.
  obtain ⟨m, hm, hmeq⟩ := exists_kostantPartition_partitionIdeal_eq_of
    (fun he he' hlt ↦ cCodim_zero_strict he he' hlt) d r h
    (q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))) hqtop
  refine ⟨m, hm, ⟨?_⟩⟩
  haveI hqp : q.IsPrime := isPrime_of_mem_topDimMinPrimes hq
  haveI hcp : (q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))).IsPrime :=
    Ideal.comap_isPrime _ q
  -- `sigmaIdeal ≤ comap q` (kernel of `mk`) and `q = (comap q).map (mkₐ)`.
  have hle : sigmaIdeal (k := k) d r ≤ q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r)) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact zero_mem q
  have hmap : (q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))).map
      (Ideal.Quotient.mkₐ k (sigmaIdeal (k := k) d r)) = q := by
    change (q.comap (Ideal.Quotient.mk (sigmaIdeal (k := k) d r))).map
        (Ideal.Quotient.mk (sigmaIdeal (k := k) d r)) = q
    exact Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  -- assemble: `(R⧸Iσ)⧸q ≃ (R⧸Iσ)⧸((comap q).map mkₐ) ≃ R⧸(comap q) ≃ R⧸orbitIdeal = orbitRing`.
  refine ((Ideal.quotientEquivAlgOfEq k hmap.symm).trans
    (DoubleQuot.quotQuotEquivQuotOfLEₐ k hle)).trans ?_
  exact Ideal.quotientEquivAlgOfEq k
    (by rw [← hmeq, partitionIdeal_eq_orbitIdeal_realizerD hm])

end DLNFibre.Core
