/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.SmoothPointRegular
import DLNFibre.Core.FibreCodimFinal
import DLNFibre.Core.FibreComponentOrbitTransport
import DLNFibre.Core.RadicalCatenary
import DLNFibre.Core.OrbitTangentCotangent
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

/-!
# `DLNFibre.Core.FibreSmoothBlock` — the smooth-block certificate (the RLCT-runway's first slab)

The **standard-smooth local model** at a smooth closed point of a top-dimensional fibre component:
the local Kähler module `Ω[A_m⁄k]` is **free**, and its rank pins to the **proved** geometric
codimension of the fibre. This is the geometric *upper-bound* local model the future RLCT bridge
will consume.

## The honest statement (rank = ambient − codim, NOT rank = codim)

⚠ For a *smooth* variety `X ⊆ 𝔸^ambient` of dimension `dim X`, the Kähler module `Ω[O_X⁄k]` is
locally free of rank `= dim X = ambient − codim` (the **relative** dimension). The module that is
free of rank `= codim` is the **conormal** module `I/I²` (equivalently `ker`/`coker` of the
Jacobian), a *different* module. This certificate reports the Kähler module `Ω` and pins its free
rank `n` as the complement of the proved codimension:

> `n + codim = ambient`,  i.e.  `rank(Ω) = ambient − codim = dim(component)`.

It does **not** claim `Ω` free of rank `= codim` (that would be the conormal statement) — see the
Codex-vetted fidelity note in the thread.

## Main results

* `free_kaehler_localizationAtPrime_of_isSmoothAt` — generic engine: a finite-type `k`-algebra,
  smooth at a maximal ideal `m`, has `Ω[A_m⁄k]` **free** (projective over a local ring).
* `kaehler_free_and_finrank_add_dim_of_isSmoothAt` — generic engine: at a smooth closed point,
  `Ω[A_m⁄k]` is free of `finrank = n` with `ringKrullDim (A_m) = n` (the relative dimension).
* `fibre_smoothBlock_certificate` — **THE deliverable**: for a top-dimensional component
  `I ∈ TopDimMinPrimes (sweepFibreRing …)` and a smooth closed point `m` of the component ring,
  `Ω[A_m⁄k]` is free of `finrank = n` with `n + codimRepCanonical (fibre d B) =
  Nat.card (RepCoord d)` — the free rank pinned to the proved codim `C + δ`.
* `exists_isSmoothAt_isMaximal_component` — a smooth closed point of the top component **exists**
  (dense smooth locus of an fp domain over alg-closed `k` + Jacobson closed points).

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Algebra MvPolynomial Matrix TensorProduct

universe u

/-! ## The generic engine — Ω free of rank = relative dimension at a smooth closed point -/

section GenericEngine

variable {k : Type*} [Field k] {A : Type*} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- **The local Kähler module is free at a smooth closed point.** For a finite-type `k`-algebra `A`
and a maximal ideal `m` at which `A` is smooth, `Ω[Localization.AtPrime m⁄k]` is a **free** module
over the local ring `Localization.AtPrime m`: smoothness gives `FormallySmooth`, hence projectivity
of the Kähler module; over a local ring a finite projective module is free. (Lifted standalone from
the body of `finrank_cotangentSpace_le_of_isSmoothAt`.) -/
theorem free_kaehler_localizationAtPrime_of_isSmoothAt
    (m : Ideal A) [hm : m.IsMaximal] [Algebra.IsSmoothAt k m] :
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) := by
  set R := Localization.AtPrime m with hR
  haveI : m.IsPrime := hm.isPrime
  haveI : Algebra.FormallySmooth k R := ‹Algebra.IsSmoothAt k m›
  haveI : Module.Finite R (Ω[R⁄k]) := by
    haveI : Algebra.EssFiniteType k R := by
      haveI : Algebra.EssFiniteType A R := .of_isLocalization _ m.primeCompl
      exact .comp _ A _
    exact KaehlerDifferential.finite k R
  haveI : Module.Projective R (Ω[R⁄k]) :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
  haveI : Module.Flat R (Ω[R⁄k]) := Module.Flat.of_projective
  exact Module.free_of_flat_of_isLocalRing

/-- **The smooth-block certificate at a smooth closed point (generic engine).** For a finite-type
`k`-algebra `A` and a maximal ideal `m` at which `A` is smooth, the local Kähler module
`Ω[Localization.AtPrime m⁄k]` is **free**, and there is a natural number `n` (the relative
dimension) with `finrank (A_m) Ω[A_m⁄k] = n` and `ringKrullDim (A_m) = n`. So `Ω` is free of rank
`= ringKrullDim (A_m)` (the local/relative dimension, *not* the codimension). -/
theorem kaehler_free_and_finrank_add_dim_of_isSmoothAt
    (m : Ideal A) [hm : m.IsMaximal] [Algebra.IsSmoothAt k m] :
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧
          ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  haveI : m.IsPrime := hm.isPrime
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  refine ⟨free_kaehler_localizationAtPrime_of_isSmoothAt m, ?_⟩
  -- the standard-smooth chart `S = A[1/f]`, the relative dimension `n`, and `dim A_m = n`.
  obtain ⟨n, f, hf, hss, hrank, hdim⟩ :=
    ringKrullDim_localizationAtPrime_eq_of_isSmoothAt (k := k) (A := A) m
  refine ⟨n, ?_, hdim⟩
  -- the chart is nontrivial (`m` survives in `A[1/f]`, maximal there since `f ∉ m`).
  haveI : (m.map (algebraMap A (Localization.Away f))).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint (S := Localization.Away f) f m hm hf
  haveI : Nontrivial (Localization.Away f) :=
    nontrivial_of_ne (0 : Localization.Away f) 1 fun hzero ↦
      (‹(m.map (algebraMap A (Localization.Away f))).IsMaximal›).ne_top
        (Ideal.eq_top_of_isUnit_mem _
          (hzero ▸ (m.map (algebraMap A (Localization.Away f))).zero_mem) isUnit_one)
  haveI : Algebra.IsStandardSmoothOfRelativeDimension n k (Localization.Away f) := hss
  exact finrank_kaehler_localizationAtPrime_eq m hf hrank

end GenericEngine

/-! ## Local ↔ global dimension at a closed point of a quotient-of-a-quotient

The component ring `sweepFibreRing ⧸ I` is a *double* quotient `(MvPolynomial σ k ⧸ J) ⧸ I`. The
banked local↔global dimension pinning `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype` is
stated for a *single* quotient `MvPolynomial σ k ⧸ I'`; we flatten the double quotient by the third
isomorphism theorem (`DoubleQuot.quotQuotEquivQuotOfLE`) and transport heights along the ring iso
(`RingEquiv.height_map`). -/

section ComponentDimension

variable {k : Type*} [Field k] {σ : Type*} [Finite σ]

omit [Finite σ] in
/-- **Third isomorphism at `ringKrullDim`** (inlined from `TopComponentsTopDim` to keep the import
surface minimal): for a prime `I` of `MvPolynomial σ k ⧸ J`,
`ringKrullDim ((MvPolynomial σ k ⧸ J) ⧸ I) = ringKrullDim (MvPolynomial σ k ⧸ I.comap (mk J))`. -/
theorem ringKrullDim_doubleQuot_mvPoly_eq (J : Ideal (MvPolynomial σ k))
    (I : Ideal (MvPolynomial σ k ⧸ J)) :
    ringKrullDim ((MvPolynomial σ k ⧸ J) ⧸ I)
      = ringKrullDim (MvPolynomial σ k ⧸ (I.comap (Ideal.Quotient.mk J))) := by
  have hle : J ≤ I.comap (Ideal.Quotient.mk J) := fun x hx ↦ by
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact zero_mem I
  have hmapeq : (I.comap (Ideal.Quotient.mk J)).map (Ideal.Quotient.mk J) = I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
  have key := ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)
  rw [hmapeq] at key
  exact key

/-- **Local ↔ global dimension at a smooth closed point of a fibre component (double-quotient
form).** For a prime `J` and a maximal ideal `m` of the double quotient `(MvPolynomial σ k ⧸ J) ⧸ I`
(`I` prime), the local ring `Localization.AtPrime m` has Krull dimension equal to that of the
component ring `(MvPolynomial σ k ⧸ J) ⧸ I`. Flattens the double quotient (third iso) and applies
the banked single-quotient pinning `ringKrullDim_localizationAtPrime_isMaximal_eq_fintype`. -/
theorem ringKrullDim_localizationAtPrime_component_eq
    (J : Ideal (MvPolynomial σ k)) (I : Ideal (MvPolynomial σ k ⧸ J)) [I.IsPrime]
    (m : Ideal ((MvPolynomial σ k ⧸ J) ⧸ I)) [m.IsMaximal] :
    ringKrullDim (Localization.AtPrime m) = ringKrullDim ((MvPolynomial σ k ⧸ J) ⧸ I) := by
  -- `dim (AtPrime m) = m.height` (a maximal ideal of the component domain).
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m)]
  set I' : Ideal (MvPolynomial σ k) := I.comap (Ideal.Quotient.mk J) with hI'
  haveI : I'.IsPrime := Ideal.comap_isPrime _ _
  have hle : J ≤ I' := fun x hx ↦ by
    rw [hI', Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact zero_mem I
  have hmapeq : I'.map (Ideal.Quotient.mk J) = I :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective I
  -- the third-iso ring equiv with LITERAL source `(MvPoly ⧸ J) ⧸ I`:
  -- `e : (MvPoly ⧸ J) ⧸ I ≃ (MvPoly ⧸ J) ⧸ (I'.map (mk J)) ≃ MvPoly ⧸ I'`.
  set e : ((MvPolynomial σ k ⧸ J) ⧸ I) ≃+* (MvPolynomial σ k ⧸ I') :=
    (Ideal.quotEquivOfEq hmapeq.symm).trans (DoubleQuot.quotQuotEquivQuotOfLE hle) with he
  -- transport `m`'s height to its (maximal) image, pin on the single quotient, undo the flatten.
  set m' : Ideal (MvPolynomial σ k ⧸ I') := m.map (e : _ →+* _) with hm'
  haveI : m'.IsMaximal := Ideal.map_isMaximal_of_equiv e
  have hheight : m.height = m'.height := (RingEquiv.height_map e m).symm
  have hpin : m'.height = ringKrullDim (MvPolynomial σ k ⧸ I') :=
    height_eq_ringKrullDim_of_isMaximal_fintype I' m'
  rw [hheight, hpin, ← ringKrullDim_doubleQuot_mvPoly_eq J I]

end ComponentDimension

/-! ## The smooth-block certificate at a top-dimensional fibre component -/

section FibreCertificate

variable {k : Type} [Field k] {N : ℕ}

/-- **The component dimension is the ambient minus the proved codimension.** For a top-dimensional
component `I ∈ TopDimMinPrimes (sweepFibreRing …)`, the Krull dimension of the component ring
`sweepFibreRing ⧸ I` plus the geometric fibre codimension equals the ambient coordinate count:

> `codimRepCanonical (fibre d (normalForm …)) + (ringKrullDim (sweepFibreRing ⧸ I)).unbotD 0
>   = Nat.card (RepCoord d)`.

`I` is top-dimensional, so `ringKrullDim (sweepFibreRing ⧸ I) = ringKrullDim (sweepFibreRing) =
varietyDim (sweepFibre)`; the reducible-locus catenary
(`codimRepCanonical_add_varietyDim_eq_card_of_nonempty`) supplies codim + varietyDim = ambient. -/
theorem codim_add_ringKrullDim_component_eq_card [IsAlgClosed k] [Infinite k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1)) (h : (kostantPartitions d r).Nonempty)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    codimRepCanonical (fibre d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))
        + (ringKrullDim (sweepFibreRing k d r hp hq ⧸ I)).unbotD 0
      = (Nat.card (RepCoord d) : ℕ∞) := by
  -- the reducible-locus catenary: codim + varietyDim (sweepFibre) = ambient.
  have hbridge := codimRepCanonical_add_varietyDim_eq_card_of_nonempty (k := k)
    (d := d) (Z := fibre d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))
    ((fibre_normalForm_nonempty d r hp hq hN h).image (canonicalCoord d))
  -- `varietyDim (sweepFibre) = (ringKrullDim (sweepFibreRing)).unbotD 0` (defeq), and
  -- `ringKrullDim (sweepFibreRing ⧸ I) = ringKrullDim (sweepFibreRing)` (I top-dimensional).
  rwa [show varietyDim (canonicalCoord d ''
        fibre d (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq))
      = (ringKrullDim (sweepFibreRing k d r hp hq ⧸ I)).unbotD 0 from by
    rw [varietyDim, hI.2]] at hbridge

/-- **THE SMOOTH-BLOCK CERTIFICATE (per smooth closed point of a top-dimensional fibre component).**
For a rank-`r` target `B` over an algebraically closed char-`0` field, a top-dimensional component
`I ∈ TopDimMinPrimes (sweepFibreRing …)` of the reduced fibre, and a maximal ideal `m` of the
component ring `A := sweepFibreRing … ⧸ I` at which `A` is smooth (a smooth closed point of the
top-dimensional fibre component), the local Kähler module `Ω[A_m⁄k]` is **free** of finrank `n`,
with

> `n + codimRepCanonical (fibre d B) = Nat.card (RepCoord d)`,

i.e. `rank(Ω) = ambient − codim` — the free rank pinned to the **proved** fibre codimension
`codimRepCanonical (fibre d B) = C + δ` (`C = cCodim d r`, `δ = r·(d_N + d_0 − r)`,
`FibreCodimFinal`). This is the standard-smooth local model the future RLCT bridge consumes.

⚠ The free rank is the **relative dimension** `ambient − codim` (the dimension of the component),
**not** `codim` itself — the module free of rank `= codim` is the conormal `I/I²`, a different
module. See the module docstring. -/
theorem fibre_smoothBlock_certificate [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq))
    (m : Ideal (sweepFibreRing k d r hp hq ⧸ I)) [m.IsMaximal] [Algebra.IsSmoothAt k m] :
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧
          (n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞) := by
  haveI : I.IsPrime := isPrime_of_mem_topDimMinPrimes hI
  -- `N ≥ 1` and the component ring is a finite-type domain over `k`.
  have hN : (0 : Fin (N + 2)) ≠ Fin.last (N + 1) := fun he ↦ by
    simp [Fin.ext_iff, Fin.val_last] at he
  haveI : Algebra.FiniteType k (sweepFibreRing k d r hp hq ⧸ I) := inferInstance
  -- generic engine: Ω free, finrank Ω = n, `ringKrullDim (A_m) = n`.
  obtain ⟨hfree, n, hfinrank, hdimAtPrime⟩ :=
    kaehler_free_and_finrank_add_dim_of_isSmoothAt (k := k) m
  refine ⟨hfree, n, hfinrank, ?_⟩
  -- `ringKrullDim (A_m) = ringKrullDim (component ring)` (local ↔ global at a closed point).
  have hcomp : ringKrullDim (Localization.AtPrime m)
      = ringKrullDim (sweepFibreRing k d r hp hq ⧸ I) :=
    ringKrullDim_localizationAtPrime_component_eq
      (vanishingIdeal k (sweepFibre k d r hp hq)) I m
  -- so `ringKrullDim (component ring) = n`, hence `(ringKrullDim …).unbotD 0 = n`.
  have hdimcomp : ringKrullDim (sweepFibreRing k d r hp hq ⧸ I) = (n : WithBot ℕ∞) := by
    rw [← hcomp, hdimAtPrime]
  have hunbot : (ringKrullDim (sweepFibreRing k d r hp hq ⧸ I)).unbotD 0 = (n : ℕ∞) := by
    rw [hdimcomp]; rfl
  -- the codim + dim = ambient bridge, with `B`'s codim transported to the normal-form codim.
  have hbridge := codim_add_ringKrullDim_component_eq_card d r hp hq hN h I hI
  rw [hunbot] at hbridge
  -- transport the goal's `codim (fibre B)` to `codim (fibre normalForm)` (same-rank invariance).
  rw [codimRepCanonical_fibre_eq_of_rank_eq d hN B
    (normalForm (k := k) (d (Fin.last (N + 1))) (d 0) r hp hq)
    (hB.trans (rank_normalForm _ _ _ hp hq).symm), add_comm]
  exact hbridge

/-! ## A smooth closed point of the top component exists (non-vacuity of the certificate) -/

/-- **A smooth closed point of a top-dimensional fibre component exists.** For a top-dimensional
component `I ∈ TopDimMinPrimes (sweepFibreRing …)`, the component ring `A := sweepFibreRing … ⧸ I`
has a maximal ideal `m` at which `A` is smooth. The component ring is a finitely-presented
`k`-algebra **domain** over the algebraically-closed (perfect) `k`, so its smooth locus is **dense**
(`isSmoothAt_bot_of_finitePresentation_domain` ⟹ `⊥ ∈ smoothLocus`, so it is nonempty) and **open**
(`Algebra.isOpen_smoothLocus`); a nonempty open of a Jacobson spectrum contains a closed point
(`exists_isClosed_singleton_of_isJacobsonRing`), i.e. a maximal ideal — automatically *on the
component*, since we work inside the component ring `A`. This certifies the smooth-block hypothesis
`[Algebra.IsSmoothAt k m]` of `fibre_smoothBlock_certificate` is satisfiable. -/
theorem exists_isSmoothAt_isMaximal_component [IsAlgClosed k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    ∃ m : Ideal (sweepFibreRing k d r hp hq ⧸ I), ∃ _ : m.IsMaximal, Algebra.IsSmoothAt k m := by
  haveI : I.IsPrime := isPrime_of_mem_topDimMinPrimes hI
  set A := sweepFibreRing k d r hp hq ⧸ I with hA
  haveI : IsDomain A := Ideal.Quotient.isDomain I
  haveI : Algebra.FinitePresentation k A :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian I)
  haveI : IsJacobsonRing A := isJacobsonRing_of_finiteType (A := k) (B := A)
  -- `⊥` is a smooth point (an fp domain over alg-closed `k` is generically smooth), so the smooth
  -- locus is a nonempty open of the Jacobson spectrum `Spec A`.
  have hbot : Algebra.IsSmoothAt k (⊥ : Ideal A) := isSmoothAt_bot_of_finitePresentation_domain A
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus k A := hbot
  obtain ⟨x, hx_mem, hx_closed⟩ := PrimeSpectrum.exists_isClosed_singleton_of_isJacobsonRing
    (Algebra.smoothLocus k A) (Algebra.isOpen_smoothLocus) ⟨_, hmem⟩
  haveI : x.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mp hx_closed
  exact ⟨x.asIdeal, ‹_›, hx_mem⟩

/-- **THE SMOOTH-BLOCK CERTIFICATE, closed over the smooth-point input (existence ∘ per-point).**
For a rank-`r` target `B` over an algebraically closed char-`0` field and a top-dimensional
component `I ∈ TopDimMinPrimes (sweepFibreRing …)` of the reduced fibre, there **exists** a smooth
closed point `m` of the component ring at which the local Kähler module `Ω[A_m⁄k]` is **free** of
finrank `n` with `n + codimRepCanonical (fibre d B) = Nat.card (RepCoord d)` — the standard-smooth
local model is realised at a closed point of the dense smooth open of the top-dimensional fibre
component, with the free rank pinned to the proved codim. Composes
`exists_isSmoothAt_isMaximal_component` (a smooth closed point exists) with
`fibre_smoothBlock_certificate` (the per-point free-rank certificate).

⚠ "Closed over the smooth-point hypothesis" discharges the `[Algebra.IsSmoothAt k m]` input — it
does **not** witness that a top component `I` exists (that `TopDimMinPrimes` is nonempty): `I` and
`hI` are still hypotheses. The closed point `m` produced is *some* point of the dense smooth open,
not a prescribed geometric (θ-generic) point — full component-incidence is a separate residual. -/
theorem exists_smoothBlock_certificate [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 2) → ℕ) (r : ℕ) (hp : r ≤ d (Fin.last (N + 1))) (hq : r ≤ d 0)
    (h : (kostantPartitions d r).Nonempty)
    (B : Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) k) (hB : B.rank = r)
    (I : Ideal (sweepFibreRing k d r hp hq))
    (hI : I ∈ TopDimMinPrimes (sweepFibreRing k d r hp hq)) :
    ∃ (m : Ideal (sweepFibreRing k d r hp hq ⧸ I)) (_ : m.IsMaximal),
      Algebra.IsSmoothAt k m ∧
      Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄k]) = n ∧
          (n : ℕ∞) + codimRepCanonical (fibre d B) = (Nat.card (RepCoord d) : ℕ∞) := by
  obtain ⟨m, hm, hsmooth⟩ := exists_isSmoothAt_isMaximal_component d r hp hq I hI
  haveI := hm
  haveI := hsmooth
  exact ⟨m, hm, hsmooth, fibre_smoothBlock_certificate d r hp hq h B hB I hI m⟩

/-! ## Non-vacuity witness for the generic engine -/

/-- The generic engine fires concretely: at any maximal ideal `m` of the affine line
`A = MvPolynomial (Fin 1) ℚ` (smooth at `m`, its smooth locus being everything), `Ω[A_m⁄ℚ]` is free
of finrank `n` with `ringKrullDim (A_m) = n` (here `n = 1`, the dimension of the line). A concrete
satisfiable instance of `kaehler_free_and_finrank_add_dim_of_isSmoothAt`. -/
example (m : Ideal (MvPolynomial (Fin 1) ℚ)) [m.IsMaximal] :
    Module.Free (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄ℚ]) ∧
      ∃ n : ℕ,
        Module.finrank (Localization.AtPrime m) (Ω[Localization.AtPrime m⁄ℚ]) = n ∧
          ringKrullDim (Localization.AtPrime m) = (n : WithBot ℕ∞) := by
  haveI : m.IsPrime := ‹m.IsMaximal›.isPrime
  haveI : Algebra.IsSmoothAt ℚ m := by
    have h : Algebra.smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) = Set.univ :=
      Algebra.smoothLocus_eq_univ
    have : (⟨m, ‹_›⟩ : PrimeSpectrum _) ∈ Algebra.smoothLocus ℚ (MvPolynomial (Fin 1) ℚ) := by
      rw [h]; trivial
    exact this
  exact kaehler_free_and_finrank_add_dim_of_isSmoothAt m

end FibreCertificate

end DLNFibre.Core

