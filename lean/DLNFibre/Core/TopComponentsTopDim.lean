/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopDimMinPrimesBridge
import DLNFibre.Core.ThetaComponentCount
import DLNFibre.Core.SigmaCodim
import DLNFibre.Core.CThetaShiftCount

/-!
# `DLNFibre.Core.TopComponentsTopDim` — `Σ̄^r` top components ↔ `TopDimMinPrimes (O(Σ̄^r))`

The DLN wire connecting the LANDED height-based `Σ̄^r` top-component count
(`Core.ThetaComponentCount.topComponents`, counted by `numTop_eq_ncard_topComponents` and
`ncard_topComponents_sigma_eq_cTheta_dminus`) to the dimension-based `Core.TopDimMinPrimes` on the
**coordinate ring** `O(Σ̄^r) = MvPolynomial (RepCoord d) k ⧸ sigmaIdeal d r`. The quotient
minimal-prime bijection `comap (Quotient.mk)` carries `TopDimMinPrimes (O(Σ̄^r))` onto
`topComponents d r h`, because:

* `(sigmaIdeal d r).height = (cCodim d r h).toNat` (the geometric codimension `=` `C`, two LANDED
  bridges: `codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal` +
  `codimRepCanonical_productRankLocusLE_eq_cCodim_enat`), so the `topComponents` predicate
  `p.height = (cCodim).toNat` is exactly `p.height = (sigmaIdeal).height`;
* on a minimal prime, `p.height = (sigmaIdeal).height ↔ ringKrullDim (R ⧸ p) = ringKrullDim (R ⧸
  sigmaIdeal)` (`Core.TopDimMinPrimesBridge.ringKrullDim_quotient_eq_iff_height_eq`);
* and `ringKrullDim ((R ⧸ I) ⧸ P) = ringKrullDim (R ⧸ comap P)` via the third isomorphism theorem.

Conclusion:

> **`ncard_topDimMinPrimes_sigma_eq_cTheta_dminus`** — over `[IsAlgClosed k] [CharZero k]`, for
> weakly-increasing `d` with `r ≤ d k`, `(TopDimMinPrimes (O(Σ̄^r))).ncard = cTheta (d − r)`.

This is the entry point of the chart transport on the count side: the next steps invert `detΔ`
(unit), pass through the chart `e`, strip the Schur polynomial extension
(`Core.TopDimMinPrimesPoly`), and land on the fibre coordinate ring.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-! ## The double-quotient dimension transport -/

/-- **The third isomorphism theorem at `ringKrullDim`.** For a prime `P` of `R ⧸ I`,
`ringKrullDim ((R ⧸ I) ⧸ P) = ringKrullDim (R ⧸ Ideal.comap (Quotient.mk I) P)` via
`DoubleQuot.quotQuotEquivQuotOfLE` (`P = (comap P).map (mk I)`, `I ≤ comap P`). -/
theorem ringKrullDim_doubleQuot_eq {R : Type*} [CommRing R] (I : Ideal R)
    (P : Ideal (R ⧸ I)) :
    ringKrullDim ((R ⧸ I) ⧸ P) = ringKrullDim (R ⧸ (P.comap (Ideal.Quotient.mk I))) := by
  have hle : I ≤ P.comap (Ideal.Quotient.mk I) := by
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact zero_mem P
  have hmapeq : (P.comap (Ideal.Quotient.mk I)).map (Ideal.Quotient.mk I) = P :=
    Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective P
  have key := ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hle)
  rw [hmapeq] at key
  exact key

/-! ## `(sigmaIdeal d r).height = (cCodim d r h).toNat` -/

/-- **The aggregate ideal's height is `C`.** `(sigmaIdeal d r).height = (cCodim d r h).toNat`:
chaining `codimRepCanonical Σ̄^r = (sigmaIdeal).height` (`Core.SigmaCodim`) with
`codimRepCanonical Σ̄^r = (cCodim).toNat` (`Core.SigmaCodim`, Brick A `ℕ∞`). -/
theorem height_sigmaIdeal_eq_cCodim [IsAlgClosed k] [CharZero k] (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    (sigmaIdeal (k := k) d r).height = ((cCodim d r h).toNat : ℕ∞) := by
  rw [← codimRepCanonical_productRankLocusLE_eq_height_sigmaIdeal,
    codimRepCanonical_productRankLocusLE_eq_cCodim_enat d r h]

/-! ## The top-component ↔ `TopDimMinPrimes` bijection on the coordinate ring -/

/-- **The `Σ̄^r` top-component count equals the `TopDimMinPrimes` count of the coordinate ring.**
`comap (Quotient.mk (sigmaIdeal d r))` is a bijection from `TopDimMinPrimes (O(Σ̄^r))` onto
`topComponents d r h`: the quotient minimal-prime bijection (`Ideal.minimalPrimes_eq_comap`)
restricted to the top-dimensional ones, which are exactly the minimal-height components
(`ringKrullDim_quotient_eq_iff_height_eq` + `height_sigmaIdeal_eq_cCodim`). The `sigmaIdeal` is
proper (`Σ̄^r` nonempty — the realizer of a Kostant partition lies in it). -/
theorem ncard_topComponents_eq_ncard_topDimMinPrimes_sigma [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    (topComponents (k := k) d r h).ncard
      = (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard := by
  set R := MvPolynomial (RepCoord d) k
  set I := sigmaIdeal (k := k) d r with hI
  -- `I` is proper: `Σ̄^r` is nonempty (the realizer of a Kostant partition), so its ideal `≠ ⊤`.
  obtain ⟨m₀, hm₀⟩ := id h
  have hIne : I ≠ ⊤ := by
    rw [hI, sigmaIdeal]
    refine vanishingIdeal_ne_top_of_nonempty ?_
    exact ⟨canonicalCoord d (realizerD (k := k) hm₀),
      ⟨realizerD (k := k) hm₀,
        orbitRankLocus_subset_productRankLocusLE d (rank_mult_realizerD hm₀).le
          (self_mem_orbitRankLocus _), rfl⟩⟩
  have hheight := height_sigmaIdeal_eq_cCodim (k := k) d r h
  -- `comap (mk I)` is the bijection `TopDimMinPrimes (R ⧸ I) → topComponents`
  symm
  have hinj : Set.InjOn (Ideal.comap (Ideal.Quotient.mk I))
      (TopDimMinPrimes (R ⧸ I)) := fun P _ P' _ hPP' ↦
    Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective hPP'
  refine hinj.ncard_image ▸ ?_
  · -- the image is exactly `topComponents`
    congr 1
    ext q
    constructor
    · -- `q = comap (mk I) P` for `P ∈ TopDimMinPrimes (R ⧸ I)`
      rintro ⟨P, ⟨hPmin, hPdim⟩, rfl⟩
      -- `comap (mk I) P ∈ I.minimalPrimes`
      have hqmin : P.comap (Ideal.Quotient.mk I) ∈ I.minimalPrimes := by
        rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hPmin, rfl⟩
      refine ⟨hqmin, ?_⟩
      -- top-dim ⟺ height = I.height = cCodim.toNat
      have hbic := (ringKrullDim_quotient_eq_iff_height_eq (k := k) I hIne hqmin).mp ?_
      · rw [hbic, hheight]
      · -- `ringKrullDim (R ⧸ comap P) = ringKrullDim (R ⧸ I)`
        rw [← ringKrullDim_doubleQuot_eq I P, hPdim]
    · -- `q ∈ topComponents` lifts to `map (mk I) q ∈ TopDimMinPrimes (R ⧸ I)`
      rintro ⟨hqmin, hqheight⟩
      -- `q ∈ I.minimalPrimes`; lift to the quotient's minimal prime `q.map (mk I)`
      have hmem : q ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (R ⧸ I) := by
        rw [← Ideal.minimalPrimes_eq_comap]; exact hqmin
      obtain ⟨P, hPmin, hPq⟩ := hmem
      refine ⟨P, ⟨hPmin, ?_⟩, hPq⟩
      -- top-dim: from `height q = cCodim = I.height` via the biconditional + double-quot transport
      have hqmin' : q ∈ I.minimalPrimes := by
        rw [Ideal.minimalPrimes_eq_comap]; exact ⟨P, hPmin, hPq⟩
      have hbic : q.height = I.height := by rw [hqheight, hheight]
      have hdimq := (ringKrullDim_quotient_eq_iff_height_eq (k := k) I hIne hqmin').mpr hbic
      rw [ringKrullDim_doubleQuot_eq I P, hPq]
      exact hdimq

/-- **The `TopDimMinPrimes` count of `O(Σ̄^r)` is the closed form `cTheta (d − r)`.** Stacks the
top-component ↔ `TopDimMinPrimes` bijection onto the LANDED
`ncard_topComponents_sigma_eq_cTheta_dminus`. The entry point of the chart count transport: the
`Σ̄^r` coordinate-ring side, ready to invert `detΔ` and traverse the chart `e`. -/
theorem ncard_topDimMinPrimes_sigma_eq_cTheta_dminus [IsAlgClosed k] [CharZero k]
    {d : Fin (N + 1) → ℕ} {r : ℕ} (hd : Monotone d) (hr : ∀ k, r ≤ d k)
    (h₀ : (kostantPartitions (dminus d r) 0).Nonempty) (hr' : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard
      = cTheta (dminus d r) := by
  rw [← ncard_topComponents_eq_ncard_topDimMinPrimes_sigma d r hr',
    ncard_topComponents_sigma_eq_cTheta_dminus hd hr h₀ hr']

end DLNFibre.Core
