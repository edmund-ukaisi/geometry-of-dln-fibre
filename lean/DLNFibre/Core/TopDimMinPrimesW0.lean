/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.TopDimMinPrimesRadical
import DLNFibre.Core.ClosureBridge
import DLNFibre.Core.CCodimCornerMono
import DLNFibre.Core.CCodimZeroStrict

/-!
# `DLNFibre.Core.TopDimMinPrimesW0` — the W0 indexing bridge (closed `≤ r` ↔ exact `= r`)

The W0 rung of the fibre-`θ` count transport (expedition `theta-components`, thread 09): the
**closed** rank-`≤ r` locus ideal `sigmaIdeal d r` and the **exact** rank-`= r` locus ideal
`vanishingIdeal (canonicalCoord d '' productRankLocus d r)` carry the **same** top-dimensional
minimal-prime count.

The mechanism is a `quotTopDimSet` set-equality (`Core.TopDimMinPrimesRadical`): both quotient
counts equal `(quotTopDimSet ·).ncard`, so it suffices to show the two ideals select the same
top-dimensional minimal primes. Write `Ile := sigmaIdeal d r` (closed, `rank ≤ r`) and
`Ieq := vanishingIdeal (canonicalCoord d '' productRankLocus d r)` (exact, `rank = r`). Both have
height `C := (cCodim d r h).toNat` (`Core.TopComponentsTopDim.height_sigmaIdeal_eq_cCodim` and the
definitional `Ieq.height = codimRepCanonical (productRankLocus d r) = C` from
`Core.ClosureBridge.codimRepCanonical_productRankLocus_eq_cCodim_enat`), and `Ile ≤ Ieq`
(anti-monotone `vanishingIdeal` against `Σ^r ⊆ Σ̄^r`). On a minimal prime the top-dimensional
predicate is `height = C` (`ringKrullDim_quotient_eq_iff_height_eq`), so:

* **`Ieq` top-dim minimal prime `q` ⟹ `Ile` top-dim**: `Ile ≤ Ieq ≤ q` and
  `q.height = C = Ile.height`, so `Ideal.mem_minimalPrimes_of_height_eq` puts `q` in
  `Ile.minimalPrimes`.
* **`Ile` top-dim minimal prime `q` ⟹ `Ieq` top-dim**: `q ∈ topComponents`, so the recovery
  `Core.CCodimCornerMono.exists_kostantPartition_partitionIdeal_eq_of` (strict corner-monotonicity
  discharged by `Core.CCodimZeroStrict.cCodim_zero_strict`) writes `q` as the orbit ideal of a
  corner-`r` realizer; the realizer orbit sits in `Σ^r`, so `Ieq ≤ q`, and
  `q.height = C = Ieq.height` gives `q ∈ Ieq.minimalPrimes`.

> **`ncard_topDimMinPrimes_sigma_eq_sweepSigma`** — the closed and exact loci have equal
> top-dimensional minimal-prime counts.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open MvPolynomial

universe u

variable {k : Type u} [Field k] {N : ℕ}

/-- **`Ieq ≤ P` (the free per-component containment, over `Fin (N+1)`).** The vanishing ideal `Ieq`
of `Σ^r = canonicalCoord d '' productRankLocus d r` is contained in the orbit-rank-locus ideal of a
corner-`r` realizer `M₀`: the realizer's orbit sits in `Σ^r`
(`orbitAsTuples_realizerD_subset_productRankLocus`), and the orbit-rank locus is `vanishingIdeal`-
equivalent to the orbit (`vanishingIdeal_orbitRankLocus_eq_orbitSet`), so anti-monotonicity of
`vanishingIdeal` against `orbitSet M₀ ⊆ Σ^r` gives the containment. The `Fin (N+1)` analogue of
`Core.SourceNoDrop.vanishingIdeal_sweepSigma_le_orbitRankLocus`. -/
theorem vanishingIdeal_productRankLocus_le_orbitRankLocus [Infinite k]
    (d : Fin (N + 1) → ℕ) (r : ℕ)
    {m : Fin (N + 1) × Fin (N + 1) → ℕ} (hm : m ∈ kostantPartitions d r) :
    (vanishingIdeal k (canonicalCoord d '' productRankLocus (k := k) d r) :
        Ideal (MvPolynomial (RepCoord d) k))
      ≤ MvPolynomial.vanishingIdeal (σ := RepCoord d) (K := k) k
          (canonicalCoord d '' orbitRankLocus (realizerD (k := k) hm)) := by
  rw [vanishingIdeal_orbitRankLocus_eq_orbitSet]
  have hsub : orbitSet (realizerD (k := k) hm)
      ⊆ canonicalCoord d '' productRankLocus (k := k) d r := by
    rw [← image_orbitAsTuples]
    exact Set.image_mono (orbitAsTuples_realizerD_subset_productRankLocus hm)
  exact MvPolynomial.vanishingIdeal_anti_mono hsub

/-! ## The three `quotTopDimSet` set equalities

The content of the W0 bridge is a set equality of top-dimensional minimal primes; the `ncard`
equality is a one-line corollary. We name three set equalities, all on `R = MvPolynomial (RepCoord
d) k`: the closed-locus `quotTopDimSet` `=` `topComponents` (`Σ̄^r`-side), the closed `=` exact
`quotTopDimSet` (the genuine W0 content), and the exact-locus `quotTopDimSet` `=` `topComponents`
(the form the W1 keystone application consumes). -/

/-- **`quotTopDimSet (sigmaIdeal) = topComponents`.** The dimension-based top-dimensional minimal
primes of the closed-locus ideal are exactly the height-based top components: on a minimal prime
`q`, `ringKrullDim (R ⧸ q) = ringKrullDim (R ⧸ sigmaIdeal)` iff `q.height = sigmaIdeal.height = C`
(`ringKrullDim_quotient_eq_iff_height_eq` + `height_sigmaIdeal_eq_cCodim`). Both sides are
`{q ∈ sigmaIdeal.minimalPrimes | <top-dim predicate>}`. -/
theorem quotTopDimSet_sigma_eq_topComponents [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    quotTopDimSet (sigmaIdeal (k := k) d r) = topComponents (k := k) d r h := by
  set R := MvPolynomial (RepCoord d) k
  set Ile : Ideal R := sigmaIdeal (k := k) d r with hIle
  have hIleHt : Ile.height = ((cCodim d r h).toNat : ℕ∞) :=
    height_sigmaIdeal_eq_cCodim (k := k) d r h
  -- `Ile` is proper (the realizer of a Kostant partition lies in `Σ̄^r`)
  have hIlene : Ile ≠ ⊤ := by
    rw [hIle, sigmaIdeal]
    refine vanishingIdeal_ne_top_of_nonempty ?_
    exact (nonempty_image_productRankLocus d r h).mono
      (Set.image_mono (productRankLocus_subset_productRankLocusLE d r))
  ext q
  simp only [quotTopDimSet, topComponents, Set.mem_setOf_eq]
  refine and_congr_right fun hqmin ↦ ?_
  rw [ringKrullDim_quotient_eq_iff_height_eq Ile hIlene hqmin, hIleHt]

/-- **`quotTopDimSet (sigmaIdeal) = quotTopDimSet (vanishingIdeal Σ^r)` — the W0 bridge content.**
The closed rank-`≤ r` locus ideal and the exact rank-`= r` locus ideal select the same
top-dimensional minimal primes. Both have height `C`; `Ile ≤ Ieq` (anti-monotone `vanishingIdeal`
against `Σ^r ⊆ Σ̄^r`); the easy direction is `Ile ≤ Ieq ≤ q` + `mem_minimalPrimes_of_height_eq`, the
hard direction recovers `q` as a corner-`r` realizer's orbit ideal (so `Ieq ≤ q`) via
`exists_kostantPartition_partitionIdeal_eq_of` (strict corner-monotonicity from
`cCodim_zero_strict`) and again `mem_minimalPrimes_of_height_eq`. -/
theorem quotTopDimSet_sigma_eq_sweepSigma [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    quotTopDimSet (sigmaIdeal (k := k) d r)
      = quotTopDimSet
          (vanishingIdeal k (canonicalCoord d '' productRankLocus (k := k) d r)) := by
  set R := MvPolynomial (RepCoord d) k
  set C : ℕ := (cCodim d r h).toNat with hC
  set Ile : Ideal R := sigmaIdeal (k := k) d r with hIle
  set Ieq : Ideal R :=
    vanishingIdeal k (canonicalCoord d '' productRankLocus (k := k) d r) with hIeq
  -- both ideals have height `C`
  have hIleHt : Ile.height = (C : ℕ∞) := height_sigmaIdeal_eq_cCodim (k := k) d r h
  have hIeqHt : Ieq.height = (C : ℕ∞) := by
    rw [hIeq, hC, ← codimRepCanonical_productRankLocus_eq_cCodim_enat (k := k) d r h,
      codimRepCanonical, codimRep]
  -- `Ile ≤ Ieq` (anti-monotone `vanishingIdeal` against `Σ^r ⊆ Σ̄^r`)
  have hsub : Ile ≤ Ieq := by
    rw [hIle, hIeq, sigmaIdeal]
    exact MvPolynomial.vanishingIdeal_anti_mono
      (Set.image_mono (productRankLocus_subset_productRankLocusLE d r))
  -- `Ile`, `Ieq` are proper (the realizer of a Kostant partition lies in `Σ^r ⊆ Σ̄^r`)
  have hIeqne : Ieq ≠ ⊤ := by
    rw [hIeq]
    exact vanishingIdeal_ne_top_of_nonempty (nonempty_image_productRankLocus d r h)
  have hIlene : Ile ≠ ⊤ := ne_top_of_le_ne_top hIeqne hsub
  ext q
  simp only [quotTopDimSet, Set.mem_setOf_eq]
  constructor
  · -- HARD direction: `Ile` top-dim minimal prime `q` ⟹ `Ieq` top-dim
    rintro ⟨hqmin, hqdim⟩
    -- convert the dim predicate to `q.height = Ile.height = C`
    have hqht : q.height = (C : ℕ∞) := by
      rw [← hIleHt]; exact (ringKrullDim_quotient_eq_iff_height_eq Ile hIlene hqmin).mp hqdim
    -- `q ∈ topComponents`: recover it as the orbit ideal of a corner-`r` realizer
    have hqtop : q ∈ topComponents (k := k) d r h := by
      refine ⟨hqmin, ?_⟩
      rw [hqht, hC]
    obtain ⟨m, hmem, hmeq⟩ := exists_kostantPartition_partitionIdeal_eq_of
      (fun he he' hlt ↦ cCodim_zero_strict he he' hlt) d r h q hqtop
    -- `Ieq ≤ q`: the realizer orbit sits in `Σ^r`
    have hIeqle : Ieq ≤ q := by
      rw [← hmeq, partitionIdeal_of_mem hmem]
      exact vanishingIdeal_productRankLocus_le_orbitRankLocus d r hmem
    -- `q ∈ Ieq.minimalPrimes` (height-equal containment)
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
    haveI : (q : Ideal R).FiniteHeight :=
      ⟨Or.inr (by rw [hqht]; exact ENat.coe_ne_top C)⟩
    have hqEqmin : q ∈ Ieq.minimalPrimes :=
      Ideal.mem_minimalPrimes_of_height_eq hIeqle (by rw [hqht, hIeqHt])
    refine ⟨hqEqmin, ?_⟩
    exact (ringKrullDim_quotient_eq_iff_height_eq Ieq hIeqne hqEqmin).mpr (by rw [hqht, hIeqHt])
  · -- EASY direction: `Ieq` top-dim minimal prime `q` ⟹ `Ile` top-dim
    rintro ⟨hqmin, hqdim⟩
    have hqht : q.height = (C : ℕ∞) := by
      rw [← hIeqHt]; exact (ringKrullDim_quotient_eq_iff_height_eq Ieq hIeqne hqmin).mp hqdim
    -- `Ile ≤ Ieq ≤ q`
    have hIlele : Ile ≤ q := hsub.trans hqmin.1.2
    haveI : q.IsPrime := Ideal.minimalPrimes_isPrime hqmin
    haveI : (q : Ideal R).FiniteHeight :=
      ⟨Or.inr (by rw [hqht]; exact ENat.coe_ne_top C)⟩
    have hqIlemin : q ∈ Ile.minimalPrimes :=
      Ideal.mem_minimalPrimes_of_height_eq hIlele (by rw [hqht, hIleHt])
    refine ⟨hqIlemin, ?_⟩
    exact (ringKrullDim_quotient_eq_iff_height_eq Ile hIlene hqIlemin).mpr (by rw [hqht, hIleHt])

/-- **`quotTopDimSet (vanishingIdeal Σ^r) = topComponents`.** The exact-locus dimension-based top
components are the height-based `Σ̄^r` top components — the form the W1 keystone application
consumes. Composes `quotTopDimSet_sigma_eq_sweepSigma` (closed `=` exact) with
`quotTopDimSet_sigma_eq_topComponents` (closed `=` `topComponents`). -/
theorem quotTopDimSet_sweepSigma_eq_topComponents [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    quotTopDimSet (vanishingIdeal k (canonicalCoord d '' productRankLocus (k := k) d r))
      = topComponents (k := k) d r h := by
  rw [← quotTopDimSet_sigma_eq_sweepSigma d r h, quotTopDimSet_sigma_eq_topComponents d r h]

/-- **The W0 indexing bridge.** The closed rank-`≤ r` locus ideal `sigmaIdeal d r` and the exact
rank-`= r` locus ideal `vanishingIdeal (canonicalCoord d '' productRankLocus d r)` carry the same
top-dimensional minimal-prime count. The `ncard` corollary of the set equality
`quotTopDimSet_sigma_eq_sweepSigma`. -/
theorem ncard_topDimMinPrimes_sigma_eq_sweepSigma [IsAlgClosed k] [CharZero k]
    (d : Fin (N + 1) → ℕ) (r : ℕ) (h : (kostantPartitions d r).Nonempty) :
    (TopDimMinPrimes (MvPolynomial (RepCoord d) k ⧸ sigmaIdeal (k := k) d r)).ncard
      = (TopDimMinPrimes (MvPolynomial (RepCoord d) k
          ⧸ vanishingIdeal k (canonicalCoord d '' productRankLocus (k := k) d r))).ncard := by
  rw [ncard_topDimMinPrimes_quotient_eq, ncard_topDimMinPrimes_quotient_eq,
    quotTopDimSet_sigma_eq_sweepSigma d r h]

end DLNFibre.Core
