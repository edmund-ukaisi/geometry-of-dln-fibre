/-
Copyright (c) 2026. Released under Apache 2.0; see LICENSE.
-/
import DLNFibre.Core.FibreBundleLocallyTrivialFull
import DLNFibre.Core.RankLocusClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# `DLNFibre.Core.FibreRankBridge` — the prime/residue-field rank bridge (S1 keystone)

The scheme-level identity that the rank-`= r` open `rankROpen` of `Spec (sweepSigmaRing k d r)` is
exactly the locus where the universal product matrix has rank `= r` over the residue field
`κ(P) = P.asIdeal.ResidueField`. Precisely, for a prime `P`:

> `P ∈ rankROpen d r  ↔  (universal matrix over κ(P)).rank = r`.

This closes the gap the `rankROpen` docstring flags (only the point-set forward inclusion
`sweepSigma_subset_chartOpen` was banked).

## The two inputs (one banked, one re-proved here)

- **`≥` direction** (`P ∈ rankROpen ⟹ rank over κ(P) ≥ r`): some pivot minor `chartDsigAt s t ∉ P`,
  so its image in `κ(P)` is nonzero, so that `r × r` minor of the matrix over `κ(P)` is invertible
  (a field), so `rank ≥ r` (`Matrix.rank_of_isUnit` + `rank_submatrix_le_rank`).
- **`≤` direction** (always, over every prime `P`): the `(r+1)`-minors of the universal matrix
  vanish in `sweepSigmaRing` (rank `≤ r` is baked into `Σ̄^r`), hence in `κ(P)`, so `rank ≤ r`
  (`rank_le_iff_forall_submatrix_det_eq_zero`, the banked over-field minor criterion from
  `Core.RankLocusClosed`). The vanishing is re-proved directly on `sweepSigma` here.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Matrix MvPolynomial

-- `rankROpen` (in `FibreBundleLocallyTrivialFull`) is fixed at `k : Type` with `[Infinite k]`, so
-- the bridge that mentions it shares those constraints. The non-`rankROpen` lemmas are stated at
-- the same constraints for a single variable block (they do not use `[Infinite k]`).
variable {k : Type} [Field k] [Infinite k] {N : ℕ}

/-! ## The universal matrix over the residue field κ(P) -/

/-- **The residue map** `MvPolynomial (RepCoord d) k →+* κ(P)` at a prime `P` of the chart-closure
ring: the quotient map to `sweepSigmaRing` followed by the residue-field algebra map. The
`(s, t)` pivot minor's det maps to the residue class of `chartDsigAt s t`. -/
noncomputable def residueMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    MvPolynomial (RepCoord d) k →+* P.asIdeal.ResidueField :=
  (algebraMap (sweepSigmaRing k d r) P.asIdeal.ResidueField).comp
    (Ideal.Quotient.mk (vanishingIdeal k (sweepSigma k d r)))

/-- **The universal product matrix over κ(P).** The generic product matrix `Matrix.of (multPoly d)`
with entries pushed into the residue field of the prime `P`. -/
noncomputable def universalMatrixResidue (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    Matrix (Fin (d (Fin.last (N + 1)))) (Fin (d 0)) P.asIdeal.ResidueField :=
  (Matrix.of (multPoly d)).map (residueMap d r P)

omit [Infinite k] in
/-- **A square minor of the universal matrix over `κ(P)` is `residueMap` of the polynomial minor.**
The general identity feeding both the `≤` and the `≥` directions: for finite selectors `br, bc` of
any common arity, the minor det of `universalMatrixResidue` is the residue map applied to the
corresponding polynomial minor det of `Matrix.of (multPoly d)`. -/
theorem det_submatrix_universalMatrixResidue_eq_residueMap (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (br : ι → Fin (d (Fin.last (N + 1)))) (bc : ι → Fin (d 0)) :
    ((universalMatrixResidue d r P).submatrix br bc).det
      = residueMap d r P (((Matrix.of (multPoly d)).submatrix br bc).det) := by
  -- map and submatrix commute; det commutes with the ring hom `residueMap`.
  rw [universalMatrixResidue, Matrix.submatrix_map, RingHom.map_det, RingHom.mapMatrix_apply]

omit [Infinite k] in
/-- The `(s, t)` minor det of the universal matrix over `κ(P)` is the residue-field class of the
pivot chart element `chartDsigAt s t`. -/
theorem det_submatrix_universalMatrixResidue (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)) :
    ((universalMatrixResidue d r P).submatrix s t).det
      = algebraMap (sweepSigmaRing k d r) P.asIdeal.ResidueField (chartDsigAt d r s t) := by
  -- the general minor identity; `residueMap = algebraMap ∘ mk` and `chartDsigAt = mk (ΔPdeepAt)`.
  rw [det_submatrix_universalMatrixResidue_eq_residueMap d r P s t]
  rfl

/-! ## The `≤` direction: rank over κ(P) is always `≤ r` -/

omit [Infinite k] in
/-- **The `(r+1)`-minors of the universal matrix vanish in `sweepSigmaRing`.** Every `(r+1) × (r+1)`
minor of `Matrix.of (multPoly d)` lies in the vanishing ideal of `sweepSigma` (rank `= r ≤ r` on the
locus), so its class in `sweepSigmaRing` is zero. -/
theorem det_submatrix_multPoly_mem_vanishingIdeal_sweepSigma (d : Fin (N + 2) → ℕ) (r : ℕ)
    (er : Fin (r + 1) → Fin (d (Fin.last (N + 1)))) (ec : Fin (r + 1) → Fin (d 0)) :
    ((Matrix.of (multPoly d)).submatrix er ec).det
      ∈ vanishingIdeal k (sweepSigma k d r) := by
  rw [mem_vanishingIdeal_iff]
  rintro x ⟨A, hA, rfl⟩
  rw [mem_productRankLocus] at hA
  -- `aeval = eval`, then the generic minor evaluates to the actual `(r+1)`-minor of `mult A`.
  rw [show aeval (R := k) (canonicalCoord d A)
        ((Matrix.of (multPoly d)).submatrix er ec).det
        = eval (canonicalCoord d A) ((Matrix.of (multPoly d)).submatrix er ec).det from by
        rw [aeval_def, eval]; rfl,
    eval_det_submatrix_multPoly d A er ec]
  exact submatrix_det_eq_zero_of_rank_le (le_of_eq hA) er ec

omit [Infinite k] in
/-- **The rank over κ(P) is always `≤ r`.** For every prime `P`, the universal matrix over the
residue field has rank `≤ r`: its `(r+1)`-minors vanish (the previous lemma pushed into `κ(P)`),
so the banked over-field minor criterion gives `rank ≤ r`. -/
theorem rank_universalMatrixResidue_le (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    (universalMatrixResidue d r P).rank ≤ r := by
  rw [rank_le_iff_forall_submatrix_det_eq_zero]
  intro er ec
  -- the `(r+1)`-minor over `κ(P)` is `residueMap` of the polynomial minor, which lies in
  -- `ker mk = vanishingIdeal (sweepSigma)`, so `mk` (and hence `residueMap`) kills it.
  rw [det_submatrix_universalMatrixResidue_eq_residueMap d r P er ec, residueMap,
    RingHom.comp_apply,
    (Ideal.Quotient.eq_zero_iff_mem).mpr
      (det_submatrix_multPoly_mem_vanishingIdeal_sweepSigma d r er ec),
    map_zero]

/-! ## The `≥` direction: membership in `rankROpen` forces rank `≥ r` -/

omit [Infinite k] in
/-- **A pivot minor outside `P` forces rank `≥ r` over κ(P).** If `chartDsigAt s t ∉ P` then its
residue-field image is a nonzero element of the field `κ(P)`, so the `(s, t)` minor of the universal
matrix over `κ(P)` is invertible, whence rank `≥ r`. -/
theorem r_le_rank_universalMatrixResidue_of_notMem (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r))
    (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0))
    (hst : chartDsigAt d r s t ∉ P.asIdeal) :
    r ≤ (universalMatrixResidue d r P).rank := by
  -- the `(s, t)` minor det over `κ(P)` is the residue-field image of `chartDsigAt s t`,
  -- which is nonzero (chart membership), hence a unit in the field `κ(P)`.
  have hdet : ((universalMatrixResidue d r P).submatrix s t).det ≠ 0 := by
    rw [det_submatrix_universalMatrixResidue d r P s t]
    exact fun h ↦ hst (Ideal.algebraMap_residueField_eq_zero.mp h)
  have hunit : IsUnit ((universalMatrixResidue d r P).submatrix s t).det :=
    isUnit_iff_ne_zero.mpr hdet
  -- a unit-det square minor has full rank `r`; a submatrix's rank is `≤` the matrix's rank.
  have hsq : ((universalMatrixResidue d r P).submatrix s t).rank = r := by
    rw [Matrix.rank_of_isUnit _ ((Matrix.isUnit_iff_isUnit_det _).mpr hunit), Fintype.card_fin]
  calc r = ((universalMatrixResidue d r P).submatrix s t).rank := hsq.symm
    _ ≤ (universalMatrixResidue d r P).rank :=
        rank_submatrix_le_rank (universalMatrixResidue d r P) s t

omit [Infinite k] in
/-- **`rankROpen` membership unfolds to a non-vanishing pivot minor.** A prime `P` lies in the
rank-`= r` open iff some pivot minor `chartDsigAt s t` is not in `P` — the complement of the
common-vanishing locus of the pivot minors. -/
theorem mem_rankROpen_iff_exists_notMem (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    P ∈ rankROpen (k := k) d r
      ↔ ∃ (s : Fin r → Fin (d (Fin.last (N + 1)))) (t : Fin r → Fin (d 0)),
          chartDsigAt d r s t ∉ P.asIdeal := by
  -- the banked cover identity: `rankROpen` is the union of the pivot principal opens.
  rw [← iSup_pivot_basicOpen_eq_rankROpen, Set.mem_iUnion]
  refine ⟨?_, ?_⟩
  · rintro ⟨st, hst⟩
    exact ⟨st.1, st.2, (PrimeSpectrum.mem_basicOpen _ _).mp hst⟩
  · rintro ⟨s, t, hst⟩
    exact ⟨(s, t), (PrimeSpectrum.mem_basicOpen _ _).mpr hst⟩

/-! ## The bridge -/

omit [Infinite k] in
/-- **The prime/residue-field rank bridge (S1 keystone).** For a prime `P` of the chart-closure ring
`sweepSigmaRing k d r`, membership in the rank-`= r` open `rankROpen` is equivalent to the universal
product matrix, evaluated over the residue field `κ(P)`, having rank exactly `r`. Since rank `≤ r`
holds for every prime (`rank_universalMatrixResidue_le`, rank `≤ r` baked into `Σ̄^r`), this also
reads as `rankROpen = {P | rank over κ(P) = r}` as a set of primes. -/
theorem mem_rankROpen_iff_rank_universalMatrixResidue_eq (d : Fin (N + 2) → ℕ) (r : ℕ)
    (P : PrimeSpectrum (sweepSigmaRing k d r)) :
    P ∈ rankROpen (k := k) d r ↔ (universalMatrixResidue d r P).rank = r := by
  rw [mem_rankROpen_iff_exists_notMem]
  constructor
  · -- some pivot minor ∉ P ⟹ rank ≥ r; with the automatic rank ≤ r, rank = r.
    rintro ⟨s, t, hst⟩
    exact le_antisymm (rank_universalMatrixResidue_le d r P)
      (r_le_rank_universalMatrixResidue_of_notMem d r P s t hst)
  · -- rank = r ⟹ some pivot minor ∉ P.
    intro hrk
    -- `r = 0`: the empty pivot minor is `chartDsigAt = mk (det of 0×0) = 1 ∉ P` (proper ideal).
    rcases r with _ | m
    · refine ⟨Fin.elim0, Fin.elim0, ?_⟩
      -- the `0 × 0` minor polynomial det is `1`, so its class `chartDsigAt = 1 ∉ P` (proper ideal).
      have hdet1 : ΔPdeepAt (k := k) d 0 Fin.elim0 Fin.elim0 = 1 := by
        rw [ΔPdeepAt]; exact Matrix.det_isEmpty
      have h1 : chartDsigAt (k := k) d 0 Fin.elim0 Fin.elim0 = 1 := by
        rw [chartDsigAt, hdet1, map_one]
      rw [h1]
      exact fun h ↦ P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top h
    · -- `r = m+1 ≥ 1`: if every `(m+1) × (m+1)` pivot minor were in `P`, all minor dets over
      -- `κ(P)` would vanish, forcing rank `≤ m < m+1`, contradicting `rank = m+1`.
      by_contra hcon
      push Not at hcon
      have hzero : ∀ (s : Fin (m + 1) → Fin (d (Fin.last (N + 1))))
          (t : Fin (m + 1) → Fin (d 0)),
          ((universalMatrixResidue d (m + 1) P).submatrix s t).det = 0 := fun s t ↦ by
        rw [det_submatrix_universalMatrixResidue d (m + 1) P s t]
        exact Ideal.algebraMap_residueField_eq_zero.mpr (hcon s t)
      have hle : (universalMatrixResidue d (m + 1) P).rank ≤ m := by
        rw [rank_le_iff_forall_submatrix_det_eq_zero]; exact hzero
      omega

end DLNFibre.Core
