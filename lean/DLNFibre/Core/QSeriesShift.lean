import DLNFibre.Core.QSeriesFivegon

/-!
# `DLNFibre.Core.QSeriesShift` — the corner shift (S1') and the corner expansion (S2)

The first leg of Thm 5.5 (M4). On the LANDED corner-dropping bijection (`CTheta.dropCorner` +
`codimForm_update_corner`), the corner-graded generating function lifts:

* **S1' (corner shift):** `Qseries d s = P s · Qseries (d − s) 0` (for `0 ≤ s ≤ min d`). A
  `Finset.sum_bij` over `dropCorner`: the `codimForm` exponent is corner-blind, and the `Pm`-factor
  splits as `Pm N m = P s · Pm N (dropCorner m)` (the single `(0,N)` factor `P s` vs `P 0 = 1`).
* **Range-gap:** `Qseries d r = 0` for `min d < r` (a corner `m (0,N) = r` forces `d_k ≥ r` at every
  vertex, so `kostantPartitions d r = ∅`).
* **S2 (corner expansion):** `Pmult d = ∑_{s=0}^{min d} P s · Qseries (d − s) 0` — rewrite the
  LANDED fivegon `∑_{s} Qseries d s = Pmult d` by S1' and drop the zero gap terms.

`min d` is `minDim d := ⊓' d` over `Fin (N+1)` (nonempty).
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- The minimum coordinate of a dimension vector `d` (the `Finset.inf'` over the nonempty
`Fin (N+1)`). This is the paper's `min d`, the top of the corner range. -/
noncomputable def minDim (d : Fin (N + 1) → ℕ) : ℕ := Finset.univ.inf' Finset.univ_nonempty d

/-- `minDim d ≤ d k` at every vertex. -/
theorem minDim_le (d : Fin (N + 1) → ℕ) (k : Fin (N + 1)) : minDim d ≤ d k :=
  Finset.inf'_le _ (Finset.mem_univ k)

/-- `minDim` is attained at some vertex. -/
theorem exists_minDim_eq (d : Fin (N + 1) → ℕ) : ∃ k, minDim d = d k := by
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty d
  exact ⟨k, hk⟩

/-- `minDim` commutes with the pointwise shift: `minDim (d − s) = minDim d − s` (ℕ truncation; holds
for all `s` — when `s > minDim d` both sides are `0`). -/
theorem minDim_dminus (d : Fin (N + 1) → ℕ) (s : ℕ) : minDim (dminus d s) = minDim d - s := by
  unfold minDim dminus
  refine le_antisymm ?_ ?_
  · obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty d
    exact (Finset.inf'_le _ (Finset.mem_univ k)).trans_eq (by rw [hk])
  · refine Finset.le_inf' _ _ (fun k _ ↦ ?_)
    have : Finset.univ.inf' Finset.univ_nonempty d ≤ d k := Finset.inf'_le _ (Finset.mem_univ k)
    omega

/-- **`Pm` factors off its corner:** `Pm N m = P (m (0, last N)) · Pm N (dropCorner m)`. The corner
`(0, last N) ∈ upperPairs N`; `dropCorner m` agrees with `m` off the corner and is `0` there
(`P 0 = 1`). -/
theorem Pm_dropCorner (m : Fin (N + 1) × Fin (N + 1) → ℕ) :
    Pm N m = P (m (0, Fin.last N)) * Pm N (dropCorner m) := by
  have hcorner : ((0 : Fin (N + 1)), Fin.last N) ∈ upperPairs N := by
    simp only [upperPairs, Finset.mem_filter, Finset.mem_univ, true_and, Fin.le_def, Fin.val_zero]
    exact Nat.zero_le _
  rw [Pm, Pm, ← Finset.mul_prod_erase (upperPairs N) (fun p ↦ P (m p)) hcorner,
    ← Finset.mul_prod_erase (upperPairs N) (fun p ↦ P (dropCorner m p)) hcorner]
  rw [dropCorner, Function.update_self, P_zero, one_mul]
  congr 1
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]

/-- **S1' — the corner shift** (paper Lemma 5.7 "add-longest"):
`Qseries d s = P s · Qseries (d − s) 0` for `s ≤ d k` at every vertex. A `Finset.sum_bij` over the
LANDED `dropCorner` bijection: the exponent is corner-blind (`codimForm_update_corner`) and the
`Pm`-factor sheds `P s` (`Pm_dropCorner`). -/
theorem Qseries_corner_shift (d : Fin (N + 1) → ℕ) (s : ℕ) (hs : ∀ k, s ≤ d k) :
    Qseries d s = P s * Qseries (dminus d s) 0 := by
  rw [Qseries, Qseries, kostantPartitions_dminus_eq_image hs,
    Finset.sum_image (fun m₁ hm₁ m₂ hm₂ ↦ dropCorner_injOn hm₁ hm₂), Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  -- corner-blind exponent + the Pm corner factor `P s`
  have hcorner : m (0, Fin.last N) = s := (mem_kostantPartitions.mp hm).2.2.2
  have hcodim : codimForm N (extendℤ (dropCorner m)) = codimForm N (extendℤ m) :=
    codimForm_update_corner m 0
  rw [hcodim, Pm_dropCorner m, hcorner]
  ring

/-- A Kostant partition with corner `r` forces `r ≤ d k` at every vertex: the corner `(0, last N)`
covers `k`, so `r = m (0, last N) ≤ ∑_{filter k} m = d k`. -/
theorem corner_le_of_mem {d : Fin (N + 1) → ℕ} {r : ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ}
    (hm : m ∈ kostantPartitions d r) (k : Fin (N + 1)) : r ≤ d k := by
  obtain ⟨_, _, hk, hcorner⟩ := mem_kostantPartitions.mp hm
  rw [← hcorner, hk k]
  exact Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) (corner_mem_filter k)

/-- **Range-gap:** `Qseries d r = 0` for `minDim d < r`. A corner `r > minDim d` is unattainable —
`kostantPartitions d r` is empty (the corner would force `d_k ≥ r` at the minimising vertex). -/
theorem Qseries_eq_zero_of_min_lt (d : Fin (N + 1) → ℕ) {r : ℕ} (hr : minDim d < r) :
    Qseries d r = 0 := by
  rw [Qseries, Finset.sum_eq_zero]
  intro m hm
  obtain ⟨k, hk⟩ := exists_minDim_eq d
  have hle := corner_le_of_mem hm k
  omega

/-- **S2 — the corner expansion:** `Pmult d = ∑_{s=0}^{min d} P s · Qseries (d − s) 0`. From the
LANDED fivegon `∑_{s ∈ range (d 0 + 1)} Qseries d s = Pmult d`: each `s ≤ min d` rewrites by S1',
and the gap terms `min d < s ≤ d 0` vanish (range-gap). -/
theorem Pmult_eq_sum_corner (d : Fin (N + 1) → ℕ) :
    Pmult d = ∑ s ∈ Finset.range (minDim d + 1), P s * Qseries (dminus d s) 0 := by
  rw [← sum_Qseries_eq_Pmult]
  -- first collapse the fivegon range `d 0 + 1` to `min d + 1` (gap terms vanish)
  have hgap : ∑ r ∈ Finset.range (d 0 + 1), Qseries d r
      = ∑ r ∈ Finset.range (minDim d + 1), Qseries d r := by
    refine (Finset.sum_subset (Finset.range_subset_range.mpr (Nat.succ_le_succ (minDim_le d 0)))
      (fun r _ hr' ↦ ?_)).symm
    rw [Finset.mem_range, Nat.lt_succ_iff, not_le] at hr'
    exact Qseries_eq_zero_of_min_lt d hr'
  rw [hgap]
  -- then rewrite each surviving term by S1'
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  rw [Finset.mem_range, Nat.lt_succ_iff] at hs
  exact Qseries_corner_shift d s (fun k ↦ hs.trans (minDim_le d k))

end DLNFibre.Core
