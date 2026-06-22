import DLNFibre.Core.QSeriesPeel
import DLNFibre.Core.QSeriesExtraction

/-!
# `DLNFibre.Core.QSeriesFivegon` — Thm 5.6 (the "5gon"), M3b

The 5gon identity (= RWY 2018, reproved zero-cited): over `ℤ⟦X⟧`,

`Pmult d = ∑_{m ∈ kostantAll d} X^{(codimForm (extendℤ m)).toNat} · Pm m`,

the sum over **all** Kostant partitions of `d` (any corner). Proved by the PEEL induction on the
number of vertices `N`, with the last-column transfer collapsing via `transferRHS_eq` (M3a, iterated
`durfee`). This file: the `kostantAll` object + the generating sum `fivegonSum` + its membership and
non-negativity foundation. The peeling induction (the bijection + `codimForm`/`Pm` split) follows.
-/

namespace DLNFibre.Core

open PowerSeries Finset

variable {N : ℕ}

/-- **All Kostant partitions of `d`** (any corner): like `kostantPartitions d r` but without the
corner constraint `m (0, last) = r`. -/
def kostantAll (d : Fin (N + 1) → ℕ) : Finset (Fin (N + 1) × Fin (N + 1) → ℕ) :=
  (Fintype.piFinset (fun p : Fin (N + 1) × Fin (N + 1) ↦
      if p.1 ≤ p.2 then Finset.range (d p.1 + 1) else Finset.range 1)).filter
    (fun m ↦ ∀ k, kostantAt d m k)

/-- Membership in `kostantAll`, unfolded (bounded `m_{ij} ≤ d_i`, supported on `i ≤ j`, Kostant at
every vertex). -/
theorem mem_kostantAll {d : Fin (N + 1) → ℕ} {m : Fin (N + 1) × Fin (N + 1) → ℕ} :
    m ∈ kostantAll d ↔
      (∀ p : Fin (N + 1) × Fin (N + 1), m p ≤ d p.1)
        ∧ (∀ p : Fin (N + 1) × Fin (N + 1), ¬ p.1 ≤ p.2 → m p = 0)
        ∧ (∀ k, kostantAt d m k) := by
  unfold kostantAll
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hpi, hk⟩
    refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, hk⟩
    · have := hpi p; split_ifs at this with h
      · simpa [Nat.lt_succ_iff] using this
      · simp only [Finset.mem_range, Nat.lt_one_iff] at this; omega
    · have := hpi p; rw [if_neg hp] at this
      simpa [Nat.lt_one_iff] using this
  · rintro ⟨hb, hs, hk⟩
    refine ⟨fun p ↦ ?_, hk⟩
    split_ifs with h
    · simp only [Finset.mem_range, Nat.lt_succ_iff]; exact hb p
    · simp only [Finset.mem_range, Nat.lt_one_iff]; exact hs p h

/-- `kostantAll` is the disjoint union of the corner-graded `kostantPartitions d r` — the corner
`m (0, last)` is determined by `m`, so each `m ∈ kostantAll` lies in exactly one `kostantPartitions`. -/
theorem kostantPartitions_subset_kostantAll {d : Fin (N + 1) → ℕ} {r : ℕ} :
    kostantPartitions d r ⊆ kostantAll d := by
  intro m hm
  rw [mem_kostantPartitions] at hm
  rw [mem_kostantAll]
  exact ⟨hm.1, hm.2.1, hm.2.2.1⟩

/-- The **Thm 5.6 generating function**: `∑_{m ∈ kostantAll d} X^{codimForm} · Pm m`. -/
noncomputable def fivegonSum (d : Fin (N + 1) → ℕ) : ℤ⟦X⟧ :=
  ∑ m ∈ kostantAll d, (X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m

/-- `fivegonSum` has non-negative coefficients (a sum of `X^c · Pm m`, each non-negative — M1). -/
theorem nonnegCoeffs_fivegonSum (d : Fin (N + 1) → ℕ) : NonnegCoeffs (fivegonSum d) := by
  intro n
  rw [fivegonSum, map_sum]
  refine Finset.sum_nonneg fun m _ ↦ ?_
  have : NonnegCoeffs ((X : ℤ⟦X⟧) ^ (codimForm N (extendℤ m)).toNat * Pm N m) := by
    refine NonnegCoeffs.mul (fun j ↦ ?_) (nonnegCoeffs_Pm m)
    rw [coeff_X_pow]; split_ifs <;> norm_num
  exact this n

end DLNFibre.Core
