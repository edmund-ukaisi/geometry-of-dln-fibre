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

/-- On `Fin 1` (a single vertex), the only Kostant partition is `m (0,0) = d 0`. -/
theorem kostantAll_zero_eq (d : Fin 1 → ℕ) :
    kostantAll d = {fun _ ↦ d 0} := by
  have fin01 : ∀ i : Fin (0 + 1), i = 0 := fun i ↦ by omega
  have prod01 : ∀ b : Fin (0 + 1) × Fin (0 + 1), b = (0, 0) := fun b ↦
    Prod.ext (fin01 b.1) (fin01 b.2)
  have hsum : ∀ (f : Fin (0 + 1) × Fin (0 + 1) → ℕ),
      ∑ p ∈ Finset.univ.filter (fun p : Fin (0 + 1) × Fin (0 + 1) ↦
        p.1 ≤ (0 : Fin (0 + 1)) ∧ (0 : Fin (0 + 1)) ≤ p.2), f p = f (0, 0) := by
    intro f
    rw [Finset.sum_eq_single (0, 0)]
    · intro b _ hb; exact absurd (prod01 b) hb
    · intro hmem
      exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, le_refl _, le_refl _⟩) hmem
  ext m
  rw [Finset.mem_singleton, mem_kostantAll]
  constructor
  · rintro ⟨-, -, hk⟩
    have hk0 := hk 0
    rw [kostantAt, hsum] at hk0
    funext p
    rw [prod01 p]
    exact hk0.symm
  · rintro rfl
    refine ⟨fun p ↦ ?_, fun p hp ↦ ?_, fun k ↦ ?_⟩
    · change d 0 ≤ d p.1; rw [fin01 p.1]
    · exact absurd (le_of_eq ((fin01 p.1).trans (fin01 p.2).symm)) hp
    · rw [kostantAt, fin01 k, hsum]

/-- **Thm 5.6 base case** (`N = 0`): `fivegonSum d = Pmult d` — the single partition contributes
`X^0 · P (d 0) = P (d 0) = Pmult d`. -/
theorem fivegon_base (d : Fin 1 → ℕ) : fivegonSum d = Pmult d := by
  rw [fivegonSum, kostantAll_zero_eq, Finset.sum_singleton]
  have hcf : codimForm 0 (extendℤ (fun _ : Fin 1 × Fin 1 ↦ d 0)) = 0 := by
    rw [codimForm, show Finset.Icc (1 : ℤ) ((0 : ℕ) : ℤ) = ∅ from by decide, Finset.sum_empty]
  rw [hcf, Int.toNat_zero, pow_zero, one_mul, Pm, Pmult, Fin.prod_univ_one,
    show upperPairs 0 = {(0, 0)} from by decide, Finset.prod_singleton]

/-! ## The peeling step (`N+1`): merge the last vertex's column

`peelPart m` drops the last vertex `Fin.last (N+1)` by merging its column into column `N`
(`m'_{i,N} = m_{i,N} + m_{i,N+1}`); columns `j < N` are untouched. This is the `m'` of the
bijection `kostantAll d ↔ Σ_{m'} (last-column data)`. -/

/-- The forward peel map: `m' = peelPart m` on `Fin (N+1)` merges `m`'s columns `N` and `N+1`. -/
def peelPart (m : Fin (N + 2) × Fin (N + 2) → ℕ) : Fin (N + 1) × Fin (N + 1) → ℕ :=
  fun p ↦ p.2.lastCases
    (m (p.1.castSucc, (Fin.last N).castSucc) + m (p.1.castSucc, Fin.last (N + 1)))
    (fun J₀ ↦ m (p.1.castSucc, J₀.castSucc.castSucc))

end DLNFibre.Core
