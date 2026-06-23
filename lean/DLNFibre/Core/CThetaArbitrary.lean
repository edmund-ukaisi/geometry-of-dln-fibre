import DLNFibre.Core.CThetaQIPConverse
import DLNFibre.Core.CThetaValue
import DLNFibre.Core.CThetaThetaBridge
import DLNFibre.Core.CThetaPermInvariance
import DLNFibre.Core.CTheta
import DLNFibre.Core.CCodimCornerMono

/-!
# Explicit closed-form `(C, θ)` for an arbitrary dimension vector

The closed forms `cValue` / `cTheta` (Lehalleur–Rimányi Thm 7.10) are stated for a **weakly
increasing** (`Monotone`) `d`. The permutation invariance of `(C, θ)` (perm-invariance expedition)
lets us drop that gate: every `d` agrees with its monotone rearrangement `d ∘ Tuple.sort d`, so the
closed form on the *sorted* vector computes `(C, θ)` of the *original* vector.

This module composes the merged sort bridge (`cCodim_comp_sort` / `numTop_comp_sort`,
`Mathlib.Tuple.monotone_sort`) with the `Monotone`-gated closed forms (`cCodim_eq_qipMin`,
`qipMin_eq_cValue`, `numTop_zero_eq_cTheta`) and the rank-shift (`cCodim_rankShift` /
`numTop_rankShift`) to give, for **arbitrary** `d`:

* `r = 0`:  `cCodim d 0 = cValue (d ∘ Tuple.sort d)`,  `numTop d 0 = cTheta (d ∘ Tuple.sort d)`;
* general `r ≤ d`:  `cCodim d r = cValue ((d − r) ∘ Tuple.sort (d − r))`, and likewise for
  `numTop` / `cTheta`.

The nonemptiness of the *sorted* Kostant set is discharged internally from `1 ≤ N` and `r ≤ d k`
(via `kostantPartitions_nonempty_of_le`); the abstract `(kostantPartitions d r).Nonempty` hypothesis
keeps the LHS clean, and the witness choice is free by proof irrelevance.

**Dependency rule:** `Core` only — never import `DLNFibre.DLN`.
-/

namespace DLNFibre.Core

open Finset

variable {N : ℕ}

/-! ## `r = 0`: the closed form on the sorted vector -/

/-- **Explicit `C` for arbitrary `d` (Thm 7.10, `r = 0`).** With no monotonicity gate, the
combinatorial codimension of the zero-product locus equals the closed form `cValue` evaluated on the
monotone rearrangement `d ∘ Tuple.sort d`. -/
theorem cCodim_zero_eq_cValue_comp_sort (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ)
    (h : (kostantPartitions d 0).Nonempty) :
    cCodim d 0 h = cValue (d ∘ _root_.Tuple.sort d) := by
  have hsorted_mono : Monotone (d ∘ _root_.Tuple.sort d) := _root_.Tuple.monotone_sort d
  have hr : ∀ k, (0 : ℕ) ≤ d k := fun _ ↦ Nat.zero_le _
  have hsorted_ne : (kostantPartitions (d ∘ _root_.Tuple.sort d) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ ↦ Nat.zero_le _)
  have hqip : (qipFeasible (d ∘ _root_.Tuple.sort d)).Nonempty :=
    (kostant_nonempty_iff_qipFeasible_nonempty (d ∘ _root_.Tuple.sort d) hsorted_mono).mp hsorted_ne
  rw [← cCodim_comp_sort d 0 hr hsorted_ne h,
    cCodim_eq_qipMin (d ∘ _root_.Tuple.sort d) hsorted_mono hsorted_ne hqip,
    qipMin_eq_cValue (d ∘ _root_.Tuple.sort d) hsorted_mono hqip]

/-- **Explicit `θ` for arbitrary `d` (Thm 7.10, `r = 0`).** The combinatorial top-component count of
the zero-product locus equals the closed form `cTheta` on the monotone rearrangement. -/
theorem numTop_zero_eq_cTheta_comp_sort (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ)
    (h : (kostantPartitions d 0).Nonempty) :
    numTop d 0 h = cTheta (d ∘ _root_.Tuple.sort d) := by
  have hsorted_mono : Monotone (d ∘ _root_.Tuple.sort d) := _root_.Tuple.monotone_sort d
  have hr : ∀ k, (0 : ℕ) ≤ d k := fun _ ↦ Nat.zero_le _
  have hsorted_ne : (kostantPartitions (d ∘ _root_.Tuple.sort d) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ ↦ Nat.zero_le _)
  rw [← numTop_comp_sort d 0 hr hsorted_ne h,
    numTop_zero_eq_cTheta (d ∘ _root_.Tuple.sort d) hsorted_mono hsorted_ne]

/-! ## General `r`: rank-shift to `r = 0` on `d − r` -/

/-- **Explicit `C` for arbitrary `d` at rank `r` (Thm 7.10).** The codimension of `Σ̄^r` equals
`cValue` on the sorted shifted vector `(d − r) ∘ sort`. The rank bound `r ≤ d k` is not assumed — it
is forced by the Kostant set being nonempty (`corner_le_dim_of_mem`). -/
theorem cCodim_eq_cValue_comp_sort (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    cCodim d r h = cValue (dminus d r ∘ _root_.Tuple.sort (dminus d r)) := by
  have hr : ∀ k, r ≤ d k := fun k ↦ corner_le_dim_of_mem h.choose_spec k
  have h₀ : (kostantPartitions (dminus d r) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ ↦ Nat.zero_le _)
  rw [← cCodim_rankShift hr h₀ h, cCodim_zero_eq_cValue_comp_sort hN (dminus d r) h₀]

/-- **Explicit `θ` for arbitrary `d` at rank `r` (Thm 7.10).** The top-component count of `Σ̄^r`
equals `cTheta` on the sorted shifted vector `(d − r) ∘ sort`. The rank bound `r ≤ d k` is not
assumed — it is forced by the Kostant set being nonempty (`corner_le_dim_of_mem`). -/
theorem numTop_eq_cTheta_comp_sort (hN : 1 ≤ N) (d : Fin (N + 1) → ℕ) (r : ℕ)
    (h : (kostantPartitions d r).Nonempty) :
    numTop d r h = cTheta (dminus d r ∘ _root_.Tuple.sort (dminus d r)) := by
  have hr : ∀ k, r ≤ d k := fun k ↦ corner_le_dim_of_mem h.choose_spec k
  have h₀ : (kostantPartitions (dminus d r) 0).Nonempty :=
    kostantPartitions_nonempty_of_le hN (fun _ ↦ Nat.zero_le _)
  rw [← numTop_rankShift hr h₀ h, numTop_zero_eq_cTheta_comp_sort hN (dminus d r) h₀]

/-! ## Witness — a genuinely NON-monotone `d`

`d = ![2,3,2]` is not weakly increasing (`d 1 = 3 > 2 = d 2`), so the `Monotone`-gated closed forms
do not apply to it directly; the sort bridge is doing real work. The arbitrary-`d` theorems compute
`(C, θ)` of `![2,3,2]` as the closed form on its monotone rearrangement `![2,2,3]` (the swap
`(1 2)`), giving `(C, θ) = (4, 2)` — matching the permutation-invariance expedition's value.

`Tuple.sort` is not kernel-reducible (it routes through `Multiset.sort`), so the closed-form values
on the sorted vector are computed by first rewriting `![2,3,2] ∘ sort ![2,3,2]` to the concrete
monotone `![2,2,3]` via the sort-uniqueness characterization, then `decide +kernel`. -/

section Witness

/-- The genuinely non-monotone dimension vector `(2,3,2)` (`d 1 = 3 > 2 = d 2`). -/
abbrev d232 : Fin 3 → ℕ := ![2, 3, 2]

/-- `(2,3,2)` is NOT weakly increasing — the `Monotone` closed-form gate fails on it. -/
theorem not_monotone_d232 : ¬ Monotone d232 := by
  intro h; have := h (show (1 : Fin 3) ≤ 2 by decide); simp [d232] at this

/-- The Kostant set of `(2,3,2)` with corner `0` is nonempty (from `1 ≤ N` and `0 ≤ d`). -/
theorem kostantPartitions_d232_nonempty : (kostantPartitions d232 0).Nonempty :=
  kostantPartitions_nonempty_of_le (by norm_num) (fun _ ↦ Nat.zero_le _)

/-- The swap `(1 2)` sorts `(2,3,2)` to the monotone `(2,2,3)`. -/
theorem d232_comp_swap : d232 ∘ (Equiv.swap 1 2) = ![2, 2, 3] := by decide

/-- `d232 ∘ Tuple.sort d232 = ![2,2,3]`: the monotone rearrangement is `(2,2,3)`, via sort
uniqueness (`comp_sort_eq_comp_iff_monotone`) applied to the swap `(1 2)`. -/
theorem d232_comp_sort : d232 ∘ _root_.Tuple.sort d232 = ![2, 2, 3] := by
  have hmono : Monotone (d232 ∘ (Equiv.swap 1 2)) := by rw [d232_comp_swap]; decide
  rw [← _root_.Tuple.comp_sort_eq_comp_iff_monotone.mpr hmono, d232_comp_swap]

/-- **Non-monotone witness, `C`.** `cCodim ![2,3,2] 0 = cValue (![2,3,2] ∘ sort)`, an instance of
`cCodim_zero_eq_cValue_comp_sort` on a non-monotone vector — the sort bridge fires. -/
theorem cCodim_d232_eq_cValue_comp_sort :
    cCodim d232 0 kostantPartitions_d232_nonempty = cValue (d232 ∘ _root_.Tuple.sort d232) :=
  cCodim_zero_eq_cValue_comp_sort (by norm_num) d232 _

/-- **Non-monotone witness, `θ`.** `numTop ![2,3,2] 0 = cTheta (![2,3,2] ∘ sort)`, an instance of
`numTop_zero_eq_cTheta_comp_sort` on a non-monotone vector. -/
theorem numTop_d232_eq_cTheta_comp_sort :
    numTop d232 0 kostantPartitions_d232_nonempty = cTheta (d232 ∘ _root_.Tuple.sort d232) :=
  numTop_zero_eq_cTheta_comp_sort (by norm_num) d232 _

/-- **`(2,3,2)`, `r = 0`: `C = 4`** (Kostant side, kernel `decide`). -/
theorem cCodim_d232_zero : cCodim d232 0 kostantPartitions_d232_nonempty = 4 := by decide +kernel

/-- **`(2,3,2)`, `r = 0`: `θ = 2`** (Kostant side, kernel `decide`). -/
theorem numTop_d232_zero : numTop d232 0 kostantPartitions_d232_nonempty = 2 := by decide +kernel

/-- **Closed form on the sorted vector: `cValue (![2,3,2] ∘ sort) = 4`.** Rewrite to the monotone
`(2,2,3)`, then kernel `decide`. -/
theorem cValue_d232_comp_sort : cValue (d232 ∘ _root_.Tuple.sort d232) = 4 := by
  rw [d232_comp_sort]; decide +kernel

/-- **Closed form on the sorted vector: `cTheta (![2,3,2] ∘ sort) = 2`.** -/
theorem cTheta_d232_comp_sort : cTheta (d232 ∘ _root_.Tuple.sort d232) = 2 := by
  rw [d232_comp_sort]; decide +kernel

end Witness

end DLNFibre.Core
